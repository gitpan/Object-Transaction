
# Copyright (C) 1999, Internet Journals Corporation <www.bepress.com>.   
# All rights reserved.  License hearby granted for anyone to use this 
# module at their own risk.   Please feed useful changes back to 
# David Muir Sharnoff <muir@idiom.com>.

package Object::Transaction;

$VERSION = 0.95;
my $magic_cookie = "O:Ta";
my $lock_debugging = 0;

require File::Flock;
use Storable;
use POSIX qw(O_CREAT O_RDWR);
require File::Sync;
use Carp;

require Exporter;
@ISA = qw(Exporter);
@EXPORT = qw(transaction commit abandon);

use strict;

# things to override

sub new { die "deferred" }
sub file { die "deferred" }
sub presave {}
sub postsave {}
sub postload {}
sub preload {}
sub preremove {}
sub postremove {}
sub id 
{
	my ($this) = @_;
	return $this->{'ID'};
}
sub precommit {}

# a few wrappers

my %locks;

sub _lock
{
	my ($file) = @_;
	if ($lock_debugging) {
		my ($package, $filename, $line) = caller;
		my ($package2, $filename2, $line2) = caller(1);
		print STDERR "\n{{{{ $file $line, $line2";
	}
	$locks{$file} = 1;
	File::Flock::lock($file);
}

sub _unlock
{
	my ($file) = @_;
	if ($lock_debugging) {
		my ($package, $filename, $line) = caller;
		my ($package2, $filename2, $line2) = caller(1);
		print STDERR "\n}}}} $file $line, $line2";
	}
	delete $locks{$file};
	File::Flock::unlock($file);
}

sub _unlock_all
{
	for my $f (keys %locks) {
		_unlock($f);
	}
}

sub _read_file
{
	my ($file) = @_;

	no strict;

	my $r;
	my (@r);

	local(*F);
	open(F, "<$file") || die "open $file: $!";
	@r = <F>;
	close(F);

	return join("",@r);
}

sub _write_file
{
	my ($f, @data) = @_;

	no strict;

	local(*F,*O);
	open(F, ">$f") || die "open >$f: $!";
	$O = select(F);
	$| = 1;
	select($O);
	(print F @data) || die "write $f: $!";
	File::Sync::fsync_fd(fileno(F)) || die "fsync $f: $!";
	close(F) || die "close $f: $!";
	return 1;
}

# now the meat

my %cache;
use vars qw($commit_inprogress);
$commit_inprogress = 0;

sub load
{
	my ($package, $baseid) = @_;

	if (exists $cache{$package}{$baseid}) {
		return $cache{$package}{$baseid};
	}

	my $newid = $package->preload($baseid);

	if ($newid && exists $cache{$package}{$newid}) {
		return $cache{$package}{$newid};
	}

	my $id = $newid || $baseid;

	return undef unless $id;

	my $file = $package->file($id);

	return undef unless -e $file;
	_lock $file;
	my $frozen = _read_file($file);
	{
		no re 'taint';
		$frozen =~ m/^\Q$magic_cookie\E(.*)$/os
			or die "corrupt file: $file";
		$frozen = $1;
	}
	my $obj = Storable::thaw $frozen;
	die "unable to thaw $file!" unless $obj;
	$obj->{'OLD'} = Storable::thaw $frozen;
	$obj->{'OLD'}{'__frozen'} = \$frozen;

	$obj->postload($id);

	_unlock $file;

	$cache{$package}{$id} = $obj;

	if ($obj->{'__transfollowers'}) {
		for my $class (sort keys %{$obj->{'__transfollowers'}}) {
			for my $id (sort keys %{$obj->{'__transfollowers'}{$class}}) {
				# will rollback as side-effect
				my $follower = _loadany($class, $id);
			}
		}
		$obj = Storable::thaw ${$obj->{'__rollback'}};
		$cache{$package}{$id} = $obj;
		_lock $file;
		$obj->postload($id);
		_unlock $file;
		$obj->_realsave();
	} elsif ($obj->{'__transleader'}) {
		my $leader = _loadany($obj->{'__transleader'}{'CLASS'}, 
			    $obj->{'__transleader'}{'ID'});
		if (exists $leader->{'__transfollower'}
			&& exists $leader->{'__transfollower'}{$package}
			&& exists $leader->{'__transfollower'}{$package}{$id})
		{
			# rollback time!
			$obj = Storable::thaw ${$obj->{'__rollback'}};
			$cache{$package}{$id} = $obj;
			_lock $file;
			$obj->postload($id);
			_unlock $file;
		} else {
			delete $obj->{'__transleader'};
			delete $obj->{'__rollback'};
		}

		eval {
			$obj->_realsave();
		};
		if ($@ =~ /^DATACHANGE: file/) {
			delete $cache{$package}{$id};
			return load($package, $baseid);
		}
		die $@ if $@;
	}

	if ($obj->{'__removenow'}) {
		$obj->_realremove();
		return undef;
	}

	return $obj;
}

sub _loadany
{
	my ($pkg, $id) = @_;
	no strict qw(refs);
	unless (defined @{"${pkg}::ISA"}) {
		require "$pkg.pm";
	}
	return load($pkg, $id);
}

my %tosave;

sub abandon
{
	%tosave = ();
}

sub uncache
{
	my ($this) = @_;
	if (ref $this) {
		delete $cache{ref $this}{$this->id()};
		$this->{'__uncached'} = 1;
	} else {
		%cache = ();
	}
}

sub removelater
{
	my ($this) = @_;
	$this->{'__removenow'} = 1;
	$this->savelater();
}

sub remove
{
	my ($this) = @_;
	$this->removelater()
		if $this;

	commit();
}

sub savelater
{
	my ($this, $trivial) = @_;
	confess "attempt to call savelater() from within a presave() or postsave()"
		if $commit_inprogress == 2;
	$tosave{ref $this}{$this->id()} = $this;
	$this->{'__readonly'} = 0;
	if ($trivial) {
		$this->{'__trivial'} = 1;
	} else {
		delete $this->{'__trivial'};
	}
}

sub readlock
{
	my ($this) = @_;
	$tosave{ref $this}{$this->id()} = $this;
	$this->{'__readonly'} = 1
		unless exists $this->{'__readonly'};
}

sub save
{
	my ($this) = @_;
	$this->savelater()
		if $this;

	commit();
}

sub transaction
{
	my ($ref, $funcref, @args) = @_;
	my (%c) = (%cache);
	my $r;
	my @r;
	for(;;) {
		eval {
			if (wantarray()) {
				@r = &$funcref(@args);
			} else {
				$r = &$funcref(@args);
			}
		};
		if ($@ =~ /^DATACHANGE: file/) {
			%cache = %c;
			redo;
		}
		require Carp;
		Carp::croak $@ if $@;
		last;
	}
	return @r if wantarray();
	return $r;
}

#
# One of the changed objects becomes the transaction leader.  The state
# of the leader determines the state of the entire transaction.  
#
# The leader gets modified twice: first to note the other participants 
# in the transaction and then later to commit the transaction.  
#
# The other participants also get written twice, but the second writing
# happens the next time the object gets loaded, rather than at the time
# of the transaction.
#

my $unlock;

sub commit
{
	confess "attemp to call commit() from within a precommit(), presave() or postsave()"
		if $commit_inprogress;
	local($commit_inprogress) = 1;

	return 0 unless %tosave;

	my @commitlist;
	my %precommitdone;

	my $done = 0;
	while (! $done) {
		$done = 1;
		for my $type (keys %tosave) {
			for my $obj (values %{$tosave{$type}}) {
				next if $precommitdone{$obj}++;
				if ($obj->precommit($obj->old)) {
					$done = 0;
				}
			}
		}
	}

	my @savelist;
	for my $cls (sort keys %tosave) {
		for my $id (sort keys %{$tosave{$cls}}) {
			push(@savelist, $tosave{$cls}{$id});
		}
	}

	$commit_inprogress = 2;

	if (@savelist == 1) {
		$savelist[0]->_realsave();
		%tosave = ();
		return 1;
	}

	my $leader = shift(@savelist);
	$leader->{'__rollback'} = exists $leader->{'OLD'} 
			? $leader->{'OLD'}{'__frozen'} 
			: Storable::nfreeze { '__removenow' => 1 };

	for my $s (@savelist) {
		die "attemp to save an 'uncached' object" 
			if exists $s->{'__uncached'};
		$leader->{'__toremove'}{ref($s)}{$s->id()} = 1
			if $s->{'__deletenow'};
		next if $s->{'__trivial'};
		$leader->{'__transfollowers'}{ref($s)}{$s->id()} = 1;
		$s->{'__transleader'} = {
			'CLASS' => ref($leader),
			'ID' => $leader->id(),
		};
		$s->{'__rollback'} = exists $s->{'OLD'}
			? $s->{'OLD'}{'__frozen'} 
			: Storable::nfreeze { '__removenow' => 1 };
	}

	delete $leader->{'__readonly'};
	if (! -e $leader->file()) {
		$leader->_realsave();
	}
	_lock $leader->file();
	$leader->_realsave(1);

	for my $s (@savelist) {
		$s->_realsave();
	}

	delete $leader->{'__transfollowers'};
	delete $leader->{'__rollback'};
	$leader->_realsave(1);

	if ($leader->{'__toremove'}) {
		$leader->_removeall();
		$leader->_realsave(1);
	}
	_unlock $leader->file();

	if (exists $leader->{'__removenow'}) {
		$leader->_realremove();
	}

	%tosave = ();
	return 1;
}

sub _realsave
{
	my ($this, $keeplock) = @_;

	my $id = $this->id();
	my $file = $this->file($id);

	my $old = $this->old();

	my (@passby) = $this->presave($old);

	if (defined $old) {
		_lock $file unless $keeplock;
		my $frozen = _read_file($file);
		$frozen =~ s/^\Q$magic_cookie\E//o 
			or die "corrupt file: $file";
		if ($frozen ne ${$old->{'__frozen'}}) {
			_unlock_all();
			%cache = ();
			die "DATACHANGE: file $file changed out from under us, please retry";
		}
		if ($this->{'__readonly'}) {
			_unlock $file unless $keeplock;
			return;
		}
	} else {
		_lock $file unless $keeplock;
	}

	delete $this->{'OLD'};
	delete $this->{'__readonly'};

	my $newfrozen = Storable::nfreeze($this);
	_write_file("$file.tmp", $magic_cookie, $newfrozen);

	rename("$file.tmp", $file) 
		or die "rename $file.tmp -> $file: $!";

	$this->postsave($old, @passby);

	if ($file ne $this->file($id)) {
		# can change sometimes
		my $new = $this->file($id);
		File::Flock::lock_rename($file, $new);
		$file = $new;
	}
	_unlock $file
		unless $keeplock;

	$this->{'OLD'} = Storable::thaw($newfrozen);
	$this->{'OLD'}{'__frozen'} = \$newfrozen;
}

sub _removeall
{
	my ($this) = @_;
	for my $class (sort keys %{$this->{'__toremove'}}) {
		for my $id (sort keys %{$this->{'__toremove'}{$class}}) {
			# will remove as side-effect
			my $follower = $class->load($id);
		}
	}
}

sub _realremove
{
	my ($this) = @_;
	_lock $this->file();
	$this->preremove();
	_unlock $this->file();
	unlink($this->file());
	$this->postremove();
	delete $cache{ref $this}{$this->id()} 
}

sub old
{
	my ($this) = @_;
	return $this->{'OLD'} if exists $this->{'OLD'};
	return undef;
}


1;
