
use ExtUtils::MakeMaker;
# See lib/ExtUtils/MakeMaker.pm for details of how to influence
# the contents of the Makefile being created.
WriteMakefile(
	'NAME' => 'Object::Transaction',
	'DISTNAME' => 'Object-Transaction',
	'VERSION_FROM' => 'Transaction.pm',
	($] >= 5.005 ?
	    ('ABSTRACT' => 'Virtual base class for transactions on files containing serialized hash objects',
	     'AUTHOR'	=> 'David Muir Sharnoff <muir@idiom.com>') : ()),
	'dist'   => {COMPRESS=>'gzip', SUFFIX=>'gz'},
	'PREREQ_PM' => {
		'File::Sync'	=> 0,
		'Storable'	=> 0,
		'File::Flock'	=> 99.121701,
	},
);

package MY;

sub postamble {
    <<"END_OF_POSTAMBLE";

pm_to_blib: README

README: Transaction.pod
\tpod2text Transaction.pod >README

END_OF_POSTAMBLE
}
