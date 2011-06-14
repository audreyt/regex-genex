Available on Hackage as: http://hackage.haskell.org/package/regex-genex

The "genex" program finds all permutations of strings that matches every
regular expressions specified in the command line, with full support
for back references (\1 .. \9) and word boundaries (\b).

The output is unsorted, but the order is deterministic across multiple runs:

    $ genex '\d' '[123abc]' # Must match both
    1.00000000              "2"
    1.00000000              "3"
    1.00000000              "1"

To enforce a fixed ordering for alternations, pipe the output to "sort -n":

    $ genex '(__|<>){1,3}' | sort -n
    2.00000000              "<>"
    2.00000001              "__"
    4.00000002              "<><>"
    4.00000003              "__<>"
    4.00000006              "<>__"
    4.00000007              "____"
    6.00000010              "<><><>"
    6.00000011              "__<><>"
    6.00000014              "<>__<>"
    6.00000015              "____<>"
    6.00000026              "<><>__"
    6.00000027              "__<>__"
    6.00000030              "<>____"
    6.00000031              "______"

Output size and maximum string length are both capped at 65535 currently,
but both can be raised if needed.

Because genex generates matches lazily, we can use "head -n" to display
only part of its output:

    genex '[abc]+[123]+.+' | head -n 10

Some caveats:

- We translate * and + quantifiers into {0,3} and {1,4}, to make output
  appear more unique.

- The set of . \D \W \S characters are limited to printable characters,
  again to make the output more pretty.

- The ^ and $ anchors are taken to mean begin-of-line and end-of-line
  (implicit /m), since we already implicitly anchor on both ends.

- No support yet for \l \u \L \U \Q \E (case and quotemeta modifiers)

- No named Unicode properties or POSIX [[:upper:]] classes yet.

Required Hackage libraries: sbv regex-tdfa stream-monad text

Required binary in PATH:

    yices # Download it from http://yices.csl.sri.com/download-yices2.shtml

You can directly run the Main.hs in the checkout directory as well:

    runghc Main.hs 'your regex here'

Pre-built MacOSX binaries are in binaries/osx/; try "make test" for a sample run.

Share and enjoy!
Audrey
