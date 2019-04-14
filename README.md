# liquid-structures

This project contains Haskell implementations of data structures from Chris
Okasaki's Book [Purely Functional Data Structures][1] with invariants statically
checked using [LiquidHaskell][2]. The implementations are based on the those
provided in the appendix of Okasaki's book but, in many cases they have been
modified to facilitate the addition of refinement types. Beyond simply ensuring
invariants, this project also attempts to use LiquidHaskell as a
[theorem prover][3] to prove other interesting properties.

[1]: http://www.cs.cmu.edu/~rwh/theses/okasaki.pdf
[2]: https://ucsd-progsys.github.io/liquidhaskell-blog/
[3]: https://ucsd-progsys.github.io/liquidhaskell-blog/2016/09/18/refinement-reflection.lhs/
