import K_ThreeDegenerateGraphs
import Theorem1

/-!
# Mechanical faithfulness check for the challenge statement

`K_ThreeDegenerateGraphs.lean` is the frozen challenge file: it defines
degeneracy from scratch and states Theorem 1, ending in an intentional
`sorry`.  `Theorem1.lean` restates it token-for-token in the
`ThreeDegenerateGraphsTarget` namespace and proves it.

This file replaces "faithfulness is checkable by diffing the two
statements" with a kernel check: the proven theorem is asserted to have
**exactly the type of the challenge theorem** (`type_of%` reads the type
off the challenge declaration itself, so any drift between the two files
fails to compile here).  The challenge's own `sorry` is irrelevant to this
check — only its *statement* is used.

Built by `lake build ChallengeFaithful` (kept out of the default targets
so the default build stays free of the challenge file's intentional
`sorry`); CI builds it alongside `Challenge`.
-/

open ThreeDegenerateGraphs in
example : type_of% @ThreeDegenerateGraphs.threeDegenerateExtremalCounterexample :=
  ThreeDegenerateGraphsTarget.threeDegenerateExtremalCounterexample
