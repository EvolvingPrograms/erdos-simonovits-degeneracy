import ThreeDegenerate.Challenge
import Theorem12r3

/-!
# Faithfulness of the original 3-degenerate challenge

The proved theorem must have the challenge's type. `type_of%` reads only the
statement, so the challenge's intentional `sorry` is not used as a proof.
The graph definitions are in `ThreeDegenerate.Definitions`.

CI builds this check with `lake build ChallengeFaithful`.
-/

open ThreeDegenerateGraphs in
example : type_of% @ThreeDegenerateGraphs.threeDegenerateExtremalCounterexample :=
  ThreeDegenerateGraphsTarget.threeDegenerateExtremalCounterexample
