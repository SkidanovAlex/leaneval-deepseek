/-
# Gap 1 discharged: `Work.FIChain.FIChainSieveGap` is now a theorem

`Work.FIChain.FIChainSieveGap` (`Target.lean`) asks for `∃ K > 0` and, for every `Δ ≥ 3`, a weight
`λ` and a constant `C_sieve ≤ K` with `SieveInput FIgtil Δ λ C_sieve`.  That is character-identical
to the statement of `Work.FIChain.rosserLambda_FIgtil_r2`, which is now **proved** (the β = 19
Rosser–Iwaniec / Fundamental-Lemma chapter: `lamPlusB`, `rdPlusB`, `LamPlusB_obligations`,
`LamPlusB_sieve`, `FIsieveGap_of_lamPlusB`, and the per-layer machinery `GpB_eq_VfB_add_oddLayers`,
`VfBFacts`, `TnB_le_VfB_mul_SnB`, `oddLayers_le_of_delta_of_layer_bound` with its majorant inputs).

So Gap 1 needs no new work here — one line.
-/
import Submission.Work.FIChain.Target
import Submission.Work.FIChain.rosserLambda_FIgtil_r2

namespace Work.FIChain

theorem FIChainSieveGap_proved : FIChainSieveGap := rosserLambda_FIgtil_r2

end Work.FIChain
