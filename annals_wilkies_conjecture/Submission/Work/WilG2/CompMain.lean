/-
  WilG2 : the jet norm is subcompositional (BNZ Lemma 4.2(ii)).

  This module instantiates the two combinatorics inputs
  * `Work.WilG2.ofp_weighted_sum`   (weighted `OrderedFinpartition` vs `Composition` count)
  * `Work.WilG2.sum_composition_mul_prod_le` (domination of the `Composition` sum by a power sum)
  to obtain the frozen SPEC hole `G2_tnorm_comp`.
-/
import Submission.Work.WilG2.CompStep
import Submission.Work.WilG2.ofp_weighted_sum
import Submission.Work.WilG2.sum_composition_mul_prod_le

set_option autoImplicit false
noncomputable section
open Classical Finset
namespace WilkiesDesign.CG
open WilkiesConjecture WilkiesDesign FirstOrder Language

/-- **G2, subcompositionality of the jet norm** (BNZ Lemma 4.2(ii)). -/
theorem G2_tnorm_comp_proved {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (r : ℕ) (F : E → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (x : E)
    (hF : ContDiffAt ℝ r F x) (hg : ContDiffAt ℝ r g (F x))
    (h1 : ∑ k ∈ Finset.Ico 1 (r + 1),
        ‖iteratedFDeriv ℝ k F x‖ / (k.factorial : ℝ) ≤ 1) :
    tnorm r (g ∘ F) x ≤ tnorm r g (F x) :=
  G2_tnorm_comp_of_inputs r F g x hF hg h1
    (fun n _ => Work.WilG2.ofp_weighted_sum n (fun k => jetCoeff k F x)
      (fun p => jetCoeff p g (F x)))
    (Work.WilG2.sum_composition_mul_prod_le r (fun k => jetCoeff k F x)
      (fun p => jetCoeff p g (F x)) (fun i => jetCoeff_nonneg i F x)
      (fun j => jetCoeff_nonneg j g (F x)))

end WilkiesDesign.CG
