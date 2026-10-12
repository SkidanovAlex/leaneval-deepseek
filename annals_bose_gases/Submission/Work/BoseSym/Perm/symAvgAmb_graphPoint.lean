import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Basic.graphPoint_add
import Submission.Work.BoseSym.Basic.graphPoint_smul
import Submission.Work.BoseSym.Perm.graphPoint_permTest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The symmetrisation average commutes with the graph point

`symAvgAmb N p = (N!)⁻¹ • ∑_σ permAmb N σ p` averages the permutation orbit of
`p` in the ambient space `Amb N`, and `symTest N L F` averages a test function
over the permutation group.  This module proves that the two constructions
match through the graph point `graphPoint N L F = (F, ∇F)`:

`symAvgAmb N (graphPoint N L F) = graphPoint N L (symTest N L F)`.

The argument is formal: `graphPoint N L` is `ℝ`-linear
(`Basic.graphPoint_add`, `Basic.graphPoint_smul`, packaged here as the linear map
`graphPointLin`), it intertwines the permutation actions
(`Perm.graphPoint_permTest`), and `symTest` is exactly the group average of the
permuted test functions (`symTest_eq_avg`).  Hence computing with the average of
the permuted graph points gives the graph point of the averaged test function.
-/

namespace Work.BoseSym.Perm

open MeasureTheory Filter

/-- The map sending a test function to its graph point `(F, ∇F)` is `ℝ`-linear. -/
noncomputable def graphPointLin (N : ℕ) (L : ℝ) : testSub N L →ₗ[ℝ] Amb N where
  toFun := graphPoint N L
  map_add' := fun F G => Basic.graphPoint_add F G
  map_smul' := fun c F => Basic.graphPoint_smul c F

/-- The symmetrised test function `symTest N L F` is the group average of the
permuted test functions `permTest N L σ F`. -/
lemma symTest_eq_avg {N : ℕ} {L : ℝ} (F : testSub N L) :
    symTest N L F = (Nat.factorial N : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin N), permTest N L σ F := by
  apply Subtype.ext
  funext x
  simp only [symTest, permTest, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, one_div,
    Submission.BoseGases.symAvg, Submodule.coe_sum, Finset.sum_apply]
  congr 1

theorem symAvgAmb_graphPoint {N : ℕ} {L : ℝ} (F : testSub N L) :
    symAvgAmb N (graphPoint N L F) = graphPoint N L (symTest N L F) := by
  have hsum : (∑ σ : Equiv.Perm (Fin N), permAmb N σ (graphPoint N L F))
      = ∑ σ : Equiv.Perm (Fin N), graphPoint N L (permTest N L σ F) :=
    Finset.sum_congr rfl (fun σ _ => graphPoint_permTest σ F)
  have hmap : (∑ σ : Equiv.Perm (Fin N), graphPoint N L (permTest N L σ F))
      = graphPoint N L (∑ σ : Equiv.Perm (Fin N), permTest N L σ F) :=
    (map_sum (graphPointLin N L) (fun σ : Equiv.Perm (Fin N) => permTest N L σ F)
      Finset.univ).symm
  rw [symAvgAmb, hsum, hmap, ← Basic.graphPoint_smul, symTest_eq_avg]

end Work.BoseSym.Perm
