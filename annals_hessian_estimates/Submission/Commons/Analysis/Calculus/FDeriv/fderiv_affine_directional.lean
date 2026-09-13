import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem fderiv_affine_directional {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) {s : Set E} {u : E → ℝ} {x : E}
    (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 2 u s) (w : E) :
    fderiv ℝ (fun z => (fderiv ℝ u z) z - u z) x w =
      ∑ k : ι, ⟪x, v k⟫ * ((iteratedFDeriv ℝ 2 u x) ![w, v k]) := by
  have huAt : ContDiffAt ℝ 2 u x := hu.contDiffAt (hs.mem_nhds hx)
  have hcu : DifferentiableAt ℝ (fun z => fderiv ℝ u z) x :=
    (huAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hu_diff : DifferentiableAt ℝ u x := huAt.differentiableAt (by norm_num)
  have h_id : DifferentiableAt ℝ (fun z : E => z) x := differentiableAt_id
  have hcu' : DifferentiableAt ℝ (fun z => (fderiv ℝ u z) z) x :=
    hcu.clm_apply h_id
  have hφ : fderiv ℝ (fun z => (fderiv ℝ u z) z - u z) x
      = (fderiv ℝ (fderiv ℝ u) x).flip x := by
    change fderiv ℝ ((fun z => (fderiv ℝ u z) z) - u) x
      = (fderiv ℝ (fderiv ℝ u) x).flip x
    rw [fderiv_sub hcu' hu_diff]
    rw [fderiv_clm_apply (u := fun z : E => z) hcu h_id]
    simp
  rw [hφ, ContinuousLinearMap.flip_apply]
  set S : E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ u) x w with hS
  have hxrepr : x = ∑ k : ι, ⟪x, v k⟫ • (v k : E) := by
    conv_lhs => rw [← v.sum_repr' x]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [real_inner_comm x (v k)]
  have hlin : S x = ∑ k : ι, ⟪x, v k⟫ * S (v k) := by
    conv_lhs => rw [hxrepr]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul]
  have hterm : ∀ k : ι, (iteratedFDeriv ℝ 2 u x) ![w, v k] = S (v k) := by
    intro k
    rw [iteratedFDeriv_two_apply]
    simp [hS]
  rw [hlin]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hterm k]

end Commons.Analysis.Calculus.FDeriv