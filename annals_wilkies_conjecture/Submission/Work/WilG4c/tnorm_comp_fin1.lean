import Mathlib
import Submission.Work.WilG4c.tnorm_shrink_le
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4a.f1affine_of_f1affine1

namespace Work.WilG4c

/-- **`tnorm` is invariant under the identification `ℝ ≃ (Fin 1 → ℝ)`**: for any
`h : ℝ → ℝ` and `x : Fin 1 → ℝ`,

    tnorm r (fun t : Fin 1 → ℝ => h (t 0)) x = tnorm r h (x 0).

This is the bridge between the engine `Work.WilkG4c.curve_bound` (whose `hbase` lives on the
domain `ℝ`) and `Work.WilkG4c.tnorm_shrink_le` (whose conclusion lives on `Fin 1 → ℝ`).
Both sides are `∑ k ∈ Finset.range (r+1), ‖iteratedFDeriv ℝ k _ _‖ / k!`, and the summands agree
for every `k` by `LinearIsometryEquiv.norm_iteratedFDeriv_comp_right` applied to the linear
isometry equivalence `(Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ`, `u ↦ u 0`
(`Work.WilG4a.fin1LIE`); no differentiability hypothesis is needed. -/
theorem tnorm_comp_fin1 (r : ℕ) (h : ℝ → ℝ) (x : Fin 1 → ℝ) :
    WilkiesDesign.CG.tnorm r (fun t : Fin 1 → ℝ => h (t 0)) x
      = WilkiesDesign.CG.tnorm r h (x 0) := by
  rw [WilkiesDesign.CG.tnorm, WilkiesDesign.CG.tnorm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hcomp : (fun t : Fin 1 → ℝ => h (t 0)) = h ∘ ⇑WilG4a.fin1LIE := rfl
  rw [hcomp, WilG4a.fin1LIE.norm_iteratedFDeriv_comp_right]
  rfl

end Work.WilG4c
