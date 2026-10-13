import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

/-!
# The `θ`-derivative of a mixed slot, at the finite order `C⁴`

For a datum `f` of class `C⁴` on the open quadrant `Q0` the operator `D_θ = sin(2θ) ∂_θ` shifts
the angular index of the mixed derivative `D_z^j D_θ^i f` (`i + j + 1 ≤ 4`, the finite-order
instance of the identity of `Submission/Work/FTS_RegExport/C4/Dth_mixed_eq_C4.lean`).  Since
`D_θ g = sin(2θ) · ∂_θ g` this gives the *plain* `θ`-derivative of the `θ`-slice:

  `HasDerivAt (fun θ' => D_z^jD_θ^i f z θ') (D_z^jD_θ^{i+1} f z θ / sin(2θ)) θ`.

The differentiability of the slice is the finite-order version of
`SmoothOpen.hasDerivAt_thslice`, obtained from `ContDiffOn ℝ 1 (uncurry ·) Q0` by the chain rule
(`Work.Spaces.deriv_slice_snd` identifies the value with `pth`).
-/

/-- For a function `g` which is `C¹` on an open set `V`, the `θ`-slice at an interior point is
differentiable with derivative `pth g z θ` (finite-order companion of
`Work.FTS_RegExport.RXT.hasDerivAt_slice_snd_of_contDiffOn`; stated here so that this file does
not need the heavy `CoercivityFix` import cone). -/
lemma hasDerivAt_slice_snd_of_contDiffOn {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ 1 (Function.uncurry g) V)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    HasDerivAt (fun θ' => g z θ') (Work.Spaces.pth g z θ) θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ) :=
    (h.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hz)
  have h2 : HasFDerivAt (fun θ' : ℝ => (z, θ')) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right z θ
  have h3 : HasDerivAt (fun θ' : ℝ => Function.uncurry g (z, θ'))
      ((fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1) θ := by
    simpa only [Function.comp_def] using (hd.hasFDerivAt.comp θ h2).hasDerivAt
  have hval : (fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1
      = Work.Spaces.pth g z θ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact (Work.Spaces.deriv_slice_snd (Function.uncurry g) z θ hd).symm
  rw [hval] at h3
  exact h3

theorem hasDerivAt_mixed_theta {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (j i : ℕ) (hji : j + i ≤ 3) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    HasDerivAt (fun θ' => Work.Spaces.mixed j i f z θ')
      (Work.Spaces.mixed j (i + 1) f z θ / Real.sin (2 * θ)) θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ, hθ'⟩
  -- `f` is `C^{1 + j + i}`, so `D_θ^i f` is `C^{1+j}` and `D_z^jD_θ^i f` is `C¹`
  have hle : (1 + j) + i ≤ 4 := by omega
  have hDth : ContDiffOn ℝ (↑(1 + j) + ↑i) (Function.uncurry f)
      Work.FTS.EllipticEst.Q0 :=
    hf.of_le (by exact_mod_cast hle)
  have hmid : ContDiffOn ℝ (1 + j) (Function.uncurry (Work.Spaces.DthIter i f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 i (1 + j) hDth
  have hmix : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 j 1 hmid
  have hd := hasDerivAt_slice_snd_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0 hmix hmem
  -- the value of the derivative: `D_θ (D_z^jD_θ^i f) = D_z^jD_θ^{i+1} f`
  have hdth := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 hf j i (by omega) hz ⟨hθ, hθ'⟩
  have hdth' : Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i f) z θ
      = Work.Spaces.mixed j (i + 1) f z θ := by
    simpa only [Work.Spaces.Dth] using hdth
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    apply ne_of_gt
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hval : Work.Spaces.pth (Work.Spaces.mixed j i f) z θ
      = Work.Spaces.mixed j (i + 1) f z θ / Real.sin (2 * θ) := by
    rw [eq_div_iff hsin, mul_comm]
    exact hdth'
  rw [hval] at hd
  exact hd

end Work.FTS_RegExport.RXT.Sys
