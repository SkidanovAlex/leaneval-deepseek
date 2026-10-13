/-
# The fundamental theorem of calculus on a single radial slice

`box_slice_ftc` is the radial fundamental theorem of calculus for the `θ`-slice of

  `BoxG f (z,θ) = z · (D_z f(z,θ) · w(z))²`,

namely, for `θ ∈ Iθ` and `R > 0`,

  `∫ z in (0,R), ∂_z (z (D_z f(z,θ) w(z))²) = R (D_z f(R,θ) w(R))²`.

It is the slice-wise input of `box_deriv_ftc` (which afterwards exchanges the `θ`-integral
with the `z`-integral by Fubini).  The proof is the fundamental theorem of calculus for the
radial function `G z = BoxG f z θ`:

* `G` is smooth on `(0,∞)` (hence differentiable there) by `contDiffOn_BoxG_slice` of
  `Submission.Work.Coercivity.BoxAux`;
* `∂_z G` is integrable on `(0,R)`: it is Borel measurable (`measurable_deriv`) and it is
  bounded there — on a right-neighbourhood `(0,δ)` of `0` by the hypothesis `hC`, and on
  the compact remainder `[δ,R] × Iθ` by compactness of the box (`box_joint_bound`) — and
  `(0,R)` has finite measure;
* `G z → 0` as `z → 0⁺` is exactly the hypothesis `hbd`, and `G` is continuous at `R`
  (indeed differentiable there) because `R > 0` lies in the smoothness range of the slice.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.BoxAux
import Submission.Work.Coercivity.box_joint_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

theorem box_slice_ftc (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hC : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ z ∈ Set.Ioo 0 δ, ∀ θ ∈ Spaces.Iθ,
      |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ C)
    {R : ℝ} (hR : 0 < R) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    ∫ z in Set.Ioo 0 R, deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
      = R * (Spaces.Dz f R θ * Spaces.w R) ^ 2 := by
  set G : ℝ → ℝ := fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2 with hG
  -- the slice is smooth (hence differentiable) on `(0,∞)`
  have hcd : ContDiffOn ℝ ⊤ G (Set.Ioi (0 : ℝ)) := by
    rw [hG]
    exact contDiffOn_BoxG_slice f hsm hθ
  have hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) R, DifferentiableAt ℝ G x := fun x hx =>
    (hcd.differentiableOn (by decide)).differentiableAt (isOpen_Ioi.mem_nhds hx.1)
  -- the derivative of the slice is bounded, hence integrable, on `(0,R)`
  obtain ⟨M, _hMpos, hM⟩ := box_joint_bound f hsm hC hR
  have hInt : IntegrableOn (deriv G) (Set.Ioo (0 : ℝ) R) := by
    refine Measure.integrableOn_of_bounded (M := M) ?_ ?_ ?_
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    · exact (measurable_deriv G).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_
      rw [Real.norm_eq_abs]
      exact hM x hx θ hθ
  -- the two boundary values
  have h0 : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [hG]
    simpa using hbd θ hθ
  have hcont : ContinuousAt G R :=
    ((hcd.differentiableOn (by decide)).differentiableAt (isOpen_Ioi.mem_nhds hR)).continuousAt
  -- fundamental theorem of calculus for the slice
  have hftc : ∫ x in Set.Ioo (0 : ℝ) R, deriv G x = G R := by
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) R, HasDerivAt G (deriv G x) x := fun x hx =>
      (hdiff x hx).hasDerivAt
    have hint' : IntervalIntegrable (deriv G) volume (0 : ℝ) R :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le).mpr hInt
    have hb : Tendsto G (𝓝[<] R) (𝓝 (G R)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hR hderiv hint' h0 hb
    rw [intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo] at h
    simpa using h
  rw [hG] at hftc ⊢
  exact hftc

end Work.Coercivity
