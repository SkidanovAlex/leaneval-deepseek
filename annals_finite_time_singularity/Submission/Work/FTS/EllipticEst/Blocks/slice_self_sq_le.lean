import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.slice_deriv_sq_le
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Blocks

/-- **Boundary bound for a smooth slice vanishing at both angular endpoints.**  With `A = ∫_{Iθ} (u'')² sin(2θ)^{-η}` (an honest finite number by the hypothesis),

`(u θ)² ≤ (π/2)² · A · ∫_{Iθ} sin(2θ)^η`   for every `θ ∈ Iθ`.

NOTE.  Put this declaration in namespace `Work.FTS.EllipticEst.Blocks` (i.e. `namespace Work.FTS.EllipticEst.Blocks`), NOT in `Work.FTS.EllipticEst`: a declaration `Work.FTS.EllipticEst.slice_self_sq_le` with this exact statement already exists in the (still `sorry`-containing) `Submission/Work/FTS/EllipticEst/slice_self_sq_le.lean`, and the same name in the same namespace would clash as soon as both modules are imported.  Do not import that file.

ROUTE (all ingredients are sorry-free in the tree): `u θ = ∫_0^θ ∂_θ u` (`intervalIntegral.integral_deriv_of_contDiffOn_Icc`), so `(u θ)² ≤ (π/2)² sup_{Iθ}(∂_θ u)²`; then `∫_{Iθ} ∂_θ u = u(π/2) - u(0) = 0` makes `slice_deriv_sq_le` applicable (it is stated for equal endpoint values), giving `(∂_θ u θ)² ≤ A · ∫ sin(2θ)^η`. -/
theorem slice_self_sq_le {u : ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SliceSmooth u)
    (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    ∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2
      ≤ (Real.pi / 2) ^ 2 * ((∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by
  -- The slice vanishes at both angular endpoints, so `slice_deriv_sq_le` (proved for equal
  -- endpoint values) bounds `(∂_θ u)²` by `A · ∫ sin(2θ)^η` on all of `Iθ`.
  have hend : u 0 = u (Real.pi / 2) := by rw [h0, h1]
  have hderiv := Work.FTS.EllipticEst.slice_deriv_sq_le hsm hend hint
  -- `u` is `C¹` on a neighbourhood of `Iθ`, hence on every sub-interval `uIcc 0 θ`.
  have hcd : ContDiffOn ℝ 1 u (Set.Ioo (-1) (Real.pi / 2 + 1)) := hsm.of_le le_top
  intro θ hθ
  have hθI := hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
  have hθ0 : (0 : ℝ) ≤ θ := hθI.1
  have hθpi : θ ≤ Real.pi / 2 := hθI.2
  -- abbreviations for the two integrals of the statement
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hB
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hx))
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hx) _)
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  -- pointwise bound for the first derivative on `Iθ`
  have hderivAB : ∀ x ∈ Work.Spaces.Iθ, (deriv u x) ^ 2 ≤ A * B := hderiv
  have hpoint : ∀ x ∈ Work.Spaces.Iθ, |deriv u x| ≤ Real.sqrt (A * B) := fun x hx =>
    Real.abs_le_sqrt (hderivAB x hx)
  -- fundamental theorem of calculus: `u θ = ∫_0^θ ∂_θ u` (and `u 0 = 0`)
  have huIcc : Set.uIcc (0 : ℝ) θ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hFTC : (∫ x in (0 : ℝ)..θ, deriv u x) = u θ - u 0 :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hcd.mono huIcc)
  have hu_eq : u θ = ∫ x in (0 : ℝ)..θ, deriv u x := by rw [hFTC, h0]; ring
  -- the integral is bounded by the length of the interval times the pointwise bound
  have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) θ, ‖deriv u x‖ ≤ Real.sqrt (A * B) := by
    intro x hx
    rw [Set.mem_uIoc] at hx
    have hxI : x ∈ Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨le_of_lt h1, le_trans h2 hθpi⟩
      · exact ⟨le_trans hθ0 (le_of_lt h1), by linarith [h2, Real.pi_pos]⟩
    rw [Real.norm_eq_abs]
    exact hpoint x hxI
  have hnorm : ‖∫ x in (0 : ℝ)..θ, deriv u x‖ ≤ Real.sqrt (A * B) * |θ - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbd
  have habs : |u θ| ≤ Real.sqrt (A * B) * (Real.pi / 2) := by
    have h1' : ‖u θ‖ ≤ Real.sqrt (A * B) * |θ - 0| := by
      rw [hu_eq]; exact hnorm
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ0), sub_zero] at h1'
    exact le_trans h1' (mul_le_mul_of_nonneg_left hθpi (Real.sqrt_nonneg _))
  have hsq : (u θ) ^ 2 ≤ (Real.sqrt (A * B) * (Real.pi / 2)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc (u θ) ^ 2 ≤ (Real.sqrt (A * B) * (Real.pi / 2)) ^ 2 := hsq
    _ = (Real.sqrt (A * B)) ^ 2 * (Real.pi / 2) ^ 2 := by ring
    _ = (A * B) * (Real.pi / 2) ^ 2 := by rw [Real.sq_sqrt hAB]
    _ = (Real.pi / 2) ^ 2 * (A * B) := by ring

end Work.FTS.EllipticEst.Blocks
