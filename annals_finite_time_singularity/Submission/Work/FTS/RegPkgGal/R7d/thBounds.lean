import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

open Set

/-- The integrating factor `φ ↦ φ · exp (K · ·)` used to turn the differential inequality
`φ' ≥ -K φ` into monotonicity. -/
noncomputable def scalExp (K : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun x => φ x * Real.exp (K * x)

/-- **Grönwall, lower bound.**  If `φ` is continuous on `[0,T]`, differentiable on `(0,T)` with
`φ' x ≥ -K φ x` there, then `φ x ≥ φ 0 · exp (-(K x))` on `[0,T]`.

Proof: `x ↦ φ x · exp (K x)` is monotone, since its derivative
`(φ' x + K φ x) · exp (K x)` is nonnegative. -/
lemma gronwall_lower_fts {φ φ' : ℝ → ℝ} {K T : ℝ}
    (hφc : ContinuousOn φ (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ioo 0 T, HasDerivAt φ (φ' x) x)
    (hineq : ∀ x ∈ Set.Ioo 0 T, -(K * φ x) ≤ φ' x) :
    ∀ x ∈ Set.Icc 0 T, φ 0 * Real.exp (-(K * x)) ≤ φ x := by
  have hfd : ∀ x ∈ Set.Ioo 0 T,
      HasDerivAt (scalExp K φ) ((φ' x + K * φ x) * Real.exp (K * x)) x := by
    intro x hx
    have he : HasDerivAt (fun y : ℝ => Real.exp (K * y)) (Real.exp (K * x) * K) x :=
      (hasDerivAt_const_mul (x := x) K).exp
    have hm : HasDerivAt (fun y : ℝ => φ y * Real.exp (K * y))
        (φ' x * Real.exp (K * x) + φ x * (Real.exp (K * x) * K)) x := (hd x hx).mul he
    have h1 : HasDerivAt (scalExp K φ)
        (φ' x * Real.exp (K * x) + φ x * (Real.exp (K * x) * K)) x := hm
    refine h1.congr_deriv ?_
    ring
  have hmono : MonotoneOn (scalExp K φ) (Set.Icc 0 T) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Icc 0 T)
      (f := scalExp K φ) (f' := fun x => (φ' x + K * φ x) * Real.exp (K * x))
      (convex_Icc 0 T) ?_ ?_ ?_
    · refine ContinuousOn.mul hφc ?_
      exact Continuous.continuousOn (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    · intro x hx
      rw [interior_Icc] at hx
      exact (hfd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact mul_nonneg (by linarith [hineq x hx]) (Real.exp_pos _).le
  intro x hx
  have hx0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_refl 0, hx.1.trans hx.2⟩
  have hmon := hmono hx0 hx hx.1
  simp only [scalExp, mul_zero, Real.exp_zero, mul_one] at hmon
  have hxsimp : φ x * Real.exp (K * x) * Real.exp (-(K * x)) = φ x := by
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have h2 := mul_le_mul_of_nonneg_right hmon (Real.exp_pos (-(K * x))).le
  rwa [hxsimp] at h2

theorem thBounds {θ V : ℝ → ℝ} {K θ₀ T : ℝ} (hθc : ContinuousOn θ (Set.Icc 0 T)) (hθ0 : θ 0 = θ₀) (hderiv : ∀ x ∈ Set.Ioo 0 T, HasDerivAt θ (-(V x)) x) (hl : ∀ x ∈ Set.Ioo 0 T, |V x| ≤ K * θ x) (hu : ∀ x ∈ Set.Ioo 0 T, |V x| ≤ K * (Real.pi / 2 - θ x)) : ∀ x ∈ Set.Icc 0 T, θ₀ * Real.exp (-(K * x)) ≤ θ x ∧ θ x ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) := by
  intro x hx
  constructor
  · -- lower bound: apply Grönwall to `θ` with `θ' = -V ≥ -K θ`
    have hineq : ∀ y ∈ Set.Ioo 0 T, -(K * θ y) ≤ -(V y) := by
      intro y hy
      have h := le_of_abs_le (hl y hy)
      linarith
    have key := gronwall_lower_fts (φ := θ) (φ' := fun y => -(V y)) (K := K) (T := T)
      hθc hderiv hineq x hx
    rwa [hθ0] at key
  · -- upper bound: apply Grönwall to `ψ = π/2 - θ` with `ψ' = V ≥ -K ψ`
    have hψc : ContinuousOn ((fun _ : ℝ => Real.pi / 2) - θ) (Set.Icc 0 T) :=
      continuousOn_const.sub hθc
    have hψd : ∀ y ∈ Set.Ioo 0 T, HasDerivAt ((fun _ : ℝ => Real.pi / 2) - θ) (V y) y := by
      intro y hy
      have h := (hasDerivAt_const y (Real.pi / 2)).sub (hderiv y hy)
      convert h using 1
      rw [zero_sub, neg_neg]
    have hψineq : ∀ y ∈ Set.Ioo 0 T, -(K * ((fun _ : ℝ => Real.pi / 2) - θ) y) ≤ V y := by
      intro y hy
      have h := neg_le_of_abs_le (hu y hy)
      simpa [Pi.sub_apply] using h
    have key := gronwall_lower_fts (φ := (fun _ : ℝ => Real.pi / 2) - θ) (φ' := V) (K := K) (T := T)
      hψc hψd hψineq x hx
    have key2 : (Real.pi / 2 - θ 0) * Real.exp (-(K * x)) ≤ Real.pi / 2 - θ x := by
      simpa [Pi.sub_apply] using key
    rw [hθ0] at key2
    linarith

end Work.FTS.RegPkgGal.R7d
