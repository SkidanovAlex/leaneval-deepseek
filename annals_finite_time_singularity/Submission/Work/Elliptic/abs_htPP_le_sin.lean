/-
Copyright: work module for the Elgindi finite-time singularity project.

Bound for the integration-by-parts boundary term `htPP` of `hardy_two`: it is
controlled by `|sin 2θ|` times a constant depending only on the two sup-norms
`Cu` of `htU f` and `Cu'` of `(htU f)'`.

Since
  `htPP f θ = sin(2θ) * (40 cos(2θ) u'(θ)² - 80 sin(2θ) u(θ) u'(θ))`,  `u = f / sin 2θ`,
the pointwise bounds `|u| ≤ Cu`, `|u'| ≤ Cu'` on the *open* interval, together with
`|sin 2θ| ≤ 1`, `|cos 2θ| ≤ 1`, give
  `|htPP f θ| ≤ |sin 2θ| * (40 Cu'² + 80 Cu Cu')`
at interior points; at `θ = 0, π/2` both sides vanish because `sin 2θ = 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.HardyTwoDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- Arithmetic core of the bound on `htPP`: for `s ∈ [0,1]`, `|c| ≤ 1`, `d² ≤ Cu'²`,
`|u| ≤ Cu`, `|d| ≤ Cu'` and `Cu, Cu' ≥ 0`,
`|40 c d² - 80 s u d| ≤ 40 Cu'² + 80 Cu Cu'`. -/
theorem abs_htPP_core (s c u d Cu Cu' : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hc : |c| ≤ 1) (hd2 : d ^ 2 ≤ Cu' ^ 2)
    (hu : |u| ≤ Cu) (hd : |d| ≤ Cu') (hCu : 0 ≤ Cu) (hCu' : 0 ≤ Cu') :
    |40 * c * d ^ 2 - 80 * s * u * d| ≤ 40 * Cu' ^ 2 + 80 * Cu * Cu' := by
  have hCuCu' : 0 ≤ Cu * Cu' := mul_nonneg hCu hCu'
  have hud : |u * d| ≤ Cu * Cu' := by
    rw [abs_mul]
    exact mul_le_mul hu hd (abs_nonneg d) hCu
  have hcd : |c| * d ^ 2 ≤ Cu' ^ 2 := by
    simpa using mul_le_mul hc hd2 (sq_nonneg d) (by norm_num : (0 : ℝ) ≤ 1)
  -- `|c|` bounds on both sides
  have hcd1 : c * d ^ 2 ≤ Cu' ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self c) (sq_nonneg d)) hcd
  have hcd2 : -(c * d ^ 2) ≤ Cu' ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (neg_le_abs c) (sq_nonneg d)
    linarith
  have hud1 : -(u * d) ≤ Cu * Cu' := neg_le.mp (abs_le.mp hud).1
  have hud2 : u * d ≤ Cu * Cu' := (abs_le.mp hud).2
  have h1 : 40 * c * d ^ 2 ≤ 40 * Cu' ^ 2 := by nlinarith [hcd1]
  have h2 : -40 * c * d ^ 2 ≤ 40 * Cu' ^ 2 := by nlinarith [hcd2]
  have h3 : -80 * s * u * d ≤ 80 * Cu * Cu' := by
    have hA : s * (-(u * d)) ≤ s * (Cu * Cu') := mul_le_mul_of_nonneg_left hud1 hs0
    have hB : s * (Cu * Cu') ≤ Cu * Cu' := by
      have h := mul_le_mul_of_nonneg_right hs1 hCuCu'
      linarith
    nlinarith [hA, hB]
  have h4 : 80 * s * u * d ≤ 80 * Cu * Cu' := by
    have hA : s * (u * d) ≤ s * (Cu * Cu') := mul_le_mul_of_nonneg_left hud2 hs0
    have hB : s * (Cu * Cu') ≤ Cu * Cu' := by
      have h := mul_le_mul_of_nonneg_right hs1 hCuCu'
      linarith
    nlinarith [hA, hB]
  rw [abs_le]
  constructor <;> linarith

theorem abs_htPP_le_sin (f : ℝ → ℝ) {Cu Cu' : ℝ} (hCu : 0 ≤ Cu) (hCu' : 0 ≤ Cu')
    (hu : ∀ x ∈ Set.Ioo 0 (π / 2), |Work.Elliptic.htU f x| ≤ Cu)
    (hu' : ∀ x ∈ Set.Ioo 0 (π / 2), |deriv (Work.Elliptic.htU f) x| ≤ Cu') :
    ∀ θ ∈ Set.Icc 0 (π / 2),
      |Work.Elliptic.htPP f θ| ≤ |Real.sin (2 * θ)| * (40 * Cu' ^ 2 + 80 * Cu * Cu') := by
  intro θ hθ
  rw [Set.mem_Icc] at hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases eq_or_lt_of_le hθ0 with h | h0
  · -- left endpoint: `htPP f 0 = 0` and `sin 0 = 0`
    subst h
    rw [htPP_zero]
    simp
  rcases eq_or_lt_of_le hθ1 with h | h2
  · -- right endpoint: `htPP f (π/2) = 0` and `sin π = 0`
    subst h
    rw [htPP_pi2]
    have hs : Real.sin (2 * (π / 2)) = 0 := by
      rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    rw [hs]
    simp
  -- interior: `θ ∈ (0, π/2)`
  have hmem : θ ∈ Set.Ioo 0 (π / 2) := ⟨h0, h2⟩
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hd2 : (deriv (htU f) θ) ^ 2 ≤ Cu' ^ 2 := by
    have h1 : |deriv (htU f) θ| ^ 2 ≤ Cu' ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hu' θ hmem) 2
    rwa [sq_abs] at h1
  have hcore : |40 * Real.cos (2 * θ) * (deriv (htU f) θ) ^ 2
      - 80 * Real.sin (2 * θ) * (htU f θ) * (deriv (htU f) θ)|
      ≤ 40 * Cu' ^ 2 + 80 * Cu * Cu' :=
    abs_htPP_core _ _ _ _ _ _ hsin0 hsin1 (Real.abs_cos_le_one _) hd2
      (hu θ hmem) (hu' θ hmem) hCu hCu'
  have hfactor : htPP f θ
      = Real.sin (2 * θ) * (40 * Real.cos (2 * θ) * (deriv (htU f) θ) ^ 2
          - 80 * Real.sin (2 * θ) * (htU f θ) * (deriv (htU f) θ)) := by
    simp only [htPP]; ring
  have habs : |Real.sin (2 * θ)| = Real.sin (2 * θ) := abs_of_nonneg hsin0
  rw [hfactor, abs_mul, habs]
  exact mul_le_mul_of_nonneg_left hcore hsin0

end Work.Elliptic
