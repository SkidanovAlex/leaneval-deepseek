import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.ConstructionInstance.gComp_abs_le
import Submission.Work.ConstructionInstance.Gamma_abs_theta_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity

noncomputable section

open Set Filter
open scoped Topology

/-! ## The quantitative bound `|ĝ x| ≤ max K Cv · r(x)^α`

`ĝ x = g (ρ(x)^{3α}) (|θ(x)|)` is the perturbation of the profile composed with the
self-similar variables.  The two data that control it are

* the *angular vanishing* `|g z θ| ≤ Cv · Γ(θ)`, whose angular factor is at most
  `Γ(θ) ≤ (r/ρ)^{2α}` off the axis, and
* the *linear vanishing at the origin* `|g z θ| ≤ K z` for `z ≤ 1`.

Off the axis one case-splits on which of the two dominates: if `r ≤ ρ²` then
`(r/ρ)^{2α} ≤ r^α` and the first gives `|ĝ| ≤ Cv r^α`; if `r > ρ²` then necessarily `ρ ≤ 1`, so
the second applies at `z = ρ^{3α} ≤ 1` and `ρ^{3α} ≤ ρ^{2α} ≤ r^α` gives `|ĝ| ≤ K r^α`.  On the
axis `r = 0` both `Γ` and `r^α` vanish.

This is the form in which the bound is consumed by the per-slice Hölder transfer
(`Work.ConstructionInstance.holder_smul_eTheta`): everything is stated directly in terms of the
two *given* constants `Cv` and `K`, with no auxiliary constant produced by a Taylor estimate.
-/

/-- `(r/ρ)^{2α} ≤ r^α` for `0 ≤ r ≤ ρ²`.  Writing `r = s ρ` (`s = r/ρ ≤ ρ`), this is
`s^{2α} ≤ s^α ρ^α`, i.e. `s^α ≤ ρ^α`. -/
private lemma rpow_two_mul_le_of_le_sq {α r ρ : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (h : r ≤ ρ ^ 2) : (r / ρ) ^ (2 * α) ≤ r ^ α := by
  have hs0 : 0 ≤ r / ρ := div_nonneg hr hρ.le
  have hsρ : r / ρ ≤ ρ := by
    rw [div_le_iff₀ hρ]; nlinarith
  have h1 : (r / ρ) ^ α ≤ ρ ^ α := Real.rpow_le_rpow hs0 hsρ hα.le
  have h2 : (r / ρ) ^ (2 * α) = (r / ρ) ^ α * (r / ρ) ^ α := by
    rw [show 2 * α = α + α from by ring, Real.rpow_add' hs0 (by positivity)]
  rw [h2]
  calc (r / ρ) ^ α * (r / ρ) ^ α ≤ (r / ρ) ^ α * ρ ^ α :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs0 α)
    _ = (r / ρ * ρ) ^ α := (Real.mul_rpow hs0 hρ.le).symm
    _ = r ^ α := by rw [div_mul_cancel₀ r hρ.ne']

/-- `ρ^{3α} ≤ r^α` for `0 < ρ ≤ 1` and `ρ² < r`.  Indeed `ρ^{3α} ≤ ρ^{2α} = (ρ²)^α ≤ r^α`. -/
private lemma rpow_three_mul_le_of_sq_lt {α r ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (h : ρ ^ 2 < r) : ρ ^ (3 * α) ≤ r ^ α := by
  have h1 : ρ ^ (3 * α) ≤ ρ ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have h2 : ρ ^ (2 * α) = (ρ ^ 2) ^ α := by
    rw [Real.rpow_mul hρ.le (2:ℝ) α, Real.rpow_two]
  calc ρ ^ (3 * α) ≤ ρ ^ (2 * α) := h1
    _ = (ρ ^ 2) ^ α := h2
    _ ≤ r ^ α := Real.rpow_le_rpow (sq_nonneg ρ) h.le hα.le

theorem gComp_abs_le_quant {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : ℝ → ℝ → ℝ}
    {Cv K : ℝ} (hCv : 0 ≤ Cv) (hK : 0 ≤ K)
    (hvt : Work.Spaces.VanishTheta g)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hlin : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → ∀ z : ℝ, 0 ≤ z → z ≤ 1 → |g z θ| ≤ K * z) :
    ∀ x : Work.FTS.Regularity.R3,
      |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
        ≤ max K Cv * (Work.Cyl.radial x) ^ α := by
  intro x
  by_cases hr : Work.Cyl.radial x = 0
  · -- On the axis `r = 0` the angular factor vanishes and the profile vanishes at `θ = 0`.
    have hθ : |Work.Cyl.theta x| = 0 := by
      rw [Work.Cyl.theta, hr, div_zero, Real.arctan_zero, abs_zero]
    have hz : Work.Cyl.radial x ^ α = 0 := by rw [hr, Real.zero_rpow hα.ne']
    rw [hθ, hvt.1, abs_zero, hz, mul_zero]
  · have hrpos : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr)
    have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hrpos (Work.Cyl.radial_le_rho x)
    have hρnn : 0 ≤ Work.Cyl.rho x := hρpos.le
    have hrn : 0 ≤ Work.Cyl.radial x := hrpos.le
    have hIθ : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := by
      refine ⟨abs_nonneg _, ?_⟩
      rw [Work.Cyl.theta]
      exact abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
        le_of_lt (Real.arctan_lt_pi_div_two _)⟩
    -- The angular vanishing bound, with `Γ(θ) ≤ (r/ρ)^{2α}`.
    have hvan' : |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
        ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := by
      calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
          ≤ Cv * Work.ConstructionInstance.Gamma α (|Work.Cyl.theta x|) :=
            hvan _ _ (Real.rpow_nonneg hρnn _) hIθ
        _ ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) :=
            mul_le_mul_of_nonneg_left
              (Work.ConstructionInstance.Gamma_abs_theta_le hα hrpos) hCv
    by_cases hρ1 : Work.Cyl.rho x ≤ 1
    · by_cases hsub : Work.Cyl.radial x ≤ (Work.Cyl.rho x) ^ 2
      · -- Sub-critical radius: the angular factor alone suffices.
        calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
            ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := hvan'
          _ ≤ Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_left
                (rpow_two_mul_le_of_le_sq hα hrn hρpos hsub) hCv
          _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_right (le_max_right K Cv) (Real.rpow_nonneg hrn α)
      · -- Super-critical radius with `ρ ≤ 1`: the linear vanishing at `z = 0` takes over.
        have hz1 : Work.Cyl.rho x ^ (3 * α) ≤ 1 :=
          Real.rpow_le_one hρnn hρ1 (by positivity)
        have hKb : |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
            ≤ K * Work.Cyl.rho x ^ (3 * α) :=
          hlin _ hIθ _ (Real.rpow_nonneg hρnn _) hz1
        have h3 : Work.Cyl.rho x ^ (3 * α) ≤ (Work.Cyl.radial x) ^ α :=
          rpow_three_mul_le_of_sq_lt hα hρpos hρ1 (not_le.mp hsub)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
            ≤ K * (Work.Cyl.rho x ^ (3 * α)) := hKb
          _ ≤ K * (Work.Cyl.radial x) ^ α := mul_le_mul_of_nonneg_left h3 hK
          _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_right (le_max_left K Cv) (Real.rpow_nonneg hrn α)
    · -- `ρ ≥ 1`: then `r ≤ ρ ≤ ρ²`, so the angular factor alone suffices again.
      have hρge : 1 ≤ Work.Cyl.rho x := le_of_lt (not_le.mp hρ1)
      have hsub : Work.Cyl.radial x ≤ (Work.Cyl.rho x) ^ 2 := by
        have h1 : Work.Cyl.radial x ≤ Work.Cyl.rho x := Work.Cyl.radial_le_rho x
        nlinarith
      calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
          ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := hvan'
        _ ≤ Cv * (Work.Cyl.radial x) ^ α :=
            mul_le_mul_of_nonneg_left
              (rpow_two_mul_le_of_le_sq hα hrn hρpos hsub) hCv
        _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right K Cv) (Real.rpow_nonneg hrn α)

end

end Work.FTS.Regularity
