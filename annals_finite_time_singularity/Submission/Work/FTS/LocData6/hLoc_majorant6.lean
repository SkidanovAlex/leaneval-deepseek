import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocDataExt.Majorant5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.LocData6.hLoc_majorant6` — the order-`6` pointwise majorant of `hLoc α`

`hLoc α = bumpZ(z)·Γ(θ)` is separable; at order `6` the only new radial ingredient is that the
`D_z`-jets of the bump are bounded up to order `6` (the delivered order-`5` bound
`LocDataExt.DzIter_bumpZ_bound5` stops at `5`).  The angular input is *not* proved here: it is
supplied as the hypothesis `hΓ` of the statement (`(D_θ^iΓ)² ≤ 10¹⁰·Γ²`, `i ≤ 6`).

The assembly is the generic separable majorant `LocDataExt.HkIntegrand_sepGam_le` at `k = 6`,
which is where the order-`6` structure of the target statement lives.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The bump at order `6` -/

/-- The `D_z`-jets of the bump `bumpZ = χ(4·-5)` up to order `6` are bounded. -/
theorem DzIter_bumpZ_bound6 :
    ∃ C : ℝ, ∀ c : ℕ, c ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => Work.FTS.LocData.bumpZ z) z θ| ≤ C := by
  classical
  refine ⟨∑ c ∈ Finset.range 7,
    Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c), ?_⟩
  intro c hc z _ θ
  have hM : ∀ d : ℕ, 0 ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) ∧
      ∀ w : ℝ, |(Work.FTS.LocData.T1^[d]) Work.FTS.LocData.bumpZ w|
        ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    fun d => Classical.choose_spec (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d)
  rw [Work.FTS.LocData.DzIter_bumpZ_eq c θ z]
  have h1 : |(Work.FTS.LocData.T1^[c]) Work.FTS.LocData.bumpZ z|
      ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c) := (hM c).2 z
  have h2 : Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c)
      ≤ ∑ d ∈ Finset.range 7,
          Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    Finset.single_le_sum (fun d _ => (hM d).1) (Finset.mem_range.mpr (by omega))
  linarith

/-- The radial bound needed by `HkIntegrand_sepGam_le` for the bump `bumpZ`, at order `6`. -/
theorem hB_bumpZ6 :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2 := by
  obtain ⟨D, hD⟩ := DzIter_bumpZ_bound6
  have hD0 : 0 ≤ D := by
    have h := hD 0 (by norm_num) 0 (by simp [Work.Spaces.Iz]) 0
    have h1 : |Work.Spaces.DzIter 0 (fun z _ => Work.FTS.LocData.bumpZ z) 0 0| = 0 := by
      rw [Work.FTS.LocData.DzIter_bumpZ_eq 0 0 0, Function.iterate_zero_apply,
        Work.FTS.LocData.bumpZ_zero, abs_zero]
    linarith [h1 ▸ h]
  refine ⟨D ^ 2 * (1771561 / 1296 : ℝ), by positivity, fun j hj z hz θ => ?_⟩
  by_cases hsupp : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
  · have hw := Work.FTS.LocData.w_sq_le_on_support hsupp
    have h1 : (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2 ≤ D ^ 2 := by
      have h := hD j hj z hz θ
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs] at h2
    rw [mul_pow]
    calc (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ D ^ 2 * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) :=
          mul_le_mul h1 hw (sq_nonneg _) (by positivity)
      _ = D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 := by ring
  · rw [Work.FTS.LocData.DzIter_bumpZ_eq j θ z,
      Work.FTS.LocData.T1_iterate_bumpZ_eq_zero hsupp j]
    have hD2 : 0 ≤ D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg D) (by norm_num)) (sq_nonneg _)
    simpa using hD2

/-! ## The order-`6` majorant -/

theorem hLoc_majorant6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.hLoc α) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨R, hR, hB⟩ := hB_bumpZ6
  refine ⟨(7 + 49 * 10 ^ 10) * R, by positivity, fun z hz θ hθ => ?_⟩
  have hmain := Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 6
    (ρ := fun z => Work.FTS.LocData.bumpZ z) (R := R) (Rθ := (10 : ℝ) ^ 10)
    hR (by positivity) hB hΓ hz hθ
  have hfun : (fun z θ => Work.FTS.LocData.bumpZ z * Work.Spaces.Gam α θ)
      = Work.FTS.LocData.hLoc α := by
    funext z θ
    rw [Work.FTS.LocData.hLoc_apply]
  rw [hfun] at hmain
  refine hmain.trans_eq ?_
  push_cast
  ring

end Work.FTS.LocData6
