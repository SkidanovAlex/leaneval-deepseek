import Mathlib
import Submission.Work.FBif.Glue
import Submission.Work.FBif.cutoff_props
import Submission.Work.FBif.norm_deriv_glueMap
import Submission.Work.FBif.radius_numerics
import Submission.Work.FBif.glue_derivs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function MeasureTheory
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open cutoffAux

/-! ## Elementary reverse triangle inequality -/

/-- `‖a‖ - ‖b‖ ≤ ‖a + b‖`. -/
theorem norm_sub_le_norm_add' (a b : ℂ) : ‖a‖ - ‖b‖ ≤ ‖a + b‖ := by
  have h := abs_norm_sub_norm_le a (-b)
  rw [norm_neg, sub_neg_eq_add] at h
  exact le_trans (le_abs_self _) h

/-! ## The model `T_c` -/

/-- The model `T_c z = z̄² + c` decreases the modulus by at most `‖c‖`. -/
theorem norm_tantibar_ge (c z : ℂ) : ‖z‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c z‖ := by
  have h : Tantibar c z = star z ^ 2 + c := rfl
  rw [h]
  have h2 := abs_norm_sub_norm_le (star z ^ 2) (-c)
  rw [norm_neg, norm_pow, norm_star, sub_neg_eq_add] at h2
  exact le_trans (le_abs_self _) h2

/-! ## Bounds on the perturbation term `ε · χ · q` -/

/-- The perturbation term `ε · χ z · q z` is bounded by `1`, given `ε · Q ≤ 1`. -/
theorem norm_eps_cutoff_mul_le (c : ℂ) (q : ℂ → ℂ) (ε Q : ℝ) (hε : 0 ≤ ε)
    (hQ : ∀ z : ℂ, ‖z‖ ≤ cutRad c → ‖q z‖ ≤ Q) (h1 : ε * Q ≤ 1) :
    ∀ z : ℂ, ‖(ε : ℂ) * ((cutoff c z : ℝ) : ℂ) * q z‖ ≤ 1 := by
  intro z
  by_cases hz : ‖z‖ ≤ cutRad c
  · have hqz := hQ z hz
    have hχ0 : 0 ≤ cutoff c z := cutoff_nonneg c z
    have hχ1 : cutoff c z ≤ 1 := cutoff_le_one c z
    have hnorm : ‖(ε : ℂ) * ((cutoff c z : ℝ) : ℂ) * q z‖ = ε * cutoff c z * ‖q z‖ := by
      rw [norm_mul, norm_mul]
      simp [abs_of_nonneg hε, abs_of_nonneg hχ0]
    rw [hnorm]
    have hstep : ε * cutoff c z * ‖q z‖ ≤ ε * 1 * Q := mul_le_mul (mul_le_mul_of_nonneg_left hχ1 hε) hqz (norm_nonneg _) (mul_nonneg hε zero_le_one)
    calc ε * cutoff c z * ‖q z‖ ≤ ε * 1 * Q := hstep
      _ = ε * Q := by ring
      _ ≤ 1 := h1
  · have hχ : cutoff c z = 0 := cutoff_eq_zero_of_cutRad_le c (le_of_lt (not_le.mp hz))
    rw [hχ]
    simp

/-! ## The geometry of the glued map -/

/-- Outside the inner ball, every point is mapped at least to the far radius. -/
theorem norm_glueMap_ge_farRad_of_inner (c : ℂ) (q : ℂ → ℂ) (ε Q : ℝ) (hε : 0 ≤ ε)
    (hQ : ∀ z : ℂ, ‖z‖ ≤ cutRad c → ‖q z‖ ≤ Q) (h1 : ε * Q ≤ 1) :
    ∀ z : ℂ, innerRad c ≤ ‖z‖ → farRad c ≤ ‖glueMap c q ε (cutoff c) z‖ := by
  intro z hz
  obtain ⟨hfpos, hipos, hcpos, hilt, hclt, hesc, hsq, hcut⟩ := radius_numerics c
  have hpert := norm_eps_cutoff_mul_le c q ε Q hε hQ h1 z
  have hT := norm_tantibar_ge c z
  have hz2 : innerRad c ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [hipos, hz, norm_nonneg z]
  have hfar1 : farRad c + 1 ≤ ‖Tantibar c z‖ := by linarith
  have htri : ‖Tantibar c z‖ - ‖(ε : ℂ) * ((cutoff c z : ℝ) : ℂ) * q z‖ ≤ ‖glueMap c q ε (cutoff c) z‖ := by
    have h := norm_sub_le_norm_add' (Tantibar c z) ((ε : ℂ) * ((cutoff c z : ℝ) : ℂ) * q z)
    rw [glueMap_apply]
    exact h
  linarith

/-- Beyond the far radius, the glued map is the model; the modulus stays above the far radius. -/
theorem norm_glueMap_ge_farRad_of_far (c : ℂ) (q : ℂ → ℂ) (ε : ℝ) :
    ∀ z : ℂ, farRad c ≤ ‖z‖ → farRad c ≤ ‖glueMap c q ε (cutoff c) z‖ := by
  intro z hz
  obtain ⟨hfpos, hipos, hcpos, hilt, hclt, hesc, hsq, hcut⟩ := radius_numerics c
  have hzext : cutRad c ≤ ‖z‖ := le_trans (le_of_lt hclt) hz
  have hχ : cutoff c z = 0 := cutoff_eq_zero_of_cutRad_le c hzext
  have hF : glueMap c q ε (cutoff c) z = Tantibar c z := by
    rw [glueMap_apply, hχ]; simp
  rw [hF]
  have hT := norm_tantibar_ge c z
  have hc_le : ‖c‖ ≤ farRad c - 1 := by
    have h8 : 8 * (‖c‖ + 1) ≤ farRad c := le_max_right _ _
    have h8' : ‖c‖ + 1 ≤ 8 * (‖c‖ + 1) := by linarith [norm_nonneg c]
    linarith
  have hz2 : farRad c ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [hfpos, hz, norm_nonneg z]
  nlinarith [hT, hc_le, hz2, sq_nonneg (farRad c - 1)]

/-! ## Where the `∂`-derivative vanishes -/

/-- Inside the inner ball the glued map equals the perturbation, hence is antiholomorphic. -/
theorem dz_glueMap_eq_zero_of_lt_inner (c : ℂ) {q : ℂ → ℂ} (hq : Antipoly q) (ε : ℝ)
    {z : ℂ} (hz : ‖z‖ < innerRad c) :
    Work.MRMT.dz (glueMap c q ε (cutoff c)) z = 0 := by
  obtain ⟨hcont, hv1, hv0, h01, hdzi, hdzo, hbnd⟩ := cutoff_props c
  have hdz : Work.MRMT.dz (realCoe (cutoff c)) z = 0 := hdzi z hz
  rw [(glue_wirtinger c hq ε hcont z).1, hdz]
  ring

/-- Outside the cut ball the glued map equals the model, which is antiholomorphic. -/
theorem dz_glueMap_eq_zero_of_cutRad_lt_norm (c : ℂ) {q : ℂ → ℂ} (hq : Antipoly q) (ε : ℝ)
    {z : ℂ} (hz : cutRad c < ‖z‖) :
    Work.MRMT.dz (glueMap c q ε (cutoff c)) z = 0 := by
  obtain ⟨hcont, hv1, hv0, h01, hdzi, hdzo, hbnd⟩ := cutoff_props c
  have hdz : Work.MRMT.dz (realCoe (cutoff c)) z = 0 := hdzo z hz
  rw [(glue_wirtinger c hq ε hcont z).1, hdz]
  ring

/-! ## The lower bound on `∂̄` of the glued map -/

/-- On the cut ball, `2‖z‖ - ε (Q Kχ + Q')` is a lower bound for `‖∂̄ (glueMap) z‖`. -/
theorem norm_dzbar_glueMap_lower (c : ℂ) {q : ℂ → ℂ} (hq : Antipoly q) (ε Q Kχ Q' : ℝ)
    (hε : 0 ≤ ε)
    (hQ : ∀ z : ℂ, ‖z‖ ≤ cutRad c → ‖q z‖ ≤ Q)
    (hKχ : ∀ z : ℂ, ‖Work.MRMT.dz (realCoe (cutoff c)) z‖ ≤ Kχ)
    (hQ' : ∀ z : ℂ, ‖z‖ ≤ cutRad c → ‖Work.MRMT.dzbar q z‖ ≤ Q') :
    ∀ z : ℂ, ‖z‖ ≤ cutRad c → 2 * ‖z‖ - ε * (Q * Kχ + Q') ≤ ‖Work.MRMT.dzbar (glueMap c q ε (cutoff c)) z‖ := by
  intro z hz
  obtain ⟨hcont, hv1, hv0, h01, hdzi, hdzo, hbnd⟩ := cutoff_props c
  have hcut0 : (0 : ℝ) ≤ cutRad c := le_of_lt (cutRad_pos c)
  have hQ0 : 0 ≤ Q := le_trans (norm_nonneg _) (hQ 0 (by rw [norm_zero]; exact hcut0))
  have hQ'0 : 0 ≤ Q' := le_trans (norm_nonneg _) (hQ' 0 (by rw [norm_zero]; exact hcut0))
  have hKχ0 : 0 ≤ Kχ := le_trans (norm_nonneg _) (hKχ 0)
  rw [(glue_wirtinger c hq ε hcont z).2]
  have hA : ‖(2 : ℂ) * star z‖ = 2 * ‖z‖ := by rw [norm_mul, norm_star]; norm_num
  have hB : ‖(ε : ℂ) * ((cutoff c z : ℝ) : ℂ) * Work.MRMT.dzbar q z‖ ≤ ε * Q' := by
    rw [norm_mul, norm_mul]
    have hεc : ‖(ε : ℂ)‖ = ε := by simp [abs_of_nonneg hε]
    have hχc : ‖((cutoff c z : ℝ) : ℂ)‖ = cutoff c z := by simp [abs_of_nonneg (h01 z).1]
    rw [hεc, hχc]
    have hstep : ε * cutoff c z * ‖Work.MRMT.dzbar q z‖ ≤ ε * 1 * Q' := mul_le_mul (mul_le_mul_of_nonneg_left (h01 z).2 hε) (hQ' z hz) (norm_nonneg _) (mul_nonneg hε zero_le_one)
    calc ε * cutoff c z * ‖Work.MRMT.dzbar q z‖ ≤ ε * 1 * Q' := hstep
      _ = ε * Q' := by ring
  have hC : ‖(ε : ℂ) * q z * Work.MRMT.dzbar (realCoe (cutoff c)) z‖ ≤ ε * Q * Kχ := by
    rw [norm_mul, norm_mul]
    have hεc : ‖(ε : ℂ)‖ = ε := by simp [abs_of_nonneg hε]
    rw [hεc, norm_dzbar_realCoe_eq hcont z]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hQ z hz) hε) (hKχ z) (norm_nonneg _) (mul_nonneg hε hQ0)
  have htri := (norm_three_bound ((2 : ℂ) * star z)
    ((ε : ℂ) * ((cutoff c z : ℝ) : ℂ) * Work.MRMT.dzbar q z)
    ((ε : ℂ) * q z * Work.MRMT.dzbar (realCoe (cutoff c)) z))
  linarith [htri, hA, hB, hC]

/-! ## The upper bound on `∂` of the glued map -/

/-- Off the inner ball, `‖∂ (glueMap) z‖ ≤ (ε Q Kχ / innerRad) ‖∂̄ (glueMap) z‖`. -/
theorem norm_dz_glueMap_le (c : ℂ) {q : ℂ → ℂ} (hq : Antipoly q) (ε Q Kχ Q' : ℝ)
    (hε : 0 ≤ ε)
    (hQ : ∀ z : ℂ, ‖z‖ ≤ cutRad c → ‖q z‖ ≤ Q)
    (hKχ : ∀ z : ℂ, ‖Work.MRMT.dz (realCoe (cutoff c)) z‖ ≤ Kχ)
    (hQ' : ∀ z : ℂ, ‖z‖ ≤ cutRad c → ‖Work.MRMT.dzbar q z‖ ≤ Q')
    (h2 : ε * (Q * Kχ + Q') ≤ innerRad c) :
    ∀ z : ℂ, ‖Work.MRMT.dz (glueMap c q ε (cutoff c)) z‖ ≤
      (ε * Q * Kχ / innerRad c) * ‖Work.MRMT.dzbar (glueMap c q ε (cutoff c)) z‖ := by
  obtain ⟨hcont, hv1, hv0, h01, hdzi, hdzo, hbnd⟩ := cutoff_props c
  have hcut0 : (0 : ℝ) ≤ cutRad c := le_of_lt (cutRad_pos c)
  have hQ0 : 0 ≤ Q := le_trans (norm_nonneg _) (hQ 0 (by rw [norm_zero]; exact hcut0))
  have hKχ0 : 0 ≤ Kχ := le_trans (norm_nonneg _) (hKχ 0)
  have hipos : 0 < innerRad c := innerRad_pos c
  have hcoef : 0 ≤ ε * Q * Kχ / innerRad c := div_nonneg (mul_nonneg (mul_nonneg hε hQ0) hKχ0) (le_of_lt hipos)
  intro z
  rcases lt_or_ge ‖z‖ (innerRad c) with hlt | hge
  · rw [dz_glueMap_eq_zero_of_lt_inner c hq ε hlt]
    simp only [norm_zero]
    exact mul_nonneg hcoef (norm_nonneg _)
  · rcases lt_or_ge (cutRad c) ‖z‖ with hgt | hle
    · rw [dz_glueMap_eq_zero_of_cutRad_lt_norm c hq ε hgt]
      simp only [norm_zero]
      exact mul_nonneg hcoef (norm_nonneg _)
    · have hqQ : ‖q z‖ ≤ Q := hQ z hle
      have hdz_le : ‖Work.MRMT.dz (glueMap c q ε (cutoff c)) z‖ ≤ ε * Q * Kχ := by
        rw [(glue_wirtinger c hq ε hcont z).1, norm_mul, norm_mul]
        have hεc : ‖(ε : ℂ)‖ = ε := by simp [abs_of_nonneg hε]
        rw [hεc]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hqQ hε) (hKχ z) (norm_nonneg _) (mul_nonneg hε hQ0)
      have hdzbar_ge : innerRad c ≤ ‖Work.MRMT.dzbar (glueMap c q ε (cutoff c)) z‖ := by
        have h := norm_dzbar_glueMap_lower c hq ε Q Kχ Q' hε hQ hKχ hQ' z hle
        have h2' : innerRad c ≤ 2 * ‖z‖ - ε * (Q * Kχ + Q') := by linarith
        linarith
      have hstep : (ε * Q * Kχ / innerRad c) * innerRad c = ε * Q * Kχ := div_mul_cancel₀ _ (ne_of_gt hipos)
      calc ‖Work.MRMT.dz (glueMap c q ε (cutoff c)) z‖ ≤ ε * Q * Kχ := hdz_le
        _ = (ε * Q * Kχ / innerRad c) * innerRad c := hstep.symm
        _ ≤ (ε * Q * Kχ / innerRad c) * ‖Work.MRMT.dzbar (glueMap c q ε (cutoff c)) z‖ := mul_le_mul_of_nonneg_left hdzbar_ge hcoef

/-! ## The statement -/

theorem glueMap_estimates (c : ℂ) {q : ℂ → ℂ} (hq : Work.FBif.Antipoly q) {ε Q Kχ Q' : ℝ}
    (hε : 0 ≤ ε)
    (hQ : ∀ z : ℂ, ‖z‖ ≤ Work.FBif.cutRad c → ‖q z‖ ≤ Q)
    (hKχ : ∀ z : ℂ, ‖Work.MRMT.dz (Work.FBif.realCoe (Work.FBif.cutoff c)) z‖ ≤ Kχ)
    (hQ' : ∀ z : ℂ, ‖z‖ ≤ Work.FBif.cutRad c → ‖Work.MRMT.dzbar q z‖ ≤ Q')
    (h1 : ε * Q ≤ 1) (h2 : ε * (Q * Kχ + Q') ≤ Work.FBif.innerRad c) :
    (∀ z : ℂ, Work.FBif.innerRad c ≤ ‖z‖ → Work.FBif.farRad c ≤
        ‖Work.FBif.glueMap c q ε (Work.FBif.cutoff c) z‖) ∧
      (∀ z : ℂ, Work.FBif.farRad c ≤ ‖z‖ → Work.FBif.farRad c ≤
        ‖Work.FBif.glueMap c q ε (Work.FBif.cutoff c) z‖) ∧
      (∀ z : ℂ, ‖z‖ < Work.FBif.innerRad c →
        Work.MRMT.dz (Work.FBif.glueMap c q ε (Work.FBif.cutoff c)) z = 0) ∧
      (∀ z : ℂ, Work.FBif.cutRad c < ‖z‖ →
        Work.MRMT.dz (Work.FBif.glueMap c q ε (Work.FBif.cutoff c)) z = 0) ∧
      (∀ z : ℂ, ‖Work.MRMT.dz (Work.FBif.glueMap c q ε (Work.FBif.cutoff c)) z‖ ≤
        (ε * Q * Kχ / Work.FBif.innerRad c) *
          ‖Work.MRMT.dzbar (Work.FBif.glueMap c q ε (Work.FBif.cutoff c)) z‖) :=
  ⟨norm_glueMap_ge_farRad_of_inner c q ε Q hε hQ h1,
   norm_glueMap_ge_farRad_of_far c q ε,
   fun _ hz => dz_glueMap_eq_zero_of_lt_inner c hq ε hz,
   fun _ hz => dz_glueMap_eq_zero_of_cutRad_lt_norm c hq ε hz,
   norm_dz_glueMap_le c hq ε Q Kχ Q' hε hQ hKχ hQ' h2⟩

end Work.FBif

end
