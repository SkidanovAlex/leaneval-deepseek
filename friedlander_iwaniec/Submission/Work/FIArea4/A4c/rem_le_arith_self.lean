import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FITop4.Areas6c

set_option maxHeartbeats 1600000

namespace Work.FIArea4.A4c

/- Arithmetic supporting the remainder bound; kept in its own nested namespace so that it cannot
collide with the (independently developed) sibling `A4c/rem_le_arith.lean`. -/
namespace RemSelfArith

open Finset
open scoped BigOperators

noncomputable section

/-- `(log y)^K ≤ y^δ` for `y` large, `K ≥ 0`, `δ > 0`. -/
theorem log_rpow_le_rpow_eventually (K : ℝ) (_hK : 0 ≤ K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ y : ℝ, M ≤ y → (Real.log y) ^ K ≤ y ^ δ := by
  have hlittle : (fun y : ℝ => Real.log y ^ K) =o[Filter.atTop] (fun y : ℝ => y ^ δ) :=
    isLittleO_log_rpow_rpow_atTop K hδ
  have hbound : ∀ᶠ y : ℝ in Filter.atTop, (Real.log y) ^ K ≤ y ^ δ := by
    have h := Asymptotics.IsLittleO.def hlittle (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with y hy hy1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hy1) K),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) δ), one_mul] at hy
    exact hy
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hbound
  exact ⟨max a 1, le_max_right _ _, fun y hy => ha y (le_trans (le_max_left _ _) hy)⟩

/-- The two basic consequences of `Params`: `x^{1/4+η} < N < x^{1/2}(log x)^{-B}`, hence
`N ≤ x`, `x` is large and `log N ≤ (1/2)·log x`. -/
theorem logN_le_half_logx (Pa : Work.FITop.Params) :
    Real.log Pa.N ≤ (1 / 2) * Real.log (Pa.x : ℝ) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlogx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have hlogx0 : (0 : ℝ) < Real.log (Pa.x : ℝ) := by linarith
  have hpow : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 := by
    calc (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ (Real.log (Pa.x : ℝ)) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith [Pa.hB])
      _ = 1 := Real.rpow_zero _
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hNlt : Pa.N < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
    have h := Pa.hNhi
    have h2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B)
        ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * 1 :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hxpos.le _)
    linarith
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  calc Real.log Pa.N ≤ Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 2)) :=
        Real.log_le_log hNpos hNlt.le
    _ = (1 / 2) * Real.log (Pa.x : ℝ) := Real.log_rpow hxpos _

/-- `C * (log y)^K ≤ y^δ` for `y` large, `C ≥ 0`, `K ≥ 0`, `δ > 0`. -/
theorem const_log_rpow_le_rpow_eventually (C K δ : ℝ) (hC : 0 ≤ C) (_hK : 0 ≤ K)
    (hδ : 0 < δ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ y : ℝ, M ≤ y → C * (Real.log y) ^ K ≤ y ^ δ := by
  have hlittle : (fun y : ℝ => C * Real.log y ^ K) =o[Filter.atTop] (fun y : ℝ => y ^ δ) :=
    (isLittleO_log_rpow_rpow_atTop K hδ).const_mul_left C
  have hbound : ∀ᶠ y : ℝ in Filter.atTop, C * (Real.log y) ^ K ≤ y ^ δ := by
    have h := Asymptotics.IsLittleO.def hlittle (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with y hy hy1
    rw [Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (Real.log_nonneg hy1) K)),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) δ), one_mul] at hy
    exact hy
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hbound
  exact ⟨max a 1, le_max_right _ _, fun y hy => ha y (le_trans (le_max_left _ _) hy)⟩

theorem nuU_pos : (0 : ℝ) < Work.FITop4.nuU := by
  unfold Work.FITop4.nuU Work.FITop4.sigmaChoice Work.FITop4.Aprime Work.FITop4.Asave
  norm_num

/-- The six facts of the absorption lemma. -/
theorem rem_le_arith_self (η : ℝ) (hη0 : 0 < η) (hη3 : η < 3 / 32)
    (δ c7 Cj : ℝ) (hδ : 0 < δ) (hc7 : 0 < c7) (hCj : 0 < Cj) :
    ∃ x0 : ℝ, ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
      Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave →
    ∀ (X : ℕ), (Real.log Pa.N) ^ (2 : ℕ) ≤ (X : ℝ) →
      (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
        (Real.log Pa.N) ^ Work.FITop4.nuU < Pa.N ^ δ ∧
        (2 : ℝ) ≤ Real.log Pa.N ∧
        (3 : ℝ) ≤ (X : ℝ) ∧
        c7 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
          ≤ 2 * c7 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 ∧
        c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
          ≤ 4 * c7 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 ∧
        Cj * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N + 1)
          ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
  have hnuU0 : (0 : ℝ) ≤ (10 : ℝ) / 3 * Work.FITop4.nuU :=
    mul_nonneg (by norm_num) nuU_pos.le
  have hKpos : (0 : ℝ) < 4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)
      + (10 : ℝ) / 3 * Work.FITop4.nuU + 1 := by
    have h2 : (0 : ℝ) < 4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ) + 1 := by
      norm_num [Work.FITop4.Asave]
    nlinarith
  obtain ⟨T1, _, hT1⟩ :=
    log_rpow_le_rpow_eventually Work.FITop4.nuU nuU_pos.le
      (((1 : ℝ) / 4 + η) * δ / 2) (by positivity)
  obtain ⟨T2, _, hT2⟩ :=
    const_log_rpow_le_rpow_eventually (2 * Cj)
      (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ) + (10 : ℝ) / 3 * Work.FITop4.nuU + 1)
      (η / 2) (by positivity) hKpos.le (by positivity)
  refine ⟨max (max T1 T2) (max (Real.exp 8)
    (Real.exp (Real.exp (Work.FITop4.nuU / 3 + 1)))), ?_⟩
  intro Pa hx hPaη hPaτ X hlog2 hXmax
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hxT1 : T1 ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hxT2 : T2 ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hxe8 : Real.exp 8 ≤ (Pa.x : ℝ) :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hxee : Real.exp (Real.exp (Work.FITop4.nuU / 3 + 1)) ≤ (Pa.x : ℝ) :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hlogx8 : (8 : ℝ) ≤ Real.log (Pa.x : ℝ) := (Real.le_log_iff_exp_le hxpos).mpr hxe8
  have hlx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by linarith
  have hlx0 : (0 : ℝ) ≤ Real.log (Pa.x : ℝ) := by linarith
  have hlxpos : (0 : ℝ) < Real.log (Pa.x : ℝ) := by linarith
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hNlo : (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η) < Pa.N := by
    rw [← hPaη]; exact Pa.hNlo
  have hNgt : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) < Pa.N := by
    have hle : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    linarith [hNlo]
  have hL_ge : (1 / 4) * Real.log (Pa.x : ℝ) ≤ Real.log Pa.N := by
    have h1 : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 4)) ≤ Real.log Pa.N :=
      Real.log_le_log (Real.rpow_pos_of_pos hxpos _) hNgt.le
    rwa [Real.log_rpow hxpos] at h1
  have hLpos : (0 : ℝ) < Real.log Pa.N := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log Pa.N := by linarith
  have hLx : Real.log Pa.N ≤ Real.log (Pa.x : ℝ) := by
    have := logN_le_half_logx Pa
    linarith
  -- item 1
  have hitem1 : (Real.log Pa.N) ^ Work.FITop4.nuU < Pa.N ^ δ := by
    have h1 : (Real.log Pa.N) ^ Work.FITop4.nuU
        ≤ (Pa.x : ℝ) ^ (((1 : ℝ) / 4 + η) * δ / 2) :=
      le_trans (Real.rpow_le_rpow hLpos.le hLx nuU_pos.le) (hT1 (Pa.x : ℝ) hxT1)
    have h2 : (Pa.x : ℝ) ^ (((1 : ℝ) / 4 + η) * δ / 2) < Pa.N ^ δ := by
      have hb : ((1 : ℝ) / 4 + η) * δ / 2 < ((1 : ℝ) / 4 + η) * δ := by nlinarith [hδ, hη0]
      have h3 : (Pa.x : ℝ) ^ (((1 : ℝ) / 4 + η) * δ / 2) < (Pa.x : ℝ) ^ (((1 : ℝ) / 4 + η) * δ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by linarith) hb
      have h4 : (Pa.x : ℝ) ^ (((1 : ℝ) / 4 + η) * δ) = ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η)) ^ δ :=
        Real.rpow_mul hxpos.le ((1 : ℝ) / 4 + η) δ
      have h5 : ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η)) ^ δ < Pa.N ^ δ :=
        Real.rpow_lt_rpow (Real.rpow_nonneg hxpos.le _) hNlo hδ
      rw [h4] at h3
      linarith
    linarith
  have hitem3 : (3 : ℝ) ≤ (X : ℝ) := by
    have h4 : (4 : ℝ) ≤ (Real.log Pa.N) ^ (2 : ℕ) := by nlinarith
    linarith
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  -- `log N ≤ X^{2/3}`
  have hL_le_X23 : Real.log Pa.N ≤ (X : ℝ) ^ ((2 : ℝ) / 3) := by
    have hp : (Real.log Pa.N) ^ (4 : ℕ) ≤ (X : ℝ) ^ (2 : ℕ) := by nlinarith
    have h1 : ((Real.log Pa.N) ^ (4 : ℕ)) ^ ((1 : ℝ) / 3)
        ≤ ((X : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hp (by norm_num)
    have h2 : ((Real.log Pa.N) ^ (4 : ℕ)) ^ ((1 : ℝ) / 3) = (Real.log Pa.N) ^ ((4 : ℝ) / 3) := by
      rw [← Real.rpow_natCast (Real.log Pa.N) 4, ← Real.rpow_mul hLpos.le]
      norm_num
    have h3 : ((X : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 3) = (X : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast (X : ℝ) 2, ← Real.rpow_mul hXpos.le]
      norm_num
    have h4 : Real.log Pa.N ≤ (Real.log Pa.N) ^ ((4 : ℝ) / 3) := by
      have := Real.rpow_le_rpow_of_exponent_le (x := Real.log Pa.N) (y := (1 : ℝ))
        (z := (4 : ℝ) / 3) (by linarith) (by norm_num)
      rwa [Real.rpow_one] at this
    rw [h2, h3] at h1
    linarith
  have hXinv : (X : ℝ)⁻¹ * Real.log Pa.N ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) := by
    have he : (X : ℝ) ^ (-(1 : ℝ)) * (X : ℝ) ^ ((2 : ℝ) / 3) = (X : ℝ) ^ (-(1 : ℝ) / 3) := by
      rw [← Real.rpow_add hXpos]; norm_num
    calc (X : ℝ)⁻¹ * Real.log Pa.N = (X : ℝ) ^ (-(1 : ℝ)) * Real.log Pa.N := by
          rw [Real.rpow_neg_one]
      _ ≤ (X : ℝ) ^ (-(1 : ℝ)) * (X : ℝ) ^ ((2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left hL_le_X23 (Real.rpow_nonneg hXpos.le _)
      _ = (X : ℝ) ^ (-(1 : ℝ) / 3) := he
  have hPzpos : (0 : ℝ) < (Pa.Pz : ℝ) := by
    have : (0 : ℕ) < Pa.Pz := by have := Pa.hP2; omega
    exact_mod_cast this
  have hLlog : Real.log (Real.log Pa.N) ≤ Real.log (Real.log (Pa.x : ℝ)) :=
    Real.log_le_log hLpos hLx
  have hloglog_pos : (0 : ℝ) < Real.log (Real.log (Pa.x : ℝ)) := Real.log_pos (by linarith)
  have hc_le : Work.FITop4.nuU / 3 + 1 ≤ Real.log (Real.log (Pa.x : ℝ)) := by
    have h1 : Real.exp (Work.FITop4.nuU / 3 + 1) ≤ Real.log (Pa.x : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp (Work.FITop4.nuU / 3 + 1))) hxee
      rwa [Real.log_exp] at h
    have h2 := Real.log_le_log (Real.exp_pos (Work.FITop4.nuU / 3 + 1)) h1
    rwa [Real.log_exp] at h2
  have hc0 : (0 : ℝ) ≤ Work.FITop4.nuU / 3 + 1 := by have := nuU_pos; linarith
  have hPzdom : (Real.log Pa.N) ^ (Work.FITop4.nuU / 3 + 1) ≤ (Pa.Pz : ℝ) := by
    rw [Real.rpow_le_iff_le_log hLpos hPzpos]
    calc (Work.FITop4.nuU / 3 + 1) * Real.log (Real.log Pa.N)
        ≤ (Work.FITop4.nuU / 3 + 1) * Real.log (Real.log (Pa.x : ℝ)) :=
          mul_le_mul_of_nonneg_left hLlog hc0
      _ ≤ Real.log (Real.log (Pa.x : ℝ)) * Real.log (Real.log (Pa.x : ℝ)) :=
          mul_le_mul_of_nonneg_right hc_le hloglog_pos.le
      _ = (Real.log (Real.log (Pa.x : ℝ))) ^ (2 : ℕ) := by ring
      _ ≤ Real.log (Pa.Pz : ℝ) := Pa.hPlo
  have hX13L : (X : ℝ) ^ ((1 : ℝ) / 3) * Real.log Pa.N ≤ (Pa.Pz : ℝ) := by
    have h1 : (X : ℝ) ^ ((1 : ℝ) / 3) ≤ (Real.log Pa.N) ^ (Work.FITop4.nuU / 3) := by
      have h := Real.rpow_le_rpow (Nat.cast_nonneg X) hXmax (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
      have h2 : ((Real.log Pa.N) ^ Work.FITop4.nuU) ^ ((1 : ℝ) / 3)
          = (Real.log Pa.N) ^ (Work.FITop4.nuU / 3) := by
        rw [← Real.rpow_mul hLpos.le]
        congr 1
        ring
      rwa [h2] at h
    calc (X : ℝ) ^ ((1 : ℝ) / 3) * Real.log Pa.N
        ≤ (Real.log Pa.N) ^ (Work.FITop4.nuU / 3) * Real.log Pa.N :=
          mul_le_mul_of_nonneg_right h1 hLpos.le
      _ = (Real.log Pa.N) ^ (Work.FITop4.nuU / 3 + 1) := by
          rw [Real.rpow_add hLpos, Real.rpow_one]
      _ ≤ (Pa.Pz : ℝ) := hPzdom
  have hPinv : (Pa.Pz : ℝ)⁻¹ * Real.log Pa.N ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) := by
    have hX13inv : (X : ℝ) ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hXpos]; norm_num
    have h1 : Real.log Pa.N ≤ (Pa.Pz : ℝ) * (X : ℝ) ^ (-(1 : ℝ) / 3) := by
      calc Real.log Pa.N = (X : ℝ) ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Real.log Pa.N := by
            rw [hX13inv, one_mul]
        _ = (X : ℝ) ^ (-(1 : ℝ) / 3) * ((X : ℝ) ^ ((1 : ℝ) / 3) * Real.log Pa.N) := by ring
        _ ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) * (Pa.Pz : ℝ) :=
            mul_le_mul_of_nonneg_left hX13L (Real.rpow_nonneg hXpos.le _)
        _ = (Pa.Pz : ℝ) * (X : ℝ) ^ (-(1 : ℝ) / 3) := by ring
    calc (Pa.Pz : ℝ)⁻¹ * Real.log Pa.N
        ≤ (Pa.Pz : ℝ)⁻¹ * ((Pa.Pz : ℝ) * (X : ℝ) ^ (-(1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hPzpos.le)
      _ = (X : ℝ) ^ (-(1 : ℝ) / 3) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hPzpos), one_mul]
  -- items 4 and 5
  have hitem4 : c7 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
      ≤ 2 * c7 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
    have hsum : ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Real.log Pa.N
        ≤ 2 * (X : ℝ) ^ (-(1 : ℝ) / 3) := by
      have h1 : ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Real.log Pa.N
          = (Pa.Pz : ℝ)⁻¹ * Real.log Pa.N + (X : ℝ)⁻¹ * Real.log Pa.N := by ring
      rw [h1]; linarith [hPinv, hXinv]
    calc c7 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
        = c7 * Pa.N ^ 2 * (((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Real.log Pa.N) := by ring
      _ ≤ c7 * Pa.N ^ 2 * (2 * (X : ℝ) ^ (-(1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hc7.le (sq_nonneg _))
      _ = 2 * c7 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by ring
  have hitem5 : c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
      ≤ 4 * c7 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
    have hsum : ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Real.log Pa.N
        ≤ 4 * (X : ℝ) ^ (-(1 : ℝ) / 3) := by
      have h1 : ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Real.log Pa.N
          = (Pa.Pz : ℝ)⁻¹ * Real.log Pa.N + 3 * ((X : ℝ)⁻¹ * Real.log Pa.N) := by ring
      rw [h1]; linarith [hPinv, hXinv]
    calc c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
        = c7 * Pa.N ^ 2 * (((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Real.log Pa.N) := by ring
      _ ≤ c7 * Pa.N ^ 2 * (4 * (X : ℝ) ^ (-(1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hc7.le (sq_nonneg _))
      _ = 4 * c7 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by ring
  -- item 6
  have hτ : Pa.τ = (Real.log (Pa.x : ℝ)) ^ (2 * Work.FITop4.Asave + (2 : ℝ) ^ (20 : ℕ)) := by
    rw [hPaτ]; rfl
  have hτ2 : Pa.τ ^ 2 = (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)) := by
    rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hlx0]
    congr 1
    norm_num [Work.FITop4.Asave]
  have hXpow : (X : ℝ) ^ ((10 : ℝ) / 3)
      ≤ (Real.log Pa.N) ^ ((10 : ℝ) / 3 * Work.FITop4.nuU) := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg X) hXmax (by norm_num : (0 : ℝ) ≤ (10 : ℝ) / 3)
    have h2 : ((Real.log Pa.N) ^ Work.FITop4.nuU) ^ ((10 : ℝ) / 3)
        = (Real.log Pa.N) ^ ((10 : ℝ) / 3 * Work.FITop4.nuU) := by
      rw [← Real.rpow_mul hLpos.le]
      congr 1
      ring
    rwa [h2] at h
  have hLb : (Real.log Pa.N) ^ ((10 : ℝ) / 3 * Work.FITop4.nuU)
      ≤ (Real.log (Pa.x : ℝ)) ^ ((10 : ℝ) / 3 * Work.FITop4.nuU) :=
    Real.rpow_le_rpow hLpos.le hLx hnuU0
  have hLp1 : Real.log Pa.N + 1 ≤ 2 * Real.log (Pa.x : ℝ) := by linarith
  have hN13 : (Pa.x : ℝ) ^ (η / 2) ≤ Pa.N ^ ((1 : ℝ) / 2) := by
    have h2 : ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η)) ^ ((1 : ℝ) / 2) ≤ Pa.N ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hxpos.le _) hNlo.le (by norm_num)
    have h3 : ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η)) ^ ((1 : ℝ) / 2)
        = (Pa.x : ℝ) ^ ((1 : ℝ) / 8 + η / 2) := by
      rw [← Real.rpow_mul hxpos.le]
      congr 1
      ring
    calc (Pa.x : ℝ) ^ (η / 2) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 8 + η / 2) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η)) ^ ((1 : ℝ) / 2) := h3.symm
      _ ≤ Pa.N ^ ((1 : ℝ) / 2) := h2
  have hb : 2 * Cj * (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)
      + (10 : ℝ) / 3 * Work.FITop4.nuU + 1) ≤ (Pa.x : ℝ) ^ (η / 2) := hT2 (Pa.x : ℝ) hxT2
  have hcollapse : (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ))
        * (Real.log (Pa.x : ℝ)) ^ ((10 : ℝ) / 3 * Work.FITop4.nuU)
        * Real.log (Pa.x : ℝ)
      = (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)
          + (10 : ℝ) / 3 * Work.FITop4.nuU + 1) := by
    calc (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ))
          * (Real.log (Pa.x : ℝ)) ^ ((10 : ℝ) / 3 * Work.FITop4.nuU)
          * Real.log (Pa.x : ℝ)
        = (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)
            + (10 : ℝ) / 3 * Work.FITop4.nuU) * Real.log (Pa.x : ℝ) := by
          rw [← Real.rpow_add hlxpos]
      _ = (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)
            + (10 : ℝ) / 3 * Work.FITop4.nuU) * (Real.log (Pa.x : ℝ)) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)
            + (10 : ℝ) / 3 * Work.FITop4.nuU + 1) :=
          (Real.rpow_add hlxpos _ 1).symm
  have h6core : Cj * Pa.τ ^ 2 * (X : ℝ) ^ ((10 : ℝ) / 3) * Pa.N ^ ((3 : ℝ) / 2)
      * (Real.log Pa.N + 1) ≤ Pa.N ^ 2 := by
    have hp1 : Pa.τ ^ 2 * (X : ℝ) ^ ((10 : ℝ) / 3)
        ≤ (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ))
          * (Real.log (Pa.x : ℝ)) ^ ((10 : ℝ) / 3 * Work.FITop4.nuU) :=
      mul_le_mul (le_of_eq hτ2) (le_trans hXpow hLb)
        (Real.rpow_nonneg (Nat.cast_nonneg X) _) (Real.rpow_nonneg hlx0 _)
    have hinner : Pa.τ ^ 2 * ((X : ℝ) ^ ((10 : ℝ) / 3) * (Real.log Pa.N + 1))
        ≤ 2 * (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)
            + (10 : ℝ) / 3 * Work.FITop4.nuU + 1) := by
      have hp2 : Pa.τ ^ 2 * ((X : ℝ) ^ ((10 : ℝ) / 3) * (Real.log Pa.N + 1))
          ≤ 2 * ((Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ))
              * (Real.log (Pa.x : ℝ)) ^ ((10 : ℝ) / 3 * Work.FITop4.nuU)
              * Real.log (Pa.x : ℝ)) := by
        rw [show Pa.τ ^ 2 * ((X : ℝ) ^ ((10 : ℝ) / 3) * (Real.log Pa.N + 1))
              = (Pa.τ ^ 2 * (X : ℝ) ^ ((10 : ℝ) / 3)) * (Real.log Pa.N + 1) by ring]
        refine le_trans (mul_le_mul hp1 hLp1 (by linarith) ?_) (le_of_eq ?_)
        · exact mul_nonneg (Real.rpow_nonneg hlx0 _) (Real.rpow_nonneg hlx0 _)
        · ring
      calc Pa.τ ^ 2 * ((X : ℝ) ^ ((10 : ℝ) / 3) * (Real.log Pa.N + 1))
          ≤ 2 * ((Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ))
              * (Real.log (Pa.x : ℝ)) ^ ((10 : ℝ) / 3 * Work.FITop4.nuU)
              * Real.log (Pa.x : ℝ)) := hp2
        _ = 2 * (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)
              + (10 : ℝ) / 3 * Work.FITop4.nuU + 1) := by rw [hcollapse]
    have hτ2'' : Cj * Pa.τ ^ 2 * (X : ℝ) ^ ((10 : ℝ) / 3) * Pa.N ^ ((3 : ℝ) / 2)
        * (Real.log Pa.N + 1)
        = (Cj * Pa.N ^ ((3 : ℝ) / 2))
          * (Pa.τ ^ 2 * ((X : ℝ) ^ ((10 : ℝ) / 3) * (Real.log Pa.N + 1))) := by ring
    rw [hτ2'']
    calc (Cj * Pa.N ^ ((3 : ℝ) / 2))
          * (Pa.τ ^ 2 * ((X : ℝ) ^ ((10 : ℝ) / 3) * (Real.log Pa.N + 1)))
        ≤ (Cj * Pa.N ^ ((3 : ℝ) / 2))
          * (2 * (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)
              + (10 : ℝ) / 3 * Work.FITop4.nuU + 1)) :=
          mul_le_mul_of_nonneg_left hinner (mul_nonneg hCj.le (Real.rpow_nonneg hNpos.le _))
      _ = 2 * Cj * (Real.log (Pa.x : ℝ)) ^ (4 * Work.FITop4.Asave + (2 : ℝ) ^ (21 : ℕ)
              + (10 : ℝ) / 3 * Work.FITop4.nuU + 1) * Pa.N ^ ((3 : ℝ) / 2) := by ring
      _ ≤ (Pa.x : ℝ) ^ (η / 2) * Pa.N ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hNpos.le _)
      _ ≤ Pa.N ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hN13 (Real.rpow_nonneg hNpos.le _)
      _ = Pa.N ^ 2 := by
          rw [← Real.rpow_add hNpos]
          norm_num
  have hitem6 : Cj * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N + 1)
      ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
    have hXp : (X : ℝ) ^ (-(1 : ℝ) / 3) * (X : ℝ) ^ ((10 : ℝ) / 3) = (X : ℝ) ^ 3 := by
      rw [← Real.rpow_add hXpos]; norm_num
    have hkey : Cj * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N + 1)
        = (X : ℝ) ^ (-(1 : ℝ) / 3)
          * (Cj * Pa.τ ^ 2 * (X : ℝ) ^ ((10 : ℝ) / 3) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N + 1)) := by
      rw [← hXp]; ring
    rw [hkey]
    exact mul_le_mul_of_nonneg_left h6core (Real.rpow_nonneg hXpos.le _)
  exact ⟨hitem1, hL2, hitem3, hitem4, hitem5, hitem6⟩

end

end RemSelfArith

end Work.FIArea4.A4c
