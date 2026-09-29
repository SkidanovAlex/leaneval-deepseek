import Mathlib
import Submission.Work.TMC16Core.Core.scale_split_nr2

/-!
# `Core.scale_sel_nr` — the scale/block selection of the non-resonant branch
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- `K₀ log (4y+4) ≤ y/2` for all large `y`. -/
theorem log_le_half_eventually (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → K₀ * Real.log (4 * (y : ℝ) + 4) ≤ (y : ℝ) / 2 := by
  refine ⟨Nat.ceil ((16 * K₀ + 2) ^ 2 / 4) + 1, fun y hy => ?_⟩
  have hyc : Nat.ceil ((16 * K₀ + 2) ^ 2 / 4) ≤ y := by omega
  have hceil : (16 * K₀ + 2) ^ 2 / 4 ≤ ((Nat.ceil ((16 * K₀ + 2) ^ 2 / 4) : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hycR : ((Nat.ceil ((16 * K₀ + 2) ^ 2 / 4) : ℕ) : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hyc
  have hthr : (16 * K₀ + 2) ^ 2 ≤ 4 * (y : ℝ) + 4 := by nlinarith
  have hxpos : (0 : ℝ) ≤ 4 * (y : ℝ) + 4 := by positivity
  have hlogs : Real.log (4 * (y : ℝ) + 4) ≤ 2 * Real.sqrt (4 * (y : ℝ) + 4) := by
    have h := Real.log_le_rpow_div hxpos (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : (4 * (y : ℝ) + 4) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2)
        = 2 * (4 * (y : ℝ) + 4) ^ ((1 : ℝ) / 2) := by ring
    rw [h2] at h
    rwa [← Real.sqrt_eq_rpow] at h
  set u : ℝ := Real.sqrt (4 * (y : ℝ) + 4) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 4 * (y : ℝ) + 4 := by rw [hu]; exact Real.sq_sqrt hxpos
  have hu_ge : 16 * K₀ + 2 ≤ u := by
    rw [hu]
    have h2 : (0 : ℝ) ≤ 16 * K₀ + 2 := by linarith
    calc 16 * K₀ + 2 = Real.sqrt ((16 * K₀ + 2) ^ 2) := (Real.sqrt_sq h2).symm
      _ ≤ Real.sqrt (4 * (y : ℝ) + 4) := Real.sqrt_le_sqrt hthr
  have hyu : (y : ℝ) = (u ^ 2 - 4) / 4 := by rw [hu2]; ring
  have hmain : K₀ * (2 * u) ≤ (u ^ 2 - 4) / 8 := by
    have hsq : u ^ 2 - 4 ≥ 16 * K₀ * u := by nlinarith [hu_ge, hu0, hK₀]
    nlinarith [hsq]
  have hl := mul_le_mul_of_nonneg_left hlogs hK₀
  have hy2 : (y : ℝ) / 2 = (u ^ 2 - 4) / 8 := by rw [hyu]; ring
  linarith [hl, hmain, hy2]

/-- A fixed lower bound on the scale `s` (sum of all the constants needed). -/
def Sconst (q : ℕ → ℕ) (m T₀ : ℕ) : ℕ :=
  q (m + 1) + q (m + 1) * q (m + 2) + 220 + (40 * q m + 178) + (T₀ + 1)

theorem scale_sel_nr {q : ℕ → ℕ} (hq : ∀ m, 0 < q m) (hmono : StrictMono q)
    (m : ℕ) (T₀ : ℕ) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∃ s a' b' : ℕ,
      1 ≤ s ∧ a' + b' = s ∧ q (m + 1) ≤ s ∧
      q (m + 1) * q (m + 2) ≤ s * q m ∧
      40 * q m + 178 ≤ s * q m ∧
      T₀ ≤ s * q m ∧
      K₀ * Real.log (4 * (y : ℝ) + 4) ≤ (s * q m : ℝ) ∧
      (s * q m : ℝ) ≤ (y : ℝ) ∧
      8 * a' * q m + 6 ≤ 5 * (s * q m) ∧ 10 * b' * q m + 37 ≤ 4 * (s * q m) := by
  have hQpos : 0 < q m := hq m
  have hQ1 : 1 ≤ q m := hQpos
  have hQR : (0 : ℝ) < (q m : ℝ) := by exact_mod_cast hQpos
  obtain ⟨Ylog, hYlog⟩ := log_le_half_eventually K₀ hK₀
  set S : ℕ := Sconst q m T₀ with hS
  have hS_q : q (m + 1) ≤ S := by rw [hS, Sconst]; omega
  have hS_C : q (m + 1) * q (m + 2) ≤ S := by rw [hS, Sconst]; omega
  have hS_40 : 40 * q m + 178 ≤ S := by rw [hS, Sconst]; omega
  have hS_T0 : T₀ + 1 ≤ S := by rw [hS, Sconst]; omega
  refine ⟨max Ylog (2 * (S * q m + 2 * q m + 2) + 1), fun y hy => ?_⟩
  have hy_log : Ylog ≤ y := le_trans (le_max_left _ _) hy
  have hy_big : 2 * (S * q m + 2 * q m + 2) + 1 ≤ y := le_trans (le_max_right _ _) hy
  have hhalf : K₀ * Real.log (4 * (y : ℝ) + 4) ≤ (y : ℝ) / 2 := hYlog y hy_log
  set e : ℕ := Nat.ceil (K₀ * Real.log (4 * (y : ℝ) + 4) / (q m : ℝ)) with he
  have hnonneg : (0 : ℝ) ≤ K₀ * Real.log (4 * (y : ℝ) + 4) / (q m : ℝ) :=
    div_nonneg (mul_nonneg hK₀ (Real.log_nonneg (by linarith))) (le_of_lt hQR)
  have he_ge : K₀ * Real.log (4 * (y : ℝ) + 4) / (q m : ℝ) ≤ (e : ℝ) := by
    rw [he]; exact Nat.le_ceil _
  have he_lt : (e : ℝ) < K₀ * Real.log (4 * (y : ℝ) + 4) / (q m : ℝ) + 1 := by
    rw [he]; exact Nat.ceil_lt_add_one hnonneg
  have hs1 : 1 ≤ S + e := by omega
  have hsq : q (m + 1) ≤ S + e := by omega
  have hsC : q (m + 1) * q (m + 2) ≤ (S + e) * q m := by
    have h1 : q (m + 1) * q (m + 2) ≤ S * q m := by
      calc q (m + 1) * q (m + 2) ≤ S := hS_C
        _ = S * 1 := (mul_one _).symm
        _ ≤ S * q m := Nat.mul_le_mul_left _ hQ1
    exact le_trans h1 (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  have hs40 : 40 * q m + 178 ≤ (S + e) * q m := by
    have h1 : 40 * q m + 178 ≤ S * q m := by
      calc 40 * q m + 178 = (40 * q m + 178) * 1 := (mul_one _).symm
        _ ≤ (40 * q m + 178) * q m := Nat.mul_le_mul_left _ hQ1
        _ ≤ S * q m := Nat.mul_le_mul_right _ hS_40
    exact le_trans h1 (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  have hsT0 : T₀ ≤ (S + e) * q m := by
    have h1 : T₀ + 1 ≤ S * q m := by
      calc T₀ + 1 ≤ S := hS_T0
        _ = S * 1 := (mul_one _).symm
        _ ≤ S * q m := Nat.mul_le_mul_left _ hQ1
    have h2 : S * q m ≤ (S + e) * q m := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  have hlog_le : K₀ * Real.log (4 * (y : ℝ) + 4) ≤ ((S + e : ℕ) : ℝ) * (q m : ℝ) := by
    have hcast : (((S + e : ℕ)) : ℝ) = (S : ℝ) + (e : ℝ) := Nat.cast_add S e
    have h1 : K₀ * Real.log (4 * (y : ℝ) + 4) ≤ (e : ℝ) * (q m : ℝ) := by
      rw [div_le_iff₀ hQR] at he_ge
      linarith
    rw [hcast]
    have hSnn : (0:ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
    have hqmnn : (0:ℝ) ≤ (q m : ℝ) := Nat.cast_nonneg (q m)
    have hprod : (0:ℝ) ≤ (S : ℝ) * (q m : ℝ) := mul_nonneg hSnn hqmnn
    linarith [h1, hprod]
  have hsupper : ((S + e : ℕ) : ℝ) * (q m : ℝ) ≤ (y : ℝ) := by
    have hcast : (((S + e : ℕ)) : ℝ) = (S : ℝ) + (e : ℝ) := Nat.cast_add S e
    have h1 : (e : ℝ) * (q m : ℝ) ≤ K₀ * Real.log (4 * (y : ℝ) + 4) + (q m : ℝ) := by
      have h2 := mul_lt_mul_of_pos_right he_lt hQR
      have h3 : (K₀ * Real.log (4 * (y : ℝ) + 4) / (q m : ℝ) + 1) * (q m : ℝ)
          = K₀ * Real.log (4 * (y : ℝ) + 4) + (q m : ℝ) := by field_simp
      linarith [h2, h3.le, h3.ge]
    have hbigR : ((2 * (S * q m + 2 * q m + 2) + 1 : ℕ) : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast hy_big
    have hkey : (S : ℝ) * (q m : ℝ) + (q m : ℝ) ≤ (y : ℝ) / 2 := by
      have hbR : 2 * ((S : ℝ) * (q m : ℝ)) + 4 * (q m : ℝ) + 5 ≤ (y : ℝ) := by
        have hcast2 : ((2 * (S * q m + 2 * q m + 2) + 1 : ℕ) : ℝ)
            = 2 * ((S : ℝ) * (q m : ℝ)) + 4 * (q m : ℝ) + 5 := by push_cast; ring
        linarith [hbigR, hcast2.le, hcast2.ge]
      linarith [hbR]
    rw [hcast]
    linarith [h1, hhalf, hkey]
  obtain ⟨a', b', hab, ha', hb'⟩ := scale_split_nr2 (q m) (S + e) hQ1 hs40
  exact ⟨S + e, a', b', hs1, hab, hsq, hsC, hs40, hsT0, hlog_le, hsupper, ha', hb'⟩

end Work.TMC16Core.Core
