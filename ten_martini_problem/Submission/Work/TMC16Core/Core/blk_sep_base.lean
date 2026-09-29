import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.CFDefs
import Submission.Work.TMC16Core.Basic.CFCore
import Submission.Work.TMC16Core.Basic.fracDist_spec
import Submission.Work.TMC16Core.CF.cf_data_bridge

noncomputable section

namespace Work.TMC16Core.Core

open Work.TMC16Core
open Work.TMC16Core.Basic

/-! ## Elementary facts about `fracDist` of rationals

`fracDist x = |x - round x|` is the distance of `x` to the nearest integer.  For a rational which
is not an integer the distance is at least the reciprocal of the denominator. -/

/-- `fracDist (t / b) ≥ 1 / b` for `b > 0` and `b ∤ t`. -/
lemma fracDist_rat_ge {t : ℤ} {b : ℕ} (hb : 0 < b) (hdvd : ¬ (b : ℤ) ∣ t) :
    1 / (b : ℝ) ≤ fracDist ((t : ℝ) / (b : ℝ)) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hkey : ∀ z : ℤ, (1 : ℝ) ≤ |(t : ℝ) - (z : ℝ) * (b : ℝ)| := by
    intro z
    have h3 : t - z * (b : ℤ) ≠ 0 := by
      intro h
      exact hdvd ⟨z, by rw [sub_eq_zero.mp h, mul_comm]⟩
    have h4 : (1 : ℤ) ≤ |t - z * (b : ℤ)| := Int.one_le_abs h3
    have hcast : ((t - z * (b : ℤ) : ℤ) : ℝ) = (t : ℝ) - (z : ℝ) * (b : ℝ) := by
      push_cast; ring
    rw [← hcast]
    exact_mod_cast h4
  have hround := hkey (round ((t : ℝ) / (b : ℝ)))
  have hsplit : (t : ℝ) / (b : ℝ) - (round ((t : ℝ) / (b : ℝ)) : ℝ)
      = ((t : ℝ) - (round ((t : ℝ) / (b : ℝ)) : ℝ) * (b : ℝ)) / (b : ℝ) := by
    field_simp
  rw [fracDist, hsplit, abs_div, abs_of_pos hbR]
  rw [div_le_div_iff_of_pos_right hbR]
  linarith [hround]

/-- `fracDist` of an integer is zero. -/
lemma fracDist_intCast (z : ℤ) : fracDist ((z : ℝ)) = 0 := by
  rw [fracDist, round_intCast]
  simp

/-- `fracDist` of a rational. -/
lemma fracDist_rat (c : ℚ) : fracDist ((c : ℝ)) = |((c.num : ℤ) : ℝ) - (round ((c : ℝ)) : ℝ) * (c.den : ℝ)| / (c.den : ℝ) := by
  have hden : (0 : ℝ) < (c.den : ℝ) := by exact_mod_cast c.pos
  have hc : (c : ℝ) = (c.num : ℝ) / (c.den : ℝ) := by
    rw [Rat.cast_def]
  rw [fracDist, hc]
  have hsplit : (c.num : ℝ) / (c.den : ℝ) - (round ((c.num : ℝ) / (c.den : ℝ)) : ℝ)
      = ((c.num : ℝ) - (round ((c.num : ℝ) / (c.den : ℝ)) : ℝ) * (c.den : ℝ)) / (c.den : ℝ) := by
    field_simp
  rw [hsplit, abs_div, abs_of_pos hden]

/-! ## The continued-fraction data force irrationality -/

/-- If `Δ m = fracDist (q m * α) > 0` and `Δ m < 1 / q (m+1)` for a strictly increasing `q`, then `α`
is irrational. -/
theorem irrat_of_cf_data {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ))) : Irrational α := by
  rintro ⟨c, hc⟩
  set b : ℕ := c.den with hbdef
  have hbpos : 0 < b := c.pos
  have hb2 : 2 ≤ b := by
    by_contra hlt
    have hb1 : b = 1 := by omega
    have hnum : (c.num : ℚ) = c := (Rat.den_eq_one_iff c).mp hb1
    have hzero : Δ 0 = 0 := by
      rw [hΔeq 0, ← hc]
      have hcz : (c : ℝ) = (c.num : ℝ) := by rw [← hnum]; simp
      rw [hcz]
      have : ((q 0 : ℝ) * (c.num : ℝ)) = ((q 0 * c.num : ℤ) : ℝ) := by push_cast; ring
      rw [this, fracDist_intCast]
    linarith [hΔpos 0]
  have hrepr : ∀ m : ℕ, ((q m : ℝ) * (c : ℝ)) = ((q m * c.num : ℤ) : ℝ) / (b : ℝ) := by
    intro m
    rw [hbdef, Rat.cast_def]
    push_cast
    ring
  have hnotdvd : ∀ m, ¬ (b : ℤ) ∣ (q m * c.num) := by
    intro m hdvd
    have hzero : fracDist (((q m * c.num : ℤ) : ℝ) / (b : ℝ)) = 0 := by
      obtain ⟨w, hw⟩ := hdvd
      rw [hw]
      have : (((b : ℤ) * w : ℤ) : ℝ) / (b : ℝ) = (w : ℝ) := by
        push_cast
        field_simp
      rw [this, fracDist_intCast]
    have : Δ m = 0 := by rw [hΔeq m, ← hc, hrepr m, hzero]
    linarith [hΔpos m]
  have hkey : ∀ m, (1 : ℝ) / (b : ℝ) ≤ Δ m := by
    intro m
    rw [hΔeq m, ← hc, hrepr m]
    exact fracDist_rat_ge hbpos (hnotdvd m)
  have hbq : ∀ m, q (m + 1) < b := by
    intro m
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
    have hqm : 0 < q (m + 1) := Nat.lt_of_lt_of_le (Nat.succ_pos m) (hmono.id_le (m + 1))
    have hqR : (0 : ℝ) < (q (m + 1) : ℝ) := by exact_mod_cast hqm
    have h1 : (1 : ℝ) / (b : ℝ) < 1 / ((q (m + 1) : ℝ)) := lt_of_le_of_lt (hkey m) (hΔup m)
    rw [one_div, one_div] at h1
    have h2 : (q (m + 1) : ℝ) < (b : ℝ) := (inv_lt_inv₀ hbR hqR).mp h1
    exact_mod_cast h2
  have hcontra : q (b + 1) < b := hbq b
  have hbig : b ≤ q (b + 1) := le_trans (Nat.le_succ b) (hmono.id_le (b + 1))
  omega

/-! ## Continued-fraction estimates for the fractional part `β` -/

/-- The convergent errors of a continued fraction decrease. -/
lemma cfDelta_anti {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β) (l : ℕ) :
    cfDelta β (l + 1) < cfDelta β l := by
  have h1 : cfDelta β (l + 1) < 1 / (cfQ β (l + 2) : ℝ) := cfDelta_lt hβ0 hβ1 hi (l + 1)
  have h2 : 1 / ((cfQ β (l + 1) : ℝ) + (cfQ β l : ℝ)) < cfDelta β l :=
    cfDelta_gt hβ0 hβ1 hi l
  have hQp : (0 : ℝ) < (cfQ β (l + 1) : ℝ) := by
    have h := cfQ_pos hβ0 hβ1 hi (l + 1)
    exact_mod_cast h
  have hQl : (0 : ℝ) < (cfQ β l : ℝ) := by
    have h := cfQ_pos hβ0 hβ1 hi l
    exact_mod_cast h
  have hA : (1 : ℝ) ≤ (cfA β (l + 1) : ℝ) := by
    have h := cfA_one_le hβ0 hβ1 hi (l + 1)
    exact_mod_cast h
  have hQ2 : (cfQ β (l + 2) : ℝ) = (cfA β (l + 1) : ℝ) * (cfQ β (l + 1) : ℝ)
      + (cfQ β l : ℝ) := by
    rw [cfQ_add_two]; push_cast; ring
  have hle : (cfQ β (l + 1) : ℝ) + (cfQ β l : ℝ) ≤ (cfQ β (l + 2) : ℝ) := by
    rw [hQ2]
    nlinarith [hA, hQp, hQl]
  have h3 : 1 / (cfQ β (l + 2) : ℝ)
      ≤ 1 / ((cfQ β (l + 1) : ℝ) + (cfQ β l : ℝ)) := by
    refine one_div_le_one_div_of_le (by linarith) hle
  linarith

/-- The tail identity `1/δ_n = cfQ β (n+1) + cfQ β n * cfX β (n+1)`, in the form
`cfQ β (n+2) + cfQ β (n+1) * cfX β (n+2) = cfQ β (n+1) / cfX β (n+1) + cfQ β n`. -/
lemma cfQ_tail_id {β : ℝ} (l : ℕ) :
    (cfQ β (l + 2) : ℝ) + (cfQ β (l + 1) : ℝ) * cfX β (l + 2)
      = (cfQ β (l + 1) : ℝ) / cfX β (l + 1) + (cfQ β l : ℝ) := by
  have hA : (cfA β (l + 1) : ℝ) = (cfX β (l + 1))⁻¹ - cfX β (l + 2) := by
    have h := cfX_inv_eq β (l + 1)
    linarith
  have hQ : (cfQ β (l + 2) : ℝ) = (cfA β (l + 1) : ℝ) * (cfQ β (l + 1) : ℝ)
      + (cfQ β l : ℝ) := by
    rw [cfQ_add_two]; push_cast; ring
  rw [hQ, hA, div_eq_mul_inv]
  ring

/-- The ratio of two consecutive convergent errors is the continued-fraction tail:
`cfDelta β (l+1) = cfDelta β l * cfX β (l+1)`. -/
lemma cfDelta_ratio {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β) (l : ℕ) :
    cfDelta β (l + 1) = cfDelta β l * cfX β (l + 1) := by
  have hx := cfX_spec hβ0 hβ1 hi
  have hx1 : cfX β (l + 1) ≠ 0 := ne_of_gt (hx (l + 1)).1
  have hden1 : (cfQ β (l + 1) : ℝ) + (cfQ β l : ℝ) * cfX β (l + 1) ≠ 0 :=
    (cfMpos hβ0 hβ1 hi l).ne'
  have hden2 : (cfQ β (l + 2) : ℝ) + (cfQ β (l + 1) : ℝ) * cfX β (l + 2) ≠ 0 :=
    (cfMpos hβ0 hβ1 hi (l + 1)).ne'
  rw [cfDelta, cfDelta]
  rw [show (1 / ((cfQ β (l + 1) : ℝ) + (cfQ β l : ℝ) * cfX β (l + 1))) * cfX β (l + 1)
      = cfX β (l + 1) / ((cfQ β (l + 1) : ℝ) + (cfQ β l : ℝ) * cfX β (l + 1)) by
        rw [div_eq_mul_inv]; ring]
  rw [div_eq_div_iff hden2 hden1]
  rw [one_mul, cfQ_tail_id l]
  field_simp

/-- The mediant identity `cfQ β (l+1) * cfDelta β l + cfQ β l * cfDelta β (l+1) = 1`. -/
lemma cfDelta_mediant {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β) (l : ℕ) :
    (cfQ β (l + 1) : ℝ) * cfDelta β l + (cfQ β l : ℝ) * cfDelta β (l + 1) = 1 := by
  have hx := cfX_spec hβ0 hβ1 hi
  have hden : (cfQ β (l + 1) : ℝ) + (cfQ β l : ℝ) * cfX β (l + 1) ≠ 0 := by
    have := cfMpos hβ0 hβ1 hi l
    exact ne_of_gt this
  rw [cfDelta_ratio hβ0 hβ1 hi l, cfDelta]
  field_simp

/-- `1 / cfQ β (l+1) < cfDelta β l + cfDelta β (l+1)` for `l ≥ 1`. -/
lemma cfDelta_sumbound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β)
    {l : ℕ} (hl : 1 ≤ l) :
    1 / (cfQ β (l + 1) : ℝ) < cfDelta β l + cfDelta β (l + 1) := by
  have hmed := cfDelta_mediant hβ0 hβ1 hi l
  have hQpos : (0 : ℝ) < (cfQ β (l + 1) : ℝ) := by
    have h := cfQ_pos hβ0 hβ1 hi (l + 1)
    exact_mod_cast h
  have hQlt : (cfQ β l : ℝ) < (cfQ β (l + 1) : ℝ) := by
    have h : cfQ β l < cfQ β (l + 1) := cfQ_lt_succ hβ0 hβ1 hi hl
    exact_mod_cast h
  have hdpos : 0 < cfDelta β (l + 1) := cfDelta_pos hβ0 hβ1 hi (l + 1)
  have key : cfDelta β l = (1 - (cfQ β l : ℝ) * cfDelta β (l + 1)) / (cfQ β (l + 1) : ℝ) := by
    rw [eq_div_iff (ne_of_gt hQpos)]
    linarith [hmed]
  have heq : cfDelta β l + cfDelta β (l + 1)
      = (1 + ((cfQ β (l + 1) : ℝ) - (cfQ β l : ℝ)) * cfDelta β (l + 1))
          / (cfQ β (l + 1) : ℝ) := by
    rw [key]
    field_simp
    ring
  rw [heq, div_lt_div_iff_of_pos_right hQpos]
  have hprod : 0 < ((cfQ β (l + 1) : ℝ) - (cfQ β l : ℝ)) * cfDelta β (l + 1) :=
    mul_pos (by linarith) hdpos
  linarith

/-- The signed convergent error: `cfQ β n * β - cfP β n = (-1)^n * cfDelta β n`. -/
lemma cfQ_mul_sub_cfP {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β) (n : ℕ) :
    (cfQ β n : ℝ) * β - (cfP β n : ℝ) = (-1 : ℝ) ^ n * cfDelta β n := by
  rw [cf_error hβ0 hβ1 hi n, cfDelta, div_eq_mul_inv]
  ring

/-- **Best approximation of the second kind** (the standard bound).  For `0 < k < cfQ β (n+1)`,
`cfDelta β n ≤ fracDist (k * β)`. -/
lemma cfDelta_le_fracDist {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β)
    {n : ℕ} {k : ℤ} (hk : 0 < k) (hkq : k < cfQ β (n + 1)) :
    cfDelta β n ≤ fracDist ((k : ℝ) * β) := by
  have h := Work.TMC16Core.CF.cf_best_approx (β := β) (Q := fun m => cfQ β m)
    (P := fun m => cfP β m) (δ := fun m => cfDelta β m)
    (fun m => cfQ_one_le hβ0 hβ1 hi m) (fun m => cf_det β m)
    (fun m => cfDelta_pos hβ0 hβ1 hi m) (fun m => cfQ_mul_sub_cfP hβ0 hβ1 hi m)
    n hk hkq (ℓ := round ((k : ℝ) * β))
  simpa only [fracDist] using h

/-- **Improved best approximation of the second kind.**  For `l ≥ 1` and `1 ≤ k < cfQ β (l+1)`,
`k ≠ cfQ β l`, we have `fracDist (k * β) ≥ cfDelta β l + cfDelta β (l+1)`. -/
lemma cfDelta_le_fracDist_improved {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β)
    {l : ℕ} (hl : 1 ≤ l) {k : ℤ} (hk1 : 1 ≤ k) (hk2 : k < cfQ β (l + 1))
    (hne : k ≠ cfQ β l) :
    cfDelta β l + cfDelta β (l + 1) ≤ fracDist ((k : ℝ) * β) := by
  set A : ℤ := cfQ β l with hA
  set B : ℤ := cfQ β (l + 1) with hB
  set Cc : ℤ := cfP β l with hC
  set D : ℤ := cfP β (l + 1) with hD
  set ℓ : ℤ := round ((k : ℝ) * β) with hℓdef
  have hdet : A * D - Cc * B = 1 ∨ A * D - Cc * B = -1 := by
    have h := cf_det β l
    rw [← hA, ← hB, ← hC, ← hD] at h
    rcases Nat.even_or_odd l with he | ho
    · left; rw [he.neg_one_pow] at h; exact h
    · right; rw [ho.neg_one_pow] at h; exact h
  have hsq : (A * D - Cc * B) * (A * D - Cc * B) = 1 := by
    rcases hdet with h | h <;> rw [h] <;> norm_num
  obtain ⟨a, b, hk_eq, hℓ_eq⟩ :
      ∃ a b : ℤ, k = a * A + b * B ∧ ℓ = a * Cc + b * D := by
    refine ⟨(A * D - Cc * B) * (D * k - B * ℓ), (A * D - Cc * B) * (A * ℓ - Cc * k), ?_, ?_⟩
    · calc k = (A * D - Cc * B) * (A * D - Cc * B) * k := by rw [hsq]; ring
        _ = (A * D - Cc * B) * (D * k - B * ℓ) * A
              + (A * D - Cc * B) * (A * ℓ - Cc * k) * B := by ring
    · calc ℓ = (A * D - Cc * B) * (A * D - Cc * B) * ℓ := by rw [hsq]; ring
        _ = (A * D - Cc * B) * (D * k - B * ℓ) * Cc
              + (A * D - Cc * B) * (A * ℓ - Cc * k) * D := by ring
  have hkR : (k : ℝ) = (a : ℝ) * (A : ℝ) + (b : ℝ) * (B : ℝ) := by
    rw [hk_eq]; push_cast; ring
  have hℓR : (ℓ : ℝ) = (a : ℝ) * (Cc : ℝ) + (b : ℝ) * (D : ℝ) := by
    rw [hℓ_eq]; push_cast; ring
  have hε1 : (A : ℝ) * β - (Cc : ℝ) = (-1 : ℝ) ^ l * cfDelta β l := by
    simpa only [hA, hC] using cfQ_mul_sub_cfP hβ0 hβ1 hi l
  have hε2 : (B : ℝ) * β - (D : ℝ) = (-1 : ℝ) ^ (l + 1) * cfDelta β (l + 1) := by
    simpa only [hB, hD] using cfQ_mul_sub_cfP hβ0 hβ1 hi (l + 1)
  have herr : (k : ℝ) * β - (ℓ : ℝ)
      = (-1 : ℝ) ^ l * ((a : ℝ) * cfDelta β l - (b : ℝ) * cfDelta β (l + 1)) := by
    calc (k : ℝ) * β - (ℓ : ℝ)
        = (a : ℝ) * ((A : ℝ) * β - (Cc : ℝ)) + (b : ℝ) * ((B : ℝ) * β - (D : ℝ)) := by
          rw [hkR, hℓR]; ring
      _ = (a : ℝ) * ((-1 : ℝ) ^ l * cfDelta β l)
            + (b : ℝ) * ((-1 : ℝ) ^ (l + 1) * cfDelta β (l + 1)) := by rw [hε1, hε2]
      _ = (-1 : ℝ) ^ l * ((a : ℝ) * cfDelta β l - (b : ℝ) * cfDelta β (l + 1)) := by
          have hs : (-1 : ℝ) ^ (l + 1) = -((-1 : ℝ) ^ l) := by rw [pow_succ]; ring
          rw [hs]; ring
  have habs : fracDist ((k : ℝ) * β)
      = |(a : ℝ) * cfDelta β l - (b : ℝ) * cfDelta β (l + 1)| := by
    rw [fracDist, ← hℓdef, herr, abs_mul, abs_neg_one_pow, one_mul]
  have hA1 : (1 : ℤ) ≤ A := by rw [hA]; exact cfQ_one_le hβ0 hβ1 hi l
  have hB1 : (1 : ℤ) ≤ B := by rw [hB]; exact cfQ_one_le hβ0 hβ1 hi (l + 1)
  have hB0 : (0 : ℤ) ≤ B := by omega
  have hcases : (1 ≤ a ∧ b ≤ 0) ∨ (a ≤ -1 ∧ 1 ≤ b) := by
    by_cases ha : 1 ≤ a
    · refine Or.inl ⟨ha, ?_⟩
      by_contra hb
      have hb1 : 1 ≤ b := by omega
      have hA0 : (0 : ℤ) ≤ A := by omega
      have h1a : A ≤ a * A := by
        calc A = 1 * A := by ring
          _ ≤ a * A := mul_le_mul_of_nonneg_right ha hA0
      have h1b : B ≤ b * B := by
        calc B = 1 * B := by ring
          _ ≤ b * B := mul_le_mul_of_nonneg_right hb1 hB0
      have hgoal : A + B ≤ k := by rw [hk_eq]; linarith
      have h2 : A + B < B := lt_of_le_of_lt hgoal hk2
      have h3 : A < 0 := by linarith
      linarith [h3, hA1]
    · have ha0 : a ≤ 0 := by omega
      have ha' : a ≤ -1 := by
        rcases lt_or_eq_of_le ha0 with h | h
        · omega
        · exfalso
          subst h
          simp only [zero_mul, zero_add] at hk_eq
          by_cases hb : b ≤ 0
          · have h4 : b * B ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb hB0
            rw [hk_eq] at hk1
            omega
          · have hb1 : 1 ≤ b := by omega
            have h4 : B ≤ b * B := by
              calc B = 1 * B := by ring
                _ ≤ b * B := mul_le_mul_of_nonneg_right hb1 hB0
            rw [hk_eq] at hk2
            omega
      refine Or.inr ⟨ha', ?_⟩
      by_contra hb
      have hb0 : b ≤ 0 := by omega
      have h2 : a * A ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      have h3 : b * B ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb0 hB0
      have hgoal : k ≤ 0 := by rw [hk_eq]; linarith
      linarith [hgoal, hk1]
  rw [habs]
  have hδl : 0 < cfDelta β l := cfDelta_pos hβ0 hβ1 hi l
  have hδs : 0 < cfDelta β (l + 1) := cfDelta_pos hβ0 hβ1 hi (l + 1)
  have hδle : cfDelta β (l + 1) < cfDelta β l := cfDelta_anti hβ0 hβ1 hi l
  rcases hcases with ⟨ha1, hb0⟩ | ⟨ha1, hb1⟩
  · have hnn : 0 ≤ (a : ℝ) * cfDelta β l - (b : ℝ) * cfDelta β (l + 1) := by
      have h1 : (0 : ℝ) ≤ (a : ℝ) * cfDelta β l :=
        mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ a)) (le_of_lt hδl)
      have h2 : (b : ℝ) * cfDelta β (l + 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hb0) (le_of_lt hδs)
      linarith
    rw [abs_of_nonneg hnn]
    by_cases hb : b = 0
    · subst hb
      have ha2 : (2 : ℤ) ≤ a := by
        rcases lt_or_eq_of_le ha1 with h | h
        · omega
        · exfalso
          have ha_eq : a = 1 := h.symm
          apply hne
          rw [hk_eq, ha_eq]; ring
      have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
      have hmono := mul_le_mul_of_nonneg_right haR (le_of_lt hδl)
      simp only [Int.cast_zero, zero_mul, sub_zero]
      linarith
    · have hbR : (b : ℝ) ≤ -1 := by
        have h : b ≤ -1 := by omega
        exact_mod_cast h
      have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
      nlinarith
  · have hnp : (a : ℝ) * cfDelta β l - (b : ℝ) * cfDelta β (l + 1) ≤ 0 := by
      have h1 : (a : ℝ) * cfDelta β l ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by
          have : (a : ℝ) ≤ -1 := by exact_mod_cast ha1
          linarith) (le_of_lt hδl)
      have h2 : (0 : ℝ) ≤ (b : ℝ) * cfDelta β (l + 1) :=
        mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ b)) (le_of_lt hδs)
      linarith
    rw [abs_of_nonpos hnp]
    have haR : (a : ℝ) ≤ -1 := by exact_mod_cast ha1
    have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    nlinarith

/-- **The separation fact.**  For `j ≥ 1` and `1 ≤ x < cfQ β (j+1)` with `x ≠ cfQ β j`,
`fracDist (x * β) ≥ 1 / cfQ β (j+1)`. -/
lemma cfQ_fact {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β)
    {j : ℕ} (hj : 1 ≤ j) {x : ℤ} (hx1 : 1 ≤ x) (hx2 : x < cfQ β (j + 1))
    (hne : x ≠ cfQ β j) :
    1 / (cfQ β (j + 1) : ℝ) ≤ fracDist ((x : ℝ) * β) := by
  have h1 := cfDelta_le_fracDist_improved hβ0 hβ1 hi hj hx1 hx2 hne
  have h2 := cfDelta_sumbound hβ0 hβ1 hi hj
  linarith

/-- The `j = 0` case of the separation fact: for `1 ≤ x < cfQ β 1` with `x ≠ 1`,
`fracDist (x * β) ≥ 1 / cfQ β 1`. -/
lemma cfQ_fact_zero {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β)
    {x : ℤ} (hx1 : 1 ≤ x) (hx2 : x < cfQ β 1) (hne : x ≠ 1) :
    1 / (cfQ β 1 : ℝ) ≤ fracDist ((x : ℝ) * β) := by
  have hQ1 : cfQ β 1 = cfA β 0 := cfQ_one β
  have hA1 : (1 : ℤ) ≤ cfA β 0 := cfA_one_le hβ0 hβ1 hi 0
  have hcnv : (cfA β 0 : ℝ) ≤ 1 / β := by
    simpa only [cfA_apply, cfX_zero, one_div] using Int.floor_le (β⁻¹)
  have hcnv2 : 1 / β < (cfA β 0 : ℝ) + 1 := by
    simpa only [cfA_apply, cfX_zero, one_div] using Int.lt_floor_add_one (β⁻¹)
  have hb2 : 2 ≤ cfA β 0 := by
    rcases lt_or_eq_of_le hA1 with h | h
    · omega
    · exfalso
      have h1 : cfQ β 1 = 1 := by rw [hQ1, h.symm]
      rw [h1] at hx2
      omega
  have hcast : (0 : ℝ) < (cfA β 0 : ℝ) := by
    exact_mod_cast (by omega : (0:ℤ) < cfA β 0)
  have hAbeta : (cfA β 0 : ℝ) * β ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hcnv (le_of_lt hβ0)
    rwa [one_div_mul_cancel (ne_of_gt hβ0)] at h
  have hβa : β ≤ 1 / (cfA β 0 : ℝ) := by
    rw [le_div_iff₀ hcast, mul_comm]
    exact hAbeta
  have hxle : (x : ℤ) ≤ cfA β 0 - 1 := by
    rw [hQ1] at hx2
    omega
  have hxβ_pos : 0 < (x : ℝ) * β := mul_pos (by exact_mod_cast (by omega : (0:ℤ) < x)) hβ0
  have hb2R : (2 : ℝ) ≤ (cfA β 0 : ℝ) := by exact_mod_cast hb2
  have hxa : (x : ℝ) * β ≤ 1 - 1 / (cfA β 0 : ℝ) := by
    have h1 : (x : ℝ) ≤ (cfA β 0 : ℝ) - 1 := by exact_mod_cast hxle
    calc (x : ℝ) * β ≤ ((cfA β 0 : ℝ) - 1) * β := mul_le_mul_of_nonneg_right h1 (le_of_lt hβ0)
      _ ≤ ((cfA β 0 : ℝ) - 1) * (1 / (cfA β 0 : ℝ)) :=
            mul_le_mul_of_nonneg_left hβa (by linarith [hb2R])
      _ = 1 - 1 / (cfA β 0 : ℝ) := by
            rw [mul_one_div, sub_div, div_self (ne_of_gt hcast)]
  have hxβ_lt1 : (x : ℝ) * β < 1 := by
    have h6 : 0 < 1 / (cfA β 0 : ℝ) := by positivity
    linarith
  have hltβ : 1 < β * ((cfA β 0 : ℝ) + 1) := by
    have h := mul_lt_mul_of_pos_right hcnv2 hβ0
    rw [div_mul_cancel₀ (1 : ℝ) (ne_of_gt hβ0), mul_comm] at h
    exact h
  have hge : 1 / (cfA β 0 : ℝ) ≤ (x : ℝ) * β := by
    have hx2R : (2 : ℝ) ≤ (x : ℝ) := by
      have : (2 : ℤ) ≤ x := by omega
      exact_mod_cast this
    have hprod : 2 < (x : ℝ) * β * ((cfA β 0 : ℝ) + 1) := by
      nlinarith [hx2R, hltβ, hβ0, hcast]
    rw [div_le_iff₀ hcast]
    nlinarith [hprod, hxβ_lt1]
  have hle' : 1 / (cfA β 0 : ℝ) ≤ 1 - (x : ℝ) * β := by linarith [hxa]
  have hfd : fracDist ((x : ℝ) * β) = min ((x : ℝ) * β) (1 - (x : ℝ) * β) := by
    rcases lt_or_ge ((x : ℝ) * β) (1 / 2) with h | h
    · have hy : (x : ℝ) * β ≤ 1 - (x : ℝ) * β := by linarith
      have hround : round ((x : ℝ) * β) = 0 := by
        rw [round_eq_iff, Set.mem_Ico]
        refine ⟨?_, ?_⟩
        · simp only [Int.cast_zero, zero_sub]
          linarith [hxβ_pos]
        · simpa using h
      rw [fracDist, hround]
      simp only [Int.cast_zero, sub_zero, abs_of_pos hxβ_pos]
      exact (min_eq_left hy).symm
    · have hy : 1 - (x : ℝ) * β ≤ (x : ℝ) * β := by linarith
      have hround : round ((x : ℝ) * β) = 1 := by
        rw [round_eq_iff, Set.mem_Ico]
        refine ⟨?_, ?_⟩
        · simp only [Int.cast_one]
          linarith
        · simp only [Int.cast_one]
          linarith [hxβ_lt1]
      rw [fracDist, hround]
      simp only [Int.cast_one]
      have h1 : (x : ℝ) * β - 1 ≤ 0 := by linarith [hxβ_lt1]
      rw [abs_of_nonpos h1, neg_sub]
      exact (min_eq_right hy).symm
  rw [hQ1, hfd]
  exact le_min hge hle'

/-! ## The chain of continued-fraction denominators -/

/-- The block of the chain lying in `[q m, q (m+1))`: for `k ≥ q 0` there is `m` with
`q m ≤ k < q (m+1)`. -/
lemma exists_block {q : ℕ → ℕ} (hmono : StrictMono q) {k : ℕ} (hk : q 0 ≤ k) :
    ∃ m, q m ≤ k ∧ k < q (m + 1) := by
  have hex : ∃ M, k < q M := ⟨k + 1, lt_of_lt_of_le (Nat.lt_succ_self k) (hmono.id_le (k + 1))⟩
  have hpos : 1 ≤ Nat.find hex := by
    by_contra h
    have h0 : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [h0] at this
    omega
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    have hnot : ¬ (k < q (Nat.find hex - 1)) := Nat.find_min hex hlt
    omega
  · have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [heq]
    exact Nat.find_spec hex

/-- **Every continued-fraction denominator beyond the base scale is a chain element.** -/
lemma chain_records {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hi : Irrational β)
    {q : ℕ → ℕ} {Δ : ℕ → ℝ} (hmono : StrictMono q) (hqpos : ∀ m, 0 < q m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * β))
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * β))
    {j : ℕ} (hj : 1 ≤ j) (hge : q 0 ≤ (cfQ β j).toNat) :
    ∃ m, q m = (cfQ β j).toNat := by
  have hQZ : ((cfQ β j).toNat : ℤ) = cfQ β j := by
    refine Int.toNat_of_nonneg ?_
    have := cfQ_one_le hβ0 hβ1 hi j
    omega
  obtain ⟨m, hm1, hm2⟩ := exists_block hmono hge
  by_cases hcase : q m = (cfQ β j).toNat
  · exact ⟨m, hcase⟩
  · exfalso
    have hlt : q m < (cfQ β j).toNat := by omega
    have hmin : Δ m ≤ fracDist (((cfQ β j).toNat : ℝ) * β) := hbest m _ hm1 hm2
    have hcast : ((cfQ β j).toNat : ℝ) = (cfQ β j : ℝ) := by
      rw [← Int.cast_natCast]
      exact_mod_cast hQZ
    have hK : fracDist (((cfQ β j).toNat : ℝ) * β) = cfDelta β j := by
      rw [hcast]
      exact cf_fracDist_eq_cfDelta hβ0 hβ1 hi hj
    have hqmj : ((q m : ℕ) : ℤ) < cfQ β j := by
      have h2 : ((q m : ℕ) : ℤ) < (((cfQ β j).toNat : ℤ)) := by exact_mod_cast hlt
      rwa [hQZ] at h2
    have hqm0 : (0 : ℤ) < (q m : ℤ) := by exact_mod_cast (hqpos m)
    have hsep := cfDelta_le_fracDist hβ0 hβ1 hi (n := j - 1) hqm0 (by
      have : j - 1 + 1 = j := Nat.sub_add_cancel hj
      rw [this]; exact hqmj)
    have hgm : cfDelta β (j - 1) ≤ Δ m := by rw [hΔeq m]; exact hsep
    have hlt2 : cfDelta β (j - 1) > cfDelta β j := by
      have h := cfDelta_anti hβ0 hβ1 hi (j - 1)
      rwa [Nat.sub_add_cancel hj] at h
    linarith [hmin, hK, hgm, hlt2]

/-- **Separation of a continued-fraction block at the base scale** (AJ §9, estimate (cf2)).

`q` is a strictly increasing sequence of "continued-fraction denominators" for the irrational
frequency `α`: `Δ m = fracDist (q m * α)` satisfies `1/(q(m+1)+q(m)) < Δ m < 1/q(m+1)`, and
`Δ m` is minimal on the block of multiples `[q m, q(m+1))`.  The claim is that the block of the
first `q 0` multiples is separated from `ℤ`: every `d ∈ [1, q 0 - 1]` has
`fracDist (d * α) ≥ 1/(2 * q 0)`.

This is the classical fact that the convergents are the denominators of the best
approximations; it is the base case of the (easy) induction over the blocks `[q m, q(m+1))`.
The content is the rigidity of the hypotheses: they force `q 0` to be a continued-fraction
denominator of `α`, after which `fracDist (d*α) ≥ Δ_{j-1} > 1/(Q_j + Q_{j-1}) ≥ 1/(2 Q_j)`.

Note (found numerically): admissibility of a *prefix* of the hypotheses is not enough --
e.g. `α = √24 - 4` admits `q 0 = 20`, `q 1 = 30`, `q 2 = 31` satisfying the hypotheses for
`m = 0,1,2` (with a violator `d = 10`, `‖10α‖ ≈ 0.0016 < 1/40`); the contradiction only appears
at the next level.  So the proof must use the hypotheses at *all* `m`.

Available machinery (all proved, in this workspace):
* `Submission.Work.TMC16Core.CF.cf_data_bridge` (`Work.TMC16Core.CF`): `cfQ`, `cfP`, `cfX`,
  `cf_error_package` (the sandwich plus `1/(cfQ (n+2)+cfQ (n+1)) < δ n`),
  `cf_best_approx` (`δ n ≤ |k*β - ℓ|` for `0 < k < Q (n+1)`), `cf_lattice_approx`.
* `Mathlib.NumberTheory.DiophantineApproximation.Basic`: `Real.exists_rat_eq_convergent`
  (Legendre: `|ξ - r| < 1/(2 * r.den^2)` implies `r` is a convergent) and `Real.convergent`.

Useful consequences of the hypotheses: `α` is irrational; `q 0 * ‖q 0 * α‖ < 1`; if
`q 1 ≥ 2 * q 0` then Legendre applied to `p = round (q 0 * α)` already identifies `q 0` with a
convergent denominator.  In the remaining case `q 0 < q 1 < 2 * q 0`, if a violator
`d < q 0` with `‖d*α‖ < 1/(2*q 0)` existed, the determinant
`q 0 * round (d*α) - round (q 0*α) * d ∈ ℤ` has absolute value `< 3/2`, hence is `0` or `±1`;
the case `0` forces `round (d*α)/d = round (q 0*α)/q 0` as reduced fractions, so that
`‖d*α‖ = d * Δ 0 / q 0 < Δ 0` exhibits `d` as a better approximation than `q 0`; the case `±1`
forces `d > q 1/2`. -/
theorem blk_sep_base {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
      Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α)) :
    ∀ d : ℕ, 1 ≤ d → d < q 0 →
      1 / (2 * (q 0 : ℝ)) ≤ Work.TMC16Core.fracDist ((d : ℝ) * α) := by
  have hαi : Irrational α := irrat_of_cf_data hmono hΔpos hΔeq hΔup
  set β : ℝ := Int.fract α with hβdef
  have hβ0 : 0 < β := by
    rw [hβdef]; exact Int.fract_pos.mpr (hαi.ne_int ⌊α⌋)
  have hβ1 : β < 1 := by rw [hβdef]; exact Int.fract_lt_one α
  have hβi : Irrational β := by
    rw [hβdef]; exact hαi.sub_intCast ⌊α⌋
  have htrans : ∀ k : ℕ, fracDist ((k : ℝ) * β) = fracDist ((k : ℝ) * α) := by
    intro k
    rw [hβdef]
    exact (Work.TMC16Core.CF.fracDist_mul_natCast_fract α k).symm
  have hΔeq' : ∀ m, Δ m = fracDist ((q m : ℝ) * β) := by
    intro m; rw [hΔeq m, htrans (q m)]
  have hbest' : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * β) := by
    intro m k h1 h2
    rw [htrans k]
    exact hbest m k h1 h2
  set Q : ℕ → ℕ := fun j => (cfQ β j).toNat with hQdef
  have hQZ : ∀ j, (Q j : ℤ) = cfQ β j := by
    intro j
    rw [hQdef]; simp only
    exact Int.toNat_of_nonneg (by have := cfQ_one_le hβ0 hβ1 hβi j; omega)
  have hQ0 : Q 0 = 1 := by rw [hQdef]; simp [cfQ_zero]
  have hQ1le : ∀ j, 1 ≤ Q j := by
    intro j
    have h1 := cfQ_one_le hβ0 hβ1 hβi j
    have h2 := hQZ j
    omega
  have hQmono : ∀ j, 1 ≤ j → Q j < Q (j + 1) := by
    intro j hj
    have h1 := cfQ_lt_succ hβ0 hβ1 hβi hj
    have h2 := hQZ j
    have h3 := hQZ (j + 1)
    omega
  have hQle : ∀ j, j ≤ Q j := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        have := hQ1le 1
        omega
      · have := hQmono j h
        omega
  have hclaim : ∃ l, Q l = q 0 := by
    by_contra hcon
    push_neg at hcon
    have hqm2 : 2 ≤ q 0 := by
      by_cases h : q 0 = 1
      · exact (hcon 0 (by rw [hQ0, h])).elim
      · have := hqpos 0
        omega
    have hex : ∃ j, q 0 ≤ Q j := ⟨q 0, hQle (q 0)⟩
    obtain ⟨j0, hj0eq⟩ : ∃ j : ℕ, j = Nat.find hex := ⟨_, rfl⟩
    have hj0spec : q 0 ≤ Q j0 := by rw [hj0eq]; exact Nat.find_spec hex
    have hj0min : ∀ i, i < j0 → ¬ (q 0 ≤ Q i) := by
      intro i hi
      have h2 : i < Nat.find hex := by omega
      exact Nat.find_min hex h2
    have hj0pos : 1 ≤ j0 := by
      by_contra h
      have h0 : j0 = 0 := by omega
      have h1 : q 0 ≤ Q 0 := by rw [h0] at hj0spec; exact hj0spec
      rw [hQ0] at h1
      omega
    have hjlt : Q (j0 - 1) < q 0 := by
      have := hj0min (j0 - 1) (by omega)
      omega
    have hjge : q 0 ≤ Q (j0 - 1 + 1) := by
      have h1 : j0 - 1 + 1 = j0 := Nat.sub_add_cancel hj0pos
      rw [h1]; exact hj0spec
    have hne : q 0 ≠ Q (j0 - 1 + 1) := by
      intro heq
      exact hcon (j0 - 1 + 1) heq.symm
    have hlt : q 0 < Q (j0 - 1 + 1) := lt_of_le_of_ne hjge hne
    obtain ⟨m', hm'⟩ := chain_records hβ0 hβ1 hβi hmono hqpos hΔeq' hbest'
      (j := j0 - 1 + 1) (by omega) (le_of_lt hlt)
    have hm'pos : 1 ≤ m' := by
      by_contra h
      have h0 : m' = 0 := by omega
      have h1 : q 0 = Q (j0 - 1 + 1) := by rw [h0] at hm'; exact hm'
      omega
    have hxge : Q (j0 - 1) < q (m' - 1) := by
      have h1 : q 0 ≤ q (m' - 1) := hmono.monotone (by omega)
      omega
    have hxlt : q (m' - 1) < Q (j0 - 1 + 1) := by
      have h1 : m' - 1 < m' := by omega
      have h2 := hmono h1
      rw [hm'] at h2
      exact h2
    have hx1 : 1 ≤ q (m' - 1) := by have := hqpos (m' - 1); omega
    have hQcast : ((Q (j0 - 1 + 1) : ℕ) : ℝ) = (cfQ β (j0 - 1 + 1) : ℝ) := by
      rw [← Int.cast_natCast]
      exact_mod_cast (hQZ (j0 - 1 + 1))
    have hfact : 1 / (Q (j0 - 1 + 1) : ℝ) ≤ fracDist ((q (m' - 1) : ℝ) * β) := by
      rcases Nat.eq_zero_or_pos (j0 - 1) with h0 | hpos
      · have hj1 : j0 - 1 + 1 = 1 := by omega
        rw [hj1] at hxlt ⊢
        have hQcast1 : ((Q 1 : ℕ) : ℝ) = (cfQ β 1 : ℝ) := by
          rw [← Int.cast_natCast]
          exact_mod_cast (hQZ 1)
        rw [hQcast1]
        refine cfQ_fact_zero hβ0 hβ1 hβi (x := (q (m' - 1) : ℤ)) ?_ ?_ ?_
        · exact_mod_cast hx1
        · have h4 : ((q (m' - 1) : ℕ) : ℤ) < (Q 1 : ℤ) := by exact_mod_cast hxlt
          rw [hQZ 1] at h4
          exact h4
        · intro hxeq
          have h6 : (2 : ℤ) ≤ (q (m' - 1) : ℤ) := by
            have h7 : q 0 ≤ q (m' - 1) := hmono.monotone (by omega)
            omega
          omega
      · rw [hQcast]
        refine cfQ_fact hβ0 hβ1 hβi hpos (x := (q (m' - 1) : ℤ)) ?_ ?_ ?_
        · exact_mod_cast hx1
        · have h4 : ((q (m' - 1) : ℕ) : ℤ) < (Q (j0 - 1 + 1) : ℤ) := by exact_mod_cast hxlt
          rwa [hQZ (j0 - 1 + 1)] at h4
        · intro hxeq
          have h5 : (Q (j0 - 1) : ℤ) < cfQ β (j0 - 1) := by
            have h6 : (Q (j0 - 1) : ℤ) < ((q (m' - 1) : ℕ) : ℤ) := by exact_mod_cast hxge
            have h7 : (q (m' - 1) : ℤ) = cfQ β (j0 - 1) := by exact_mod_cast hxeq
            rw [h7] at h6
            exact h6
          rw [hQZ (j0 - 1)] at h5
          exact absurd h5 (lt_irrefl _)
    have hup := hΔup (m' - 1)
    have hqm' : q (m' - 1 + 1) = Q (j0 - 1 + 1) := by
      have h1 : m' - 1 + 1 = m' := Nat.sub_add_cancel hm'pos
      rw [h1, hm']
    rw [hqm', hΔeq' (m' - 1)] at hup
    linarith [hfact, hup]
  obtain ⟨l, hl⟩ := hclaim
  rcases Nat.eq_zero_or_pos l with hl0 | hlpos
  · intro d hd1 hd0
    have h1 : q 0 = 1 := by rw [← hl, hl0, hQ0]
    omega
  · have hl1 : 1 ≤ l := hlpos
    have hcfq : (cfQ β l : ℝ) = (q 0 : ℝ) := by
      have h1 : (Q l : ℝ) = (cfQ β l : ℝ) := by
        rw [← Int.cast_natCast]
        exact_mod_cast (hQZ l)
      rw [← h1, hl]
    intro d hd1 hd0
    have hdQ : ((d : ℕ) : ℤ) < cfQ β l := by
      have h1 : d < Q l := by rw [hl]; exact hd0
      have h3 : ((d : ℕ) : ℤ) < (Q l : ℤ) := by exact_mod_cast h1
      rwa [hQZ l] at h3
    have hsep : cfDelta β (l - 1) ≤ fracDist ((d : ℝ) * β) := by
      refine cfDelta_le_fracDist hβ0 hβ1 hβi (n := l - 1) (k := (d : ℤ))
        (by exact_mod_cast (by omega : (0 : ℤ) < (d : ℤ))) ?_
      have h1 : l - 1 + 1 = l := Nat.sub_add_cancel hl1
      rw [h1]
      exact hdQ
    have hgt : 1 / ((cfQ β l : ℝ) + (cfQ β (l - 1) : ℝ)) < cfDelta β (l - 1) := by
      have h1 : l - 1 + 1 = l := Nat.sub_add_cancel hl1
      simpa only [h1] using cfDelta_gt hβ0 hβ1 hβi (l - 1)
    have hle : (cfQ β (l - 1) : ℝ) ≤ (cfQ β l : ℝ) := by
      rcases Nat.eq_zero_or_pos (l - 1) with h | h
      · have h1 : l = 1 := by omega
        rw [h, h1, cfQ_zero]
        have := cfQ_one_le hβ0 hβ1 hβi 1
        exact_mod_cast this
      · have h1 := cfQ_lt_succ hβ0 hβ1 hβi h
        have h2 : l - 1 + 1 = l := Nat.sub_add_cancel hl1
        rw [h2] at h1
        exact_mod_cast h1.le
    have hQlpos : (0 : ℝ) < (cfQ β l : ℝ) := by
      have h := cfQ_one_le hβ0 hβ1 hβi l
      have h' : (1 : ℝ) ≤ (cfQ β l : ℝ) := by exact_mod_cast h
      linarith
    have hQlmpos : (0 : ℝ) < (cfQ β (l - 1) : ℝ) := by
      have h := cfQ_one_le hβ0 hβ1 hβi (l - 1)
      have h' : (1 : ℝ) ≤ (cfQ β (l - 1) : ℝ) := by exact_mod_cast h
      linarith
    have hmain : 1 / (2 * (cfQ β l : ℝ)) ≤ fracDist ((d : ℝ) * β) := by
      have h2 : (2 * (cfQ β l : ℝ))⁻¹ ≤ ((cfQ β l : ℝ) + (cfQ β (l - 1) : ℝ))⁻¹ := by
        rw [inv_le_inv₀ (by linarith) (by linarith)]
        linarith
      calc 1 / (2 * (cfQ β l : ℝ)) = (2 * (cfQ β l : ℝ))⁻¹ := by rw [one_div]
        _ ≤ ((cfQ β l : ℝ) + (cfQ β (l - 1) : ℝ))⁻¹ := h2
        _ = 1 / ((cfQ β l : ℝ) + (cfQ β (l - 1) : ℝ)) := by rw [one_div]
        _ ≤ fracDist ((d : ℝ) * β) := le_of_lt (lt_of_lt_of_le hgt hsep)
    rw [htrans d, hcfq] at hmain
    exact hmain

end Work.TMC16Core.Core
