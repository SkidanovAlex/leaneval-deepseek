import Mathlib
import Submission.Work.Resample.buDefs

namespace Work.Resample

open HvdH

theorem buArith (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    5 + (Work.Resample.egN p α s t : ℝ) * (18 * (Work.Resample.egM p α : ℝ) + 24)
      < (p : ℝ) ^ 2 := by
  have hs0 : 0 < s := by omega
  have hspos : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs0
  have hA2 : (2:ℝ) ≤ (α:ℝ) := by exact_mod_cast hα
  have hApos : (0:ℝ) < (α:ℝ) := by linarith
  have hx100 : (100:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hxpos : (0:ℝ) < (p:ℝ) := by linarith
  have htsle : s ≤ t := le_of_lt hst
  have hMpos : 0 < α ^ 2 * (t - s) := by
    apply Nat.mul_pos
    · exact pow_pos (by omega) 2
    · exact Nat.sub_pos_of_lt hst
  have hMposR : (0:ℝ) < ((α ^ 2 * (t - s) : ℕ) : ℝ) := by exact_mod_cast hMpos
  -- key real fact from hθ : p s ≤ α^4 (t - s)
  have hsub : ((t - s : ℕ) : ℝ) = (t:ℝ) - (s:ℝ) := Nat.cast_sub htsle
  have hθs : ((p:ℝ) / (α:ℝ)^4) * (s:ℝ) ≤ ((t - s : ℕ):ℝ) := by
    have h := mul_le_mul_of_nonneg_right hθ (le_of_lt hspos)
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hspos), one_mul] at h
    rw [← hsub] at h
    exact h
  have hA4pos : 0 < (α:ℝ)^4 := pow_pos hApos 4
  have hps : (p:ℝ) * (s:ℝ) ≤ ((t - s : ℕ):ℝ) * (α:ℝ)^4 := by
    have h := mul_le_mul_of_nonneg_right hθs (le_of_lt hA4pos)
    have h1 : ((p:ℝ)/(α:ℝ)^4 * (s:ℝ)) * (α:ℝ)^4 = (p:ℝ)*(s:ℝ) := by
      field_simp
    rwa [h1] at h
  -- bound on egN
  have hN : (egN p α s t : ℝ) ≤ (α:ℝ)^2 + 1 := by
    rw [egN]
    have hcast : (((p * s - 1) / (α ^ 2 * (t - s)) : ℕ) : ℝ) ≤ (α:ℝ)^2 := by
      have h1 : (((p * s - 1) / (α ^ 2 * (t - s)) : ℕ) : ℝ) ≤
          (((p * s) / (α ^ 2 * (t - s)) : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_le_div_right (Nat.sub_le _ _)
      have h2 : (((p * s) / (α ^ 2 * (t - s)) : ℕ) : ℝ) ≤
          ((p * s : ℕ) : ℝ) / ((α ^ 2 * (t - s) : ℕ) : ℝ) := Nat.cast_div_le
      have h3 : ((p * s : ℕ) : ℝ) / ((α ^ 2 * (t - s) : ℕ) : ℝ) ≤ (α:ℝ)^2 := by
        rw [div_le_iff₀ hMposR]
        have hMeq : ((α ^ 2 * (t - s) : ℕ) : ℝ) = (α:ℝ)^2 * ((t - s : ℕ):ℝ) := by
          push_cast; ring
        rw [hMeq]
        calc ((p * s : ℕ) : ℝ) = (p:ℝ)*(s:ℝ) := by push_cast; ring
          _ ≤ ((t - s : ℕ):ℝ) * (α:ℝ)^4 := hps
          _ = (α:ℝ)^2 * ((α:ℝ)^2 * ((t - s : ℕ):ℝ)) := by ring
      linarith
    push_cast
    linarith
  -- bound on egM
  have hM : (egM p α : ℝ) ≤ Real.sqrt (p:ℝ) / (2 * (α:ℝ)) + 1 := by
    rw [egM]
    have hcast : ((Nat.sqrt p / (2 * α) : ℕ) : ℝ) ≤ Real.sqrt (p:ℝ) / (2 * (α:ℝ)) := by
      calc ((Nat.sqrt p / (2 * α) : ℕ) : ℝ)
          ≤ (Nat.sqrt p : ℝ) / ((2 * α : ℕ) : ℝ) := Nat.cast_div_le
        _ = (Nat.sqrt p : ℝ) / (2 * (α:ℝ)) := by push_cast; ring
        _ ≤ Real.sqrt (p:ℝ) / (2 * (α:ℝ)) := by
              apply div_le_div_of_nonneg_right _ (by linarith : (0:ℝ) ≤ 2 * (α:ℝ))
              have hsq : ((Nat.sqrt p : ℕ):ℝ) ^ 2 ≤ (p:ℝ) := by
                have := Nat.sqrt_le' p
                exact_mod_cast this
              exact (Real.le_sqrt (by positivity : (0:ℝ) ≤ (Nat.sqrt p : ℝ))
                (le_of_lt hxpos)).mpr hsq
    push_cast
    linarith
  have hstep1 : 18 * (egM p α : ℝ) + 24 ≤ 9 * Real.sqrt (p:ℝ) / 2 + 42 := by
    have hdiv : Real.sqrt (p:ℝ) / (2 * (α:ℝ)) ≤ Real.sqrt (p:ℝ) / 4 :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) (by linarith)
    linarith [hM, hdiv]
  have hαpR : (α:ℝ)^2 + 1 ≤ (p:ℝ) := by
    have : α ^ 2 + 1 ≤ p := by omega
    exact_mod_cast this
  have hsqrt : Real.sqrt (p:ℝ) ≤ (p:ℝ) / 10 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have hxy : 9 * Real.sqrt (p:ℝ) / 2 + 42 ≤ 9 * (p:ℝ) / 20 + 42 := by linarith [hsqrt]
  have hfinal : (p:ℝ) * (9 * Real.sqrt (p:ℝ) / 2 + 42) ≤ (p:ℝ) * (9 * (p:ℝ) / 20 + 42) :=
    mul_le_mul_of_nonneg_left hxy (le_of_lt hxpos)
  have hprod : (egN p α s t : ℝ) * (18 * (egM p α : ℝ) + 24) ≤
      (p:ℝ) * (9 * Real.sqrt (p:ℝ) / 2 + 42) := by
    have h2 : (0:ℝ) ≤ 18 * (egM p α : ℝ) + 24 := by positivity
    have h3 : (0:ℝ) ≤ (α:ℝ)^2 + 1 := by positivity
    calc (egN p α s t : ℝ) * (18 * (egM p α : ℝ) + 24)
        ≤ ((α:ℝ)^2 + 1) * (9 * Real.sqrt (p:ℝ) / 2 + 42) := mul_le_mul hN hstep1 h2 h3
      _ ≤ (p:ℝ) * (9 * Real.sqrt (p:ℝ) / 2 + 42) :=
            mul_le_mul_of_nonneg_right hαpR (by positivity)
  have hlast : 5 + (p:ℝ) * (9 * (p:ℝ) / 20 + 42) < (p:ℝ)^2 := by nlinarith
  linarith [hprod, hfinal, hlast]

end Work.Resample
