import Mathlib

/-!
# The scalar estimate behind the smallness bound for `CH(P,Q)`

A self-contained proof of the one-variable estimate used in `CHp_le_of_unions`: for nonnegative
`c : Fin n → ℝ` whose entries are each at most their total, and any `i₀`,

`∑ i, φ(c i) ≤ φ(∑ i, c i) + 2 (∑ i, c i - c i₀) + 2√n √((∑ i, c i) (2 (∑ i, c i - c i₀)))`,

where `φ = Real.negMulLog`.  The proof normalises (`p i = c i / b`, `b = ∑ c`) and uses the two
elementary bounds `φ x ≤ 1 - x` and `φ x ≤ 2√x` on `[0,1]` together with Cauchy–Schwarz.
-/

open Finset

namespace Work.EKLComp

/-- `φ x ≤ 2√x` on `[0,1]`. -/
theorem negMulLog_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.negMulLog x ≤ 2 * Real.sqrt x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    simp
  · set t := Real.sqrt x with ht
    have ht0 : 0 < t := Real.sqrt_pos.mpr h
    have hx_eq : x = t ^ 2 := (Real.sq_sqrt hx).symm
    have hlogx : Real.log x = 2 * Real.log t := by
      rw [hx_eq, Real.log_pow]
      norm_num
    have hlogt : Real.log t = -Real.log (1 / t) := by
      rw [one_div, Real.log_inv, neg_neg]
    have hbound : Real.log (1 / t) ≤ 1 / t - 1 := Real.log_le_sub_one_of_pos (by positivity)
    simp only [Real.negMulLog_eq_neg]
    rw [hlogx, hx_eq, hlogt]
    have h2 : -(t ^ 2 * (2 * -Real.log (1 / t))) = 2 * t ^ 2 * Real.log (1 / t) := by ring
    rw [h2]
    have h3 : 2 * t ^ 2 * Real.log (1 / t) ≤ 2 * t ^ 2 * (1 / t - 1) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    have h4 : 2 * t ^ 2 * (1 / t - 1) = 2 * t - 2 * t ^ 2 := by
      field_simp <;> ring
    nlinarith [h3, h4, sq_nonneg t]

/-- **The scalar estimate.** -/
theorem negMulLog_sum_le_delta_le {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hcb : ∀ i, c i ≤ ∑ j, c j) (i₀ : Fin n) :
    ∑ i, Real.negMulLog (c i) ≤ Real.negMulLog (∑ i, c i)
      + 2 * (∑ i, c i - c i₀)
      + 2 * Real.sqrt n * Real.sqrt ((∑ i, c i) * (2 * (∑ i, c i - c i₀))) := by
  set b := ∑ i, c i with hb
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun i _ => hc i
  have hd0 : 0 ≤ b - c i₀ := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) c (Finset.mem_univ i₀)
    have hnn : 0 ≤ ∑ i ∈ (Finset.univ.erase i₀), c i := Finset.sum_nonneg fun i _ => hc i
    rw [hb]
    linarith
  rcases eq_or_lt_of_le hb0 with hb_eq | hb_pos
  · have hc0 : ∀ i, c i = 0 := fun i =>
      le_antisymm (by have := hcb i; rw [← hb_eq] at this; exact this) (hc i)
    have : b = 0 := hb_eq.symm
    simp [hc0, this]
  · set p : Fin n → ℝ := fun i => c i / b with hp
    have hp0 : ∀ i, 0 ≤ p i := fun i => div_nonneg (hc i) hb0
    have hp1 : ∀ i, p i ≤ 1 := fun i => by
      rw [hp]
      exact div_le_one_of_le₀ (hcb i) hb0
    have hsum_p : ∑ i, p i = 1 := by
      simp only [hp]
      rw [← Finset.sum_div, hb]
      exact div_self (by rw [← hb]; exact ne_of_gt hb_pos)
    have hcp : ∀ i, c i = b * p i := by
      intro i
      rw [hp]
      field_simp
    have hid : ∑ i, Real.negMulLog (c i)
        = Real.negMulLog b + b * ∑ i, Real.negMulLog (p i) := by
      calc ∑ i, Real.negMulLog (c i)
          = ∑ i, Real.negMulLog (b * p i) :=
              Finset.sum_congr rfl fun i _ => by rw [hcp i]
        _ = ∑ i, (p i * Real.negMulLog b + b * Real.negMulLog (p i)) :=
              Finset.sum_congr rfl fun i _ => Real.negMulLog_mul b (p i)
        _ = (∑ i, p i) * Real.negMulLog b + b * ∑ i, Real.negMulLog (p i) := by
              rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        _ = Real.negMulLog b + b * ∑ i, Real.negMulLog (p i) := by rw [hsum_p, one_mul]
    have hpbound : ∑ i, Real.negMulLog (p i)
        ≤ (1 - p i₀) + 2 * Real.sqrt ((n : ℝ) * (1 - p i₀)) := by
      have hi₀ : Real.negMulLog (p i₀) ≤ 1 - p i₀ := Real.negMulLog_le_one_sub_self (hp0 i₀)
      have hsplit : ∑ i, Real.negMulLog (p i)
          = Real.negMulLog (p i₀) + ∑ i ∈ (Finset.univ.erase i₀), Real.negMulLog (p i) := by
        have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
          (fun i => Real.negMulLog (p i)) (Finset.mem_univ i₀)
        linarith
      have hsum_erase : ∑ i ∈ (Finset.univ.erase i₀), p i = 1 - p i₀ := by
        have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) p (Finset.mem_univ i₀)
        rw [hsum_p] at h
        linarith
      have hcard : (((Finset.univ.erase i₀).card : ℕ) : ℝ) ≤ (n : ℝ) := by
        have h : (Finset.univ.erase i₀).card ≤ n := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
          omega
        exact_mod_cast h
      have hother : ∑ i ∈ (Finset.univ.erase i₀), Real.negMulLog (p i)
          ≤ ∑ i ∈ (Finset.univ.erase i₀), 2 * Real.sqrt (p i) :=
        Finset.sum_le_sum fun i _ => negMulLog_le_two_sqrt (hp0 i) (hp1 i)
      have hcs : ∑ i ∈ (Finset.univ.erase i₀), Real.sqrt (p i)
          ≤ Real.sqrt (((Finset.univ.erase i₀).card : ℕ) : ℝ)
            * Real.sqrt (∑ i ∈ (Finset.univ.erase i₀), p i) := by
        have h := Real.sum_sqrt_mul_sqrt_le (s := Finset.univ.erase i₀)
          (f := fun _ : Fin n => (1 : ℝ)) (g := p) (fun _ => zero_le_one) (fun i => hp0 i)
        simpa using h
      have hblock : ∑ i ∈ (Finset.univ.erase i₀), Real.negMulLog (p i)
          ≤ 2 * (Real.sqrt (((Finset.univ.erase i₀).card : ℕ) : ℝ) * Real.sqrt (1 - p i₀)) := by
        calc ∑ i ∈ (Finset.univ.erase i₀), Real.negMulLog (p i)
            ≤ ∑ i ∈ (Finset.univ.erase i₀), 2 * Real.sqrt (p i) := hother
          _ = 2 * ∑ i ∈ (Finset.univ.erase i₀), Real.sqrt (p i) := by rw [Finset.mul_sum]
          _ ≤ 2 * (Real.sqrt (((Finset.univ.erase i₀).card : ℕ) : ℝ)
                * Real.sqrt (∑ i ∈ (Finset.univ.erase i₀), p i)) := by linarith [hcs]
          _ = 2 * (Real.sqrt (((Finset.univ.erase i₀).card : ℕ) : ℝ)
                * Real.sqrt (1 - p i₀)) := by rw [hsum_erase]
      rw [hsplit]
      refine le_trans (add_le_add hi₀ hblock) ?_
      have h1 : 0 ≤ 1 - p i₀ := by linarith [hp1 i₀]
      have h2 : Real.sqrt ((((Finset.univ.erase i₀).card : ℕ) : ℝ)) ≤ Real.sqrt (n : ℝ) :=
        Real.sqrt_le_sqrt hcard
      have h3 : 0 ≤ Real.sqrt (1 - p i₀) := Real.sqrt_nonneg _
      have h4 : Real.sqrt ((((Finset.univ.erase i₀).card : ℕ) : ℝ)) * Real.sqrt (1 - p i₀)
          ≤ Real.sqrt (n : ℝ) * Real.sqrt (1 - p i₀) :=
        mul_le_mul_of_nonneg_right h2 h3
      calc (1 - p i₀) + 2 * (Real.sqrt (((Finset.univ.erase i₀).card : ℕ) : ℝ)
              * Real.sqrt (1 - p i₀))
          ≤ (1 - p i₀) + 2 * (Real.sqrt (n : ℝ) * Real.sqrt (1 - p i₀)) := by linarith [h4]
        _ = (1 - p i₀) + 2 * Real.sqrt ((n : ℝ) * (1 - p i₀)) := by
            rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
    have hb1p : b * (1 - p i₀) = b - c i₀ := by
      rw [hp]
      field_simp <;> ring
    have hfin : b * ((1 - p i₀) + 2 * Real.sqrt ((n : ℝ) * (1 - p i₀)))
        ≤ 2 * (b - c i₀) + 2 * Real.sqrt ((n : ℝ) * (b * (2 * (b - c i₀)))) := by
      have hsq : b * Real.sqrt ((n : ℝ) * (1 - p i₀))
          = Real.sqrt ((n : ℝ) * (b * (b - c i₀))) := by
        have hb_sq : b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb0).symm
        calc b * Real.sqrt ((n : ℝ) * (1 - p i₀))
            = Real.sqrt (b ^ 2) * Real.sqrt ((n : ℝ) * (1 - p i₀)) :=
              congrArg (fun z => z * Real.sqrt ((n : ℝ) * (1 - p i₀))) hb_sq
          _ = Real.sqrt (b ^ 2 * ((n : ℝ) * (1 - p i₀))) := by
              rw [← Real.sqrt_mul (sq_nonneg b)]
          _ = Real.sqrt ((n : ℝ) * (b * (b - c i₀))) := by
              congr 1
              rw [← hb1p]
              ring
      have h4 : Real.sqrt ((n : ℝ) * (b * (b - c i₀)))
          ≤ Real.sqrt ((n : ℝ) * (b * (2 * (b - c i₀)))) := by
        refine Real.sqrt_le_sqrt ?_
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by linarith [hd0]) hb0) (Nat.cast_nonneg n)
      have h5 : b * ((1 - p i₀) + 2 * Real.sqrt ((n : ℝ) * (1 - p i₀)))
          = (b - c i₀) + 2 * (b * Real.sqrt ((n : ℝ) * (1 - p i₀))) := by
        rw [mul_add, hb1p]
        ring
      rw [h5, hsq]
      linarith
    have hmain : ∑ i, Real.negMulLog (c i) - Real.negMulLog b
        ≤ b * ((1 - p i₀) + 2 * Real.sqrt ((n : ℝ) * (1 - p i₀))) := by
      rw [hid]
      have hb2 : b * ∑ i, Real.negMulLog (p i)
          ≤ b * ((1 - p i₀) + 2 * Real.sqrt ((n : ℝ) * (1 - p i₀))) :=
        mul_le_mul_of_nonneg_left hpbound hb0
      linarith
    have hbr : Real.sqrt (n : ℝ) * Real.sqrt (b * (2 * (b - c i₀)))
        = Real.sqrt ((n : ℝ) * (b * (2 * (b - c i₀)))) :=
      (Real.sqrt_mul (Nat.cast_nonneg n) (b * (2 * (b - c i₀)))).symm
    linarith [hmain, hfin, hbr]

end Work.EKLComp
