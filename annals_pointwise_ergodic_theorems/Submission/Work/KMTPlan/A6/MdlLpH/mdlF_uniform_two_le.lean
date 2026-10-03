import Mathlib
import Submission.Work.KMTPlan.A6.mdlF_two_le

namespace Work.KMTPlan.A6.MdlLpH

open MeasureTheory
open scoped ENNReal BigOperators

/-- `⌈x⌉² ≤ 4x²` for `x ≥ 1`. -/
private lemma ceil_sq_le_four_mul (x : ℝ) (hx : 1 ≤ x) :
    ((Nat.ceil x : ℕ) : ℝ) ^ 2 ≤ 4 * x ^ 2 := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have h := Nat.ceil_lt_add_one hx0
  have hQx : ((Nat.ceil x : ℕ) : ℝ) ≤ 2 * x := by linarith
  have hstep : ((Nat.ceil x : ℕ) : ℝ) ^ 2 ≤ (2 * x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hQx 2
  calc ((Nat.ceil x : ℕ) : ℝ) ^ 2 ≤ (2 * x) ^ 2 := hstep
    _ = 4 * x ^ 2 := by ring

/-- `(2^{a})^2 = 2^{2a}` for real exponents. -/
private lemma rpow_sq (a : ℝ) :
    ((2 : ℝ) ^ a) ^ 2 = (2 : ℝ) ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- The scale count `uScale ρ A = ⌊2^{2ρA}⌋` is at least `1` for `ρ ≥ 0`. -/
private lemma one_le_uScale_real (ρ : ℝ) (hρ : 0 ≤ ρ) (A : ℕ) :
    (1 : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ A : ℝ) := by
  have hfl : ((Work.KMTAreas.A7.uScale ρ A : ℕ) : ℝ)
      = ((⌊(2 : ℝ) ^ (2 * ρ * (A : ℝ))⌋₊ : ℕ) : ℝ) := by
    simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat,
      Nat.cast_one, one_mul]
  rw [hfl]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (A : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have h2 : 1 ≤ ⌊(2 : ℝ) ^ (2 * ρ * (A : ℝ))⌋₊ := Nat.le_floor (n := 1) (by exact_mod_cast h1)
  exact_mod_cast h2

/-- The scale count `uScale ρ A = ⌊2^{2ρA}⌋` is at least `2^{2ρA} - 1`. -/
private lemma uScale_ge_rpow_sub_one (ρ : ℝ) (A : ℕ) :
    (2 : ℝ) ^ (2 * ρ * (A : ℝ)) - 1 ≤ (Work.KMTAreas.A7.uScale ρ A : ℝ) := by
  have hfl : ((Work.KMTAreas.A7.uScale ρ A : ℕ) : ℝ)
      = ((⌊(2 : ℝ) ^ (2 * ρ * (A : ℝ))⌋₊ : ℕ) : ℝ) := by
    simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat,
      Nat.cast_one, one_mul]
  rw [hfl]
  have := Nat.lt_floor_add_one ((2 : ℝ) ^ (2 * ρ * (A : ℝ)))
  linarith

/-- `2^{-uScale ρ A} ≤ 2^{-(2^{ρA})²/2}`: the exponential gain `2^{-u}` beats any
polynomial-in-`2^{ρA}` quantity with room to spare once squared. -/
private lemma rpow_neg_uScale_le (ρ : ℝ) (hρ : 0 < ρ) (A : ℕ) :
    (2 : ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ A : ℕ) : ℤ))
      ≤ (2 : ℝ) ^ (-(((2 : ℝ) ^ (ρ * (A : ℝ))) * ((2 : ℝ) ^ (ρ * (A : ℝ))) / 2)) := by
  set t : ℝ := (2 : ℝ) ^ (ρ * (A : ℝ)) with ht
  set Y : ℝ := (2 : ℝ) ^ (2 * ρ * (A : ℝ)) with hY
  have hYt : Y = t * t := by
    rw [hY, ht, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hu : Y - 1 ≤ (Work.KMTAreas.A7.uScale ρ A : ℝ) := by
    rw [hY]
    exact uScale_ge_rpow_sub_one ρ A
  have hu1 : (1 : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ A : ℝ) := one_le_uScale_real ρ hρ.le A
  have hz : (2 : ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ A : ℕ) : ℤ))
      = (2 : ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ A : ℕ) : ℝ)) := by
    rw [← Real.rpow_intCast (2 : ℝ) (-(((Work.KMTAreas.A7.uScale ρ A : ℕ) : ℤ)))]
    simp only [Int.cast_neg, Int.cast_natCast]
  rw [hz]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  rcases le_or_gt Y 2 with h2 | h2
  · linarith
  · have : Y / 2 ≤ Y - 1 := by linarith
    linarith

/-- **The uniform `ℓ²` bound for the model input `mdlF`.**  The pointwise constant
`2 (1 + 2 · 2^{-u} Q²)` of `mdlF_two_le` is bounded uniformly in the two scales: with
`u = uScale ρ A = ⌊2^{2ρA}⌋` and any denominator bound `Q` growing like
`2^{C₁ 2^{ρA}}` (which `iwP_element_le` supplies), the product `2^{-u} Q²` is bounded by
`8 · 2^{2C₁²}` — the exponential gain `2^{-2^{2ρA}}` beats `2^{2C₁ 2^{ρA}}` by completing
the square: `2 C₁ 2^{ρA} - 2^{2ρA}/2 ≤ 2 C₁²`. -/
theorem mdlF_uniform_two_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l A : ℕ), l ≤ A → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ A) l f) 2
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.Analysis.IonescuWainger.iwP_element_le hρ
  refine ⟨2 * (1 + 8 * (2 : ℝ) ^ (2 * C₁ * C₁)), by positivity, ?_⟩
  intro l A hl f
  -- the uniform denominator bound at the largest scale
  set Q : ℕ := Nat.ceil ((2 : ℝ) ^ (C₁ * (2 : ℝ) ^ (ρ * (A : ℝ)))) with hQ
  have hQA : ∀ l' : ℕ, l' ≤ A → ∀ q ∈ Work.Analysis.IonescuWainger.iwP ρ l', q ≤ Q := by
    intro l' hl' q hq
    have h1 := hC₁ l' q hq
    have hmono : (2 : ℝ) ^ (ρ * (l' : ℝ)) ≤ (2 : ℝ) ^ (ρ * (A : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hc : (l' : ℝ) ≤ (A : ℝ) := by exact_mod_cast hl'
      nlinarith [hρ]
    have hmono2 : (2 : ℝ) ^ (C₁ * (2 : ℝ) ^ (ρ * (l' : ℝ)))
        ≤ (2 : ℝ) ^ (C₁ * (2 : ℝ) ^ (ρ * (A : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      exact mul_le_mul_of_nonneg_left hmono hC₁pos.le
    have h2 : (q : ℝ) ≤ ((Q : ℕ) : ℝ) := by
      rw [hQ]
      exact le_trans (le_trans h1 hmono2) (Nat.le_ceil _)
    exact_mod_cast h2
  have hm := Work.KMTPlan.A6.mdlF_two_le ρ (Work.KMTAreas.A7.uScale ρ A) l Q (hQA l hl)
    (hQA (l - 1) (le_trans (Nat.sub_le l 1) hl)) f
  refine le_trans hm ?_
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  -- the arithmetic: `2 · 2^{-u} · Q² ≤ 8 · 2^{2C₁²}`
  have hkey : 2 * (2 : ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ A : ℕ) : ℤ)) * ((Q : ℕ) : ℝ) ^ 2
      ≤ 8 * (2 : ℝ) ^ (2 * C₁ * C₁) := by
    set t : ℝ := (2 : ℝ) ^ (ρ * (A : ℝ)) with ht
    have ht1 : 1 ≤ t :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hQ2 : ((Q : ℕ) : ℝ) ^ 2 ≤ 4 * (2 : ℝ) ^ (2 * C₁ * t) := by
      have hx : 1 ≤ (2 : ℝ) ^ (C₁ * t) :=
        Real.one_le_rpow (by norm_num) (mul_nonneg hC₁pos.le (le_trans zero_le_one ht1))
      rw [hQ]
      calc ((Nat.ceil ((2 : ℝ) ^ (C₁ * t)) : ℕ) : ℝ) ^ 2
          ≤ 4 * ((2 : ℝ) ^ (C₁ * t)) ^ 2 := ceil_sq_le_four_mul _ hx
        _ = 4 * (2 : ℝ) ^ (2 * C₁ * t) := by
            rw [rpow_sq, show (2 : ℝ) * (C₁ * t) = 2 * C₁ * t by ring]
    have hp : (2 : ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ A : ℕ) : ℤ))
        ≤ (2 : ℝ) ^ (-(t * t / 2)) := by
      rw [ht]
      exact rpow_neg_uScale_le ρ hρ A
    have hpow : (2 : ℝ) ^ (-(t * t / 2)) * (2 : ℝ) ^ (2 * C₁ * t)
        = (2 : ℝ) ^ (2 * C₁ * t - t * t / 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hexp : 2 * C₁ * t - t * t / 2 ≤ 2 * C₁ * C₁ := by
      nlinarith [sq_nonneg (t - 2 * C₁)]
    calc 2 * (2 : ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ A : ℕ) : ℤ)) * ((Q : ℕ) : ℝ) ^ 2
        ≤ 2 * (2 : ℝ) ^ (-(t * t / 2)) * (4 * (2 : ℝ) ^ (2 * C₁ * t)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hQ2 (by positivity) ?_
          positivity
      _ = 8 * ((2 : ℝ) ^ (-(t * t / 2)) * (2 : ℝ) ^ (2 * C₁ * t)) := by ring
      _ = 8 * (2 : ℝ) ^ (2 * C₁ * t - t * t / 2) := by rw [hpow]
      _ ≤ 8 * (2 : ℝ) ^ (2 * C₁ * C₁) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  linarith

end Work.KMTPlan.A6.MdlLpH
