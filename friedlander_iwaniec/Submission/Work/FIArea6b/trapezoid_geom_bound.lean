import Mathlib
import Submission.Work.FIArea6b.aux_lem_P
import Submission.Work.FIArea6b.aux_lem_Q
import Submission.Work.FIArea6b.aux_sq_diff_le_ball

/-!
# The trapezoid geometry bound of Friedlander--Iwaniec (Area 6b)
-/

namespace Work.FIArea6b

private lemma abs_sub_le_abs_add (A B : ℝ) : |A - B| ≤ |A| + |B| := by
  calc |A - B| = |A + (-B)| := by ring_nf
    _ ≤ |A| + |-B| := abs_add_le A (-B)
    _ = |A| + |B| := by rw [abs_neg]

private theorem key_arith (p q d K w R : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (hpq : p^2 + q^2 = 1)
    (hR : 0 ≤ R) (hw : 0 ≤ w) (hd : 0 ≤ d) (hK : 0 ≤ K) (hKd : K^2 + d^2 = (2*R)^2) :
    d + (min K ((w - p*d)/q) + min K ((w + p*d)/q)) / 2 ≤ 2*R + w := by
  have hxy : (w - p*d)/q ≤ (w + p*d)/q := by
    have h2 : 0 ≤ 2*p*d/q := div_nonneg (by nlinarith [mul_nonneg hp hd]) (le_of_lt hq)
    have h3 : (w + p*d)/q - (w - p*d)/q = 2*p*d/q := by field_simp; ring
    linarith
  by_cases hA : K ≤ (w - p*d)/q
  · have hAy : K ≤ (w + p*d)/q := le_trans hA hxy
    rw [min_eq_left hA, min_eq_left hAy]
    have hw' : p*d + q*K ≤ w := by
      have h1 : K * q ≤ w - p*d := (le_div_iff₀ hq).mp hA
      linarith
    have hP := aux_lem_P p q d K R hp (le_of_lt hq) hpq hR hK hKd hd
    linarith
  · have hx_lt : (w - p*d)/q < K := lt_of_not_ge hA
    have hxK : w - p*d < K*q := (div_lt_iff₀ hq).mp hx_lt
    by_cases hB : K ≤ (w + p*d)/q
    · rw [min_eq_right (le_of_lt hx_lt), min_eq_left hB]
      have hwge : q*K - p*d ≤ w := by
        have h1 : K*q ≤ w + p*d := (le_div_iff₀ hq).mp hB
        linarith
      have hQ := aux_lem_Q p q d K R hp hq hpq hR hK hKd hd
      by_cases hq2 : (1:ℝ)/2 ≤ q
      · have hident : d + ((w - p*d)/q + K)/2 - w
            = ((1+p-p/q)*d + (1-q)*K) + (w - (q*K - p*d))*(1/(2*q) - 1) := by
          field_simp; ring
        have hcoef : 1/(2*q) - 1 ≤ 0 := by
          have h : 1/(2*q) ≤ 1 := by
            rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*q)]; linarith
          linarith
        have hmono : (w - (q*K - p*d))*(1/(2*q) - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) hcoef
        linarith
      · have hq2' : q < 1/2 := not_le.mp hq2
        have hcoef : 0 ≤ 1/(2*q) - 1 := by
          have h : 1 ≤ 1/(2*q) := by
            rw [le_div_iff₀ (by linarith : (0:ℝ) < 2*q)]; linarith
          linarith
        have hident2 : d + ((w - p*d)/q + K)/2 - w
            = ((1-p)*d + (1-q)*K) + (w - (p*d + q*K))*(1/(2*q) - 1) := by
          field_simp; ring
        have hmono : (w - (p*d + q*K))*(1/(2*q) - 1) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hcoef
        have hP := aux_lem_P p q d K R hp (le_of_lt hq) hpq hR hK hKd hd
        linarith
    · have hB' : (w + p*d)/q < K := not_le.mp hB
      have hyK : w + p*d < K*q := (div_lt_iff₀ hq).mp hB'
      rw [min_eq_right (le_of_lt hx_lt), min_eq_right (le_of_lt hB')]
      have hsum : ((w - p*d)/q + (w + p*d)/q)/2 = w/q := by field_simp; ring
      rw [hsum]
      have hQ := aux_lem_Q p q d K R hp hq hpq hR hK hKd hd
      have hq1 : q ≤ 1 := by nlinarith [hpq, sq_nonneg p, hq]
      have hcoef : 0 ≤ 1/q - 1 := by
        have h : 1 ≤ 1/q := by rw [le_div_iff₀ hq]; linarith
        linarith
      have hident3 : d + w/q - w
            = ((1+p-p/q)*d + (1-q)*K) + (w - (q*K - p*d))*(1/q - 1) := by
        field_simp; ring
      have hmono : (w - (q*K - p*d))*(1/q - 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hcoef
      linarith

private theorem key_raw (p q d X Y w R : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p^2 + q^2 = 1)
    (hR : 0 ≤ R) (hw : 0 ≤ w) (hd : 0 ≤ d)
    (hX : d^2 + X^2 ≤ (2*R)^2) (hY : d^2 + Y^2 ≤ (2*R)^2)
    (hXs : p*d + q*X ≤ w) (hYs : -(p*d) + q*Y ≤ w) :
    d + (X+Y)/2 ≤ 2*R + w := by
  set K : ℝ := Real.sqrt ((2*R)^2 - d^2) with hKdef
  have hKnon : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K^2 = (2*R)^2 - d^2 := by
    rw [hKdef]; exact Real.sq_sqrt (by nlinarith [sq_nonneg X, hX])
  have hXK : X ≤ K := le_of_sq_le_sq (by rw [hKsq]; linarith [hX]) hKnon
  have hYK : Y ≤ K := le_of_sq_le_sq (by rw [hKsq]; linarith [hY]) hKnon
  rcases eq_or_lt_of_le hq with hq0 | hqpos
  · have hp1 : p = 1 := by nlinarith [hpq, hq0, hp, sq_nonneg (p-1), sq_nonneg (p+1)]
    have hdw : d ≤ w := by nlinarith [hXs, hp1, hq0]
    have hK2R : K ≤ 2*R := le_of_sq_le_sq (by rw [hKsq]; nlinarith [sq_nonneg d]) (by linarith)
    linarith
  · have hXx : X ≤ (w - p*d)/q := by rw [le_div_iff₀ hqpos]; linarith
    have hYy : Y ≤ (w + p*d)/q := by rw [le_div_iff₀ hqpos]; linarith
    have hKd : K^2 + d^2 = (2*R)^2 := by linarith [hKsq]
    have hka := key_arith p q d K w R hp hqpos hpq hR hw hd hKnon hKd
    have hm1 : (X+Y)/2 ≤ (min K ((w-p*d)/q) + min K ((w+p*d)/q))/2 := by
      have a1 := le_min hXK hXx
      have a2 := le_min hYK hYy
      linarith
    linarith

theorem trapezoid_geom_bound (R w : ℝ) (hR : 0 ≤ R) (hw : 0 ≤ w) (n : ℝ × ℝ) (k : ℝ)
    (a b la lb ua ub : ℝ) (c : ℝ × ℝ)
    (hab : a ≤ b) (h1 : la ≤ ua) (h2 : lb ≤ ub) (hn : n.1 ^ 2 + n.2 ^ 2 = 1)
    (hball : ∀ p : ℝ × ℝ, (p = (a, la) ∨ p = (b, lb) ∨ p = (b, ub) ∨ p = (a, ua)) →
      (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 ≤ R ^ 2)
    (hstrip : ∀ p : ℝ × ℝ, (p = (a, la) ∨ p = (b, lb) ∨ p = (b, ub) ∨ p = (a, ua)) →
      |n.1 * p.1 + n.2 * p.2 - k| ≤ w / 2) :
    (ua - la) / 2 + (ub - lb) / 2 + (b - a) ≤ 2 * R + w := by
  have hAc : (a - c.1)^2 + (la - c.2)^2 ≤ R^2 := hball (a,la) (Or.inl rfl)
  have hBc : (b - c.1)^2 + (lb - c.2)^2 ≤ R^2 := hball (b,lb) (Or.inr (Or.inl rfl))
  have hCc : (b - c.1)^2 + (ub - c.2)^2 ≤ R^2 := hball (b,ub) (Or.inr (Or.inr (Or.inl rfl)))
  have hDc : (a - c.1)^2 + (ua - c.2)^2 ≤ R^2 := hball (a,ua) (Or.inr (Or.inr (Or.inr rfl)))
  have hCA : (b-a)^2 + (ub-la)^2 ≤ (2*R)^2 := by
    have := aux_sq_diff_le_ball (b - c.1) (a - c.1) (ub - c.2) (la - c.2) R hR hCc hAc
    nlinarith [this]
  have hDB : (b-a)^2 + (ua-lb)^2 ≤ (2*R)^2 := by
    have := aux_sq_diff_le_ball (a - c.1) (b - c.1) (ua - c.2) (lb - c.2) R hR hDc hBc
    nlinarith [this]
  have hd : 0 ≤ b - a := by linarith
  have hsA : |n.1 * a + n.2 * la - k| ≤ w/2 := hstrip (a,la) (Or.inl rfl)
  have hsB : |n.1 * b + n.2 * lb - k| ≤ w/2 := hstrip (b,lb) (Or.inr (Or.inl rfl))
  have hsC : |n.1 * b + n.2 * ub - k| ≤ w/2 := hstrip (b,ub) (Or.inr (Or.inr (Or.inl rfl)))
  have hsD : |n.1 * a + n.2 * ua - k| ≤ w/2 := hstrip (a,ua) (Or.inr (Or.inr (Or.inr rfl)))
  have hwA : |n.1 * (b-a) + n.2 * (ub-la)| ≤ w := by
    have hle := abs_sub_le_abs_add (n.1*b + n.2*ub - k) (n.1*a + n.2*la - k)
    have hid : (n.1*b + n.2*ub - k) - (n.1*a + n.2*la - k) = n.1*(b-a) + n.2*(ub-la) := by ring
    rw [hid] at hle; linarith
  have hwB : |-(n.1 * (b-a)) + n.2 * (ua-lb)| ≤ w := by
    have hle := abs_sub_le_abs_add (n.1*a + n.2*ua - k) (n.1*b + n.2*lb - k)
    have hid : (n.1*a + n.2*ua - k) - (n.1*b + n.2*lb - k) = -(n.1*(b-a)) + n.2*(ua-lb) := by ring
    rw [hid] at hle; linarith
  suffices main_for : ∀ (n' : ℝ × ℝ) (k' : ℝ), n'.1^2 + n'.2^2 = 1 →
      (∀ p : ℝ × ℝ, (p = (a, la) ∨ p = (b, lb) ∨ p = (b, ub) ∨ p = (a, ua)) →
        |n'.1 * p.1 + n'.2 * p.2 - k'| ≤ w / 2) → 0 ≤ n'.2 →
      (ua - la) / 2 + (ub - lb) / 2 + (b - a) ≤ 2 * R + w by
    by_cases hβ : 0 ≤ n.2
    · exact main_for n k hn hstrip hβ
    · have hβ' : n.2 < 0 := not_le.mp hβ
      have hn' : (-n).1^2 + (-n).2^2 = 1 := by
        rw [Prod.fst_neg, Prod.snd_neg, neg_sq, neg_sq]; exact hn
      have hs' : ∀ p : ℝ × ℝ,
          (p = (a, la) ∨ p = (b, lb) ∨ p = (b, ub) ∨ p = (a, ua)) →
          |(-n).1 * p.1 + (-n).2 * p.2 - (-k)| ≤ w / 2 := by
        intro p hp
        have hh := hstrip p hp
        have heq : (-n).1 * p.1 + (-n).2 * p.2 - (-k) = -(n.1 * p.1 + n.2 * p.2 - k) := by
          rw [Prod.fst_neg, Prod.snd_neg]; ring
        rw [heq, abs_neg]; exact hh
      have hbm : 0 ≤ (-n).2 := by rw [Prod.snd_neg]; linarith
      exact main_for (-n) (-k) hn' hs' hbm
  intro n' k' hn' hs hβ2
  have hsA' : |n'.1 * a + n'.2 * la - k'| ≤ w/2 := hs (a,la) (Or.inl rfl)
  have hsB' : |n'.1 * b + n'.2 * lb - k'| ≤ w/2 := hs (b,lb) (Or.inr (Or.inl rfl))
  have hsC' : |n'.1 * b + n'.2 * ub - k'| ≤ w/2 := hs (b,ub) (Or.inr (Or.inr (Or.inl rfl)))
  have hsD' : |n'.1 * a + n'.2 * ua - k'| ≤ w/2 := hs (a,ua) (Or.inr (Or.inr (Or.inr rfl)))
  have hwA' : |n'.1 * (b-a) + n'.2 * (ub-la)| ≤ w := by
    have hle := abs_sub_le_abs_add (n'.1*b + n'.2*ub - k') (n'.1*a + n'.2*la - k')
    have hid : (n'.1*b + n'.2*ub - k') - (n'.1*a + n'.2*la - k') = n'.1*(b-a) + n'.2*(ub-la) := by ring
    rw [hid] at hle; linarith
  have hwB' : |-(n'.1 * (b-a)) + n'.2 * (ua-lb)| ≤ w := by
    have hle := abs_sub_le_abs_add (n'.1*a + n'.2*ua - k') (n'.1*b + n'.2*lb - k')
    have hid : (n'.1*a + n'.2*ua - k') - (n'.1*b + n'.2*lb - k') = -(n'.1*(b-a)) + n'.2*(ua-lb) := by ring
    rw [hid] at hle; linarith
  by_cases ha0 : 0 ≤ n'.1
  · have hk := key_raw n'.1 n'.2 (b-a) (ub-la) (ua-lb) w R ha0 hβ2 hn' hR hw hd hCA hDB
      (by have h := (abs_le.mp hwA').2; linarith)
      (by have h := (abs_le.mp hwB').2; linarith)
    linarith
  · have hp' : 0 ≤ -n'.1 := by linarith
    have hpq' : (-n'.1)^2 + n'.2^2 = 1 := by rw [neg_sq]; exact hn'
    have hk := key_raw (-n'.1) n'.2 (b-a) (ua-lb) (ub-la) w R hp' hβ2 hpq' hR hw hd hDB hCA
      (by have h := (abs_le.mp hwB').2
          have h2 : (-n'.1)*(b-a) + n'.2*(ua-lb) = -(n'.1*(b-a)) + n'.2*(ua-lb) := by ring
          rw [h2]; exact h)
      (by have h := (abs_le.mp hwA').2
          have h2 : -((-n'.1)*(b-a)) + n'.2*(ub-la) = n'.1*(b-a) + n'.2*(ub-la) := by ring
          rw [h2]; exact h)
    linarith

end Work.FIArea6b
