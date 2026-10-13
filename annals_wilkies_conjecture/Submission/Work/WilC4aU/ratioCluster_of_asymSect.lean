import Mathlib
import Submission.Work.WilC4aU.Defs

namespace Work.WilC4aU

/-! ## The numerical core

Given two fibre points `y` above `x` and `y'` above `2 x` whose ratios `y / x ^ q` and
`y' / (2 x) ^ q` are both `δ`-close to a nonzero `a`, with `δ` small enough, the ratio
`y' / y` is `ε`-close to `2 ^ q`.  Everything is stated division-free. -/
theorem clusterPair_bound {q : ℚ} {a ε δ x y y' : ℝ} (ha : a ≠ 0) (hε : 0 < ε) (hx : 0 < x)
    (hδ1 : δ ≤ |a|/2) (hδ2 : δ ≤ ε * |a| / (8 * (2:ℝ)^(q:ℝ)))
    (hy : |y / x^(q:ℝ) - a| < δ) (hy' : |y' / (2*x)^(q:ℝ) - a| < δ) :
    (y' - (2:ℝ)^(q:ℝ) * y)^2 < ε^2 * y^2 := by
  have haabs : 0 < |a| := abs_pos.mpr ha
  have hLpos : 0 < (2:ℝ)^(q:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hxq : 0 < x^(q:ℝ) := Real.rpow_pos_of_pos hx _
  have hyub : |y - a * x^(q:ℝ)| < δ * x^(q:ℝ) := by
    have heq : y - a * x^(q:ℝ) = x^(q:ℝ) * (y / x^(q:ℝ) - a) := by field_simp
    rw [heq, abs_mul, abs_of_pos hxq]
    simpa [mul_comm] using mul_lt_mul_of_pos_left hy hxq
  have hylo : |a|/2 * x^(q:ℝ) < |y| := by
    have htri : |a| - |y / x^(q:ℝ) - a| ≤ |y / x^(q:ℝ)| := by
      have h := abs_sub_abs_le_abs_sub a (a - y / x^(q:ℝ))
      rw [abs_sub_comm a (y / x^(q:ℝ)), sub_sub_cancel] at h
      exact h
    have h3 : |a|/2 < |y / x^(q:ℝ)| := by linarith
    rw [abs_div, abs_of_pos hxq] at h3
    rwa [lt_div_iff₀ hxq] at h3
  have h2xq : (2*x)^(q:ℝ) = (2:ℝ)^(q:ℝ) * x^(q:ℝ) := by
    rw [Real.mul_rpow (by norm_num) (le_of_lt hx)]
  have h2xqpos : 0 < (2*x)^(q:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hy'ub : |y' - a * (2*x)^(q:ℝ)| < δ * (2*x)^(q:ℝ) := by
    have heq : y' - a * (2*x)^(q:ℝ) = (2*x)^(q:ℝ) * (y' / (2*x)^(q:ℝ) - a) := by field_simp
    rw [heq, abs_mul, abs_of_pos h2xqpos]
    simpa [mul_comm] using mul_lt_mul_of_pos_left hy' h2xqpos
  have hcomb : |y' - (2:ℝ)^(q:ℝ) * y| < 2 * δ * (2:ℝ)^(q:ℝ) * x^(q:ℝ) := by
    have hsec : |a * (2*x)^(q:ℝ) - (2:ℝ)^(q:ℝ) * y| < (2:ℝ)^(q:ℝ) * (δ * x^(q:ℝ)) := by
      have heq : a * (2*x)^(q:ℝ) - (2:ℝ)^(q:ℝ) * y
          = -((2:ℝ)^(q:ℝ) * (y - a * x^(q:ℝ))) := by
        rw [h2xq]; ring
      rw [heq, abs_neg, abs_mul, abs_of_pos hLpos]
      exact mul_lt_mul_of_pos_left hyub hLpos
    calc |y' - (2:ℝ)^(q:ℝ) * y|
        = |(y' - a * (2*x)^(q:ℝ)) + (a * (2*x)^(q:ℝ) - (2:ℝ)^(q:ℝ) * y)| := by ring_nf
      _ ≤ |y' - a * (2*x)^(q:ℝ)| + |a * (2*x)^(q:ℝ) - (2:ℝ)^(q:ℝ) * y| := abs_add_le _ _
      _ < δ * (2*x)^(q:ℝ) + (2:ℝ)^(q:ℝ) * (δ * x^(q:ℝ)) := add_lt_add hy'ub hsec
      _ = 2 * δ * (2:ℝ)^(q:ℝ) * x^(q:ℝ) := by rw [h2xq]; ring
  have hstep : 2 * δ * (2:ℝ)^(q:ℝ) * x^(q:ℝ) ≤ ε * |a| * x^(q:ℝ) / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hδ2
      (show (0:ℝ) ≤ 2 * (2:ℝ)^(q:ℝ) * x^(q:ℝ) by positivity)
    have hrw : ε * |a| / (8 * (2:ℝ)^(q:ℝ)) * (2 * (2:ℝ)^(q:ℝ) * x^(q:ℝ))
        = ε * |a| * x^(q:ℝ) / 4 := by
      field_simp
      ring
    rw [hrw] at hmul
    nlinarith [hmul]
  have hDpos : 0 < ε * |a| * x^(q:ℝ) / 4 := by positivity
  have hA : (y' - (2:ℝ)^(q:ℝ) * y)^2 < (ε * |a| * x^(q:ℝ) / 4)^2 := by
    rw [sq_lt_sq]
    rw [abs_of_pos hDpos]
    linarith
  have hc2 : (|a|/2 * x^(q:ℝ))^2 < y^2 := by
    have h2 : 0 < |a|/2 * x^(q:ℝ) := mul_pos (div_pos haabs (by norm_num)) hxq
    have h1 : |(|a|/2 * x^(q:ℝ))| < |y| := by rw [abs_of_pos h2]; exact hylo
    exact (sq_lt_sq (a := |a|/2 * x^(q:ℝ)) (b := y)).mpr h1
  have hB : (ε * |a| * x^(q:ℝ) / 4)^2 < ε^2 * y^2 := by
    have hpos : 0 < (|a|/2 * x^(q:ℝ))^2 := by positivity
    calc (ε * |a| * x^(q:ℝ) / 4)^2
        = ε^2 * ((|a|/2 * x^(q:ℝ))^2 / 4) := by ring
      _ < ε^2 * ((|a|/2 * x^(q:ℝ))^2) := by
            apply mul_lt_mul_of_pos_left _ (by positivity : (0:ℝ) < ε^2)
            linarith
      _ < ε^2 * y^2 := mul_lt_mul_of_pos_left hc2 (by positivity : (0:ℝ) < ε^2)
  linarith

/-- **C4aU.Produce.**  A fibre whose section is asymptotic to `a * x ^ q` with `a ≠ 0` and whose
`x`-support contains a half line has `2 ^ q` as a cluster value of the ratio `f (2 x) / f x`.

This is the direction that lets the finite cluster set carry the exponents: it produces the pairs
`(x, 2 x)` (via `hsupp`) at which the asymptotic can be compared.

Proof plan (`Work.WilC4aU.AsymSect` is `a ≠ 0 ∧ ∀ ε > 0, ∃ R, ∀ x y, R ≤ x →
Fin.cons x (Fin.cons y c) ∈ Y → |y / x ^ (q : ℝ) - a| < ε`).
Given `ε > 0`, put `δ := min (|a| / 2) (ε * |a| / (8 * 2 ^ (q : ℝ)))`, which is positive because
`2 ^ (q : ℝ) > 0`; let `R` be the asymptotic threshold for error `δ` (applied twice: at `x` and at
`2 * x`), and let `b` be the half-line bound of `hsupp`.  Take the point `x := max R b` (so that
`x ≥ b`, `2 * x ≥ R` and `2 * x ≥ b`), let `y` be a fibre point above `x` and `y'` a fibre point
above `2 * x`.  From `|y / x ^ q - a| < δ` and `δ ≤ |a| / 2` we get
`|y - a * x ^ q| < δ * x ^ q` and `|y| ≥ (|a| / 2) * x ^ q > 0`, so `y ≠ 0`; likewise
`|y' - a * (2 * x) ^ q| < δ * (2 * x) ^ q` with `(2 * x) ^ q = 2 ^ q * x ^ q` (`Real.mul_rpow`,
`x > 0`).  Then `|y' - 2 ^ q * y| ≤ 2 * δ * 2 ^ q * x ^ q` and, since `δ ≤ ε * |a| / (8 * 2 ^ q)`,
`(y' - 2 ^ q * y) ^ 2 < ε ^ 2 * y ^ 2`, which is the last condition of `RatioCluster` (its
condition `1 ≤ ε * x` is met by taking `x ≥ 1 / ε` as well). -/
theorem ratioCluster_of_asymSect {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ}
    {q : ℚ} {a : ℝ} (h : Work.WilC4aU.AsymSect Y c q a)
    (hsupp : ∃ b : ℝ, ∀ x ≥ b, ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y) :
    Work.WilC4aU.RatioCluster Y c ((2 : ℝ) ^ (q : ℝ)) := by
  obtain ⟨ha, hasym⟩ := h
  obtain ⟨b, hb⟩ := hsupp
  intro ε hε
  have haabs : 0 < |a| := abs_pos.mpr ha
  have hLpos : 0 < (2:ℝ)^(q:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  set δ : ℝ := min (|a|/2) (ε * |a| / (8 * (2:ℝ)^(q:ℝ))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (div_pos haabs (by norm_num))
      (div_pos (mul_pos hε haabs) (by positivity))
  have hδ1 : δ ≤ |a|/2 := by rw [hδdef]; exact min_le_left _ _
  have hδ2 : δ ≤ ε * |a| / (8 * (2:ℝ)^(q:ℝ)) := by rw [hδdef]; exact min_le_right _ _
  obtain ⟨R, hR⟩ := hasym δ hδpos
  set X : ℝ := max (max R b) (max (1/ε) 1) with hXdef
  have hXR : R ≤ X := by
    rw [hXdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hXb : b ≤ X := by
    rw [hXdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hX1ε : 1/ε ≤ X := by
    rw [hXdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hX1 : 1 ≤ X := by
    rw [hXdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX1
  have hεX : 1 ≤ ε * X := by
    have h := hX1ε
    rw [div_le_iff₀ hε] at h
    linarith
  have h2XR : R ≤ 2*X := by linarith
  have h2Xb : b ≤ 2*X := by linarith
  obtain ⟨y, hy⟩ := hb X hXb
  obtain ⟨y', hy'⟩ := hb (2*X) h2Xb
  have hyδ : |y / X^(q:ℝ) - a| < δ := hR X y hXR hy
  have hy'δ : |y' / (2*X)^(q:ℝ) - a| < δ := hR (2*X) y' h2XR hy'
  have hbound := clusterPair_bound ha hε hXpos hδ1 hδ2 hyδ hy'δ
  have hne : y ≠ 0 := by
    intro h0
    rw [h0] at hbound
    simp only [mul_zero, sub_zero, pow_two, mul_zero] at hbound
    nlinarith [sq_nonneg y']
  exact ⟨X, y, y', hεX, hy, hne, hy', hbound⟩

end Work.WilC4aU
