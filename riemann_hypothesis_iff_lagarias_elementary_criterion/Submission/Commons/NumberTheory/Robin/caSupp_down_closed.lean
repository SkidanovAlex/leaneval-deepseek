import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.Robin

/-- For reals `1 ≤ a ≤ b` and `0 < ε`, the map `t ↦ t ^ (1+ε) - t` is monotone:
`a^(1+ε) - a ≤ b^(1+ε) - b`.  Both factors of `t^(1+ε) - t = t·(t^ε - 1)` are
non-negative and non-decreasing on `[1,∞)`. -/
private lemma rpow_sub_self_mono {a b ε : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hε : 0 < ε) :
    a ^ (1 + ε) - a ≤ b ^ (1 + ε) - b := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have haε : 1 ≤ a ^ ε := Real.one_le_rpow ha (le_of_lt hε)
  have hbε : 1 ≤ b ^ ε := Real.one_le_rpow (le_trans ha hab) (le_of_lt hε)
  have hbpow : a ^ ε ≤ b ^ ε := Real.rpow_le_rpow (le_of_lt ha0) hab (le_of_lt hε)
  have h1 : a * (a ^ ε - 1) ≤ b * (a ^ ε - 1) :=
    mul_le_mul_of_nonneg_right hab (by linarith)
  have h2 : b * (a ^ ε - 1) ≤ b * (b ^ ε - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hb0)
  have hae : a ^ (1 + ε) = a * a ^ ε := by rw [Real.rpow_add ha0, Real.rpow_one]
  have hbe : b ^ (1 + ε) = b * b ^ ε := by rw [Real.rpow_add hb0, Real.rpow_one]
  calc
    a ^ (1 + ε) - a = a * (a ^ ε - 1) := by rw [hae]; ring
    _ ≤ b * (b ^ ε - 1) := le_trans h1 h2
    _ = b ^ (1 + ε) - b := by rw [hbe]; ring

/-- For real `x > 1` and `ε > 0`, with `μ(x,ε) = log((x^{1+ε}−1)/(x^{1+ε}−x))/log x`:

    `1 ≤ ⌊μ(x,ε)⌋₊ ⟺ x^{1+ε} ≤ x + 1`.

The floor condition is `μ ≥ 1`, i.e. `log((x^{1+ε}−1)/(x^{1+ε}−x)) ≥ log x`, i.e.
`(x^{1+ε}−1)/(x^{1+ε}−x) ≥ x`, which upon clearing the (positive) denominator is
`x^{1+ε}(x−1) ≤ (x−1)(x+1)`, i.e. `x^{1+ε} ≤ x+1` (since `x−1 > 0`). -/
private lemma one_le_floor_mu_iff {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) :
    1 ≤ ⌊Real.log ((x ^ (1 + ε) - 1) / (x ^ (1 + ε) - x)) / Real.log x⌋₊
      ↔ x ^ (1 + ε) ≤ x + 1 := by
  set y : ℝ := x ^ (1 + ε) with hy
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hxε : 1 < x ^ ε := Real.one_lt_rpow hx hε
  have hxy : x < y := by
    rw [hy, Real.rpow_add hx0, Real.rpow_one]
    exact lt_mul_of_one_lt_right hx0 hxε
  have hden : 0 < y - x := by linarith
  have hnum : 0 < y - 1 := by linarith
  have hApos : 0 < (y - 1) / (y - x) := div_pos hnum hden
  have hAgt1 : 1 < (y - 1) / (y - x) := by
    rw [one_lt_div hden]; linarith
  have hfl : 1 ≤ ⌊Real.log ((y - 1) / (y - x)) / Real.log x⌋₊ ↔
      (1 : ℝ) ≤ Real.log ((y - 1) / (y - x)) / Real.log x :=
    Nat.one_le_floor_iff _
  have hlog : (1 : ℝ) ≤ Real.log ((y - 1) / (y - x)) / Real.log x ↔
      x ≤ (y - 1) / (y - x) := by
    rw [le_div_iff₀ hlogx, one_mul]
    exact Real.log_le_log_iff hx0 hApos
  have hAx : x ≤ (y - 1) / (y - x) ↔ y ≤ x + 1 := by
    have hxm1 : 0 < x - 1 := by linarith
    have hmid : (x * (y - x) ≤ y - 1) ↔ y * (x - 1) ≤ (x - 1) * (x + 1) := by
      constructor <;> intro h <;> nlinarith [h]
    have hlast : (y * (x - 1) ≤ (x - 1) * (x + 1)) ↔ y ≤ x + 1 := by
      rw [← le_div_iff₀ hxm1, mul_div_cancel_left₀ (x + 1) (ne_of_gt hxm1)]
    exact (le_div_iff₀ hden).trans (hmid.trans hlast)
  exact hfl.trans (hlog.trans hAx)

theorem caSupp_down_closed {ε : ℝ} (hε : 0 < ε) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hlt : p < q) (hqin : q ∈ (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊))) : p ∈ (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) := by
  rw [Finset.mem_filter] at hqin
  obtain ⟨hqin', hqcond⟩ := hqin
  rw [Finset.mem_filter, Finset.mem_range] at hqin'
  obtain ⟨hqbound, hqprime⟩ := hqin'
  have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hqr : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hqcond' : (q : ℝ) ^ (1 + ε) ≤ (q : ℝ) + 1 :=
    (one_le_floor_mu_iff (x := (q : ℝ)) (ε := ε) hqr hε).mp hqcond
  have hpq : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast (le_of_lt hlt)
  have hmono : (p : ℝ) ^ (1 + ε) - (p : ℝ) ≤ (q : ℝ) ^ (1 + ε) - (q : ℝ) :=
    rpow_sub_self_mono (le_of_lt hpr) hpq hε
  have hpcond : (p : ℝ) ^ (1 + ε) ≤ (p : ℝ) + 1 := by linarith
  have hpfloor : 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ :=
    (one_le_floor_mu_iff (x := (p : ℝ)) (ε := ε) hpr hε).mpr hpcond
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_trans hlt hqbound), hp⟩, hpfloor⟩

end Commons.NumberTheory.Robin