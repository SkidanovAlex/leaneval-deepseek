import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.theta_range_fast
import Submission.Work.TMC16Core.Main.theta_refold
import Submission.Work.TMC16Core.Main.theta_residue_bound

namespace Work.TMC16Core.Assembly.Aux2

/-! ## Arithmetic core for the doubled index range

`theta_range_fast` re-folds the index range `|k| ≤ 4 (q(n+1))^{8/9} + 8 q n + 4` around the
near-period `q n`; `theta_range_fast2` does the same with the range *doubled*,
`|k| ≤ 8 (q(n+1))^{8/9} + 8 q n + 4`, keeping the same output constant `2/(q n)²`.  The only
new input is the shift-cost estimate

`((8 b^{8/9} + 8a + 4)/a + 1/2) Δ ≤ 2/a²`   whenever  `1 ≤ a`, `(8a)^9 ≤ b`, `Δ < 1/b`,

proved below.  It splits into the `b^{8/9}` contribution, which uses `b^{1/9} ≥ 8a`, and the
elementary contribution, which uses `b ≥ 2^27 a^9`. -/

/-- `b^{8/9} ≤ b/(8a)` as soon as `(8a)^9 ≤ b` and `a ≥ 1`: indeed `b^{1/9} ≥ 8a`. -/
lemma rpow_eight_ninths_le_div {a b : ℝ} (ha : 1 ≤ a) (hb : (8 * a) ^ 9 ≤ b) :
    Real.rpow b (8 / 9) ≤ b / (8 * a) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have h8a : 0 < 8 * a := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  -- `b^{1/9} ≥ 8a`
  have h2 : ((8 * a) ^ 9) ^ ((1 : ℝ) / 9) = 8 * a := by
    have hcast : ((8 * a) ^ 9 : ℝ) = (8 * a) ^ (9 : ℝ) :=
      (Real.rpow_natCast (8 * a) 9).symm
    rw [hcast, ← Real.rpow_mul (le_of_lt h8a) (9 : ℝ) ((1 : ℝ) / 9),
      show (9 : ℝ) * (1 / 9) = 1 by norm_num, Real.rpow_one]
  have hs : 8 * a ≤ b ^ ((1 : ℝ) / 9) := by
    have h1 : ((8 * a) ^ 9) ^ ((1 : ℝ) / 9) ≤ b ^ ((1 : ℝ) / 9) :=
      Real.rpow_le_rpow (by positivity) hb (by norm_num)
    linarith [h1, h2]
  -- `b^{8/9} = b / b^{1/9}`
  have ht : b ^ ((8 : ℝ) / 9) = b / b ^ ((1 : ℝ) / 9) := by
    have hh := Real.rpow_add hb0 (1 : ℝ) (-(1 / 9))
    rw [show (1 : ℝ) + -(1 / 9) = (8 : ℝ) / 9 by norm_num] at hh
    rw [Real.rpow_one, Real.rpow_neg (le_of_lt hb0), div_eq_mul_inv] at hh
    exact hh
  have hgoal : b ^ ((8 : ℝ) / 9) ≤ b / (8 * a) := by
    rw [ht]
    exact div_le_div_of_nonneg_left (le_of_lt hb0) h8a hs
  exact hgoal

/-- **Shift cost for the doubled range.**  If `a ≥ 1`, `(8a)^9 ≤ b`, `0 ≤ Δ < 1/b`, then
`((8 b^{8/9} + 8a + 4)/a + 1/2) Δ ≤ 2/a²`. -/
lemma fast_shift_arith2 {a b Δ : ℝ} (ha : 1 ≤ a) (hΔ0 : 0 ≤ Δ)
    (hb : (8 * a) ^ 9 ≤ b) (hΔb : Δ < 1 / b) :
    ((8 * Real.rpow b (8 / 9) + 8 * a + 4) / a + 1 / 2) * Δ ≤ 2 / a ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have ha2pos : (0 : ℝ) < a ^ 2 := by positivity
  have ht := rpow_eight_ninths_le_div ha hb
  -- (A) the `b^{8/9}` contribution: `8 a b^{8/9} Δ ≤ 1`
  have hkey : 8 * a * Real.rpow b (8 / 9) * Δ ≤ 1 := by
    have h8a : 0 < 8 * a := by linarith
    have h1 : 8 * a * Real.rpow b (8 / 9) ≤ b := by
      have h := mul_le_mul_of_nonneg_left ht (le_of_lt h8a)
      have h2 : 8 * a * (b / (8 * a)) = b := by
        rw [mul_div_assoc', mul_div_cancel_left₀ b (ne_of_gt h8a)]
      linarith [h, h2]
    calc 8 * a * Real.rpow b (8 / 9) * Δ ≤ b * Δ := mul_le_mul_of_nonneg_right h1 hΔ0
      _ ≤ b * (1 / b) := le_of_lt (mul_lt_mul_of_pos_left hΔb hb0)
      _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hb0)]
  -- (B) the elementary contribution
  have hb9 : 134217728 * a ^ 9 ≤ b := by
    have h := hb
    rw [mul_pow] at h
    norm_num at h
    linarith
  have ha2le : a ^ 2 ≤ a ^ 9 := pow_le_pow_right₀ ha (by norm_num)
  have hale : a ≤ a ^ 9 := by
    calc a = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ 9 := pow_le_pow_right₀ ha (by norm_num)
  have hcomb : 8 * a ^ 2 + 4 * a + a ^ 2 / 2 ≤ b := by
    have h9nn : (0 : ℝ) ≤ a ^ 9 := pow_nonneg (le_of_lt ha0) 9
    nlinarith [ha2le, hale, hb9, h9nn]
  have hrest : (8 * a ^ 2 + 4 * a + a ^ 2 / 2) * Δ ≤ 1 := by
    have hcoef : 0 ≤ 8 * a ^ 2 + 4 * a + a ^ 2 / 2 := by positivity
    have h1 : (8 * a ^ 2 + 4 * a + a ^ 2 / 2) * Δ
        ≤ (8 * a ^ 2 + 4 * a + a ^ 2 / 2) * (1 / b) :=
      mul_le_mul_of_nonneg_left (le_of_lt hΔb) hcoef
    have h2 : (8 * a ^ 2 + 4 * a + a ^ 2 / 2) * (1 / b) ≤ 1 := by
      rw [mul_one_div, div_le_one hb0]
      exact hcomb
    linarith [h1, h2]
  -- combine
  rw [le_div_iff₀ ha2pos]
  have hsplit : ((8 * Real.rpow b (8 / 9) + 8 * a + 4) / a + 1 / 2) * Δ * a ^ 2
      = 8 * a * Real.rpow b (8 / 9) * Δ + (8 * a ^ 2 + 4 * a + a ^ 2 / 2) * Δ := by
    field_simp
    ring
  calc ((8 * Real.rpow b (8 / 9) + 8 * a + 4) / a + 1 / 2) * Δ * a ^ 2
      = 8 * a * Real.rpow b (8 / 9) * Δ + (8 * a ^ 2 + 4 * a + a ^ 2 / 2) * Δ := hsplit
    _ ≤ 1 + 1 := add_le_add hkey hrest
    _ = 2 := by norm_num

/-- **`theta_range_fast2`.**  Doubled-range version of `theta_range_fast`: the index range
`|k| ≤ 8 (q(n+1))^{8/9} + 8 q n + 4` still carries the bound `2/(q n)²`, in the fast
(Liouville) regime `q(n+1) ≥ (8 q n)^9`.

As in `theta_range_fast`: the residue bound `4/(q n)²` holds on `|r| ≤ q n/2`
(`theta_residue_bound`, using `csm * (q n)² ≥ 10⁶`), and re-folding `k = m·q n + r` around the
near-period `q n` costs `(Y/(q n) + 1/2) Δ n ≤ 2/(q n)²` because `Δ n < 1/q(n+1)` and
`q(n+1) ≥ (8 q n)^9` — that is exactly `fast_shift_arith2`. -/
theorem theta_range_fast2 {α θ : ℝ} {K₀ : ℤ} {csm : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ}
    (hK₀1 : 1 ≤ K₀) (hcsm : 0 < csm)
    (h1 : ∀ k : ℤ, |k| < K₀ → csm ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀ ≤ |k| → (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (hqpos : ∀ i, 0 < q i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hn : 1 ≤ n) (hbig : 10 ^ 6 ≤ csm * (q n : ℝ) ^ 2)
    (hfast : (8 * q n) ^ 9 ≤ q (n + 1)) :
    ∀ j : ℤ, |(j : ℝ)| ≤ 8 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 8 * (q n : ℝ) + 4 →
      2 / (q n : ℝ) ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α) := by
  have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hqnpos : 0 < q n := hqpos n
  have ha1 : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqnpos
  -- `hfast` over the reals
  have hfastR : (8 * (q n : ℝ)) ^ 9 ≤ (q (n + 1) : ℝ) := by exact_mod_cast hfast
  -- elementary facts about `Δ n`
  have hΔ0 : 0 ≤ Δ n := by rw [hΔeq n]; exact abs_nonneg _
  have hΔlt : Δ n < 1 / (q (n + 1) : ℝ) := hΔup n
  -- (1) reduced-index bound with constant `4/(q n)²`
  have hred : ∀ r : ℤ, ((|r| : ℤ) : ℝ) ≤ (q n : ℝ) / 2 →
      4 / (q n : ℝ) ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (r : ℝ) * α) :=
    Main.theta_residue_bound hK₀1 hcsm h1 h2 hqnpos hbig
  have hc : (0 : ℝ) < 4 / (q n : ℝ) ^ 2 := by positivity
  -- (2) the shift cost, for the doubled range
  have hshift :
      ((8 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 8 * (q n : ℝ) + 4) / (q n : ℝ) + 1 / 2) * Δ n
        ≤ (4 / (q n : ℝ) ^ 2) / 2 := by
    have h1' := fast_shift_arith2 (a := (q n : ℝ)) (b := (q (n + 1) : ℝ)) (Δ := Δ n)
      ha1 hΔ0 hfastR hΔlt
    have he : (4 / (q n : ℝ) ^ 2) / 2 = 2 / (q n : ℝ) ^ 2 := by ring
    rw [he]; exact h1'
  -- (3) re-fold the index range
  have key := Main.theta_refold (α := α) (θ := θ) (Q := q n) (Δ := Δ n)
      (c := 4 / (q n : ℝ) ^ 2)
      (Y := 8 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 8 * (q n : ℝ) + 4)
      hqnpos hc (hΔeq n) hred hshift
  intro j hj
  have hj' := key j hj
  have he : (4 / (q n : ℝ) ^ 2) / 2 = 2 / (q n : ℝ) ^ 2 := by ring
  rw [he] at hj'
  exact hj'

end Work.TMC16Core.Assembly.Aux2
