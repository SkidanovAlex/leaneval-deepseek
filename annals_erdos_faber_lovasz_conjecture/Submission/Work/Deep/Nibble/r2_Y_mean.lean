import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Nibble.r2_own_b

/-!
# The expected number of uncovered vertices after one round of the nibble

Each edge of the hypergraph `𝓖` is kept independently with probability `p = θ/D`.  A vertex
is uncovered iff none of the edges through it is kept, so the expected number of uncovered
vertices is `∑_v (1-p)^{d(v)}` where `d(v) = hd 𝓖 v` is the degree of `v`.

Since `(1 - θ/D)^D ≈ e^{-θ}`, and each degree is within a relative `ε` of `D` with
`4ε ≤ δ`, `8θ² ≤ δD`, the expectation is `e^{-θ} |V| (1 ± δ/2)`.

The whole content is one per-vertex numerical estimate: for `|d - D| ≤ εD`,

  `|(1-p)^d - e^{-θ}| ≤ δ/8 + δ/400 ≤ δ/2`,

the first term being `|e^{-θ} - (1-p)^D| ≤ D p² = θ²/D ≤ δ/8` (a difference of two `D`-th
powers, estimated by `abs_pow_sub_pow_le` and `e^{-p} - (1-p) ≤ p²`), and the second being
the effect of the degree irregularity, `|(1-p)^d - (1-p)^D| ≤ ε D p = εθ ≤ δ/400`
(Bernoulli's inequality).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Elementary numerical estimates -/

/-- Bernoulli's inequality for a natural exponent: `1 - n p ≤ (1 - p)^n` for `0 ≤ p ≤ 1`. -/
lemma r2Y_bernoulli {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * p ≤ (1 - p) ^ n := by
  have h := one_add_mul_le_pow (a := -p) (by linarith) n
  have e1 : (1 + (n : ℝ) * (-p)) = (1 - (n : ℝ) * p) := by ring
  have e2 : (1 + -p : ℝ) = (1 - p) := by ring
  rw [e1, e2] at h
  exact h

/-- `e^{-p} - (1 - p) ≤ p²` for `p ≥ 0`. -/
lemma r2Y_exp_neg_sub {p : ℝ} (hp0 : 0 ≤ p) : Real.exp (-p) - (1 - p) ≤ p ^ 2 := by
  have hp1 : 0 < 1 + p := by linarith
  have hne : (1 : ℝ) + p ≠ 0 := ne_of_gt hp1
  have hexp : 1 + p ≤ Real.exp p := by
    have := Real.add_one_le_exp p
    linarith
  have hle : Real.exp (-p) ≤ 1 / (1 + p) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hp1 hexp
  have h1 : 1 - p ≤ Real.exp (-p) := by
    have := Real.add_one_le_exp (-p)
    linarith
  have h2 : (1 : ℝ) / (1 + p) - (1 - p) = p ^ 2 / (1 + p) := by
    field_simp
    ring
  have h3 : p ^ 2 / (1 + p) ≤ p ^ 2 := by
    rw [div_le_iff₀ hp1]
    nlinarith [sq_nonneg p, hp0]
  linarith

/-- **Comparison of two `(1-p)`-powers with nearby exponents.**
If `|b - x| ≤ t` then `|(1-p)^b - (1-p)^x| ≤ t p`. -/
lemma r2Y_pow_close {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {b x : ℕ} {t : ℝ}
    (h : |(b : ℝ) - (x : ℝ)| ≤ t) :
    |(1 - p) ^ b - (1 - p) ^ x| ≤ t * p := by
  have ht : 0 ≤ t := le_trans (abs_nonneg _) h
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  rcases le_total x b with hle | hle
  · -- `x ≤ b`
    have hcast : ((b - x : ℕ) : ℝ) = (b : ℝ) - (x : ℝ) := Nat.cast_sub hle
    have hbx : b = x + (b - x) := by omega
    have hpow : (1 - p) ^ b = (1 - p) ^ x * (1 - p) ^ (b - x) := by
      conv_lhs => rw [hbx, pow_add]
    have hsplit : (1 - p) ^ x - (1 - p) ^ b = (1 - p) ^ x * (1 - (1 - p) ^ (b - x)) := by
      rw [hpow]; ring
    have hbern := r2Y_bernoulli hp0 hp1 (b - x)
    have hbnd2 : 0 ≤ 1 - (1 - p) ^ (b - x) := by
      have := pow_le_one₀ hq0 hq1 (n := b - x)
      linarith
    have hmono : (1 - p) ^ b ≤ (1 - p) ^ x := by
      rw [hpow]
      exact mul_le_of_le_one_right (pow_nonneg hq0 x) (pow_le_one₀ hq0 hq1)
    have hbt : ((b - x : ℕ) : ℝ) ≤ t := by
      rw [hcast]
      exact (abs_le.mp h).2
    rw [abs_of_nonpos (by linarith : (1 - p) ^ b - (1 - p) ^ x ≤ 0)]
    have hgoal : (1 - p) ^ x - (1 - p) ^ b ≤ t * p := by
      rw [hsplit]
      calc (1 - p) ^ x * (1 - (1 - p) ^ (b - x))
          ≤ 1 * (1 - (1 - p) ^ (b - x)) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hbnd2
        _ = 1 - (1 - p) ^ (b - x) := one_mul _
        _ ≤ ((b - x : ℕ) : ℝ) * p := by linarith [hbern]
        _ ≤ t * p := mul_le_mul_of_nonneg_right hbt hp0
    linarith
  · -- `b ≤ x`
    have hcast : ((x - b : ℕ) : ℝ) = (x : ℝ) - (b : ℝ) := Nat.cast_sub hle
    have hxb : x = b + (x - b) := by omega
    have hpow : (1 - p) ^ x = (1 - p) ^ b * (1 - p) ^ (x - b) := by
      conv_lhs => rw [hxb, pow_add]
    have hsplit : (1 - p) ^ b - (1 - p) ^ x = (1 - p) ^ b * (1 - (1 - p) ^ (x - b)) := by
      rw [hpow]; ring
    have hbern := r2Y_bernoulli hp0 hp1 (x - b)
    have hbnd2 : 0 ≤ 1 - (1 - p) ^ (x - b) := by
      have := pow_le_one₀ hq0 hq1 (n := x - b)
      linarith
    have hmono : (1 - p) ^ x ≤ (1 - p) ^ b := by
      rw [hpow]
      exact mul_le_of_le_one_right (pow_nonneg hq0 b) (pow_le_one₀ hq0 hq1)
    have hbt : ((x - b : ℕ) : ℝ) ≤ t := by
      rw [hcast]
      linarith [(abs_le.mp h).1]
    rw [abs_of_nonneg (by linarith : 0 ≤ (1 - p) ^ b - (1 - p) ^ x)]
    have hgoal : (1 - p) ^ b - (1 - p) ^ x ≤ t * p := by
      rw [hsplit]
      calc (1 - p) ^ b * (1 - (1 - p) ^ (x - b))
          ≤ 1 * (1 - (1 - p) ^ (x - b)) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hbnd2
        _ = 1 - (1 - p) ^ (x - b) := one_mul _
        _ ≤ ((x - b : ℕ) : ℝ) * p := by linarith [hbern]
        _ ≤ t * p := mul_le_mul_of_nonneg_right hbt hp0
    linarith

/-- **`e^{-θ}` is close to `(1-p)^D` when `p D = θ`:** the difference is at most `D p²`. -/
lemma r2Y_exp_pow_close {p θ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {D : ℕ}
    (hpD : p * (D : ℝ) = θ) :
    |Real.exp (-θ) - (1 - p) ^ D| ≤ (D : ℝ) * p ^ 2 := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have he : Real.exp (-p) ^ D = Real.exp (-θ) := by
    rw [← Real.exp_nat_mul, mul_neg, mul_comm (D : ℝ) p, hpD]
  rw [← he]
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hp2 : (0 : ℝ) ≤ p ^ 2 := sq_nonneg p
  have ha1 : |Real.exp (-p)| ≤ 1 := by
    rw [abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
    linarith
  have hb1 : |1 - p| ≤ 1 := by
    rw [abs_of_nonneg hq0]
    exact hq1
  have hmax : max |Real.exp (-p)| |1 - p| ^ (D - 1) ≤ 1 :=
    pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) (max_le ha1 hb1)
  have hbase : |Real.exp (-p) - (1 - p)| ≤ p ^ 2 := by
    have h1 : 1 - p ≤ Real.exp (-p) := by
      have := Real.add_one_le_exp (-p)
      linarith
    rw [abs_of_nonneg (by linarith)]
    exact r2Y_exp_neg_sub hp0
  have hstep : |Real.exp (-p) - (1 - p)| * (D : ℝ) ≤ p ^ 2 * (D : ℝ) :=
    mul_le_mul_of_nonneg_right hbase hD0
  calc |Real.exp (-p) ^ D - (1 - p) ^ D|
      ≤ |Real.exp (-p) - (1 - p)| * (D : ℝ) * max |Real.exp (-p)| |1 - p| ^ (D - 1) :=
        abs_pow_sub_pow_le _ _ _
    _ = (|Real.exp (-p) - (1 - p)| * (D : ℝ)) * max |Real.exp (-p)| |1 - p| ^ (D - 1) := by
        ring
    _ ≤ (p ^ 2 * (D : ℝ)) * 1 :=
        mul_le_mul hstep hmax (by positivity) (by positivity)
    _ = (D : ℝ) * p ^ 2 := by ring

/-! ## The per-vertex estimate -/

/-- **Per-vertex estimate.**  If `p = θ/D`, `|d - D| ≤ εD`, `4ε ≤ δ` and `8θ² ≤ δD`, then the
probability `(1-p)^d` that a vertex of degree `d` is uncovered is within `δ/2` of `e^{-θ}`. -/
lemma r2Y_per_vertex {θ δ ε p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ)
    (hε0 : 0 < ε) (hεδ : 4 * ε ≤ δ) {D d : ℕ} (hD : 8 ≤ D)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hpD : p * (D : ℝ) = θ)
    (hbig : 8 * θ ^ 2 ≤ δ * (D : ℝ)) (hdeg : |(d : ℝ) - (D : ℝ)| ≤ ε * (D : ℝ)) :
    |(1 - p) ^ d - Real.exp (-θ)| ≤ δ / 2 := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  have hp_eq : p = θ / (D : ℝ) := by
    rw [eq_div_iff hDne]
    exact hpD
  -- the systematic part: `|e^{-θ} - (1-p)^D| ≤ D p² = θ²/D ≤ δ/8`
  have hA : |Real.exp (-θ) - (1 - p) ^ D| ≤ δ / 8 := by
    have h := r2Y_exp_pow_close hp0 hp1 hpD
    have hDp2 : (D : ℝ) * p ^ 2 = θ ^ 2 / (D : ℝ) := by
      have h1 : (D : ℝ) * p = θ := by rw [mul_comm]; exact hpD
      have h2 : θ * p = θ ^ 2 / (D : ℝ) := by
        rw [hp_eq, mul_div]; ring
      calc (D : ℝ) * p ^ 2 = ((D : ℝ) * p) * p := by ring
        _ = θ * p := by rw [h1]
        _ = θ ^ 2 / (D : ℝ) := h2
    have hb : θ ^ 2 / (D : ℝ) ≤ δ / 8 := by
      rw [div_le_iff₀ hDpos]
      nlinarith [hbig]
    linarith
  -- the irregularity: `|(1-p)^d - (1-p)^D| ≤ εθ ≤ δ/400`
  have hB : |(1 - p) ^ d - (1 - p) ^ D| ≤ δ / 400 := by
    have h := r2Y_pow_close hp0 hp1 (b := d) (x := D) (t := ε * (D : ℝ)) hdeg
    have he1 : (ε * (D : ℝ)) * p = ε * θ := by
      rw [mul_assoc, mul_comm (D : ℝ) p, hpD]
    have hkey : (4 * ε) * (100 * θ) ≤ δ * 1 :=
      mul_le_mul hεδ (by linarith) (by linarith) hδ0.le
    have he2 : ε * θ ≤ δ / 400 := by nlinarith [hkey]
    linarith [h, he1, he2]
  have htri : |(1 - p) ^ d - Real.exp (-θ)|
      ≤ |(1 - p) ^ d - (1 - p) ^ D| + |(1 - p) ^ D - Real.exp (-θ)| := by
    have := dist_triangle ((1 - p) ^ d) ((1 - p) ^ D) (Real.exp (-θ))
    simpa [Real.dist_eq] using this
  have hsym : |(1 - p) ^ D - Real.exp (-θ)| = |Real.exp (-θ) - (1 - p) ^ D| := abs_sub_comm _ _
  linarith [htri, hA, hB, hsym]

/-! ## The mean of the number of uncovered vertices -/

theorem r2_Y_mean {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V))
    {θ δ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ) (hε0 : 0 < ε)
    (hεδ : 4 * ε ≤ δ)
    {D : ℕ} (hD : 8 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hθD : θ / (D : ℝ) ≤ 1 / 2) (hbig : 8 * θ ^ 2 ≤ δ * (D : ℝ))
    (hdeg : ∀ v : V, |((Work.Deep.Nibble.hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ)) :
    |(Work.Deep.Nibble.edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
        (fun ω => ((Work.Deep.Nibble.uncovF 𝓖 ω).card : ℝ))
        - Real.exp (-θ) * (Fintype.card V : ℝ)| ≤ δ * (Fintype.card V : ℝ) / 2 := by
  classical
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  have hpd : (θ / (D : ℝ)) * (D : ℝ) = θ := div_mul_cancel₀ θ hDne
  have hE := (r2_exp_basic 𝓖 hp0 hp1).2.2.2.2
  rw [hE]
  have hsplit : (∑ v : V, ((1 - θ / (D : ℝ)) ^ (hd 𝓖 v) - Real.exp (-θ)))
      = (∑ v : V, (1 - θ / (D : ℝ)) ^ (hd 𝓖 v))
        - Real.exp (-θ) * (Fintype.card V : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  rw [← hsplit]
  calc |∑ v : V, ((1 - θ / (D : ℝ)) ^ (hd 𝓖 v) - Real.exp (-θ))|
      ≤ ∑ v : V, |(1 - θ / (D : ℝ)) ^ (hd 𝓖 v) - Real.exp (-θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, δ / 2 := by
        refine Finset.sum_le_sum (fun v _ => ?_)
        exact r2Y_per_vertex hθ0 hθ1 hδ0 hε0 hεδ hD hp0 hp1 hpd hbig (hdeg v)
    _ = δ * (Fintype.card V : ℝ) / 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Work.Deep.Nibble
