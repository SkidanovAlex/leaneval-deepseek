import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.interfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- `primesIn a b` only contains primes lying in the real interval `[a, b]`. -/
lemma le_of_mem_primesIn {a b : ℝ} {p : ℕ} (hp : p ∈ primesIn a b) : a ≤ (p : ℝ) := by
  simp only [primesIn, natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
  exact le_trans (Nat.le_ceil a) (by exact_mod_cast hp.1.1)

/-- `primesIn a b` only contains primes lying in the real interval `[a, b]`. -/
lemma mem_primesIn_le {a b : ℝ} {p : ℕ} (hp : p ∈ primesIn a b) : (p : ℝ) ≤ b := by
  simp only [primesIn, natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
  have hge : (2 : ℝ) ≤ (⌊b⌋₊ : ℝ) := by
    have hp2 : (2 : ℕ) ≤ p := hp.2.two_le
    have h1 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have h2 : (p : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast hp.1.2
    linarith
  have hb : 0 ≤ b := by
    by_contra hb
    have hb' : b < 0 := not_le.mp hb
    have h0 : ⌊b⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [h0] at hge
    norm_num at hge
  exact le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le hb)

/-- The distance between two distinct naturals, viewed as reals, is at least `1`. -/
lemma one_le_abs_cast_sub {m n : ℕ} (h : m ≠ n) : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
  have h' : ((m : ℤ) - (n : ℤ)) ≠ 0 := by simp [sub_ne_zero, h]
  have h1 : (1 : ℤ) ≤ |((m : ℤ) - (n : ℤ))| := Int.one_le_abs h'
  have hcast : ((|((m : ℤ) - (n : ℤ))| : ℤ) : ℝ) = |(m : ℝ) - (n : ℝ)| := by
    simp only [Int.cast_abs, Int.cast_sub, Int.cast_natCast]
  rw [← hcast]
  exact_mod_cast h1

/-- Two distinct primes `p₁ ≠ p₂` in the narrow range `[a₁, b₁]` (with `a₁ ≥ 2`) cannot both
arise from the same source point `x` in the `incPairs` incidence set: the two rescaled points
`x/p₁`, `x/p₂` would have to be simultaneously within `3H/a₁` of `X'` and separated by at
least `x/b₁² ≥ 20 H`. -/
theorem incPairs_two_primes_forbidden {k : ℕ} {X H a₁ b₁ C : ℝ} {S₀ : Finset ℝ}
    {pol : ℝ → Polynomial ℝ} {pol' : Polynomial ℝ} {x X' : ℝ} {p₁ p₂ : ℕ}
    (hS₀ : IsFam X H S₀) (ha₁ : 0 < a₁) (hb₁ : 0 < b₁) (hH : 0 < H)
    (hn : 5 * b₁ ≤ 7 * a₁) (hXH : 200 * b₁ ^ 2 ≤ X / H) (hX : 0 < X) (h2a : 2 ≤ a₁)
    (hne : p₁ ≠ p₂)
    (h1 : (x, p₁) ∈ incPairs k C S₀ a₁ b₁ H (3 * H / a₁) (H / a₁) pol pol' X')
    (h2 : (x, p₂) ∈ incPairs k C S₀ a₁ b₁ H (3 * H / a₁) (H / a₁) pol pol' X') :
    False := by
  simp only [incPairs, Finset.mem_filter, Finset.mem_product] at h1 h2
  obtain ⟨⟨hx1, hp1⟩, hbnd1, -⟩ := h1
  obtain ⟨⟨-, hp2⟩, hbnd2, -⟩ := h2
  have hq1lo : a₁ ≤ (p₁ : ℝ) := le_of_mem_primesIn hp1
  have hq1hi : (p₁ : ℝ) ≤ b₁ := mem_primesIn_le hp1
  have hq2lo : a₁ ≤ (p₂ : ℝ) := le_of_mem_primesIn hp2
  have hq2hi : (p₂ : ℝ) ≤ b₁ := mem_primesIn_le hp2
  have hxge : X / 10 ≤ x := (hS₀.1 x hx1).1
  -- `x` is large: `x ≥ X/10 ≥ 20 b₁² H`
  have hXlarge : 20 * b₁ ^ 2 * H ≤ x := by
    have h : 200 * b₁ ^ 2 * H ≤ X := by
      have h' := (le_div_iff₀ hH).mp hXH
      linarith
    linarith
  -- `|p₁ - p₂| ≥ 1` as reals
  have hdiff : 1 ≤ |(p₂ : ℝ) - (p₁ : ℝ)| :=
    one_le_abs_cast_sub (Ne.symm hne)
  -- lower bound for the separation of the two rescaled points
  have hlow : 20 * H ≤ |x / (p₁ : ℝ) - x / (p₂ : ℝ)| := by
    set q1 : ℝ := (p₁ : ℝ) with hq1def
    set q2 : ℝ := (p₂ : ℝ) with hq2def
    have hq1pos : 0 < q1 := lt_of_lt_of_le ha₁ hq1lo
    have hq2pos : 0 < q2 := lt_of_lt_of_le ha₁ hq2lo
    have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hXlarge
    have hq1q2pos : 0 < q1 * q2 := mul_pos hq1pos hq2pos
    have hprod : q1 * q2 ≤ b₁ ^ 2 := by
      have h : q1 * q2 ≤ b₁ * b₁ :=
        mul_le_mul hq1hi hq2hi (le_of_lt hq2pos) (le_of_lt hb₁)
      nlinarith
    have hid : x / q1 - x / q2 = x * (q2 - q1) / (q1 * q2) := by
      field_simp
    have habs : |x / q1 - x / q2| = x * |q2 - q1| / (q1 * q2) := by
      rw [hid, abs_div, abs_mul, abs_of_pos hxpos, abs_of_pos hq1q2pos]
    rw [habs]
    have hnum : 20 * b₁ ^ 2 * H ≤ x * |q2 - q1| := by
      have h1' : x * 1 ≤ x * |q2 - q1| := mul_le_mul_of_nonneg_left hdiff (le_of_lt hxpos)
      linarith
    have step1 : 20 * b₁ ^ 2 * H / (q1 * q2) ≤ x * |q2 - q1| / (q1 * q2) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hq1q2pos)
    have step2 : 20 * b₁ ^ 2 * H / b₁ ^ 2 ≤ 20 * b₁ ^ 2 * H / (q1 * q2) :=
      div_le_div_of_nonneg_left (by positivity) hq1q2pos hprod
    have step3 : 20 * b₁ ^ 2 * H / b₁ ^ 2 = 20 * H := by
      field_simp
    linarith [step1, step2, step3]
  -- upper bound: both rescaled points are within `3H/a₁` of `X'`
  have hup : |x / (p₁ : ℝ) - x / (p₂ : ℝ)| ≤ 3 * H / a₁ + 3 * H / a₁ := by
    have htri : |x / (p₁ : ℝ) - x / (p₂ : ℝ)| ≤
        |x / (p₁ : ℝ) - X'| + |x / (p₂ : ℝ) - X'| := by
      have h := abs_sub_le (x / (p₁ : ℝ)) X' (x / (p₂ : ℝ))
      rwa [abs_sub_comm X' (x / (p₂ : ℝ))] at h
    linarith
  have hsmall : 3 * H / a₁ + 3 * H / a₁ ≤ 3 * H := by
    rw [← add_div, div_le_iff₀ ha₁]
    nlinarith
  linarith [hlow, hup, hsmall]

end Work.BMF
