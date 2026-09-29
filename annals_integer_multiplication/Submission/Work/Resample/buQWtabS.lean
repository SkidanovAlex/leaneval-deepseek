import Mathlib
import Submission.Work.Resample.buQWtab

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.buQWtabS`: sizes of the five static table entries (rounded constants)

This is the `2`-vs-`4` and `p+4`-vs-`p+6` variant of `Work.Resample.buQWtab`: the same five bounds
with slack (the cost budgets elsewhere are stated with `4·(·+1)·(p+6)` and `16·(egM+1)·(·+1)·(p+6)`),
together with the size of the six parameter values that the word pushes as `Val.int` (their
`natAbs` is `< 2^(p+1)`, hence parse in `≤ p+3` glyphs).
-/

/-- The size of `Val.int n` for `n < 2^k` (a natural is encoded by `size + 2` glyphs). -/
private lemma buQWtabS_vsz_int (n p : ℕ) (h : n < 2 ^ (p + 1)) :
    vsz (Val.int (n : ℤ)) ≤ p + 3 := by
  rw [Work.Fx.vsz_int, isz, Int.natAbs_natCast]
  have h2 : n.size ≤ p + 1 := Nat.size_le.mpr h
  omega

/-- `egN p α s t ≤ α²+1`: the Neumann depth is a rounded quotient, and `θ ≥ p/α⁴` forces
`p·s ≤ α⁴(t-s)`. -/
private lemma buQWtabS_egN_le (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    egN p α s t ≤ α ^ 2 + 1 := by
  have hαR : (α : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (α : ℝ) := by exact_mod_cast (by omega : 0 < α)
    exact ne_of_gt this
  have hsR0 : (s : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
    exact ne_of_gt this
  have hsub : (t : ℝ) / (s : ℝ) - 1 = ((t - s : ℕ) : ℝ) / (s : ℝ) := by
    have h2 : ((t - s : ℕ) : ℝ) = (t : ℝ) - (s : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hst)]
    rw [h2]
    have hsR : (s : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
      exact ne_of_gt this
    field_simp
  rw [hsub] at hθ
  have h1 : (p : ℝ) * (s : ℝ) ≤ (α : ℝ) ^ 4 * ((t - s : ℕ) : ℝ) := by
    have h2 : (p : ℝ) / (α : ℝ) ^ 4 * ((α : ℝ) ^ 4 * (s : ℝ)) ≤
        ((t - s : ℕ) : ℝ) / (s : ℝ) * ((α : ℝ) ^ 4 * (s : ℝ)) :=
      mul_le_mul_of_nonneg_right hθ (by positivity)
    have e1 : (p : ℝ) / (α : ℝ) ^ 4 * ((α : ℝ) ^ 4 * (s : ℝ)) = (p : ℝ) * (s : ℝ) := by
      field_simp
    have e2 : ((t - s : ℕ) : ℝ) / (s : ℝ) * ((α : ℝ) ^ 4 * (s : ℝ)) =
        ((t - s : ℕ) : ℝ) * (α : ℝ) ^ 4 := by
      field_simp
    linarith [e1 ▸ h2, e2 ▸ h2]
  have h1n : p * s ≤ α ^ 4 * (t - s) := by exact_mod_cast h1
  have hX : p * s ≤ (α ^ 2 * (t - s)) * α ^ 2 := by
    have he : (α ^ 2 * (t - s)) * α ^ 2 = α ^ 4 * (t - s) := by ring
    omega
  have hdiv : (p * s - 1) / (α ^ 2 * (t - s)) ≤ α ^ 2 :=
    Nat.div_le_of_le_mul (le_trans (Nat.sub_le _ _) hX)
  simp only [egN]
  omega

/-- numeric slack `2k(p+4) ≤ 4k(p+6)`. -/
private lemma buQWtabS_slack (k p : ℕ) : 2 * k * (p + 4) ≤ 4 * k * (p + 6) := by
  have h : 2 * (p + 4) ≤ 4 * (p + 6) := by omega
  calc 2 * k * (p + 4) = k * (2 * (p + 4)) := by ring
    _ ≤ k * (4 * (p + 6)) := Nat.mul_le_mul_left k h
    _ = 4 * k * (p + 6) := by ring

/-- numeric slack `8M(s+1)(p+4) ≤ 16M(s+1)(p+6)`. -/
private lemma buQWtabS_slackM (M s p : ℕ) :
    8 * (M + 1) * (s + 1) * (p + 4) ≤ 16 * (M + 1) * (s + 1) * (p + 6) := by
  have h : 8 * (p + 4) ≤ 16 * (p + 6) := by omega
  calc 8 * (M + 1) * (s + 1) * (p + 4) = ((M + 1) * (s + 1)) * (8 * (p + 4)) := by ring
    _ ≤ ((M + 1) * (s + 1)) * (16 * (p + 6)) := Nat.mul_le_mul_left _ h
    _ = 16 * (M + 1) * (s + 1) * (p + 6) := by ring

theorem buQWtabS (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p) (hα : 2 ≤ α)
    (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
    (hwt : ∀ ℓ h : ℤ, h ≠ 0 → (Work.Resample.buWt p α s t ℓ h).natAbs ≤ 2 ^ (p + 1))
    (hwd : ∀ ℓ : ℤ, 8 * (Work.Resample.buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p) :
    HvdH.vsz (Work.Resample.buKeysT s t) ≤ 4 * (t + 1) * (p + 6) ∧
    HvdH.vsz (Work.Resample.buKeysS s t) ≤ 4 * (s + 1) * (p + 6) ∧
    HvdH.vsz (Work.Resample.buWdL p α s t) ≤ 4 * (s + 1) * (p + 6) ∧
    HvdH.vsz (Work.Resample.buColsT p α s t) ≤ 16 * (Work.Resample.egM p α + 1) * (s + 1) * (p + 6) ∧
    HvdH.vsz (Work.Resample.buSignsT p α s t) ≤ 8 * (Work.Resample.egN p α s t + 1) ∧
    HvdH.vsz (HvdH.Val.int (p : ℤ)) ≤ p + 3 ∧ HvdH.vsz (HvdH.Val.int (α : ℤ)) ≤ p + 3 ∧
    HvdH.vsz (HvdH.Val.int (s : ℤ)) ≤ p + 3 ∧ HvdH.vsz (HvdH.Val.int (t : ℤ)) ≤ p + 3 ∧
    HvdH.vsz (HvdH.Val.int ((Work.Resample.egM p α : ℕ) : ℤ)) ≤ p + 3 ∧
    HvdH.vsz (HvdH.Val.int ((Work.Resample.egN p α s t : ℕ) : ℤ)) ≤ p + 3 := by
  obtain ⟨hkT, hkS, hwdL, hcols, hsigns⟩ := buQWtab p α s t hs hst htp hα hp hwt hwd
  -- the six parameters are all `< 2^(p+1)`
  have hp1 : p < 2 ^ (p + 1) := lt_trans (Nat.lt_succ_self p) (Nat.lt_two_pow_self (n := p + 1))
  have hα1 : α < 2 ^ (p + 1) := by
    have hαle : α ≤ α ^ 2 := by
      calc α = α * 1 := by ring
        _ ≤ α * α := Nat.mul_le_mul_left α (by omega)
        _ = α ^ 2 := by ring
    exact lt_of_lt_of_le (lt_of_le_of_lt hαle hαp) (le_of_lt hp1)
  have hpow : (2 : ℕ) ^ p ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs1 : s < 2 ^ (p + 1) := lt_of_lt_of_le (lt_trans hst htp) hpow
  have ht1 : t < 2 ^ (p + 1) := lt_of_lt_of_le htp hpow
  have hM1 : egM p α < 2 ^ (p + 1) := by
    have h1 : egM p α ≤ Nat.sqrt p + 1 := by
      have := Nat.div_le_self (Nat.sqrt p) (2 * α)
      simp only [egM]
      omega
    have h2 : Nat.sqrt p ≤ p := Nat.sqrt_le_self p
    have h3 : p + 1 < 2 ^ (p + 1) := Nat.lt_two_pow_self (n := p + 1)
    omega
  have hN1 : egN p α s t < 2 ^ (p + 1) := by
    have h1 := buQWtabS_egN_le p α s t hs hst hα hθ
    have h2 : α ^ 2 + 1 ≤ p := by omega
    omega
  exact ⟨le_trans hkT (buQWtabS_slack (t + 1) p), le_trans hkS (buQWtabS_slack (s + 1) p),
    le_trans hwdL (buQWtabS_slack (s + 1) p), le_trans hcols (buQWtabS_slackM (egM p α) s p), hsigns,
    buQWtabS_vsz_int p p hp1, buQWtabS_vsz_int α p hα1, buQWtabS_vsz_int s p hs1,
    buQWtabS_vsz_int t p ht1, buQWtabS_vsz_int (egM p α) p hM1, buQWtabS_vsz_int (egN p α s t) p hN1⟩

end Work.Resample
