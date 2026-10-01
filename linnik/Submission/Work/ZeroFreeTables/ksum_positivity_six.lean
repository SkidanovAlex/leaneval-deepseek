/-
# ZeroFreeTables — `ksum_positivity_six`

The six-term positivity of the Heath–Brown §6 / (9.1) type, for a pair of
characters `(χ₁, χ₂)` with `χ₁² = 1`, the *pair* being the two characters
`χ₂^k` and `χ₁ · χ₂^k`, `k = 0,1,2`:

```
0 ≤ (κ² + ½)·(K(β, χ₁) + K(β, 1))
  + 2κ·(K(β+iγ, χ₂) + K(β+iγ, χ₁χ₂))
  + ½·(K(β+2iγ, χ₂²) + K(β+2iγ, χ₁χ₂²)),
```

where `K(s, χ) = Σ'_n Λ(n)·ℜ(χ(n) n^{-s})·f(log n / L)`.

The mathematics is the classical pointwise observation.  For `n` a unit of
`ZMod q` put `a = χ₁(n) ∈ {1, −1}` (because `χ₁² = 1`) and `b = χ₂(n)·n^{-iγ}`,
a point of the unit circle.  Since `ℜ(χ(n) n^{-β-iγ}) = n^{-β} ℜ(χ(n) n^{-iγ})`,
the `n`-th summand of the two `k`-th pieces equals `Λ(n) f(log n/L) n^{-β}`
times

```
(κ² + ½)(ℜa + 1) + 2κ(ℜb + ℜ(ab)) + ½(ℜ(b²) + ℜ(ab²)) = (1 + ℜa)(κ + ℜb)² ≥ 0,
```

using `a = ±1` (so `ab = ±b`, `ℜ(b²) = 2ℜ(b)² − 1` for `‖b‖ = 1`) — the kernel
identity `six_kernel_identity`.  For `n` not a unit every character value
vanishes and the whole summand is `0`.  The `tsum`s are finite because `f` is
supported below `x₀`, which reduces the statement to the finite-sum assembly
`combination_six_nonneg`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.TrigPolyPos
import Submission.Work.ZeroFreeTables.six_kernel_identity
import Submission.Work.ZeroFreeTables.combination_six_nonneg
import Submission.Work.ZeroFreeTables.exists_vanishing_log_div

open Complex DirichletCharacter MulChar
open scoped BigOperators
noncomputable section

-- `hx₀` and `hk` are part of the requested statement; the argument does not need them.
set_option linter.unusedVariables false

namespace Work.ZeroFreeTables

/-- **Pointwise (in `n`) form of HB (6.3) for the pair `(χ₂ᵏ, χ₁χ₂ᵏ)`.**  For `n ≥ 1`, a real
character `χ₁` (`χ₁² = 1`), any `χ₂`, `κ ∈ ℝ` and `f ≥ 0`, the six summands at `n` combine to
`Λ(n) f(log n / L) n^{-β} (1 + ℜχ₁(n))(κ + ℜ(χ₂(n) n^{-iγ}))² ≥ 0`. -/
private theorem ksum_six_pointwise {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {L β γ k : ℝ} (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ * χ₁ = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (k ^ 2 + 1/2) *
          ((ArithmeticFunction.vonMangoldt n : ℝ) *
             (χ₁ (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re * f (Real.log n / L)
           + (ArithmeticFunction.vonMangoldt n : ℝ) *
             ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
               * f (Real.log n / L))
      + 2 * k *
          ((ArithmeticFunction.vonMangoldt n : ℝ) *
             (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
               * f (Real.log n / L)
           + (ArithmeticFunction.vonMangoldt n : ℝ) *
             ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
               * f (Real.log n / L))
      + (1/2) *
          ((ArithmeticFunction.vonMangoldt n : ℝ) *
             ((χ₂ * χ₂) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ : ℂ) + (γ : ℂ)) * Complex.I)).re
               * f (Real.log n / L)
           + (ArithmeticFunction.vonMangoldt n : ℝ) *
             ((χ₁ * (χ₂ * χ₂)) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ : ℂ) + (γ : ℂ)) * Complex.I)).re
               * f (Real.log n / L)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  by_cases hunit : IsUnit (n : ZMod q)
  · -- `n` is a unit of `ZMod q`: the kernel is `(1 + ℜa)(κ + ℜb)²`
    set a : ℂ := χ₁ (n : ZMod q) with ha
    set b : ℂ := χ₂ (n : ZMod q) * (n : ℂ) ^ (-((γ : ℂ) * Complex.I)) with hbdef
    have ha_sq : a * a = 1 := by
      rw [ha, ← MulChar.mul_apply, hχ₁]
      exact MulChar.one_apply hunit
    have hafac : (a - 1) * (a + 1) = 0 := by linear_combination ha_sq
    have hacases : a = 1 ∨ a = -1 := by
      rcases mul_eq_zero.mp hafac with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)
    have hbnorm : ‖b‖ = 1 := by
      rw [hbdef, Complex.norm_mul]
      have h1 : ‖χ₂ (n : ZMod q)‖ = 1 := by
        rw [← hunit.unit_spec]; exact DirichletCharacter.unit_norm_eq_one χ₂ hunit.unit
      have h2 : ‖(n : ℂ) ^ (-((γ : ℂ) * Complex.I))‖ = 1 := by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
        simp
      rw [h1, h2, one_mul]
    have h1n : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 1 := MulChar.one_apply hunit
    have h12 : (χ₁ * χ₂) (n : ZMod q) = a * χ₂ (n : ZMod q) := by
      rw [MulChar.mul_apply, ← ha]
    have h122 : (χ₁ * (χ₂ * χ₂)) (n : ZMod q) = a * (χ₂ (n : ZMod q) * χ₂ (n : ZMod q)) := by
      rw [MulChar.mul_apply, MulChar.mul_apply, ← ha]
    have hsplit2 : (n : ℂ) ^ (-(((γ : ℂ) + (γ : ℂ)) * Complex.I))
        = (n : ℂ) ^ (-((γ : ℂ) * Complex.I)) * (n : ℂ) ^ (-((γ : ℂ) * Complex.I)) := by
      rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
    have hAB : (χ₁ * χ₂) (n : ZMod q) * (n : ℂ) ^ (-((γ : ℂ) * Complex.I)) = a * b := by
      rw [h12, hbdef]; ring
    have hBB : (χ₂ * χ₂) (n : ZMod q) * (n : ℂ) ^ (-(((γ : ℂ) + (γ : ℂ)) * Complex.I)) = b * b := by
      rw [hbdef, MulChar.mul_apply, hsplit2]; ring
    have h122B : (χ₁ * (χ₂ * χ₂)) (n : ZMod q)
        * (n : ℂ) ^ (-(((γ : ℂ) + (γ : ℂ)) * Complex.I)) = a * (b * b) := by
      rw [h122, hbdef, hsplit2]; ring
    have re1 : (a / (n : ℂ) ^ (β : ℂ)).re = (n : ℝ) ^ (-β) * a.re := by
      rw [ha]
      have h := re_div_cpow_eq χ₁ hn β 0
      simp only [add_zero, neg_zero, Complex.cpow_zero, mul_one] at h
      rw [h]
    have re0 : (((1 : DirichletCharacter ℂ q)) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
        = (n : ℝ) ^ (-β) * 1 := by
      have h := re_div_cpow_eq (1 : DirichletCharacter ℂ q) hn β 0
      simp only [add_zero, neg_zero, Complex.cpow_zero, mul_one] at h
      rw [h, h1n]
      simp
    have re2 : (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
        = (n : ℝ) ^ (-β) * b.re := by
      rw [re_div_cpow_eq χ₂ hn β ((γ : ℂ) * Complex.I), hbdef]
    have re3 : ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
        = (n : ℝ) ^ (-β) * (a * b).re := by
      rw [re_div_cpow_eq (χ₁ * χ₂) hn β ((γ : ℂ) * Complex.I), hAB]
    have re4 : ((χ₂ * χ₂) (n : ZMod q) /
          (n : ℂ) ^ ((β : ℂ) + ((γ : ℂ) + (γ : ℂ)) * Complex.I)).re
        = (n : ℝ) ^ (-β) * (b * b).re := by
      rw [re_div_cpow_eq (χ₂ * χ₂) hn β (((γ : ℂ) + (γ : ℂ)) * Complex.I), hBB]
    have re5 : ((χ₁ * (χ₂ * χ₂)) (n : ZMod q) /
          (n : ℂ) ^ ((β : ℂ) + ((γ : ℂ) + (γ : ℂ)) * Complex.I)).re
        = (n : ℝ) ^ (-β) * (a * (b * b)).re := by
      rw [re_div_cpow_eq (χ₁ * (χ₂ * χ₂)) hn β (((γ : ℂ) + (γ : ℂ)) * Complex.I), h122B]
    set t1 : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ) * (a / (n : ℂ) ^ (β : ℂ)).re
        * f (Real.log n / L) with ht1
    set t2 : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)
        * (((1 : DirichletCharacter ℂ q)) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
        * f (Real.log n / L) with ht2
    set t3 : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)
        * (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
        * f (Real.log n / L) with ht3
    set t4 : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)
        * ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
        * f (Real.log n / L) with ht4
    set t5 : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)
        * ((χ₂ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ : ℂ) + (γ : ℂ)) * Complex.I)).re
        * f (Real.log n / L) with ht5
    set t6 : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)
        * ((χ₁ * (χ₂ * χ₂)) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + ((γ : ℂ) + (γ : ℂ)) * Complex.I)).re
        * f (Real.log n / L) with ht6
    have hmain : (k ^ 2 + 1/2) * (t1 + t2) + 2 * k * (t3 + t4) + (1/2) * (t5 + t6)
        = (ArithmeticFunction.vonMangoldt n : ℝ) * f (Real.log n / L) * (n : ℝ) ^ (-β)
          * ((k ^ 2 + 1/2) * (a.re + 1) + 2 * k * (b.re + (a * b).re)
              + (1/2) * ((b * b).re + (a * (b * b)).re)) := by
      rw [ht1, ht2, ht3, ht4, ht5, ht6, re1, re0, re2, re3, re4, re5]
      ring
    have hbracket : 0 ≤ (k ^ 2 + 1/2) * (a.re + 1) + 2 * k * (b.re + (a * b).re)
        + (1/2) * ((b * b).re + (a * (b * b)).re) := by
      rw [six_kernel_identity k hacases hbnorm]
      exact mul_nonneg (by rcases hacases with h | h <;> rw [h] <;> norm_num) (sq_nonneg _)
    rw [hmain]
    have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by positivity
    have hF : 0 ≤ f (Real.log n / L) := hf _
    have hnb : 0 ≤ (n : ℝ) ^ (-β) := Real.rpow_nonneg hnpos.le _
    exact mul_nonneg (mul_nonneg (mul_nonneg hΛ hF) hnb) hbracket
  · -- `n` is not a unit: every character value vanishes, so every summand is `0`
    have hχ₁n : χ₁ (n : ZMod q) = 0 := MulChar.map_nonunit χ₁ hunit
    have hχ₂n : χ₂ (n : ZMod q) = 0 := MulChar.map_nonunit χ₂ hunit
    have h1n : ((1 : DirichletCharacter ℂ q)) (n : ZMod q) = 0 := MulChar.map_nonunit 1 hunit
    have h12n : (χ₁ * χ₂) (n : ZMod q) = 0 := MulChar.map_nonunit (χ₁ * χ₂) hunit
    have h22n : (χ₂ * χ₂) (n : ZMod q) = 0 := MulChar.map_nonunit (χ₂ * χ₂) hunit
    have h122n : (χ₁ * (χ₂ * χ₂)) (n : ZMod q) = 0 :=
      MulChar.map_nonunit (χ₁ * (χ₂ * χ₂)) hunit
    rw [hχ₁n, hχ₂n, h1n, h12n, h22n, h122n]
    simp

theorem ksum_positivity_six {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {x₀ L β γ k : ℝ} (hx₀ : 0 < x₀) (hL : 0 < L)
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ * χ₁ = 1) (hk : 0 ≤ k) :
    0 ≤ (k ^ 2 + 1/2) * ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (χ₁ (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
              * f (Real.log n / L)))
      + 2 * k * ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
              * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
              * f (Real.log n / L)))
      + (1/2) * ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₂ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ : ℂ) + (γ : ℂ)) * Complex.I)).re
              * f (Real.log n / L))
          + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * (χ₂ * χ₂)) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ : ℂ) + (γ : ℂ)) * Complex.I)).re
              * f (Real.log n / L))) := by
  classical
  -- beyond `N` the weight `f(log n / L)` vanishes, so every `tsum` is a finite sum
  obtain ⟨N, hN⟩ := exists_vanishing_log_div hL hsupp
  set s1 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ₁ (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re * f (Real.log n / L) with hs1
  set s2 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
        * f (Real.log n / L) with hs2
  set s3 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
        * f (Real.log n / L) with hs3
  set s4 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
        * f (Real.log n / L) with hs4
  set s5 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₂ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ : ℂ) + (γ : ℂ)) * Complex.I)).re
        * f (Real.log n / L) with hs5
  set s6 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * (χ₂ * χ₂)) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ : ℂ) + (γ : ℂ)) * Complex.I)).re
        * f (Real.log n / L) with hs6
  have hz1 : ∀ n : ℕ, N ≤ n → s1 n = 0 := fun n hn => by
    simp only [hs1, hN n hn]; ring
  have hz2 : ∀ n : ℕ, N ≤ n → s2 n = 0 := fun n hn => by
    simp only [hs2, hN n hn]; ring
  have hz3 : ∀ n : ℕ, N ≤ n → s3 n = 0 := fun n hn => by
    simp only [hs3, hN n hn]; ring
  have hz4 : ∀ n : ℕ, N ≤ n → s4 n = 0 := fun n hn => by
    simp only [hs4, hN n hn]; ring
  have hz5 : ∀ n : ℕ, N ≤ n → s5 n = 0 := fun n hn => by
    simp only [hs5, hN n hn]; ring
  have hz6 : ∀ n : ℕ, N ≤ n → s6 n = 0 := fun n hn => by
    simp only [hs6, hN n hn]; ring
  have hterm : ∀ n : ℕ, 0 ≤ (k ^ 2 + 1/2) * (s1 n + s2 n) + 2 * k * (s3 n + s4 n)
      + (1/2) * (s5 n + s6 n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · -- `n = 0`: `Λ(0) = 0` kills every summand
      subst h
      have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact not_isPrimePow_zero
      have hzero : (k ^ 2 + 1/2) * (s1 0 + s2 0) + 2 * k * (s3 0 + s4 0)
          + (1/2) * (s5 0 + s6 0) = 0 := by
        simp only [hs1, hs2, hs3, hs4, hs5, hs6, hΛ0, Nat.cast_zero]
        ring
      rw [hzero]
    · -- `n ≥ 1`: the pointwise kernel is non-negative
      simpa only [hs1, hs2, hs3, hs4, hs5, hs6] using
        ksum_six_pointwise hf χ₁ χ₂ hχ₁ h
  exact combination_six_nonneg hz1 hz2 hz3 hz4 hz5 hz6 hterm

end Work.ZeroFreeTables
