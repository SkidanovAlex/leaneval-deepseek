import Mathlib
import Submission.Commons.NumberTheory.Linnik.Ksum_positivity

open MulChar
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.Linnik

/-- A real character (satisfying `χ * χ = 1`) takes only the values `0`, `1`, `-1`. -/
theorem realChar_values {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hreal : χ * χ = 1)
    (a : ZMod q) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases hu : IsUnit a
  · have hsq : χ a * χ a = 1 := by
      rw [← MulChar.mul_apply, hreal, MulChar.one_apply hu]
    have hfac : (χ a - 1) * (χ a + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (add_eq_zero_iff_eq_neg.mp h))
  · exact Or.inl (MulChar.map_nonunit χ hu)

/-- **HB (6.11), pointwise.**  For `n ≥ 1` and a real `χ`,
`Λ(n) n^{-β} f(log n/L) · (χ₀(n) + χ(n))(1 + ℜ(n^{-iγ})) ≥ 0`; written out, the four `K`-summands
`K(β,χ₀) + K(β,χ) + K(β+iγ,χ) + K(β+iγ,χ₀)` are non-negative. -/
theorem Ksum_pointwise_real {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) {L β γ : ℝ}
    (χ : DirichletCharacter ℂ q) (hreal : χ * χ = 1) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
            * f (Real.log n / L) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hnorm_unit : ∀ w : ℂ, ‖(n : ℂ) ^ w‖ = Real.exp (w.re * Real.log n) := by
    intro w
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  -- the values of `χ` and of the principal character at `n`
  have hvalχ := realChar_values χ hreal (n : ZMod q)
  have hval0 : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 0 ∨
      ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 1 := by
    by_cases hu : IsUnit (n : ZMod q)
    · exact Or.inr (by rw [← hu.unit_spec]; exact MulChar.one_apply hu)
    · exact Or.inl (MulChar.map_nonunit (1 : DirichletCharacter ℂ q) hu)
  set p : ℝ := ((1 : DirichletCharacter ℂ q) (n : ZMod q)).re with hp
  set c : ℝ := (χ (n : ZMod q)).re with hc
  set e : ℝ := ((n : ℂ) ^ (-((γ : ℂ) * Complex.I))).re with he
  set d : ℝ := (χ (n : ZMod q) * (n : ℂ) ^ (-((γ : ℂ) * Complex.I))).re with hd
  have hp01 : p = 0 ∨ p = 1 := by
    rcases hval0 with h | h
    · exact Or.inl (by rw [hp, h]; simp)
    · exact Or.inr (by rw [hp, h]; simp)
  have hc01 : c = 0 ∨ c = 1 ∨ c = -1 := by
    rcases hvalχ with h | h | h
    · left; rw [hc, h]; simp
    · right; left; rw [hc, h]; simp
    · right; right; rw [hc, h]; norm_num
  have hcd : d = c * e := by
    have him : (χ (n : ZMod q)).im = 0 := by
      rcases hvalχ with h | h | h <;> (rw [h]; simp)
    rw [hd, hc, he, Complex.mul_re, him]
    ring
  have hpc0 : p = 0 → c = 0 := by
    intro h0
    have h0' : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 0 := by
      rcases hval0 with hh | hh
      · exact hh
      · exfalso; rw [hp, hh] at h0; norm_num at h0
    have hnu : ¬ IsUnit (n : ZMod q) := by
      intro hu
      have h1 : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 1 := by
        rw [← hu.unit_spec]; exact MulChar.one_apply hu
      rw [h0'] at h1; exact zero_ne_one h1
    rw [hc, MulChar.map_nonunit χ hnu]; simp
  have hpc : 0 ≤ p + c := by
    rcases hp01 with h | h
    · rw [h, hpc0 h]; norm_num
    · rcases hc01 with h2 | h2 | h2 <;> rw [h, h2] <;> norm_num
  have he1 : -1 ≤ e := by
    have h2 := Complex.abs_re_le_norm ((n : ℂ) ^ (-((γ : ℂ) * Complex.I)))
    rw [hnorm_unit] at h2
    have hzero : (-((γ : ℂ) * Complex.I)).re = 0 := by simp
    rw [hzero, zero_mul, Real.exp_zero] at h2
    have h4 : |e| ≤ 1 := by rw [he]; exact h2
    exact (abs_le.mp h4).1
  -- rewrite the four summands
  have e1 : ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
      = (n : ℝ) ^ (-β) * p := by
    have h := re_div_cpow_eq (1 : DirichletCharacter ℂ q) hn β 0
    simp only [add_zero, neg_zero, Complex.cpow_zero, mul_one] at h
    rw [h, hp]
  have e2 : (χ (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re = (n : ℝ) ^ (-β) * c := by
    have h := re_div_cpow_eq χ hn β 0
    simp only [add_zero, neg_zero, Complex.cpow_zero, mul_one] at h
    rw [h, hc]
  have e3 : (χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
      = (n : ℝ) ^ (-β) * d := by
    rw [re_div_cpow_eq χ hn β ((γ : ℂ) * Complex.I), hd]
  have e4 : ((1 : DirichletCharacter ℂ q) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (p * e) := by
    rw [re_div_cpow_eq (1 : DirichletCharacter ℂ q) hn β ((γ : ℂ) * Complex.I)]
    have hpr : ((1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-((γ : ℂ) * Complex.I))).re
        = p * e := by
      rw [Complex.mul_re, hp, he]
      have him : ((1 : DirichletCharacter ℂ q) (n : ZMod q)).im = 0 := by
        rcases hval0 with h | h <;> (rw [h]; simp)
      rw [him]; ring
    rw [hpr]
  have hmain : (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      + (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
            * f (Real.log n / L)
      = (ArithmeticFunction.vonMangoldt n : ℝ) * f (Real.log n / L) * (n : ℝ) ^ (-β)
          * ((p + c) * (1 + e)) := by
    rw [e1, e2, e3, e4, hcd]
    ring
  rw [hmain]
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hff : 0 ≤ f (Real.log n / L) := hf _
  have hnb : 0 ≤ (n : ℝ) ^ (-β) := Real.rpow_nonneg hnpos.le _
  exact mul_nonneg (mul_nonneg (mul_nonneg hΛ hff) hnb) (mul_nonneg hpc (by linarith))

/-- **HB (6.11).**  For a non-negative `f` supported in `[0,x₀]` and a real character `χ`,
`K(β,χ₀) + K(β,χ) + K(β+iγ,χ) + K(β+iγ,χ₀) ≥ 0`. -/
theorem Ksum_positivity_real {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t)
    {x₀ L β γ : ℝ} (hx₀ : 0 < x₀) (hL : 0 < L)
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (χ : DirichletCharacter ℂ q) (hreal : χ * χ = 1) :
    0 ≤ (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
            * f (Real.log n / L))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re * f (Real.log n / L))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
            * f (Real.log n / L))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((1 : DirichletCharacter ℂ q) (n : ZMod q) /
            (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
            * f (Real.log n / L)) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → x₀ ≤ Real.log n / L := by
    refine ⟨Nat.ceil (Real.exp (x₀ * L)) + 1, fun n hn => ?_⟩
    have h1 : Real.exp (x₀ * L) ≤ (n : ℝ) := by
      have : (Nat.ceil (Real.exp (x₀ * L)) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) hn)
      exact le_trans (Nat.le_ceil _) this
    have h2 : x₀ * L ≤ Real.log (n : ℝ) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    rw [le_div_iff₀ hL]
    linarith
  have hvan : ∀ n : ℕ, N ≤ n → f (Real.log n / L) = 0 := fun n hn => hsupp _ (hN n hn)
  set s₀ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
        * f (Real.log n / L) with hs₀
  set s₁ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re * f (Real.log n / L) with hs₁
  set s₂ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
        * f (Real.log n / L) with hs₂
  set s₃ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((1 : DirichletCharacter ℂ q) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + (γ : ℂ) * Complex.I)).re
        * f (Real.log n / L) with hs₃
  have hzero : ∀ n : ℕ, N ≤ n → s₀ n = 0 ∧ s₁ n = 0 ∧ s₂ n = 0 ∧ s₃ n = 0 := by
    intro n hn
    have h := hvan n hn
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · simp only [hs₀, hs₁, hs₂, hs₃, h]
        ring
  have h0 : (∑' n : ℕ, s₀ n) = ∑ n ∈ Finset.range N, s₀ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).1)
  have h1 : (∑' n : ℕ, s₁ n) = ∑ n ∈ Finset.range N, s₁ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.1)
  have h2 : (∑' n : ℕ, s₂ n) = ∑ n ∈ Finset.range N, s₂ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.1)
  have h3 : (∑' n : ℕ, s₃ n) = ∑ n ∈ Finset.range N, s₃ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.2)
  have hterm : ∀ n ∈ Finset.range N, 0 ≤ s₀ n + s₁ n + s₂ n + s₃ n := by
    intro n _
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
        rintro ⟨p, k, hp, hk, hpk⟩
        have h1 : 0 < p ^ k := pow_pos (Nat.prime_iff.mpr hp).pos k
        omega
      simp only [hs₀, hs₁, hs₂, hs₃, hΛ0]
      norm_num
    · simpa only [hs₀, hs₁, hs₂, hs₃] using Ksum_pointwise_real hf χ hreal h
  rw [h0, h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_nonneg hterm

end Commons.NumberTheory.Linnik
