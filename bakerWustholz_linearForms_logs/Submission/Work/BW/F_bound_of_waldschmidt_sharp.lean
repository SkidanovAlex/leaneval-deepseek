import Mathlib
import Submission.Work.BW.aligned_defs
import Submission.Work.BW.sum_mul_prod_erase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp `F`-bound from Waldschmidt's relation bound

## Status: the requested statement is FALSE as written (mis-parenthesised)

The requested lemma

```
wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) t ≤
  (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i) /
    (9 * (Module.finrank ℚ K : ℝ) ^ 2)
```

is parsed by Lean's big-operator notation with the trailing `/ (9 d²)` **inside** the `∏`-binder,
because a `∏ i, …` body extends as far to the right as possible.  That is, the right-hand side is

`(9 m d³)^m · ∏ i, (h'(αᵢ, ℓᵢ) / (9 d²)) = (9 m d³)^m · (∏ i, h'(αᵢ, ℓᵢ)) / (9 d²)^m`,

which is far *smaller* than the intended sharp bound

`(9 m d³)^m · (∏ i, h'(αᵢ, ℓᵢ)) / (9 d²)`.

The intended statement (division **outside** the product) is true, and is proved below as
`F_bound_of_waldschmidt_sharp_explicit`; the requested statement is refuted by a concrete
counterexample.

### Counterexample to the statement as parsed

Take `K = ℚ` (so `d = 1`), `m = 2`, `α = ![1, 1]`, `ℓ = ![0, 0]`, `t = ![9, 9]`.

* `h'(1, 0) = max(logHeight₁ 1, ‖0‖, 1) = 1`, so `∏_{j ≠ k} h'(α_j, ℓ_j) = 1` and the
  hypothesis `ht` reads `|t k| ≤ (9 · 1 · 1³)¹ · 1 = 9`, which holds with equality.
* The left-hand side is `wn ![9,9] = 9·1 + 9·1 = 18`.
* The right-hand side is `18² · (1/9)² = 324/81 = 4`.

So the conclusion would be `18 ≤ 4`, which is false.
-/

namespace Work.BW

open Complex

/-- Arithmetic core of the *intended* sharp `F`-bound: for `d > 0` and any `m : ℕ`,
`m · d · (9(m-1)d³)^{m-1} ≤ (9 m d³)^m / (9 d²)`. -/
lemma F_bound_arith_sharp (m : ℕ) {d : ℝ} (hd : 0 < d) :
    (m : ℝ) * d * (9 * ((m : ℝ) - 1) * d ^ 3) ^ (m - 1) ≤
      (9 * (m : ℝ) * d ^ 3) ^ m / (9 * d ^ 2) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero, Nat.zero_sub, pow_zero, mul_one, zero_mul]
    positivity
  · have hd2 : (0 : ℝ) < 9 * d ^ 2 := by positivity
    rw [le_div_iff₀ hd2]
    have hd3 : (0 : ℝ) ≤ d ^ 3 := by positivity
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hbase0 : (0 : ℝ) ≤ 9 * ((m : ℝ) - 1) * d ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hd3
    have hbase_le : 9 * ((m : ℝ) - 1) * d ^ 3 ≤ 9 * (m : ℝ) * d ^ 3 := by
      have h1 : 9 * ((m : ℝ) - 1) ≤ 9 * (m : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right h1 hd3
    have hpow : (9 * ((m : ℝ) - 1) * d ^ 3) ^ (m - 1) ≤
        (9 * (m : ℝ) * d ^ 3) ^ (m - 1) :=
      pow_le_pow_left₀ hbase0 hbase_le (m - 1)
    have hstep : (m : ℝ) * d * (9 * ((m : ℝ) - 1) * d ^ 3) ^ (m - 1) * (9 * d ^ 2) ≤
        (m : ℝ) * d * (9 * (m : ℝ) * d ^ 3) ^ (m - 1) * (9 * d ^ 2) := by
      have h0 : (0 : ℝ) ≤ (m : ℝ) * d * (9 * d ^ 2) := by positivity
      nlinarith [hpow]
    calc (m : ℝ) * d * (9 * ((m : ℝ) - 1) * d ^ 3) ^ (m - 1) * (9 * d ^ 2)
        ≤ (m : ℝ) * d * (9 * (m : ℝ) * d ^ 3) ^ (m - 1) * (9 * d ^ 2) := hstep
      _ = (9 * (m : ℝ) * d ^ 3) * (9 * (m : ℝ) * d ^ 3) ^ (m - 1) := by ring
      _ = (9 * (m : ℝ) * d ^ 3) ^ m := by
          rw [← pow_succ']
          congr 1
          omega

/-- The modified height `h'(α, ℓ)` is nonnegative, since it dominates `1 / [K : ℚ] ≥ 0`. -/
private lemma hmod_nonneg_sharp {K : Type*} [Field K] [NumberField K] (β : K) (ℓ : ℂ) :
    0 ≤ hmod β ℓ := by
  have hd : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
  have h : (0 : ℝ) ≤ 1 / (Module.finrank ℚ K : ℝ) := by
    rw [one_div_nonneg]
    exact hd
  unfold hmod
  exact le_trans h (le_trans (le_max_right _ _) (le_max_right _ _))

/-- **The (intended) sharp `F`-bound from Waldschmidt's relation bound.**  Note the explicit
parentheses around the product: the division by `9 d²` is *outside* the product.  If every
coordinate `t k` satisfies `|t k| ≤ (9 (m-1) d³)^{m-1} ∏_{j ≠ k} h'(α_j, ℓ_j)`, then the
weighted `ℓ¹`-norm with weights `d · h'(αᵢ, ℓᵢ)` is at most
`(9 m d³)^m · (∏ᵢ h'(αᵢ, ℓᵢ)) / (9 d²)`, where `d = [K : ℚ]`. -/
theorem F_bound_of_waldschmidt_sharp_explicit {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (α : Fin m → K) (ℓ : Fin m → ℂ) (t : Fin m → ℤ)
    (ht : ∀ k : Fin m, |((t k : ℤ) : ℝ)| ≤
      (9 * ((m : ℝ) - 1) * (Module.finrank ℚ K : ℝ) ^ 3) ^ (m - 1) *
        ∏ j ∈ Finset.univ.erase k, hmod (α j) (ℓ j)) :
    wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) t ≤
      (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m *
        (∏ i, hmod (α i) (ℓ i)) / (9 * (Module.finrank ℚ K : ℝ) ^ 2) := by
  classical
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast h
  have hdpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := lt_of_lt_of_le zero_lt_one hd1
  have hmod0 : ∀ i, 0 ≤ hmod (α i) (ℓ i) := fun i => hmod_nonneg_sharp (α i) (ℓ i)
  rw [wn]
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hddef
  set C : ℝ := (9 * ((m : ℝ) - 1) * d ^ 3) ^ (m - 1) with hCdef
  have hP0 : 0 ≤ ∏ i, hmod (α i) (ℓ i) := Finset.prod_nonneg fun i _ => hmod0 i
  have hd0 : (0 : ℝ) ≤ d := hdpos.le
  -- the one-omitted products sum to `m · ∏ h`
  have hsum : ∑ i, hmod (α i) (ℓ i) * ∏ j ∈ Finset.univ.erase i, hmod (α j) (ℓ j)
      = (m : ℝ) * ∏ i, hmod (α i) (ℓ i) :=
    sum_mul_prod_erase (fun i => hmod (α i) (ℓ i))
  have harith : (m : ℝ) * d * C ≤ (9 * (m : ℝ) * d ^ 3) ^ m / (9 * d ^ 2) := by
    rw [hCdef]
    exact F_bound_arith_sharp m hdpos
  calc ∑ i, |((t i : ℤ) : ℝ)| * (d * hmod (α i) (ℓ i))
      ≤ ∑ i, (C * ∏ j ∈ Finset.univ.erase i, hmod (α j) (ℓ j)) *
          (d * hmod (α i) (ℓ i)) := by
        -- multiply the coordinatewise Waldschmidt bound by the nonnegative weight `d · h'`
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (ht i) (mul_nonneg hd0 (hmod0 i))
    _ = (C * d) * ((m : ℝ) * ∏ i, hmod (α i) (ℓ i)) := by
        -- every summand equals `(C * d) * ∏ h`
        rw [← hsum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ((m : ℝ) * d * C) * (∏ i, hmod (α i) (ℓ i)) := by ring
    _ ≤ (((9 * (m : ℝ) * d ^ 3) ^ m / (9 * d ^ 2)) * (∏ i, hmod (α i) (ℓ i))) :=
        mul_le_mul_of_nonneg_right harith hP0
    _ = (9 * (m : ℝ) * d ^ 3) ^ m * (∏ i, hmod (α i) (ℓ i)) / (9 * d ^ 2) := by
        rw [div_mul_eq_mul_div]

/-- **Formal refutation of the requested statement.**  With `K = ℚ` (`d = 1`), `m = 2`,
`α = ![1,1]`, `ℓ = ![0,0]`, `t = ![9,9]`: the hypothesis `ht` holds with equality, the left-hand
side is `18`, and the right-hand side *as parsed* is `4`, so the conclusion would demand
`18 ≤ 4`. -/
example :
    (∀ k : Fin 2, |(((![9,9] : Fin 2 → ℤ) k : ℤ) : ℝ)|
        ≤ (9 * ((2 : ℝ) - 1) * (Module.finrank ℚ ℚ : ℝ) ^ 3) ^ (2 - 1) *
            ∏ j ∈ Finset.univ.erase k, hmod (![1,1] j : ℚ) (![0,0] j : ℂ)) ∧
      wn (fun i : Fin 2 => (Module.finrank ℚ ℚ : ℝ) * hmod (![1,1] i : ℚ) (![0,0] i : ℂ))
          ![9,9] = 18 ∧
      (9 * (2 : ℝ) * (Module.finrank ℚ ℚ : ℝ) ^ 3) ^ 2 *
          ∏ i : Fin 2, hmod (![1,1] i : ℚ) (![0,0] i : ℂ) /
            (9 * (Module.finrank ℚ ℚ : ℝ) ^ 2) = 4 := by
  have h : ∀ j : Fin 2, hmod (![1,1] j : ℚ) (![0,0] j : ℂ) = 1 := by
    intro j
    fin_cases j <;> norm_num [hmod, Height.logHeight₁_one, Module.finrank_self]
  refine ⟨?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> simp only [h, Module.finrank_self] <;> norm_num
  · simp only [h, Module.finrank_self]
    norm_num [wn]
  · simp only [h, Module.finrank_self]
    norm_num

end Work.BW
