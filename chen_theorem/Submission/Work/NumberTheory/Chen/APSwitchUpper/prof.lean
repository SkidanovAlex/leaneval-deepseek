/-
# `APSwitchUpper.prof` — the Rosser–Iwaniec profile pair of the linear sieve

The two profile functions of the sharp (Rosser–Iwaniec) linear sieve that the switched-window
excess bound `window_excess_le` needs.

**Indexing / clamp parity (important — a previous attempt got this wrong).**  The family is the
classical delay-difference family `f_{n+1}` of Nathanson, *Additive Number Theory: the Classical
Bases*, Ch. 9, Thm. 9.4 / Bordignon arXiv:2007.08774 Lemma 1:

```
f_1(s) = (3 − s)/s                     (1 ≤ s ≤ 3, and 0 for s ≥ 3)
f_n(s) = 0                             for s ≥ n + 2      (support)
n even (n ≥ 2), s ≥ 2 :  s f_n(s) = ∫_s^∞ f_{n−1}(t−1) dt          (no clamp)
n odd  (n ≥ 3), s ≥ 1 :  s f_n(s) = ∫_{max(s,3)}^∞ f_{n−1}(t−1) dt (clamp at 3)
```

so the clamp sits at **odd** indices.  `profC j = f_{j+1}`, hence `profC j` is clamped for
`j` **even** (not odd — the `delayC` of `ri_delay_classical.lean` has this parity inverted, which
makes its even-index sum `0.75` at `s = 2` instead of `F(2) − 1 = e^γ − 1 = 0.7811`);
`profC 0 s = (3−s)/s` is the base case.  The profiles are

* `riPhi s = Σ_j profC (2j)   = F(s) − 1`   (`F` = the R–I upper function),
* `riPsi s = Σ_j profC (2j+1) = 1 − f(s)`   (`f` = the R–I lower function),
* `riUp  s = 1 + riPhi s      = F(s)`.

Numerically (the correct family, verified in `scratch/int.py`): `riUp s = 2e^γ/s` on `[1,3]`,
`1 − riPsi s = 2e^γ log(s−1)/s` on `[2,4]`, `F(2.2) = 1.6192`, `F(3) = 1.1874`, `F(4) = 1.0216`;
`riPhi`,`riPsi` decay like `exp(−2.5 s)` for large `s`.
-/
import Mathlib

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open MeasureTheory

/-- The delay-difference family `f_{j+1}` of the linear sieve (clamp at 3 for **even** `j ≥ 2`;
no clamp, `s ≥ 2`, for odd `j`). -/
noncomputable def profC : ℕ → ℝ → ℝ
  | 0 => fun s => if 1 ≤ s ∧ s ≤ 3 then (3 - s) / s else 0
  | (n + 1) => fun s =>
      if (n + 1) % 2 = 0 then
        (if 1 ≤ s ∧ s < (n : ℝ) + 4 then
          (∫ t in max s 3..((n : ℝ) + 4), profC n (t - 1)) / s else 0)
      else
        (if 2 ≤ s ∧ s < (n : ℝ) + 4 then
          (∫ t in s..((n : ℝ) + 4), profC n (t - 1)) / s else 0)

@[simp] theorem profC_zero (s : ℝ) :
    profC 0 s = if 1 ≤ s ∧ s ≤ 3 then (3 - s) / s else 0 := rfl

@[simp] theorem profC_succ (n : ℕ) (s : ℝ) :
    profC (n + 1) s =
      if (n + 1) % 2 = 0 then
        (if 1 ≤ s ∧ s < (n : ℝ) + 4 then
          (∫ t in max s 3..((n : ℝ) + 4), profC n (t - 1)) / s else 0)
      else
        (if 2 ≤ s ∧ s < (n : ℝ) + 4 then
          (∫ t in s..((n : ℝ) + 4), profC n (t - 1)) / s else 0) := rfl

/-- **Support.**  `profC j s = 0` for `s ≥ j + 3` (i.e. `f_{j+1}(s) = 0` for `s ≥ j + 3`, the
classical support edge `f_n(s) = 0` for `s ≥ n + 2`). -/
theorem profC_support : ∀ j : ℕ, ∀ s : ℝ, (j : ℝ) + 3 ≤ s → profC j s = 0 := by
  intro j
  induction j with
  | zero =>
      intro s hs
      rw [profC_zero]
      by_cases h : 1 ≤ s ∧ s ≤ 3
      · rw [if_pos h]
        have hs3 : s = 3 := le_antisymm h.2 (by linarith [hs])
        rw [hs3]; norm_num
      · rw [if_neg h]
  | succ n ih =>
      intro s hs
      have h4 : (n : ℝ) + 4 ≤ s := by
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hs
        linarith
      rw [profC_succ]
      by_cases hpar : (n + 1) % 2 = 0
      · rw [if_pos hpar, if_neg (by rintro ⟨-, h⟩; linarith)]
      · rw [if_neg hpar, if_neg (by rintro ⟨-, h⟩; linarith)]

/-- **Nonnegativity of the delay family.**  `profC j s ≥ 0` for all `j, s` (induction; each
recursion step is an integral of a nonnegative function, `intervalIntegral.integral_nonneg_of_forall`,
divided by `s > 0`). -/
theorem profC_nonneg : ∀ j : ℕ, ∀ s : ℝ, 0 ≤ profC j s := by
  intro j
  induction j with
  | zero =>
      intro s
      rw [profC_zero]
      by_cases h : 1 ≤ s ∧ s ≤ 3
      · rw [if_pos h]
        exact div_nonneg (by linarith [h.2]) (by linarith [h.1])
      · rw [if_neg h]
  | succ n ih =>
      intro s
      rw [profC_succ]
      by_cases hpar : (n + 1) % 2 = 0
      · rw [if_pos hpar]
        by_cases h1 : 1 ≤ s ∧ s < (n : ℝ) + 4
        · rw [if_pos h1]
          refine div_nonneg ?_ (by linarith [h1.1])
          refine intervalIntegral.integral_nonneg_of_forall ?_ (fun u => ih _)
          rw [max_le_iff]
          exact ⟨le_of_lt h1.2, by push_cast; linarith⟩
        · rw [if_neg h1]
      · rw [if_neg hpar]
        by_cases h2 : 2 ≤ s ∧ s < (n : ℝ) + 4
        · rw [if_pos h2]
          refine div_nonneg ?_ (by linarith [h2.1])
          exact intervalIntegral.integral_nonneg_of_forall (le_of_lt h2.2) (fun u => ih _)
        · rw [if_neg h2]

/-- The upper profile `F(s) − 1 = Σ_{n odd} f_n`. -/
noncomputable def riPhi (s : ℝ) : ℝ := ∑' j : ℕ, profC (2 * j) s

/-- The lower profile `1 − f(s) = Σ_{n even} f_n`. -/
noncomputable def riPsi (s : ℝ) : ℝ := ∑' j : ℕ, profC (2 * j + 1) s

/-- The Rosser–Iwaniec upper function `F`. -/
noncomputable def riUp (s : ℝ) : ℝ := 1 + riPhi s

/-- `riPhi` is nonnegative. -/
theorem riPhi_nonneg (s : ℝ) : 0 ≤ riPhi s :=
  tsum_nonneg (fun j => profC_nonneg (2 * j) s)

/-- `riPsi` is nonnegative. -/
theorem riPsi_nonneg (s : ℝ) : 0 ≤ riPsi s :=
  tsum_nonneg (fun j => profC_nonneg (2 * j + 1) s)

end

end Work.NumberTheory.Chen.APSwitchUpper
