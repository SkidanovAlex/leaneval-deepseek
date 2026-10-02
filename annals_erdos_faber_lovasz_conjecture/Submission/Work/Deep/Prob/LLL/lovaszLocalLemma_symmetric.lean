/-
# The symmetric Lovász local lemma

`Work.Deep.Prob.LLL.lovaszLocalLemma_symmetric` : for a finite family `A : ι → Set Ω` of bad
events in a finite probability space, each of probability at most `p`, each dependent on at
most `d` of the others (witnessed by the `Finset`s `D i` together with the independence
hypothesis `hindep` of the asymmetric lemma), and with `e · p · (d+1) ≤ 1`, the probability
that *none* of the events occurs is positive.

The proof is the classical reduction of the symmetric statement to the asymmetric one: the
asymmetric (lopsided) local lemma is applied with the constant witness
`x i = 1/(d+2)`.  The only arithmetic input is

  `e · p · (d+1) ≤ 1  ⟹  p ≤ (1/(d+2)) · ((d+1)/(d+2))^d`,

which follows from `(1 + 1/(d+1))^(d+1) ≤ e`.  This choice of `x` is legitimate for every
`d : ℕ` (unlike the optimal `x = 1/(d+1)`, which equals `1` when `d = 0`).
-/
import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Prob.Basic
import Submission.Work.Deep.Prob.Spaces
import Submission.Work.Deep.Prob.LLL.lovaszLocalLemma_lopsided

namespace Work.Deep.Prob.LLL

open scoped BigOperators
open Finset

/-- The elementary bound `(1 + 1/n)^n ≤ e` for `n : ℕ`, as used in the LLL. -/
private theorem exp_one_add_inv_pow_le (n : ℕ) :
    (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hle : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
      have h := Real.add_one_le_exp (1 / (n : ℝ))
      linarith
    have hpow : (Real.exp (1 / (n : ℝ))) ^ n = Real.exp 1 := by
      rw [← Real.exp_nat_mul, one_div, mul_inv_cancel₀ hn']
    calc (1 + 1 / (n : ℝ)) ^ n ≤ (Real.exp (1 / (n : ℝ))) ^ n :=
          pow_le_pow_left₀ (by positivity) hle n
      _ = Real.exp 1 := hpow

/-- The numeric core of the symmetric local lemma: `e · p · (d+1) ≤ 1` forces `p` below the
value `x · (1-x)^d` of the asymmetric lemma at the constant witness `x = 1/(d+2)`. -/
private theorem lll_numeric_bound {p : ℝ} {d : ℕ} (h : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) :
    p ≤ (1 / ((d : ℝ) + 2)) * (((d : ℝ) + 1) / ((d : ℝ) + 2)) ^ d := by
  by_cases hp0 : p ≤ 0
  · have hA : 0 ≤ (1 / ((d : ℝ) + 2)) * (((d : ℝ) + 1) / ((d : ℝ) + 2)) ^ d :=
      mul_nonneg (by positivity) (by positivity)
    linarith
  · have hp0' : 0 < p := not_le.mp hp0
    -- `p ≤ 1/(e (d+1))`, and the reciprocal of `e (d+1)` is below the right-hand side.
    have hp1 : p ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h]
    have hkey : (1 + 1 / ((d : ℝ) + 1)) ^ (d + 1) ≤ Real.exp 1 := by
      have h' := exp_one_add_inv_pow_le (d + 1)
      simpa [Nat.cast_add, Nat.cast_one] using h'
    -- the two algebraic shapes of the right-hand side
    have hshift : (1 + 1 / ((d : ℝ) + 1)) = ((d : ℝ) + 2) / ((d : ℝ) + 1) := by
      have hne : ((d : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hmul : ((d : ℝ) + 1) * (((d : ℝ) + 2) / ((d : ℝ) + 1)) = ((d : ℝ) + 2) :=
      mul_div_cancel₀ _ (by positivity : ((d : ℝ) + 1) ≠ 0)
    have hdecomp : ((d : ℝ) + 2) * ((((d : ℝ) + 2) / ((d : ℝ) + 1)) ^ d)
        = ((d : ℝ) + 1) * ((1 + 1 / ((d : ℝ) + 1)) ^ (d + 1)) := by
      rw [hshift, pow_succ', ← mul_assoc, hmul]
    have hA : (1 / ((d : ℝ) + 2)) * (((d : ℝ) + 1) / ((d : ℝ) + 2)) ^ d
        = 1 / (((d : ℝ) + 2) * ((((d : ℝ) + 2) / ((d : ℝ) + 1)) ^ d)) := by
      rw [one_div, one_div, mul_inv, ← inv_pow, inv_div]
    have hYpos : (0 : ℝ) < ((d : ℝ) + 2) * ((((d : ℝ) + 2) / ((d : ℝ) + 1)) ^ d) := by
      positivity
    have hYE : ((d : ℝ) + 2) * ((((d : ℝ) + 2) / ((d : ℝ) + 1)) ^ d)
        ≤ ((d : ℝ) + 1) * Real.exp 1 := by
      rw [hdecomp]
      exact mul_le_mul_of_nonneg_left hkey (by positivity)
    have hp2 : p ≤ 1 / (((d : ℝ) + 2) * ((((d : ℝ) + 2) / ((d : ℝ) + 1)) ^ d)) := by
      rw [le_div_iff₀ hYpos]
      calc p * (((d : ℝ) + 2) * ((((d : ℝ) + 2) / ((d : ℝ) + 1)) ^ d))
          ≤ p * (((d : ℝ) + 1) * Real.exp 1) := mul_le_mul_of_nonneg_left hYE hp0'.le
        _ = Real.exp 1 * p * ((d : ℝ) + 1) := by ring
        _ ≤ 1 := h
    rw [hA]
    exact hp2

theorem lovaszLocalLemma_symmetric {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω) {ι : Type*}
    [Fintype ι] (A : ι → Set Ω) (D : ι → Finset ι) {p : ℝ} (hp : ∀ i, P.prob (A i) ≤ p)
    {d : ℕ} (hd : ∀ i, (D i).card ≤ d)
    (hindep : ∀ i (T : Finset ι), (∀ j ∈ T, j ∉ D i ∧ j ≠ i) →
      FinProbSpace.indepOfCompls P (A i) A T)
    (hpd : Real.exp 1 * p * (d + 1) ≤ 1) :
    0 < P.prob (⋂ i, (A i)ᶜ) := by
  classical
  -- The constant witness `x i = 1/(d+2)`.
  set x : ι → ℝ := fun _ => 1 / ((d : ℝ) + 2) with hx
  have hx_fact : ∀ j : ι, 1 - x j = ((d : ℝ) + 1) / ((d : ℝ) + 2) := by
    intro j
    have hne : ((d : ℝ) + 2) ≠ 0 := by positivity
    simp only [hx]
    field_simp
    ring
  have hx0 : ∀ i, 0 ≤ x i := by
    intro i; simp only [hx]; positivity
  have hx1 : ∀ i, x i < 1 := by
    intro i
    have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
    simp only [hx]
    rw [div_lt_one hd2]
    linarith
  -- The asymmetric hypothesis at that witness.
  have hbound : ∀ i, P.prob (A i) ≤ x i * ∏ j ∈ D i, (1 - x j) := by
    intro i
    have hprod : ∏ j ∈ D i, (1 - x j) = (((d : ℝ) + 1) / ((d : ℝ) + 2)) ^ (D i).card := by
      rw [Finset.prod_congr rfl (fun j _ => hx_fact j), Finset.prod_const]
    have hbase0 : (0 : ℝ) ≤ ((d : ℝ) + 1) / ((d : ℝ) + 2) := by positivity
    have hbase1 : ((d : ℝ) + 1) / ((d : ℝ) + 2) ≤ 1 := by
      have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
      rw [div_le_one hd2]
      linarith
    have hle : (((d : ℝ) + 1) / ((d : ℝ) + 2)) ^ d
        ≤ (((d : ℝ) + 1) / ((d : ℝ) + 2)) ^ (D i).card :=
      pow_le_pow_of_le_one hbase0 hbase1 (hd i)
    calc P.prob (A i) ≤ p := hp i
      _ ≤ (1 / ((d : ℝ) + 2)) * (((d : ℝ) + 1) / ((d : ℝ) + 2)) ^ d :=
            lll_numeric_bound hpd
      _ ≤ x i * ∏ j ∈ D i, (1 - x j) := by
            rw [hprod]
            simp only [hx]
            exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hlops : ∀ i (T : Finset ι), (∀ j ∈ T, j ∉ D i ∧ j ≠ i) →
      FinProbSpace.LopsidedIndep P (A i) A T :=
    fun i T hT => FinProbSpace.indepOfCompls.lopsided P (hindep i T hT)
  have hmain : ∏ i, (1 - x i) ≤ P.prob (⋂ i, (A i)ᶜ) :=
    lovaszLocalLemma_lopsided P A D x hx0 hx1 hbound hlops
  have hpos : 0 < ∏ i : ι, (1 - x i) := by
    refine Finset.prod_pos (fun i _ => ?_)
    rw [hx_fact i]
    positivity
  exact lt_of_lt_of_le hpos hmain

end Work.Deep.Prob.LLL
