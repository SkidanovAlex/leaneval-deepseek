import Mathlib
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_mean

namespace Commons.NumberTheory.Sieve

/-!
# Clearing denominators in the linear forms condition (Green–Tao §9, proof of Prop. 9.8)

## Mathematical content

In Green–Tao Definition 3.1 the linear forms have *rational* coefficients with numerator and
denominator at most `L₀`.  Green–Tao clear denominators (writing "at the expense of increasing the
bound on `L_ij` to `(k+1)!`").  The present statement makes that step rigorous: the linear forms
condition for rational coefficients follows from the same statement for *integer* coefficients.

Given rational coefficients `L i j = num/den` with `|num|, den ≤ L₀`, put `q := L₀ !` (a common
multiple of every denominator, and `q < p`), and set `A i j := q * (L i j).num / (L i j).den ∈ ℤ`
(exact division).  Then `|A i j| ≤ q * L₀ = L₀! * L₀`, and, crucially, for the *substitution*
`x ↦ q • x` on `(ZMod p)^t` (a bijection because `q` is a unit mod `p`, as `0 < q < p`),

`linForm p (L i) (b i) (q • x) = (∑_j (A i j : ZMod p) * x_j) + b i`

(the constant term `b i` is *not* scaled).  Hence

`∑_x ∏_i ν (linForm p (L i) (b i) x) = ∑_y ∏_i ν ((∑_j (A i j : ZMod p) * y_j) + b i)`

and the integer-coefficient hypothesis `h` (stated with the form inlined above) applies.

## Proof sketch
* `q := L₀ !`; for every denominator `den` occurring we have `den ≠ 0`, `den ≤ L₀`, hence
  `den ∣ L₀ !` (`Nat.dvd_factorial`) and `(den : ZMod p) ≠ 0` since `den ≤ L₀ < p`.
* `qmod p (L i j) * (q : ZMod p) = (A i j : ZMod p)`: expand
  `qmod p L = (num : ZMod p) / (den : ZMod p)`, use `(den : ZMod p) * (den : ZMod p)⁻¹ = 1` and
  `(q : ZMod p) = (den : ZMod p) * (q / den : ℕ)` with `A = num * (q / den)`.
* The map `x ↦ q • x` on `Fin t → ZMod p` is a bijection (`ZMod` is a field, `q ≠ 0`), so reindex the
  sum with `Fintype.sum_equiv`/`Finset.sum_bij` (note the summand is
  `∏_i ν (linForm p (L i) (b i) (q • x))`).
* Proportionality: `A i' = q • A i`-proportionality over `ℚ` coincides with `L i'`-proportionality
  over `ℚ` because `q ≠ 0`; the non-vanishing conditions transport similarly.
* Finally transport the hypothesis `h` (stated for `Fin m`) along `Fintype.equivFin ι` to obtain the
  `LinFormsCond` conclusion for an arbitrary finite index type `ι`.

## Interface notes
* `L₀.factorial < p` is needed for the invertibility of the common denominator.
* Keep the statement exactly as given (it is consumed by the §9 localisation step for `nuGT`).
-/

open Finset
open scoped BigOperators


/-- A positive natural number strictly below the prime `p` is a nonzero element of `ZMod p`. -/
lemma zmod_natCast_ne_zero_of_pos_of_lt {p n : ℕ} [Fact p.Prime] (hn0 : 0 < n) (hnp : n < p) :
    (n : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ n := (CharP.cast_eq_zero_iff (ZMod p) p n).mp h
  exact absurd (Nat.le_of_dvd hn0 hdvd) (not_le.mpr hnp)

/-- Clearing the denominator of a rational number: if `r.den ∣ q` and `c = q / r.den`, then the
integer `r.num * c` is the rational value `q * r`. -/
lemma rat_clear_mul {r : ℚ} {q : ℕ} (hdvd : r.den ∣ q) :
    ((r.num * ((q / r.den : ℕ) : ℤ) : ℤ) : ℚ) = (q : ℚ) * r := by
  have hr : (r.num : ℚ) = (r.den : ℚ) * r := by
    have h := Rat.num_div_den r
    field_simp at h
    exact h
  have hqc : (q : ℚ) = (r.den : ℚ) * ((q / r.den : ℕ) : ℚ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  calc ((r.num * ((q / r.den : ℕ) : ℤ) : ℤ) : ℚ)
      = (r.num : ℚ) * ((q / r.den : ℕ) : ℚ) := by rw [Int.cast_mul, Int.cast_natCast]
    _ = ((r.den : ℚ) * r) * ((q / r.den : ℕ) : ℚ) := by rw [hr]
    _ = (q : ℚ) * r := by rw [hqc]; ring

/-- Clearing denominators of a small rational coefficient of a linear form: for `L₀ ! < p` and a
rational `r` with `|r.num|, r.den ≤ L₀`, the value of `qmod p r` times `L₀ !` in `ZMod p` is the
integer form `r.num * (L₀ ! / r.den)`. -/
lemma qmod_mul_factorial {p : ℕ} [Fact p.Prime] {L₀ : ℕ} (hL₀ : L₀.factorial < p)
    {r : ℚ} (hr : IsSmallRat L₀ r) :
    qmod p r * (L₀.factorial : ZMod p)
      = ((r.num * ((L₀.factorial / r.den : ℕ) : ℤ) : ℤ) : ZMod p) := by
  have hden_pos : 0 < r.den := Rat.den_pos r
  have hden_le : r.den ≤ L₀ := hr.2
  have hden_dvd : r.den ∣ L₀.factorial := Nat.dvd_factorial hden_pos hden_le
  have hden_lt : r.den < p :=
    lt_of_le_of_lt (le_trans hden_le (Nat.self_le_factorial L₀)) hL₀
  have hden0 : (r.den : ZMod p) ≠ 0 := zmod_natCast_ne_zero_of_pos_of_lt hden_pos hden_lt
  have hqc : (L₀.factorial : ZMod p)
      = (r.den : ZMod p) * ((L₀.factorial / r.den : ℕ) : ZMod p) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hden_dvd]
  have hcast : ((r.num * ((L₀.factorial / r.den : ℕ) : ℤ) : ℤ) : ZMod p)
      = (r.num : ZMod p) * ((L₀.factorial / r.den : ℕ) : ZMod p) := by
    rw [Int.cast_mul, Int.cast_natCast]
  have key : (r.num : ZMod p) * (r.den : ZMod p)⁻¹
      * ((r.den : ZMod p) * ((L₀.factorial / r.den : ℕ) : ZMod p))
      = (r.num : ZMod p) * ((L₀.factorial / r.den : ℕ) : ZMod p) := by
    have hD : (r.den : ZMod p)⁻¹ * (r.den : ZMod p) = 1 := inv_mul_cancel₀ hden0
    calc (r.num : ZMod p) * (r.den : ZMod p)⁻¹
            * ((r.den : ZMod p) * ((L₀.factorial / r.den : ℕ) : ZMod p))
        = (r.num : ZMod p) * ((r.den : ZMod p)⁻¹ * (r.den : ZMod p))
            * ((L₀.factorial / r.den : ℕ) : ZMod p) := by ring
      _ = (r.num : ZMod p) * 1 * ((L₀.factorial / r.den : ℕ) : ZMod p) := by rw [hD]
      _ = (r.num : ZMod p) * ((L₀.factorial / r.den : ℕ) : ZMod p) := by ring
  rw [qmod, hqc, div_eq_mul_inv, hcast]
  exact key

/-- **Clearing denominators in the linear forms condition.** -/
theorem linFormsCond_of_int_coeff {p : ℕ} [Fact p.Prime] {ν : ZMod p → ℝ} {m₀ t₀ L₀ : ℕ}
    {ε : ℝ} (hL₀ : L₀.factorial < p)
    (h : ∀ (m : ℕ), 1 ≤ m → m ≤ m₀ →
        ∀ (t : ℕ), 1 ≤ t → t ≤ t₀ →
        ∀ (A : Fin m → Fin t → ℤ), (∀ i j, (A i j).natAbs ≤ L₀.factorial * L₀) →
          (∀ i, ∃ j, A i j ≠ 0) →
          (∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ)) →
          ∀ b : Fin m → ZMod p,
            |((Fintype.card (Fin t → ZMod p) : ℝ))⁻¹ *
              ∑ x : Fin t → ZMod p,
                ∏ i, ν ((∑ j, ((A i j : ℤ) : ZMod p) * x j) + b i) - 1| ≤ ε) :
    LinFormsCond p ν m₀ t₀ L₀ ε := by
  intro ι instι decι hcard1 hcardM t ht1 htt L hsmall hnonzero hnonprop b
  -- The cleared-denominator integer matrix.
  let A : ι → Fin t → ℤ := fun i j => (L i j).num * ((L₀.factorial / (L i j).den : ℕ) : ℤ)
  have hdivdvd : ∀ (i : ι) (j : Fin t), (L i j).den ∣ L₀.factorial :=
    fun i j => Nat.dvd_factorial (Rat.den_pos (L i j)) (hsmall i j).2
  have hclear : ∀ (i : ι) (j : Fin t), (A i j : ℚ) = (L₀.factorial : ℚ) * L i j := by
    intro i j
    exact rat_clear_mul (hdivdvd i j)
  have hq0Q : (L₀.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero L₀
  -- `A` still has no zero row.
  have hnonzeroA : ∀ i, ∃ j, A i j ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := hnonzero i
    refine ⟨j, ?_⟩
    intro hzero
    have hdivpos : 0 < L₀.factorial / (L i j).den :=
      Nat.div_pos (le_trans (hsmall i j).2 (Nat.self_le_factorial L₀)) (Rat.den_pos _)
    have hcZ : ((L₀.factorial / (L i j).den : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hdivpos)
    have hnum : (L i j).num = 0 := by
      rcases (mul_eq_zero.mp hzero) with h | h
      · exact h
      · exact absurd h hcZ
    exact hj (by rw [← Rat.num_div_den (L i j), hnum]; simp)
  -- `A` still has no proportional pair of rows.
  have hnonpropA : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ) := by
    intro i i' hne hprop
    apply hnonprop i i' hne
    obtain ⟨lam, hlam⟩ := hprop
    refine ⟨lam, ?_⟩
    intro j
    have hh := hlam j
    rw [hclear i' j, hclear i j] at hh
    have h2 : (L₀.factorial : ℚ) * L i' j = (L₀.factorial : ℚ) * (lam * L i j) := by
      rw [hh]; ring
    exact mul_left_cancel₀ hq0Q h2
  -- The size bound `|Aᵢⱼ| ≤ L₀! · L₀`.
  have hboundA : ∀ i j, (A i j).natAbs ≤ L₀.factorial * L₀ := by
    intro i j
    have h1 : (L i j).num.natAbs ≤ L₀ := (hsmall i j).1
    have h2 : L₀.factorial / (L i j).den ≤ L₀.factorial := Nat.div_le_self _ _
    have hnat : (A i j).natAbs = (L i j).num.natAbs * (L₀.factorial / (L i j).den) := by
      simp only [A, Int.natAbs_mul, Int.natAbs_natCast]
    rw [hnat]
    calc (L i j).num.natAbs * (L₀.factorial / (L i j).den)
        ≤ L₀ * L₀.factorial := Nat.mul_le_mul h1 h2
      _ = L₀.factorial * L₀ := Nat.mul_comm _ _
  -- The substitution `x ↦ q • x` (i.e. multiplication of every coordinate by `L₀ !`).
  have hq0 : (L₀.factorial : ZMod p) ≠ 0 :=
    zmod_natCast_ne_zero_of_pos_of_lt (Nat.factorial_pos L₀) hL₀
  let f : (Fin t → ZMod p) → (Fin t → ZMod p) := fun x j => (L₀.factorial : ZMod p) * x j
  let g : (Fin t → ZMod p) → (Fin t → ZMod p) := fun y j => (L₀.factorial : ZMod p)⁻¹ * y j
  have hleft : Function.LeftInverse g f := by
    intro x; funext j
    simp only [f, g]; rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
  have hright : Function.RightInverse g f := by
    intro y; funext j
    simp only [f, g]; rw [← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
  let eL : (Fin t → ZMod p) ≃ (Fin t → ZMod p) :=
    Equiv.ofBijective f ⟨hleft.injective, hright.surjective⟩
  -- The integer linear form agrees with the rational one after scaling.
  have hlin : ∀ (i : ι) (y : Fin t → ZMod p),
      linForm p (L i) (b i) (eL y) = (∑ j, ((A i j : ℤ) : ZMod p) * y j) + b i := by
    intro i y
    change linForm p (L i) (b i) (fun j => (L₀.factorial : ZMod p) * y j)
      = (∑ j, ((A i j : ℤ) : ZMod p) * y j) + b i
    rw [linForm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    show qmod p (L i j) * ((L₀.factorial : ZMod p) * y j)
      = ((A i j : ℤ) : ZMod p) * y j
    rw [← mul_assoc, qmod_mul_factorial hL₀ (hsmall i j)]
  -- Transfer `ι` to `Fin m`.
  let m := Fintype.card ι
  let e := Fintype.equivFin ι
  let A' : Fin m → Fin t → ℤ := fun i j => A (e.symm i) j
  let b' : Fin m → ZMod p := fun i => b (e.symm i)
  have hboundA' : ∀ (i : Fin m) (j : Fin t), (A' i j).natAbs ≤ L₀.factorial * L₀ :=
    fun i j => by simpa only [A'] using hboundA (e.symm i) j
  have hnonzeroA' : ∀ i : Fin m, ∃ j, A' i j ≠ 0 :=
    fun i => by simpa only [A'] using hnonzeroA (e.symm i)
  have hnonpropA' : ∀ i i' : Fin m, i ≠ i' →
      ¬ ∃ lam : ℚ, ∀ j, (A' i' j : ℚ) = lam * (A' i j : ℚ) := by
    intro i i' hne
    have hne' : e.symm i ≠ e.symm i' := fun h => hne (e.symm.injective h)
    simpa only [A'] using hnonpropA (e.symm i) (e.symm i') hne'
  have hmain := h m hcard1 hcardM t ht1 htt A' hboundA' hnonzeroA' hnonpropA' b'
  -- Reindex the product over `ι` as a product over `Fin m`.
  have hprod : ∀ y : Fin t → ZMod p,
      (∏ i : ι, ν (linForm p (L i) (b i) (eL y)))
      = (∏ i : Fin m, ν ((∑ j, ((A' i j : ℤ) : ZMod p) * y j) + b' i)) := by
    intro y
    rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hlin i y])]
    exact Fintype.prod_equiv e
      (fun i : ι => ν ((∑ j, ((A i j : ℤ) : ZMod p) * y j) + b i))
      (fun i : Fin m => ν ((∑ j, ((A' i j : ℤ) : ZMod p) * y j) + b' i))
      (fun i => by simp only [A', b', Equiv.symm_apply_apply])
  -- Reindex the sum over the substitution `eL`.
  have hsum : (∑ x : Fin t → ZMod p, ∏ i : ι, ν (linForm p (L i) (b i) x))
      = (∑ x : Fin t → ZMod p,
          ∏ i : Fin m, ν ((∑ j, ((A' i j : ℤ) : ZMod p) * x j) + b' i)) := by
    have step1 := Fintype.sum_equiv eL.symm
      (fun x : Fin t → ZMod p => ∏ i : ι, ν (linForm p (L i) (b i) x))
      (fun y : Fin t → ZMod p => ∏ i : ι, ν (linForm p (L i) (b i) (eL y)))
      (fun x => by simp)
    rw [step1]
    exact Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hprod y)
  rw [hsum]
  exact hmain

end Commons.NumberTheory.Sieve
