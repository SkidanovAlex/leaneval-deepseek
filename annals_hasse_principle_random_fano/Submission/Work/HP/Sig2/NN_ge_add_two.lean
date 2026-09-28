import Mathlib
import Submission.Work.HP.Defs

/-!
# `N_{d,n} ≥ n + 2` for `2 ≤ d ≤ n`

The number `NN d n` of degree-`d` monomials in `n+1` variables is the cardinality of the subtype
`Mon d n` of degree-`d` exponent vectors.  For `2 ≤ d ≤ n` we exhibit an injection

`Option (Fin (n+1)) → Mon d n`,  `none ↦ x_0^{d-1} x_1`,  `some i ↦ x_i^d`,

of an `(n+2)`-element type into `Mon d n`.  The `n+2` monomials `x_i^d` (`i : Fin (n+1)`) and
`x_0^{d-1} x_1` are pairwise distinct: the exponent vector of `x_i^d` is `d` at position `i` and
`0` elsewhere, so the nonzero position recovers `i`, while the extra monomial has exponent `d - 1`
at position `0`, which is neither `0` nor `d`.
-/

namespace Work.HP.Sig2

open Finset

noncomputable section

/-- Build an element of `Mon d n` (a degree-`d` exponent vector in `n+1` variables) from a
natural-number-valued exponent function of total mass `d`. -/
private def mkMon' (d n : ℕ) (g : Fin (n + 1) → ℕ) (hg : ∀ i, g i ≤ d)
    (hsum : ∑ i, g i = d) : Mon d n :=
  ⟨fun i => ⟨g i, Nat.lt_succ_of_le (hg i)⟩, by simpa using hsum⟩

/-- The value of `mkMon'` at a position is the exponent function it was built from. -/
private lemma mkMon'_val (d n : ℕ) (g : Fin (n + 1) → ℕ) (hg : ∀ i, g i ≤ d)
    (hsum : ∑ i, g i = d) (j : Fin (n + 1)) :
    (((mkMon' d n g hg hsum).1 j : Fin (d + 1)) : ℕ) = g j := rfl

/-- Exponent function of the monomial `x_i^d`. -/
private def famP (d n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) → ℕ :=
  fun j => if j = i then d else 0

/-- Exponent function of the monomial `x_z^{d-1} x_o`. -/
private def famD (d n : ℕ) (z o : Fin (n + 1)) : Fin (n + 1) → ℕ :=
  fun j => (if j = z then d - 1 else 0) + (if j = o then 1 else 0)

private lemma sum_famP (d n : ℕ) (i : Fin (n + 1)) : ∑ j, famP d n i j = d := by
  simp only [famP]
  rw [Fintype.sum_ite_eq']

private lemma le_famP (d n : ℕ) (i j : Fin (n + 1)) : famP d n i j ≤ d := by
  simp only [famP]; split <;> omega

private lemma sum_famD (d n : ℕ) (hd : 1 ≤ d) (z o : Fin (n + 1)) (_h : z ≠ o) :
    ∑ j, famD d n z o j = d := by
  simp only [famD]
  rw [Finset.sum_add_distrib, Fintype.sum_ite_eq', Fintype.sum_ite_eq']
  omega

private lemma le_famD (d n : ℕ) (hd : 2 ≤ d) (z o : Fin (n + 1)) (j : Fin (n + 1)) :
    famD d n z o j ≤ d := by
  simp only [famD]
  split_ifs <;> omega

/-- The exponent of `x_z^{d-1} x_o` at the distinguished position `z` is `d - 1`. -/
private lemma famD_self (d n : ℕ) (z o : Fin (n + 1)) (h : z ≠ o) :
    famD d n z o z = d - 1 := by
  show ((if z = z then d - 1 else 0) + (if z = o then 1 else 0) : ℕ) = d - 1
  rw [ite_eq_left rfl, ite_eq_right h, add_zero]

/-- The injection `Option (Fin (n+1)) → Mon d n`, `none ↦ x_z^{d-1} x_o`, `some i ↦ x_i^d`. -/
private def wit (d n : ℕ) (hd : 2 ≤ d) (z o : Fin (n + 1)) (hzo : z ≠ o) :
    Option (Fin (n + 1)) → Mon d n
  | none => mkMon' d n (famD d n z o) (le_famD d n hd z o) (sum_famD d n (by omega) z o hzo)
  | some i => mkMon' d n (famP d n i) (le_famP d n i) (sum_famP d n i)

private lemma wit_none (d n : ℕ) (hd : 2 ≤ d) (z o : Fin (n + 1)) (hzo : z ≠ o) :
    wit d n hd z o hzo none
      = mkMon' d n (famD d n z o) (le_famD d n hd z o) (sum_famD d n (by omega) z o hzo) :=
  rfl

private lemma wit_some (d n : ℕ) (hd : 2 ≤ d) (z o : Fin (n + 1)) (hzo : z ≠ o)
    (i : Fin (n + 1)) :
    wit d n hd z o hzo (some i) = mkMon' d n (famP d n i) (le_famP d n i) (sum_famP d n i) :=
  rfl

/-- For `2 ≤ d ≤ n`, the number `N_{d,n}` of degree-`d` monomials in `n+1` variables is at
least `n+2` (witnessed by `x_0^d`, `x_0^{d-1}x_1, …, x_0^{d-1}x_n` and `x_1^d`). -/
theorem NN_ge_add_two (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) : n + 2 ≤ NN d n := by
  let z : Fin (n + 1) := ⟨0, by omega⟩
  let o : Fin (n + 1) := ⟨1, by omega⟩
  have hzo : z ≠ o := by
    intro h
    have := congrArg Fin.val h
    simp [z, o] at this
  have hinj : Function.Injective (wit d n hd z o hzo) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some i =>
        exfalso
        have hv := congrArg (fun m : Mon d n => ((m.1 z : Fin (d + 1)) : ℕ)) hab
        simp only [wit_none, wit_some, mkMon'_val] at hv
        rw [famD_self d n z o hzo] at hv
        simp only [famP] at hv
        by_cases h : z = i
        · rw [ite_eq_left h] at hv; omega
        · rw [ite_eq_right h] at hv; omega
    | some i =>
      cases b with
      | none =>
        exfalso
        have hv := congrArg (fun m : Mon d n => ((m.1 z : Fin (d + 1)) : ℕ)) hab
        simp only [wit_none, wit_some, mkMon'_val] at hv
        rw [famD_self d n z o hzo] at hv
        simp only [famP] at hv
        by_cases h : z = i
        · rw [ite_eq_left h] at hv; omega
        · rw [ite_eq_right h] at hv; omega
      | some i' =>
        congr 1
        have hv := congrArg (fun m : Mon d n => ((m.1 i : Fin (d + 1)) : ℕ)) hab
        simp only [wit_some, mkMon'_val] at hv
        simp only [famP] at hv
        by_cases h : i = i'
        · exact h
        · rw [ite_eq_left trivial, ite_eq_right h] at hv; omega
  have hcard : Fintype.card (Option (Fin (n + 1))) = n + 2 := by
    simp [Fintype.card_option]
  rw [← hcard]
  exact Fintype.card_le_of_injective _ hinj

end

end Work.HP.Sig2
