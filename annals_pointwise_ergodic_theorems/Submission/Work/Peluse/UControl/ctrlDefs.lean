import Mathlib
import Submission.Work.Peluse.UControl.petShiftDefs

/-!
# The coefficient-degree invariant of the phase-1 PET chain

`Work.Peluse.UControl.coeffBd d C Q` bounds the *evaluated* coefficients of a slot polynomial `Q`
on the box `|a_s| ≤ B` by `C · B^{d - j}`.  The proof of `phase1TerminalCoeffBd` tracks the
following, simpler, coefficient-wise invariant along the chain: **the `y^j`-coefficient of a slot
polynomial is a polynomial in the tower parameters of total degree at most `d - j`**.

The invariant is preserved by the PET step: the step replaces a slot polynomial `Q` by
`Q(y + a_new) - Q_{i₀}`, and `y + a_new` is `Ctrl 1`.  This file sets up `Ctrl` and its closure
properties (`Ctrl.mul`, `Ctrl.add`, `Ctrl.sub`, the compatibility of `Ctrl` with `y ↦ y + s`, and
with the coefficient-ring extension `histRen`).  The invariant itself at the terminal state is
proved in `phase1TerminalCoeffBd.lean`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

variable {n : ℕ}

/-- **The coefficient-degree bound.**  `Ctrl d p` says that for every `j` the `y^j`-coefficient of
`p` is a polynomial in the parameters whose total degree is at most `d - j`. -/
def Ctrl (d : ℕ) (p : Polynomial (MvPolynomial (Fin n) ℤ)) : Prop :=
  ∀ j : ℕ, (p.coeff j).totalDegree ≤ d - j

/-- The invariant along the history chain: every live slot polynomial satisfies `Ctrl d`. -/
def HistData.Ctrl {d n : ℕ} (X : HistData d n) : Prop :=
  ∀ x ∈ X.H, Work.Peluse.UControl.Ctrl d (X.Q x.1 x.2)

lemma Ctrl.zero {d : ℕ} : Ctrl d (0 : Polynomial (MvPolynomial (Fin n) ℤ)) := by
  intro j
  simp

lemma Ctrl.one : Ctrl 0 (1 : Polynomial (MvPolynomial (Fin n) ℤ)) := by
  intro j
  rw [Polynomial.coeff_one]
  split_ifs <;> simp

lemma Ctrl.add {dp dq : ℕ} {p q : Polynomial (MvPolynomial (Fin n) ℤ)}
    (hp : Ctrl dp p) (hq : Ctrl dq q) : Ctrl (max dp dq) (p + q) := by
  intro j
  rw [Polynomial.coeff_add]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · exact le_trans (hp j) (by omega)
  · exact le_trans (hq j) (by omega)

lemma Ctrl.sub {dp dq : ℕ} {p q : Polynomial (MvPolynomial (Fin n) ℤ)}
    (hp : Ctrl dp p) (hq : Ctrl dq q) : Ctrl (max dp dq) (p - q) := by
  intro j
  rw [Polynomial.coeff_sub]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · exact le_trans (hp j) (by omega)
  · exact le_trans (hq j) (by omega)

/-- Multiplication adds the degree bounds.  The `natDegree` hypotheses upgrade the truncated
subtraction `d - j` at the indices above the degree, where the coefficient vanishes. -/
lemma Ctrl.mul {dp dq : ℕ} {p q : Polynomial (MvPolynomial (Fin n) ℤ)}
    (hp : Ctrl dp p) (hq : Ctrl dq q) (hpd : p.natDegree ≤ dp) (hqd : q.natDegree ≤ dq) :
    Ctrl (dp + dq) (p * q) := by
  intro j
  rw [Polynomial.coeff_mul]
  refine MvPolynomial.totalDegree_finsetSum_le (fun x hx => ?_)
  have hxj : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  by_cases h1 : x.1 ≤ dp
  · by_cases h2 : x.2 ≤ dq
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h := add_le_add (hp x.1) (hq x.2)
      omega
    · have hz : q.coeff x.2 = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, mul_zero]
      exact Nat.zero_le _
  · have hz : p.coeff x.1 = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, zero_mul]
    exact Nat.zero_le _

/-- The same-bound forms of `Ctrl.add`/`Ctrl.sub` (the general versions carry `max`). -/
lemma Ctrl.add' {d : ℕ} {p q : Polynomial (MvPolynomial (Fin n) ℤ)}
    (hp : Ctrl d p) (hq : Ctrl d q) : Ctrl d (p + q) := by
  have h := Ctrl.add hp hq
  rwa [max_self] at h

lemma Ctrl.sub' {d : ℕ} {p q : Polynomial (MvPolynomial (Fin n) ℤ)}
    (hp : Ctrl d p) (hq : Ctrl d q) : Ctrl d (p - q) := by
  have h := Ctrl.sub hp hq
  rwa [max_self] at h

/-- A finite sum of `Ctrl d` polynomials is `Ctrl d`. -/
lemma Ctrl.sum {d : ℕ} {ι : Type*} (t : Finset ι)
    {f : ι → Polynomial (MvPolynomial (Fin n) ℤ)} (h : ∀ i ∈ t, Ctrl d (f i)) :
    Ctrl d (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (Ctrl.zero (n := n) (d := d))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : Ctrl d (f a) := h a (Finset.mem_insert_self a s)
    have h2 : Ctrl d (∑ x ∈ s, f x) := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h3 := Ctrl.add h1 h2
    rwa [max_self] at h3

/-- `Ctrl` is preserved by a coefficient-ring extension `Polynomial.map`. -/
lemma Ctrl.map_rename {d m : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℤ)} (hp : Ctrl d p)
    (f : Fin n → Fin m) :
    Ctrl d (p.map (MvPolynomial.rename f).toRingHom) := by
  intro j
  rw [Polynomial.coeff_map]
  exact le_trans (MvPolynomial.totalDegree_rename_le f _) (hp j)

/-- The shift `y ↦ y + s` is `Ctrl 1` whenever `s` has total degree at most `1`. -/
lemma Ctrl.X_add_C {s : MvPolynomial (Fin n) ℤ} (hs : s.totalDegree ≤ 1) :
    Ctrl 1 (Polynomial.X + Polynomial.C s) := by
  intro j
  have hcoeff : (Polynomial.X + Polynomial.C s : Polynomial (MvPolynomial (Fin n) ℤ)).coeff j
      = (if 1 = j then 1 else 0) + (if j = 0 then s else 0) := by
    rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
  rw [hcoeff]
  rcases j with _ | _ | j
  · simp only [if_neg (show ¬ ((1:ℕ) = 0) by omega), zero_add]
    simpa using hs
  · simp
  · have h1 : ¬ ((1:ℕ) = (j + 1 + 1)) := by omega
    have h2 : ¬ ((j + 1 + 1 : ℕ) = 0) := by omega
    rw [if_neg h1, if_neg h2, add_zero]
    simp

lemma X_add_C_natDegree (s : MvPolynomial (Fin n) ℤ) :
    (Polynomial.X + Polynomial.C s : Polynomial (MvPolynomial (Fin n) ℤ)).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_X_add_C]

lemma X_add_C_pow_natDegree (s : MvPolynomial (Fin n) ℤ) (k : ℕ) :
    ((Polynomial.X + Polynomial.C s : Polynomial (MvPolynomial (Fin n) ℤ)) ^ k).natDegree ≤ k := by
  calc _ ≤ k * (Polynomial.X + Polynomial.C s : Polynomial (MvPolynomial (Fin n) ℤ)).natDegree :=
        Polynomial.natDegree_pow_le
    _ = k := by rw [Polynomial.natDegree_X_add_C, mul_one]

lemma Ctrl.X_add_C_pow {s : MvPolynomial (Fin n) ℤ} (hs : s.totalDegree ≤ 1) (k : ℕ) :
    Ctrl k ((Polynomial.X + Polynomial.C s) ^ k) := by
  induction k with
  | zero => simpa using (Ctrl.one (n := n))
  | succ k ih =>
    rw [pow_succ]
    have h := Ctrl.mul ih (Ctrl.X_add_C hs) (X_add_C_pow_natDegree s k) (X_add_C_natDegree s)
    simpa using h

/-- Multiplying a `Ctrl e` polynomial by the constant coefficient `a` gives a `Ctrl d` polynomial as
soon as `a` has total degree at most `d - e`.  The `natDegree` hypothesis again handles the
truncation. -/
lemma Ctrl.C_mul_of {d e : ℕ} {a : MvPolynomial (Fin n) ℤ}
    {q : Polynomial (MvPolynomial (Fin n) ℤ)} (hed : e ≤ d) (ha : a.totalDegree ≤ d - e)
    (hq : Ctrl e q) (hqd : q.natDegree ≤ e) : Ctrl d (Polynomial.C a * q) := by
  intro j
  rw [Polynomial.coeff_C_mul]
  by_cases hj : j ≤ e
  · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h1 := hq j
    omega
  · have hz : q.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, mul_zero]
    exact Nat.zero_le _

/-- **The composite `p(y + s)` of a `Ctrl d` polynomial.**  Composing with `y + s` preserves the
invariant: `y + s` is `Ctrl 1`, and the coefficients of a product add their degree bounds. -/
lemma Ctrl.comp_X_add_C {d : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℤ)} (hp : Ctrl d p)
    (hdeg : p.natDegree ≤ d) {s : MvPolynomial (Fin n) ℤ} (hs : s.totalDegree ≤ 1) :
    Ctrl d (p.comp (Polynomial.X + Polynomial.C s)) := by
  have hexp : p.comp (Polynomial.X + Polynomial.C s)
      = p.sum (fun k a => Polynomial.C a * (Polynomial.X + Polynomial.C s) ^ k) := by
    conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
    rw [Polynomial.sum_def, Polynomial.sum_comp, Polynomial.sum_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Polynomial.C_mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
  rw [hexp, Polynomial.sum_def]
  refine Ctrl.sum _ (fun k hk => ?_)
  exact Ctrl.C_mul_of (le_trans (Polynomial.le_natDegree_of_mem_supp k hk) hdeg) (hp k)
    (Ctrl.X_add_C_pow hs k) (X_add_C_pow_natDegree s k)

end

end Work.Peluse.UControl
