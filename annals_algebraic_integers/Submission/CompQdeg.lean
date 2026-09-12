import Submission.CompQNums
import Submission.Bclps

/-!
# Monicity and degree of the complementary polynomial

Helper for `Submission/CompQRoots.lean`.  If `T` is monic of degree `r ≥ 1`
and `Q0 = ∏_{j'<D}(T − C(c_{r,j'}))` then `Q0` is monic of degree `D·r`.
Adding the ε-perturbation (`auxPoly t` has degree `t ≤ d = (D−1)·r`) and the
constant `N` keeps `Q` monic of degree `D·r`.
-/

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.CompQdeg

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.Bclps
open Submission.DivLinear
open Submission.CompQNums

/-- the auxiliary-degree `d = (D−1)·r` (same as in `CompQRoots`). -/
def d (r : ℕ) : ℕ := (Bclps.Dconst - 1) * r

/-- Adding a polynomial of strictly smaller degree to a monic polynomial of
degree `m` preserves both monicity and the degree. -/
lemma monic_add_of_natDegree_lt {p q : Polynomial ℝ} {m : ℕ}
    (hp : p.Monic) (hpm : p.natDegree = m) (hq : q.natDegree < m) :
    (p + q).Monic ∧ (p + q).natDegree = m := by
  have hle : (p + q).natDegree ≤ m := by
    calc
      (p + q).natDegree ≤ max p.natDegree q.natDegree := Polynomial.natDegree_add_le p q
      _ = m := by
        rw [hpm]
        exact Nat.max_eq_left (le_of_lt hq)
  have hge : m ≤ (p + q).natDegree := by
    by_contra h
    have hlt : (p + q).natDegree < m := Nat.lt_of_not_ge h
    have hcoeff0 : (p + q).coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    have hcoeff1 : (p + q).coeff m = 1 := by
      rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_natDegree_lt hq]
      rw [← hpm]
      simpa using hp.coeff_natDegree
    rw [hcoeff1] at hcoeff0
    norm_num at hcoeff0
  constructor
  · rw [Monic, Polynomial.leadingCoeff]
    rw [le_antisymm hle hge]
    rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_natDegree_lt hq]
    rw [← hpm]
    simpa using hp.coeff_natDegree
  · exact le_antisymm hle hge

/-- Subtracting a constant from a monic polynomial of degree `r ≥ 1` leaves it
monic of degree `r`. -/
lemma sub_C_monic {p : Polynomial ℝ} {r : ℕ} (hr : 1 ≤ r) (hp : p.Monic)
    (hdeg : p.natDegree = r) (a : ℝ) : (p - C a).Monic ∧ (p - C a).natDegree = r := by
  have hdegsub : (p - C a).natDegree = r := by
    rw [Polynomial.natDegree_sub_C, hdeg]
  constructor
  · rw [Monic, Polynomial.leadingCoeff, hdegsub, Polynomial.coeff_sub]
    have hca : (C a).coeff r = 0 := by
      rw [Polynomial.coeff_C]
      by_cases hr0 : r = 0
      · subst hr0
        omega
      · simp [hr0]
    rw [hca, sub_zero, ← hdeg]
    exact hp.coeff_natDegree
  · exact hdegsub

/-- The ε-sum degree bound `d = (D−1)·r`: every term `C(ε_t)·auxPoly t`
(`t ≤ d`) has degree `≤ d`. -/
lemma term_natDegree_le (r t : ℕ) (eps : ℕ → ℝ) (ht : t ≤ d r) :
    (C (eps t) * Bclps.auxPoly t).natDegree ≤ d r := by
  calc
    (C (eps t) * Bclps.auxPoly t).natDegree ≤ (Bclps.auxPoly t).natDegree := by
      exact Polynomial.natDegree_C_mul_le (eps t) (Bclps.auxPoly t)
    _ = t := Bclps.auxPoly_natDegree t
    _ ≤ d r := ht

/-- for `1 ≤ t ≤ d` the auxiliary polynomial has degree `t`, and every term of
the ε-sum has degree `≤ d`. -/
theorem aux_sum_natDegree_le (r : ℕ) (eps : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc 1 (d r), Polynomial.C (eps t) * Bclps.auxPoly t).natDegree ≤ d r := by
  refine Polynomial.natDegree_sum_le_of_forall_le (Finset.Icc 1 (d r))
    (fun t => Polynomial.C (eps t) * Bclps.auxPoly t) ?_
  intro t ht
  exact term_natDegree_le r t eps (Finset.mem_Icc.mp ht).2

/-- **`Q0` and `Q` are monic of degree `D·r`.** -/
theorem monic_degree (r : ℕ) (hr : 1 ≤ r) {T Q0 Q1 Q : Polynomial ℝ}
    (eps : ℕ → ℝ) (N : ℝ)
    (hTmon : T.Monic) (hTdeg : T.natDegree = r)
    (hQ0 : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
    (hQ1 : Q1 = Q0 + (∑ t ∈ Finset.Icc 1 (d r), Polynomial.C (eps t) * Bclps.auxPoly t))
    (hQ : Q = Q1 + Polynomial.C N) :
    Q0.Monic ∧ Q0.natDegree = Bclps.Dconst * r ∧
    Q.Monic ∧ Q.natDegree = Bclps.Dconst * r := by
  have hD1 : 1 ≤ Bclps.Dconst := Bclps.Dconst_pos
  have hrpos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hr
  have hDrpos : 0 < Bclps.Dconst * r := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hD1) hrpos
  have hdlt : d r < Bclps.Dconst * r := by
    unfold d
    calc
      (Bclps.Dconst - 1) * r < ((Bclps.Dconst - 1) + 1) * r := by
        exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self (Bclps.Dconst - 1)) hrpos
      _ = Bclps.Dconst * r := by
        rw [Nat.sub_add_cancel hD1]
  have hfmon : ∀ j' ∈ Finset.range Bclps.Dconst,
      (T - Polynomial.C (factorCenter r j')).Monic := by
    intro j' hj'
    exact (sub_C_monic hr hTmon hTdeg (factorCenter r j')).1
  have hQ0prodM : (∏ j' ∈ Finset.range Bclps.Dconst,
      (T - Polynomial.C (factorCenter r j'))).Monic := by
    exact Polynomial.monic_prod_of_monic (Finset.range Bclps.Dconst)
      (fun j' => T - Polynomial.C (factorCenter r j')) hfmon
  have hQ0prodD : (∏ j' ∈ Finset.range Bclps.Dconst,
      (T - Polynomial.C (factorCenter r j'))).natDegree = Bclps.Dconst * r := by
    calc
      (∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j'))).natDegree
          = ∑ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')).natDegree := by
            exact Polynomial.natDegree_prod_of_monic (Finset.range Bclps.Dconst)
              (fun j' => T - Polynomial.C (factorCenter r j')) hfmon
      _ = ∑ j' ∈ Finset.range Bclps.Dconst, r := by
            refine Finset.sum_congr rfl ?_
            intro j' hj'
            exact (sub_C_monic hr hTmon hTdeg (factorCenter r j')).2
      _ = Bclps.Dconst * r := by
            simp
  have hQ0M : Q0.Monic := by
    rw [hQ0]
    exact hQ0prodM
  have hQ0D : Q0.natDegree = Bclps.Dconst * r := by
    rw [hQ0]
    exact hQ0prodD
  let pert : Polynomial ℝ :=
    ∑ t ∈ Finset.Icc 1 (d r), Polynomial.C (eps t) * Bclps.auxPoly t
  have hPlt : pert.natDegree < Bclps.Dconst * r := by
    change (∑ t ∈ Finset.Icc 1 (d r),
        Polynomial.C (eps t) * Bclps.auxPoly t).natDegree < Bclps.Dconst * r
    exact lt_of_le_of_lt (aux_sum_natDegree_le r eps) hdlt
  have hQ1add : (Q0 + pert).Monic ∧ (Q0 + pert).natDegree = Bclps.Dconst * r := by
    exact monic_add_of_natDegree_lt (p := Q0) (q := pert) (m := Bclps.Dconst * r)
      hQ0M hQ0D hPlt
  have hQ1M : Q1.Monic := by
    rw [hQ1]
    exact hQ1add.1
  have hQ1D : Q1.natDegree = Bclps.Dconst * r := by
    rw [hQ1]
    exact hQ1add.2
  have hCNlt : (C N).natDegree < Bclps.Dconst * r := by
    rw [Polynomial.natDegree_C]
    exact hDrpos
  have hQadd : (Q1 + C N).Monic ∧ (Q1 + C N).natDegree = Bclps.Dconst * r := by
    exact monic_add_of_natDegree_lt (p := Q1) (q := C N) (m := Bclps.Dconst * r)
      hQ1M hQ1D hCNlt
  have hQM : Q.Monic := by
    rw [hQ]
    exact hQadd.1
  have hQD : Q.natDegree = Bclps.Dconst * r := by
    rw [hQ]
    exact hQadd.2
  exact ⟨hQ0M, hQ0D, hQM, hQD⟩

end Submission.CompQdeg
