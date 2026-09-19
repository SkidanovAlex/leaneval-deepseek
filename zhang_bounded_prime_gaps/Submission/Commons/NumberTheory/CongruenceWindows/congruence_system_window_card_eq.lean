import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Order.Interval.Finset.Nat
import Submission.Commons.NumberTheory.CongruenceWindows.card_window_modEq_bounds

namespace Commons.NumberTheory.CongruenceWindows

/-! # CRT: a congruence-window equals a single residue class modulo the product

For a finite system of pairwise-coprime congruences `n ≡ a i [MOD s i]`
(`i ∈ t`) with a solution produced by `Nat.chineseRemainderOfFinset`, the set of
solutions inside any window is exactly the set of numbers lying in the single
residue class of that solution modulo `t.prod s`.  Consequently the two counts
over the window `[N, 2N]` agree.
-/

open scoped BigOperators

/-- From congruences modulo each pairwise-coprime factor to a congruence modulo
the whole product (Chinese remainder theorem, uniqueness direction). -/
private lemma modEq_prod_of_forall {ι : Type*} (t : Finset ι) (s : ι → ℕ) (a b : ℕ)
    (hcop : (t : Set ι).Pairwise (fun i j => Nat.Coprime (s i) (s j)))
    (h : ∀ i ∈ t, a ≡ b [MOD s i]) : a ≡ b [MOD t.prod s] := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (Nat.modEq_one : a ≡ b [MOD 1])
  | insert x s' hx ih =>
      rw [Finset.prod_insert hx]
      have hcop_prod : Nat.Coprime (s x) (s'.prod s) := by
        rw [Nat.coprime_prod_right_iff]
        intro i hi
        exact hcop (by simp) (Finset.mem_insert_of_mem hi) (by
          intro hxi
          exact hx (by simpa [hxi] using hi))
      rw [← Nat.modEq_and_modEq_iff_modEq_mul (m := s x) (n := s'.prod s) (a := a) (b := b) hcop_prod]
      constructor
      · exact h x (Finset.mem_insert_self x s')
      · exact ih (Set.Pairwise.mono (by intro i hi; exact Finset.mem_insert_of_mem hi) hcop)
          (fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- In a pairwise-coprime system the solutions are exactly the numbers whose
residue modulo `t.prod s` equals the CRT solution's residue. -/
private lemma residue_window_eq_mod_prod {ι : Type*} (a s : ι → ℕ) (t : Finset ι)
    (hs : ∀ i ∈ t, s i ≠ 0)
    (hcop : (t : Set ι).Pairwise (fun i j => Nat.Coprime (s i) (s j))) :
    ∀ n : ℕ,
      (∀ i ∈ t, n ≡ a i [MOD s i]) ↔
        n % (t.prod s) =
          (Nat.chineseRemainderOfFinset a s t hs hcop).1 % (t.prod s) := by
  classical
  intro n
  constructor
  · intro h
    have hnc : n ≡ (Nat.chineseRemainderOfFinset a s t hs hcop).1 [MOD t.prod s] := by
      apply modEq_prod_of_forall (t := t) (s := s) (a := n) (b := (Nat.chineseRemainderOfFinset a s t hs hcop).1) hcop
      intro i hi
      exact (h i hi).trans ((Nat.chineseRemainderOfFinset a s t hs hcop).2 i hi).symm
    simpa [Nat.ModEq] using hnc
  · intro hmod i hi
    have hni : n ≡ (Nat.chineseRemainderOfFinset a s t hs hcop).1 [MOD s i] := by
      exact Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem s hi) (by simpa [Nat.ModEq] using hmod)
    exact hni.trans ((Nat.chineseRemainderOfFinset a s t hs hcop).2 i hi)

theorem congruence_system_window_card_eq {ι : Type*} (a s : ι → ℕ) (t : Finset ι)
    (N : ℕ) (hs : ∀ i ∈ t, s i ≠ 0)
    (hcop : (t : Set ι).Pairwise (fun i j => Nat.Coprime (s i) (s j))) :
    let c := Nat.chineseRemainderOfFinset a s t hs hcop
    ((Finset.Icc N (2 * N)).filter
      (fun n => ∀ i ∈ t, n ≡ a i [MOD s i])).card =
    ((Finset.Icc N (2 * N)).filter
      (fun n => n % (t.prod s) = c.1 % (t.prod s))).card := by
  classical
  have hmem : ∀ n : ℕ,
      (∀ i ∈ t, n ≡ a i [MOD s i]) ↔
        n % (t.prod s) = (Nat.chineseRemainderOfFinset a s t hs hcop).1 % (t.prod s) := by
    intro n
    exact residue_window_eq_mod_prod a s t hs hcop n
  have hfilter :
      (Finset.Icc N (2 * N)).filter (fun n => ∀ i ∈ t, n ≡ a i [MOD s i]) =
        (Finset.Icc N (2 * N)).filter
          (fun n => n % (t.prod s) = (Nat.chineseRemainderOfFinset a s t hs hcop).1 % (t.prod s)) := by
    exact Finset.filter_congr (fun n hn => hmem n)
  rw [hfilter]

end Commons.NumberTheory.CongruenceWindows