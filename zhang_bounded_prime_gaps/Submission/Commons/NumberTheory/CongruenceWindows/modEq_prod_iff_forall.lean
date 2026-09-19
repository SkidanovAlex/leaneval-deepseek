import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.ModEq
import Submission.Commons.NumberTheory.CongruenceWindows.exists_mem_Icc_mod_shift

namespace Commons.NumberTheory.CongruenceWindows

open scoped BigOperators

lemma modEq_of_modEq_prod {ι : Type*} (t : Finset ι) (s : ι → ℕ) {a b : ℕ} {i : ι}
    (hi : i ∈ t) (h : a ≡ b [MOD t.prod s]) : a ≡ b [MOD s i] :=
  Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem s hi) h

lemma modEq_prod_of_forall {ι : Type*} (t : Finset ι) (s : ι → ℕ) (a b : ℕ)
    (hcop : (t : Set ι).Pairwise (fun i j => Nat.Coprime (s i) (s j)))
    (h : ∀ i ∈ t, a ≡ b [MOD s i]) : a ≡ b [MOD t.prod s] := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (Nat.modEq_one : a ≡ b [MOD 1])
  | insert x s' hx ih =>
      have hcopmul : Nat.Coprime (s x) (s'.prod s) := by
        refine Nat.Coprime.prod_right ?_
        intro i hi
        exact hcop (by simp) (by exact Finset.mem_insert_of_mem hi) (by
          intro hxi
          exact hx (by simpa [hxi] using hi))
      have hcop' : (s' : Set ι).Pairwise (fun i j => Nat.Coprime (s i) (s j)) := by
        exact Set.Pairwise.mono (by
          intro i hi
          exact Finset.mem_insert_of_mem hi) hcop
      rw [Finset.prod_insert hx]
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hcopmul]
      exact ⟨h x (Finset.mem_insert_self x s'), ih hcop' (fun i hi => h i (Finset.mem_insert_of_mem hi))⟩

theorem modEq_prod_iff_forall {ι : Type*} (t : Finset ι) (s : ι → ℕ) (a b : ℕ)
    (hs : ∀ i ∈ t, s i ≠ 0)
    (hcop : (t : Set ι).Pairwise (fun i j => Nat.Coprime (s i) (s j))) :
    (a ≡ b [MOD t.prod s]) ↔ (∀ i ∈ t, a ≡ b [MOD s i]) := by
  constructor
  · intro h i hi
    exact modEq_of_modEq_prod t s hi h
  · exact modEq_prod_of_forall t s a b hcop

end Commons.NumberTheory.CongruenceWindows