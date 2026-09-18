import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Interval.Finset.Nat

open Finset
open scoped BigOperators
open scoped Nat

namespace Commons.NumberTheory.DuffinSchaeffer

private lemma orderEmbOfFin_add_two_le {s : Finset ℕ} (hs : ∀ x ∈ s, 2 ≤ x)
    (i : Fin s.card) :
    i.1 + 2 ≤ s.orderEmbOfFin rfl i := by
  classical
  let a := s.orderEmbOfFin rfl i
  let T := s.filter (fun x => x ≤ a)
  have hcardT : i.1 + 1 ≤ T.card := by
    let f : Fin (i.1 + 1) ↪ {x // x ∈ T} :=
    { toFun := fun j =>
        have hjle : j.1 ≤ i.1 := Nat.le_of_lt_succ j.isLt
        have hjs : j.1 < s.card := lt_of_le_of_lt hjle i.isLt
        ⟨s.orderEmbOfFin rfl ⟨j.1, hjs⟩, by
          change s.orderEmbOfFin rfl ⟨j.1, hjs⟩ ∈ s.filter (fun x => x ≤ a)
          rw [mem_filter]
          constructor
          · exact Finset.orderEmbOfFin_mem s rfl _
          · have hjle' : (⟨j.1, hjs⟩ : Fin s.card) ≤ i := by
              rw [Fin.mk_le_mk]
              exact hjle
            exact (s.orderEmbOfFin rfl).monotone hjle'⟩
      inj' := by
        intro j k h
        have hjle : j.1 ≤ i.1 := Nat.le_of_lt_succ j.isLt
        have hjs : j.1 < s.card := lt_of_le_of_lt hjle i.isLt
        have hkle : k.1 ≤ i.1 := Nat.le_of_lt_succ k.isLt
        have hks : k.1 < s.card := lt_of_le_of_lt hkle i.isLt
        have h' : s.orderEmbOfFin rfl ⟨j.1, hjs⟩ =
                   s.orderEmbOfFin rfl ⟨k.1, hks⟩ := by
          exact congrArg (fun z : {x // x ∈ T} => (z : ℕ)) h
        have hfin : (⟨j.1, hjs⟩ : Fin s.card) = ⟨k.1, hks⟩ :=
          (s.orderEmbOfFin rfl).injective h'
        exact Fin.ext (by simpa using (Fin.ext_iff.mp hfin)) }
    have hle := Fintype.card_le_of_embedding f
    simpa [Fintype.card_fin, Fintype.card_coe T] using hle
  by_contra hlt
  have hle_a : a ≤ i.1 + 1 := by omega
  have hsub : T ⊆ Icc 2 (i.1 + 1) := by
    intro x hx
    change x ∈ s.filter (fun y => y ≤ a) at hx
    rw [mem_filter] at hx
    exact Finset.mem_Icc.mpr ⟨hs x hx.1, le_trans hx.2 hle_a⟩
  have hcard_le : T.card ≤ (Icc 2 (i.1 + 1)).card := Finset.card_le_card hsub
  have hIcc : (Icc 2 (i.1 + 1)).card = i.1 := by
    rw [Nat.card_Icc]
    omega
  have : i.1 + 1 ≤ i.1 := by omega
  omega

private lemma factorial_succ_le_prod_of_two_le {s : Finset ℕ} (hs : ∀ x ∈ s, 2 ≤ x) :
    (s.card + 1)! ≤ ∏ x ∈ s, x := by
  classical
  have hle : (∏ i : Fin s.card, (i.1 + 2)) ≤ ∏ i : Fin s.card, s.orderEmbOfFin rfl i := by
    apply Finset.prod_le_prod'
    intro i hi
    exact orderEmbOfFin_add_two_le hs i
  have hleft : (∏ i : Fin s.card, (i.1 + 2)) = (s.card + 1)! := by
    rw [Fin.prod_univ_eq_prod_range (fun x => x + 2)]
    have hshift : (∏ x ∈ range s.card, (x + 2)) = ∏ x ∈ range (s.card + 1), (x + 1) := by
      rw [Finset.prod_range_succ' (fun x => x + 1) s.card]
      simp [add_assoc]
    rw [hshift]
    rw [Finset.prod_range_add_one_eq_factorial]
  have hright : (∏ i : Fin s.card, s.orderEmbOfFin rfl i) = ∏ x ∈ s, x := by
    have hcomp := Equiv.prod_comp (s.orderIsoOfFin rfl).toEquiv (fun x : s => (x : ℕ))
    have hsubtype : (∏ x : s, (x : ℕ)) = ∏ x ∈ s, x := by
      simpa using (Finset.prod_finset_coe (fun x : ℕ => x) s)
    rw [← hsubtype]
    rw [← hcomp]
    apply Finset.prod_congr rfl
    intro i hi
    rfl
  exact by simpa [hleft, hright] using hle

theorem factorial_succ_le_prod_primeFactors (n : ℕ) :
    (n.primeFactors.card + 1)! ≤ ∏ p ∈ n.primeFactors, p := by
  classical
  exact factorial_succ_le_prod_of_two_le (s := n.primeFactors) fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le

end Commons.NumberTheory.DuffinSchaeffer