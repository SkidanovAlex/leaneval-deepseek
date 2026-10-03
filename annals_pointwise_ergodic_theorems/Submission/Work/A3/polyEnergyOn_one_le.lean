import Mathlib
import Submission.Work.A3.polyEnergyOn

/-!
# The `s = 1` energy is linear in `|A|`

`polyEnergyOn Q 1 A` is the number of pairs `(x, y) ∈ A × A` with `Q x = Q y`.  For a *nonconstant*
polynomial `Q` — here `1 ≤ Q.natDegree` — each value `Q x` is taken at most `Q.natDegree` times
(`Y ↦ Q Y - Q x` is a nonzero polynomial of degree `Q.natDegree`, and `ℤ` is an integral domain), so
the energy is at most `Q.natDegree · |A|`.  This is the exact `s = 1` counterpart of the trivial
bound `polyEnergyOn_le_card_pow` (`E_s(A) ≤ |A|^{2s}`) of `Submission/Work/A3/polyEnergyOn.lean`.

The hypothesis `1 ≤ Q.natDegree` cannot be dropped: for constant `Q` the energy is `|A|²`.
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial

/-- For `s = 1` the energy of `Q` over `A` is the number of pairs `(x, y) ∈ A × A` with
`Q x = Q y`: an element of `Fintype.piFinset (fun _ : Fin 1 => A)` is determined by its single
entry (at `0`). -/
lemma polyEnergyOn_one_eq (Q : ℤ[X]) (A : Finset ℤ) :
    polyEnergyOn Q 1 A
      = ((A.product A).filter (fun p : ℤ × ℤ => Q.eval p.1 = Q.eval p.2)).card := by
  unfold polyEnergyOn
  refine Finset.card_bij (fun p _ => (p.1 0, p.2 0)) ?h1 ?h2 ?h3
  case h1 =>
    intro p hp
    obtain ⟨hpT, he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := mem_product_iff.mp hpT
    rw [Fintype.mem_piFinset] at hp1 hp2
    refine Finset.mem_filter.mpr ⟨mem_product_iff.mpr ⟨hp1 0, hp2 0⟩, ?_⟩
    simpa [Fin.sum_univ_one] using he
  case h2 =>
    intro p _ q _ hpq
    have h1 : p.1 0 = q.1 0 := congrArg Prod.fst hpq
    have h2 : p.2 0 = q.2 0 := congrArg Prod.snd hpq
    refine Prod.ext ?_ ?_
    · funext i
      rw [Subsingleton.elim i 0]
      exact h1
    · funext i
      rw [Subsingleton.elim i 0]
      exact h2
  case h3 =>
    intro q hq
    obtain ⟨hqT, he⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hq2⟩ := mem_product_iff.mp hqT
    refine ⟨(fun _ : Fin 1 => q.1, fun _ : Fin 1 => q.2), ?h, ?e⟩
    case h =>
      refine Finset.mem_filter.mpr ⟨mem_product_iff.mpr ⟨?_, ?_⟩, ?_⟩
      · rw [Fintype.mem_piFinset]; intro i; exact hq1
      · rw [Fintype.mem_piFinset]; intro i; exact hq2
      · simpa [Fin.sum_univ_one] using he
    case e => rfl

/-- **Each value of `Q` is taken at most `Q.natDegree` times on `A`** (for `Q` nonconstant):
the elements `y` with `Q y = Q x` are roots of the nonzero polynomial `Q - C (Q x)`, of degree
`Q.natDegree`. -/
lemma card_filter_eval_eq_le (Q : ℤ[X]) (hd : 1 ≤ Q.natDegree) (A : Finset ℤ) (x : ℤ) :
    (A.filter (fun y => Q.eval y = Q.eval x)).card ≤ Q.natDegree := by
  have hne : Q - Polynomial.C (Q.eval x) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h0 : Q.natDegree = 0 := by rw [h, Polynomial.natDegree_C]
    omega
  have hdeg : (Q - Polynomial.C (Q.eval x)).natDegree = Q.natDegree := by
    refine Polynomial.natDegree_sub_eq_left_of_natDegree_lt ?_
    rw [Polynomial.natDegree_C]
    omega
  have hsub : A.filter (fun y => Q.eval y = Q.eval x) ⊆
      (Q - Polynomial.C (Q.eval x)).roots.toFinset := by
    intro y hy
    obtain ⟨_, hyeq⟩ := Finset.mem_filter.mp hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def,
      Polynomial.eval_sub, Polynomial.eval_C, hyeq, sub_self]
  calc (A.filter (fun y => Q.eval y = Q.eval x)).card
      ≤ ((Q - Polynomial.C (Q.eval x)).roots.toFinset).card := Finset.card_le_card hsub
    _ ≤ ((Q - Polynomial.C (Q.eval x)).roots).card := Multiset.toFinset_card_le _
    _ ≤ (Q - Polynomial.C (Q.eval x)).natDegree := Polynomial.card_roots' _
    _ = Q.natDegree := hdeg

/-- **The `s = 1` energy bound.**  For a nonconstant polynomial `Q` of degree `d` and any finite
set `A ⊆ ℤ`, the number of pairs `(x, y) ∈ A × A` with `Q x = Q y` is at most `d · |A|`: grouping
the pairs by their first coordinate, every fibre has at most `d` elements
(`card_filter_eval_eq_le`). -/
theorem polyEnergyOn_one_le (Q : Polynomial ℤ) (hd : 1 ≤ Polynomial.natDegree Q) (A : Finset ℤ) :
    polyEnergyOn Q 1 A ≤ Polynomial.natDegree Q * A.card := by
  have hS := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (s := (A.product A).filter (fun p : ℤ × ℤ => Q.eval p.1 = Q.eval p.2)) (t := A)
    (fun p hp => (mem_product_iff.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).1).1)
  rw [polyEnergyOn_one_eq]
  calc ((A.product A).filter (fun p : ℤ × ℤ => Q.eval p.1 = Q.eval p.2)).card
      = ∑ b ∈ A, (((A.product A).filter (fun p : ℤ × ℤ => Q.eval p.1 = Q.eval p.2)).filter
          (fun p => p.1 = b)).card := hS
    _ ≤ ∑ _b ∈ A, Polynomial.natDegree Q := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        refine le_trans (Finset.card_le_card_of_injOn (f := fun p : ℤ × ℤ => p.2) ?_ ?_)
          (card_filter_eval_eq_le Q hd A b)
        · intro p hp
          rw [Finset.mem_coe] at hp
          obtain ⟨hpS, hp1⟩ := Finset.mem_filter.mp hp
          obtain ⟨hpA, he⟩ := Finset.mem_filter.mp hpS
          obtain ⟨_, h2⟩ := mem_product_iff.mp hpA
          exact Finset.mem_filter.mpr ⟨h2, by rw [← he, hp1]⟩
        · intro p hp q hq hpq
          rw [Finset.mem_coe] at hp hq
          obtain ⟨_, hp1⟩ := Finset.mem_filter.mp hp
          obtain ⟨_, hq1⟩ := Finset.mem_filter.mp hq
          exact Prod.ext (by rw [hp1, hq1]) hpq
    _ = Polynomial.natDegree Q * A.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

end Work.A3
