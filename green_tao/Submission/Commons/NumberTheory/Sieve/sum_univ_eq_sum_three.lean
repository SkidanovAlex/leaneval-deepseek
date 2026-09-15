import Mathlib
import Submission.Commons.NumberTheory.Sieve.locCount_ite_le

namespace Commons.NumberTheory.Sieve

open Finset
open scoped BigOperators

set_option linter.unusedVariables false

/-- Splitting a sum over `PrimeData m` according to `|σ.X ∪ σ.X'|` being `0`, `1` or at least `2`.

(`PrimeData m` is the structure with fields `X X' : Finset (Fin m)` and `0 = (∅,∅)`; note
`(σ.X ∪ σ.X').card = 0 ↔ σ = 0`.)

Proof sketch: the three finsets `{0}`, `{σ | (σ.X ∪ σ.X').card = 1}` and
`{σ | 2 ≤ (σ.X ∪ σ.X').card}` are pairwise disjoint and their union is `Finset.univ` (every natural
number is `0`, `1` or `≥ 2`); use `Finset.sum_union`, `Finset.sum_filter`, `Finset.ext`,
`Finset.mem_filter`, `Finset.mem_singleton`, and `Finset.card_eq_zero`/`Finset.union_eq_empty` for
the `= 0` case. -/
theorem sum_univ_eq_sum_three (m : ℕ) (F : PrimeData m → ℂ) :
    (∑ σ : PrimeData m, F σ)
      = F 0 + (∑ σ ∈ Finset.univ.filter (fun σ => (σ.X ∪ σ.X').card = 1), F σ)
        + (∑ σ ∈ Finset.univ.filter (fun σ => 2 ≤ (σ.X ∪ σ.X').card), F σ) := by
  classical
  -- `(σ.X ∪ σ.X').card = 0` exactly for the zero datum.
  have hcard0 : ∀ σ : PrimeData m, (σ.X ∪ σ.X').card = 0 ↔ σ = 0 := by
    intro σ
    rw [Finset.card_eq_zero, Finset.union_eq_empty]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨X, X'⟩ := σ
      change X = ∅ at h1
      change X' = ∅ at h2
      rw [h1, h2]
      rfl
    · rintro rfl
      exact ⟨rfl, rfl⟩
  set s1 : Finset (PrimeData m) :=
    Finset.univ.filter (fun σ => (σ.X ∪ σ.X').card = 1) with hs1
  set s2 : Finset (PrimeData m) :=
    Finset.univ.filter (fun σ => 2 ≤ (σ.X ∪ σ.X').card) with hs2
  have hmem1 : ∀ σ : PrimeData m, σ ∈ s1 ↔ (σ.X ∪ σ.X').card = 1 := by
    intro σ; rw [hs1]; simp
  have hmem2 : ∀ σ : PrimeData m, σ ∈ s2 ↔ 2 ≤ (σ.X ∪ σ.X').card := by
    intro σ; rw [hs2]; simp
  have hd2 : Disjoint ({0} : Finset (PrimeData m)) s1 := by
    rw [Finset.disjoint_left]
    intro σ h0 h1
    rw [Finset.mem_singleton] at h0
    have hc0 := (hcard0 σ).mpr h0
    have hc1 := (hmem1 σ).mp h1
    omega
  have hd1 : Disjoint (({0} : Finset (PrimeData m)) ∪ s1) s2 := by
    rw [Finset.disjoint_left]
    intro σ h0 h2
    rw [Finset.mem_union] at h0
    have hc2 := (hmem2 σ).mp h2
    rcases h0 with h0 | h0
    · rw [Finset.mem_singleton] at h0
      have hc0 := (hcard0 σ).mpr h0
      omega
    · have hc1 := (hmem1 σ).mp h0
      omega
  have hunion : ({0} : Finset (PrimeData m)) ∪ s1 ∪ s2 = Finset.univ := by
    ext σ
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_univ, iff_true]
    rw [← hcard0 σ, hmem1 σ, hmem2 σ]
    omega
  have key : Finset.univ.sum F
      = ({0} : Finset (PrimeData m)).sum F + s1.sum F + s2.sum F := by
    rw [← hunion, Finset.sum_union hd1, Finset.sum_union hd2]
  rw [key, Finset.sum_singleton]

end Commons.NumberTheory.Sieve
