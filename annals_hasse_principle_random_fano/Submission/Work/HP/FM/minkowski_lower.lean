import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.numaux.lam_le_iff
import Submission.Work.HP.Q44Child.snoc_linIndep
import Submission.Work.HP.numaux.detL_span_le_prod
import Submission.Work.HP.detgam_detL_le_of_le

/-!
# The lower bound of Minkowski's second theorem

For an integral lattice `L ⊆ ℤ^ι` with successive minima `lam L 1, …, lam L (rk L)` for the
Euclidean unit ball,

`detL L ≤ ∏ i ∈ Finset.range (rk L), lam L (i + 1)`.

This is the easy half of Minkowski's second theorem, and the proof below is the classical one.
Choose `ℤ`-linearly independent lattice vectors `f 0, …, f (n-1)` (`n = rk L`) with
`‖f j‖ ≤ λ_{j+1}`: since every successive minimum is attained (`Work.HP.numaux.lam_attained`)
one appends one vector at a time (`Work.HP.Q44Child.snoc_linIndep`).  Then
`P := ℤf 0 + ⋯ + ℤf (n-1)` is a rank-`n` sublattice of `L`, so `detL L ≤ detL P`
(`Work.HP.detgam_detL_le_of_le`), and Hadamard's inequality
(`Work.HP.numaux.detL_span_le_prod`) bounds `detL P ≤ ∏ j, ‖f j‖ ≤ ∏ j, λ_{j+1}`.

Note that the classical proof via a Minkowski-reduced basis is not needed: the span of the
greedy family already has the same rank as `L` and its covolume dominates `detL L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.FM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- There are `rk L` `ℤ`-linearly independent vectors of `L` whose `j`-th one has norm at most
the `(j+1)`-st successive minimum: greedily append to a family of `k` vectors a vector of norm
at most `lam L (k+1)` that keeps the family independent (the successive minima are attained, and
among `k+1` independent vectors one leaves the `k`-dimensional span of the family). -/
theorem exists_indep_le_lam (L : Submodule ℤ (ι → ℤ)) :
    ∃ f : Fin (rk L) → (ι → ℤ), (∀ j, f j ∈ L) ∧ LinearIndependent ℤ f ∧
      ∀ j, eNorm (f j) ≤ lam L (j.1 + 1) := by
  have key : ∀ m : ℕ, m ≤ rk L → ∃ f : Fin m → (ι → ℤ), (∀ j, f j ∈ L) ∧
      LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ lam L (j.1 + 1) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨fun i => i.elim0, fun i => i.elim0, linearIndependent_empty_type,
        fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨f, hfL, hfI, hfb⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨g, hgL, hgI, hgb⟩ := Work.HP.numaux.lam_attained L (j := k + 1) hk
      obtain ⟨t, ht⟩ := Work.HP.Q44Child.snoc_linIndep hfI hgI
      refine ⟨Fin.snoc f (g t), ?_, ht, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨m, rfl⟩ | rfl
        · simpa using hfL m
        · simpa using hgL t
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨m, rfl⟩ | rfl
        · simpa using hfb m
        · simpa using hgb t
  exact key (rk L) le_rfl

theorem minkowski_lower {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) :
    detL L ≤ ∏ i ∈ Finset.range (rk L), lam L (i + 1) := by
  obtain ⟨f, hfL, hfI, hfb⟩ := exists_indep_le_lam L
  -- The `ℤ`-span of the family: a sublattice of `L` of the same rank.
  have hPL : Submodule.span ℤ (Set.range f) ≤ L :=
    Submodule.span_le.mpr (by rintro x ⟨j, rfl⟩; exact hfL j)
  have hrk : rk (Submodule.span ℤ (Set.range f)) = rk L := by
    rw [rk, Module.finrank_eq_card_basis (Module.Basis.span hfI)]
    simp
  -- `detL` is antitone for inclusions of equal rank.
  have h1 : detL L ≤ detL (Submodule.span ℤ (Set.range f)) :=
    detgam_detL_le_of_le hPL hrk
  -- Hadamard's inequality for the covolume of the span of an independent family.
  have h2 : detL (Submodule.span ℤ (Set.range f)) ≤ ∏ j : Fin (rk L), eNorm (f j) :=
    Work.HP.numaux.detL_span_le_prod hfI
  have h3 : (∏ j : Fin (rk L), eNorm (f j)) ≤ ∏ j : Fin (rk L), lam L (j.1 + 1) :=
    Finset.prod_le_prod₀ (fun _ _ => eNorm_nonneg _) fun j _ => hfb j
  have h4 : (∏ j : Fin (rk L), lam L (j.1 + 1)) = ∏ i ∈ Finset.range (rk L), lam L (i + 1) :=
    (Finset.prod_range (fun i => lam L (i + 1))).symm
  calc detL L ≤ detL (Submodule.span ℤ (Set.range f)) := h1
    _ ≤ ∏ j : Fin (rk L), eNorm (f j) := h2
    _ ≤ ∏ j : Fin (rk L), lam L (j.1 + 1) := h3
    _ = ∏ i ∈ Finset.range (rk L), lam L (i + 1) := h4

end Work.HP.FM
