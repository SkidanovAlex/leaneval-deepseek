/-
  WilC6 — Compact: shared definitions for the compactness step.

  This file sets up the theory used in the compactness argument of
  `Work.WilC6.Compact.exists_model_of_isEF` (step 3 of the design, see
  `Submission/Work/WilC6/DESIGN.md`).  The goal of that step is: given a tuple `b` in a model `N`
  of `TE` which realizes every `IsEF` consequence of `φ`, find a model `M` of `TE` with a tuple
  `a` such that `M ⊨ φ(a)` and such that the existential (`IsEF`) type of `a` is contained in the
  existential type of `b`.

  The idea is the usual compactness argument: the theory

    `TE ∪ {φ} ∪ {¬Ψ : IsEF Ψ, N ⊭ Ψ(b)}`

  over the language `LEc[[Fin n]]` (the free variables are named by constants) is satisfiable.  It
  is finitely satisfiable because a finite subset of the negated part is encoded by a single
  `IsEF` formula (the disjunction `Ψ'` of its members), and either `Ψ'` is an `IsEF` consequence of
  `φ` — in which case it is realized at `b`, contradicting the choice of the members — or it is
  not, in which case a counterexample model provides a model of the finite piece.

  The finite pieces are indexed by `Finset (EFIndex b)` here, so that the finite satisfiability
  statement (`cTheory_isSatisfiable`, proved in `Compact/cTheory_satisfiable.lean`) is the content
  of the file `Compact/cTheory_satisfiable.lean`, while the passage to the full theory via the
  compactness theorem is the content of `Compact/exists_model_of_isEF.lean`.
-/
import Mathlib
import Submission.Work.WilC6.Base

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC6.Compact

/-- The index type of the compactness argument: existential formulas of `Fin n` which are *not*
realized at the tuple `b`. -/
abbrev EFIndex {n : ℕ} {N : Type} [LEc.Structure N] (b : Fin n → N) : Type :=
  {Ψ : LEc.Formula (Fin n) // Work.WilC6.IsEF Ψ ∧ ¬ Ψ.Realize b}

/-- The `F`-th finite piece of the compactness theory: the transported theory `TE`, the sentence
`φ` (with the free variables named by constants) and the negations of the formulas of `F`. -/
def cTheory {n : ℕ} {N : Type} [LEc.Structure N] (φ : LEc.Formula (Fin n))
    (b : Fin n → N) (F : Finset (EFIndex b)) : (LEc[[Fin n]]).Theory :=
  (LEc.lhomWithConstants (Fin n)).onTheory TE ∪ {Formula.equivSentence φ} ∪
    {ψ | ∃ Ψ : EFIndex b, Ψ ∈ F ∧ ψ = (Formula.equivSentence Ψ.val).not}

variable {n : ℕ} {N : Type} [LEc.Structure N]

theorem onTheory_subset_cTheory (φ : LEc.Formula (Fin n)) (b : Fin n → N)
    (F : Finset (EFIndex b)) :
    (LEc.lhomWithConstants (Fin n)).onTheory TE ⊆ cTheory φ b F :=
  fun _ hψ => Or.inl (Or.inl hψ)

theorem equivSentence_mem_cTheory (φ : LEc.Formula (Fin n)) (b : Fin n → N)
    (F : Finset (EFIndex b)) : Formula.equivSentence φ ∈ cTheory φ b F :=
  Or.inl (Or.inr rfl)

theorem not_equivSentence_mem_cTheory {φ : LEc.Formula (Fin n)} {b : Fin n → N}
    {F : Finset (EFIndex b)} {Ψ : EFIndex b} (hΨ : Ψ ∈ F) :
    (Formula.equivSentence Ψ.val).not ∈ cTheory φ b F :=
  Or.inr ⟨Ψ, hΨ, rfl⟩

theorem cTheory_mono {φ : LEc.Formula (Fin n)} {b : Fin n → N} {F F' : Finset (EFIndex b)}
    (h : F ⊆ F') : cTheory φ b F ⊆ cTheory φ b F' := by
  intro ψ hψ
  rcases hψ with (hψ | hψ) | hψ
  · exact Or.inl (Or.inl hψ)
  · exact Or.inl (Or.inr hψ)
  · rcases hψ with ⟨Ψ, hΨF, rfl⟩
    exact Or.inr ⟨Ψ, h hΨF, rfl⟩

/-- The union over all finite pieces is the full compactness theory. -/
theorem cTheory_iUnion (φ : LEc.Formula (Fin n)) (b : Fin n → N) :
    (⋃ F : Finset (EFIndex b), cTheory φ b F) =
      (LEc.lhomWithConstants (Fin n)).onTheory TE ∪ {Formula.equivSentence φ} ∪
        {ψ | ∃ Ψ : EFIndex b, ψ = (Formula.equivSentence Ψ.val).not} := by
  ext ψ
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨F, (h1 | h2) | h3⟩
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h2)
    · obtain ⟨Ψ, -, rfl⟩ := h3
      exact Or.inr ⟨Ψ, rfl⟩
  · rintro ((h1 | h2) | h3)
    · exact ⟨∅, Or.inl (Or.inl h1)⟩
    · exact ⟨∅, Or.inl (Or.inr h2)⟩
    · obtain ⟨Ψ, rfl⟩ := h3
      exact ⟨{Ψ}, Or.inr ⟨Ψ, Finset.mem_singleton_self Ψ, rfl⟩⟩

end Work.WilC6.Compact
