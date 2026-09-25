import Mathlib
import Submission.Work.Tower.Defs

/-!
# Tower cutting: basic API for `generatorRank` and for Galois groups

This module contains the elementary group-theoretic facts about the minimal number of generators
`Work.Tower.generatorRank` that the tower-cutting argument (paper Proposition 3.8, Steps 2-3)
uses, together with the easy Galois-theoretic bookkeeping (Galois groups of a sup, of an image
under an `F`-embedding, and their effect on `generatorRank`).
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace TowerCut

variable {G H : Type*}

/-- A finite group is a quotient of the free group on `Fintype.card G` generators, so the set
defining `generatorRank` is nonempty. -/
theorem nonempty_generatorSet (G : Type*) [Group G] [Fintype G] :
    ({d : ℕ | ∃ ψ : FreeGroup (Fin d) →* G, Function.Surjective ψ} : Set ℕ).Nonempty := by
  refine ⟨Fintype.card G,
    FreeGroup.lift fun i : Fin (Fintype.card G) => (Fintype.equivFin G).symm i, ?_⟩
  intro g
  exact ⟨FreeGroup.of (Fintype.equivFin G g), by
    rw [FreeGroup.lift_apply_of, Equiv.symm_apply_apply]⟩

/-- `generatorRank` is the least number of generators: if `G` is a quotient of the free group on
`d` generators, then `generatorRank G ≤ d`. -/
theorem generatorRank_le {G : Type*} [Group G] {d : ℕ}
    (h : ∃ ψ : FreeGroup (Fin d) →* G, Function.Surjective ψ) : generatorRank G ≤ d :=
  Nat.sInf_le h

/-- `generatorRank` is monotone under surjective homomorphisms. -/
theorem generatorRank_le_of_surjective {G H : Type*} [Group G] [Fintype G]
    [Group H] [Fintype H] (φ : G →* H) (hφ : Function.Surjective φ) :
    generatorRank H ≤ generatorRank G := by
  obtain ⟨ψ, hψ⟩ := Nat.sInf_mem (nonempty_generatorSet G)
  exact generatorRank_le ⟨φ.comp ψ, hφ.comp hψ⟩

/-- `generatorRank` is invariant under group isomorphisms. -/
theorem generatorRank_eq_of_mulEquiv {G H : Type*} [Group G] [Fintype G]
    [Group H] [Fintype H] (e : G ≃* H) : generatorRank G = generatorRank H := by
  refine le_antisymm ?_ ?_
  · exact generatorRank_le_of_surjective (G := H) (H := G) (e.symm : H →* G) e.symm.surjective
  · exact generatorRank_le_of_surjective (G := G) (H := H) (e : G →* H) e.surjective

/-- The trivial group has `generatorRank` zero. -/
theorem generatorRank_eq_zero_of_subsingleton {G : Type*} [Group G] [Subsingleton G] :
    generatorRank G = 0 := by
  refine le_antisymm (generatorRank_le ⟨FreeGroup.lift fun i : Fin 0 => i.elim0, ?_⟩)
    (Nat.zero_le _)
  intro g
  exact ⟨1, Subsingleton.elim _ _⟩

/-- A group with positive `generatorRank` is nontrivial. -/
theorem nontrivial_of_generatorRank_pos {G : Type*} [Group G] (h : 0 < generatorRank G) :
    Nontrivial G := by
  by_contra hnt
  haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hnt
  rw [generatorRank_eq_zero_of_subsingleton] at h
  exact lt_irrefl _ h

/-- The compositum of a finite family of Galois extensions is Galois.  (Mathlib has the binary
case as an instance; this is the finite-family version.) -/
theorem isGalois_iSup {ι : Type*} [Finite ι] {F A : Type*} [Field F] [Field A] [Algebra F A]
    (M : ι → IntermediateField F A) [∀ i, IsGalois F (M i)] :
    IsGalois F ↥(⨆ i, M i) :=
  IsGalois.mk


end TowerCut
end Tower
end Work
