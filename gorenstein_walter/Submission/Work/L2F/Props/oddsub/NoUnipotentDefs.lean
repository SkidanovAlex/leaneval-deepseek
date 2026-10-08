import Mathlib
import Submission.Work.L2F.Props.OddSubDefs

/-!
# The commutant of a subgroup of `SL(2,F)` and the "no common eigenvector" condition

Vocabulary for `Work.L2F.Props.oddsub.no_unipotent_of_normal_abelian_irreducible`.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

variable {F : Type*} [Field F]

/-- The commutant of `A ≤ SL(2,F)` inside `M₂(F)`: matrices commuting with every element of `A`
(seen as a matrix). -/
def MatCent (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (M : Matrix (Fin 2) (Fin 2) F) : Prop :=
  ∀ a ∈ A, M * (a : Matrix (Fin 2) (Fin 2) F) = (a : Matrix (Fin 2) (Fin 2) F) * M

/-- `A ≤ SL(2,F)` has a common eigenvector in `F²`. -/
def HasCommonEigenvector (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) : Prop :=
  ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ a ∈ A, ∃ c : F,
    Matrix.mulVec ((a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) v = c • v

/-- A subspace of `F²` containing a nonzero vector `v` and different from the whole space is
spanned by `v`. -/
theorem eq_smul_of_mem_of_ne_top {W : Submodule F (Fin 2 → F)} {v : Fin 2 → F}
    (hv : v ∈ W) (hv0 : v ≠ 0) (hW : W ≠ ⊤) : ∀ w ∈ W, ∃ c : F, c • v = w := by
  have hlt : Module.finrank F ↥W < Module.finrank F (Fin 2 → F) := Submodule.finrank_lt hW
  rw [Module.finrank_fin_fun] at hlt
  haveI : Nontrivial ↥W :=
    ⟨⟨⟨v, hv⟩, 0, fun h => hv0 (by simpa using congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank F ↥W := Module.finrank_pos
  have h1 : Module.finrank F ↥W = 1 := by omega
  intro w hw
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one h1 (x := (⟨v, hv⟩ : ↥W))
    (by simpa using hv0) (⟨w, hw⟩ : ↥W)
  exact ⟨c, by simpa using congrArg Subtype.val hc⟩

end Work.L2F.Props.oddsub
