import Mathlib
import Submission.Work.MotC2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open Polynomial WeierstrassCurve.Affine

variable {L : Type*} [Field L]

/-- The affine coordinate ring `L[X, Y]/(W_E)` is generated over `L` by the two coordinate
classes `coordX E` and `coordY E`.

Proof: `L[X, Y]/(W_E) = AdjoinRoot (polynomial E)` is generated over the polynomial ring `L[X]`
by the adjoined root `root (polynomial E) = coordY E` (`AdjoinRoot.adjoinRoot_eq_top`), and
`L[X]` is generated over `L` by `X`, whose image is `coordX E`.  The two statements are glued by
`Algebra.adjoin_eq_adjoin_union`. -/
private lemma adjoin_coordX_coordY (E : WeierstrassCurve L) :
    Algebra.adjoin L ({coordX E, coordY E} : Set (Coord E)) = ⊤ := by
  have hroot : Algebra.adjoin (L[X]) ({AdjoinRoot.root (polynomial E)} : Set (Coord E)) = ⊤ :=
    AdjoinRoot.adjoinRoot_eq_top
  have h := Algebra.adjoin_eq_adjoin_union (R := L) (A := L[X]) (B := Coord E)
      ({Polynomial.X} : Set L[X]) ({AdjoinRoot.root (polynomial E)} : Set (Coord E))
      Polynomial.adjoin_X
  rw [hroot, Subalgebra.restrictScalars_top] at h
  rw [h]
  congr 1
  ext z
  simp [Work.MotC2.coordX, Work.MotC2.coordY]
  tauto

/-- The image of `L[coordX E, coordY E]` under the structure map `L[X, Y]/(W_E) → L(E)` is
`L[genX E, genY E]`. -/
private lemma map_adjoin_coordX_coordY (E : WeierstrassCurve L) :
    (Algebra.adjoin L ({coordX E, coordY E} : Set (Coord E))).map
        (IsScalarTower.toAlgHom L (Coord E) (Func E))
      = Algebra.adjoin L ({genX E, genY E} : Set (Func E)) := by
  rw [AlgHom.map_adjoin]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨coordX E, Or.inl rfl, rfl⟩
    · exact ⟨coordY E, Or.inr rfl, rfl⟩

theorem affRing_eq_adjoin (L : Type*) [Field L] (E : WeierstrassCurve L) :
    Work.MotC2.affRing E = Algebra.adjoin L ({Work.MotC2.genX E, Work.MotC2.genY E} :
      Set (Work.MotC2.Func E)) := by
  have hgen := adjoin_coordX_coordY (L := L) E
  have hmap := map_adjoin_coordX_coordY (L := L) E
  rw [show Work.MotC2.affRing E =
      Algebra.adjoin L (Set.range (algebraMap (Coord E) (Func E))) from rfl]
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · -- `L[genX, genY]` contains the image of `L[X, Y]/(W_E)`
    rintro z ⟨a, rfl⟩
    rw [← hmap]
    exact Subalgebra.mem_map.mpr ⟨a, by rw [hgen]; trivial, rfl⟩
  · -- conversely `genX` and `genY` are in the image of the structure map
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Algebra.subset_adjoin ⟨coordX E, rfl⟩
    · exact Algebra.subset_adjoin ⟨coordY E, rfl⟩

end Work.MotC2
