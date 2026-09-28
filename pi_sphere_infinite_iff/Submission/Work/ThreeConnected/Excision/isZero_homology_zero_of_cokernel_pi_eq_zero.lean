import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.epi_homologyMap_of_cycles

/-!
# `H₀` of a cokernel of chain complexes vanishes when the projection kills `H₀`

Let `f : C ⟶ D` be a morphism of chain complexes of `ℤ`-modules (indexed by `ℕ`) and let
`π : D ⟶ coker f` be the projection to the cokernel of `f` in the category of chain complexes.
For a chain complex indexed by `ℕ` with differentials of degree `-1`, homology in degree `0` is
right exact: `H₀(coker f)` is the cokernel of `H₀(f)`, i.e. the image of
`H₀(π) : H₀(D) ⟶ H₀(coker f)` (exactness of the long exact sequence
`H₀(C) ⟶ H₀(D) ⟶ H₀(coker f) ⟶ H₋₁(C) = 0`).

Hence **if `H₀(π) = 0` then `H₀(coker f) = 0`**: `H₀(π)` is an epimorphism (it is surjective since
`π` is degreewise surjective, the components of a cokernel of chain complexes being computed
degreewise), and an epimorphism that is zero has zero target: `e ≫ 𝟙 = e ≫ 0` gives `𝟙 = 0` by
cancellation, and `IsZero.iff_id_eq_zero`.

The epimorphy is `Work.Cohomology.epi_homologyMap_of_cycles`: it suffices to lift every `0`-cycle
of the cokernel, up to a boundary, to a cycle of `D`; in degree `0` every element of `D.X 0` is a
cycle (`d 0 0 = 0`), and `(π).f 0` is surjective because for an epimorphism `φ` of homological
complexes each component `φ.f n` is an epimorphism (Mathlib instance, since the evaluation functor
preserves colimits).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.ThreeConnected.Excision

/-- An epimorphism which is the zero morphism has zero target. -/
lemma isZero_of_epi_of_eq_zero {C : Type*} [Category* C] [HasZeroMorphisms C] {X Y : C}
    (e : X ⟶ Y) [he : Epi e] (h : e = 0) : IsZero Y := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi e]
  rw [Category.comp_id, comp_zero, h]

/-- The `0`-th component of the projection to the cokernel of a chain map is surjective: the
components of a cokernel are computed degreewise. -/
lemma surjective_cokernel_pi_f_zero {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) :
    Function.Surjective ⇑(ConcreteCategory.hom ((cokernel.π f).f 0)) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- `H₀` of the cokernel projection of a chain map is an epimorphism: every `0`-cycle of
`coker f` -- that is, every element of `(coker f).X 0` -- lifts to an element of `D.X 0`, which in
degree `0` is automatically a cycle, and the boundary correction may be taken to be `0`. -/
lemma epi_homologyMap_cokernel_pi_zero {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) :
    Epi (HomologicalComplex.homologyMap (cokernel.π f) 0) := by
  refine Work.Cohomology.epi_homologyMap_of_cycles (cokernel.π f) 0 (fun z _hz => ?_)
  obtain ⟨c, hc⟩ := surjective_cokernel_pi_f_zero f z
  exact ⟨c, 0, by simp, by rw [hc]; simp⟩

theorem isZero_homology_zero_of_cokernel_pi_eq_zero {C D : ChainComplex (ModuleCat ℤ) ℕ}
    (f : C ⟶ D) (h : HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π f) 0 = 0) :
    CategoryTheory.Limits.IsZero ((CategoryTheory.Limits.cokernel f).homology 0) :=
  isZero_of_epi_of_eq_zero (e := HomologicalComplex.homologyMap (cokernel.π f) 0)
    (he := epi_homologyMap_cokernel_pi_zero f) (h := h)

end Work.ThreeConnected.Excision
