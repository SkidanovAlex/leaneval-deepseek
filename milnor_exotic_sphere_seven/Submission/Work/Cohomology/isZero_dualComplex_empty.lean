import Mathlib
import Submission.Work.Cohomology.DualComplex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dual cochain complex of the empty space

The empty space has no singular `n`-simplices (there is no continuous map from the nonempty
standard `n`-simplex into `∅`), so its module of `n`-chains — a coproduct indexed by an empty
type — is a zero object.  Consequently every component `Hom(C_n, R)` of the dual cochain complex
is a zero object as well, and a cochain complex all of whose components are zero objects is itself
a zero object.

This is the lemma `Work.Cohomology.isZero_dualComplex_empty`.
-/

set_option linter.style.haveILetI false

open CategoryTheory Limits Work.Cohomology
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The singular `n`-simplices of the empty space form an empty type: a singular simplex is a
continuous map from the (nonempty) standard `n`-simplex into the empty space, of which there are
none. -/
lemma isEmpty_singularSimplex_empty (X : TopCat) (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj (TopCat.of (∅ : Set X))).obj (Opposite.op ⦋n⦌)) := by
  refine ⟨fun x => ?_⟩
  have hx := (TopCat.toSSetObjEquiv (TopCat.of (∅ : Set X)) (Opposite.op ⦋n⦌)) x
  haveI : Nonempty (↑(stdSimplex ℝ (Fin ((Opposite.unop (Opposite.op ⦋n⦌)).len + 1)))) :=
    inferInstance
  exact (Set.notMem_empty _) (hx (Classical.arbitrary _)).2

/-- A coproduct over an empty index type is a zero object. -/
lemma isZero_coproduct_of_isEmpty {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] {β : Type*} [IsEmpty β] (f : β → C) [HasCoproduct f] :
    IsZero (∐ f) :=
  (coproductIsCoproduct f).isZero_pt
    ((Functor.isZero_iff (Discrete.functor f)).mpr (fun X => isEmptyElim X.as))

/-- The `n`-th dual module of a chain complex all of whose components are zero objects is a zero
object. -/
lemma isZero_dualObj_of_isZero (R : Type) [CommRing R] (C : ChainComplex (ModuleCat R) ℕ)
    (h : ∀ n, IsZero (C.X n)) (n : ℕ) : IsZero (dualObj R C n) := by
  haveI : Subsingleton (C.X n) := ModuleCat.subsingleton_of_isZero (h n)
  haveI : Subsingleton ((C.X n) →ₗ[R] R) :=
    ⟨fun f g => by ext x; rw [Subsingleton.elim x 0]; simp⟩
  exact ModuleCat.isZero_of_subsingleton (dualObj R C n)

/-- If every component of a chain complex is a zero object, then its dual cochain complex is a
zero object. -/
lemma isZero_dualComplex_of_isZero_X (R : Type) [CommRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (h : ∀ n, IsZero (C.X n)) :
    IsZero (dualComplex R C) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.id_f, HomologicalComplex.zero_f]
  exact (IsZero.iff_id_eq_zero (dualObj R C n)).mp (isZero_dualObj_of_isZero R C h n)

/-- The dual cochain complex of the singular chains of the empty space is a zero object. -/
theorem isZero_dualComplex_empty (X : TopCat) :
    IsZero (dualComplex ℤ (singularChains ℤ (TopCat.of (∅ : Set X)))) := by
  apply isZero_dualComplex_of_isZero_X
  intro n
  haveI : IsEmpty ((TopCat.toSSet.obj (TopCat.of (∅ : Set X))).obj (Opposite.op ⦋n⦌)) :=
    isEmpty_singularSimplex_empty X n
  exact isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj (TopCat.of (∅ : Set X))).obj (Opposite.op ⦋n⦌)) =>
      ModuleCat.of ℤ ℤ)

end

end Work.Cohomology
