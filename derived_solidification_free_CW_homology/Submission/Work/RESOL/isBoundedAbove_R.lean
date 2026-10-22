import Mathlib
import Submission.Work.RESOL.Bicomplex
import Submission.Work.RESOL.isZero_X_of_isZero

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open HomologicalComplex

noncomputable section

namespace Work.RESOL

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

attribute [local instance] Classical.propDecidable

/-! ## Two generalities about zero objects -/

/-- The terms of a zero homological complex are zero objects: an object of
`HomologicalComplex V c` is zero as soon as its identity morphism is zero, and the components of
the identity of a complex are the identities of its terms. -/
lemma isZero_X_of_isZero_complex {V : Type*} [Category* V] [HasZeroMorphisms V]
    {ι : Type*} {c : ComplexShape ι} {C : HomologicalComplex V c} (hC : IsZero C) (i : ι) :
    IsZero (C.X i) := by
  rw [IsZero.iff_id_eq_zero] at hC ⊢
  have := HomologicalComplex.congr_hom hC i
  simpa using this

/-- In a category with zero morphisms, a "graded sum" `X.mapObj p j` of zero objects (i.e. a
coproduct of the `X i` with `p i = j`, as in `GradedObject.mapObj`) is a zero object.  It
suffices to test the identity against all the coproduct inclusions, and those are zero because
they start at zero objects. -/
lemma isZero_mapObj {I J : Type*} {C : Type*} [Category* C] [HasZeroMorphisms C]
    (X : GradedObject I C) (p : I → J) [X.HasMap p] (j : J)
    (h : ∀ i : p ⁻¹' {j}, IsZero (X i)) : IsZero (X.mapObj p j) := by
  rw [IsZero.iff_id_eq_zero]
  apply GradedObject.mapObj_ext (X := X) (p := p) (j := j) (f := 𝟙 (X.mapObj p j)) (g := 0)
  intro i hij
  rw [Category.comp_id, Limits.comp_zero]
  exact (h ⟨i, hij⟩).eq_of_src _ _

/-- The total complex `R.obj B` of the resolution bicomplex of a bounded-above complex is bounded
above: for `B.X p` a zero object the resolution `X.obj (B.X p)` is the zero complex, so all the
columns in large degrees vanish. -/
theorem isBoundedAbove_R {B : Work.RESOL.Cpx} (hB : Work.RESOL.IsBoundedAbove B) :
    Work.RESOL.IsBoundedAbove (Work.RESOL.R.obj B) := by
  obtain ⟨N, hN⟩ := hB
  refine ⟨N, fun n hn => ?_⟩
  -- the degree `n` term of the total complex is the coproduct of the `(R.X p).X q` with
  -- `p - q = n` (here `q : ℕ`, so `p ≥ n > N` and the corresponding column vanishes)
  rw [show (R.obj B).X n = (bicomplexObj B).toGradedObject.mapObj
      (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ)) n from rfl]
  apply isZero_mapObj
  rintro ⟨⟨p, q⟩, hp⟩
  have hpq : p - (q : ℤ) = n := hp
  have hp' : N < p := by omega
  exact isZero_X_of_isZero_complex (isZero_X_of_isZero (hN p hp')) q

end Work.RESOL
