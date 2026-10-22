import Mathlib
import Submission.Work.RESOL.ZeroTruncSES

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL

/-- A small coproduct of zero objects is a zero object. -/
lemma isZero_sigma_of_forall {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type*}
    (f : ι → C) [HasCoproduct f] (h : ∀ i, IsZero (f i)) : IsZero (∐ f) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro i
  rw [Category.comp_id, comp_zero]
  exact (h i).eq_zero_of_src _

/-- The degree-`i` term of a zero cochain complex is a zero object. -/
lemma isZero_X_of_isZero_cochainComplex {C : Type*} [Category C] [HasZeroMorphisms C]
    {K : CochainComplex C ℤ} (h : IsZero K) (i : ℤ) : IsZero (K.X i) :=
  Functor.map_isZero (HomologicalComplex.eval C (ComplexShape.up ℤ) i) h

theorem zIsZeroCutX (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M : LightCondAb, CategoryTheory.Epi (π.app M)) (B : Work.RESOL.Cpx)
    (b j : ℤ) (hj : b + 1 ≤ j)
    (hB : ∀ q : ℤ, b < q → CategoryTheory.Limits.IsZero (B.X q)) :
    (∀ n : ℤ, CategoryTheory.Limits.IsZero ((Work.RESOL.Zero.totCut F π hπ j B).X n)) ∧
      (∀ n : ℤ, CategoryTheory.Limits.IsZero ((Work.RESOL.trunc j B).X n)) := by
  constructor
  · intro n
    refine isZero_sigma_of_forall _ (fun y => ?_)
    have hq : b < y.1.1 := by have h := y.2.2; omega
    exact isZero_X_of_isZero_cochainComplex
      (Functor.map_isZero (Zero.Rco F π hπ) (hB y.1.1 hq)) y.1.2
  · intro n
    by_cases hn : j ≤ n
    · rw [trunc_X_of_le B j hn]
      exact hB n (by omega)
    · rw [trunc_X_of_not_le B j hn]
      exact isZero_zero LightCondAb

end Work.RESOL
