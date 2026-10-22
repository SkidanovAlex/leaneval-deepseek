import Mathlib
import Submission.Work.ANALYTIC.CechPt.SolidChain
import Submission.Work.TOOLKIT.Main

/-!
# The comparison `ℤ[T_•] ⟶ ℤ■[T_•]` is a solid-equivalence

`Work.ANALYTIC.CechPt.cmpcpx` is the comparison, in cochain complexes concentrated in degrees
`≤ 0`, between the free Čech complex `R^p = ℤ[T_p]` of the Cantor cover and the solid Čech
complex `D^p = (ℤ[T_p] ⟹ 𝟙) ⟹ 𝟙`.  Its `q`-th component is the double-dual unit at `ℤ[T_{-q}]`,
conjugated by the isomorphisms identifying the extension-by-zero complex with the original
nonnegatively graded chain complex.

Since `cmpcpx` is a degreewise double-dual unit, it is a solid-equivalence as soon as every
double-dual unit `ℤ[T] ⟶ ℤ■[T]` is one; that is the hypothesis `h` below.  The conclusion is
obtained from the degreewise criterion `Work.TOOLKIT.solidEquiv_levelwise` for complexes
concentrated in degrees `≤ 0`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Submission.Blueprint

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

/-- In degree `-(p : ℤ)`, the comparison `cmpcpx` is the double-dual unit at `ℤ[T_p]`,
conjugated by the isomorphisms identifying the extension-by-zero cochain complex with the
original nonnegatively graded chain complex. -/
lemma cmpcpx_f_neg (p : ℕ) :
    cmpcpx.f (-(p : ℤ)) =
      (HomologicalComplex.extendXIso Rchain ComplexShape.embeddingDownNat
        (ComplexShape.embeddingDownNat_f p)).hom ≫
      doubleDualUnit (zf (cechTerm p)) ≫
      (HomologicalComplex.extendXIso Dchain ComplexShape.embeddingDownNat
        (ComplexShape.embeddingDownNat_f p)).inv := by
  have hcmp : cmpcpx = HomologicalComplex.extendMap cmpChain ComplexShape.embeddingDownNat :=
    ComplexShape.Embedding.extendFunctor_map ComplexShape.embeddingDownNat LightCondAb cmpChain
  rw [hcmp]
  exact HomologicalComplex.extendMap_f cmpChain ComplexShape.embeddingDownNat
    (ComplexShape.embeddingDownNat_f p)

/-- For `q > 0` both `Rcpx.X q` and `Dcpx.X q` vanish, so the `q`-th component of `cmpcpx` is
an isomorphism, hence (as a morphism of the derived category) a solid-equivalence. -/
lemma isZero_Rcpx_of_pos {q : ℤ} (hq : 0 < q) : IsZero (Rcpx.X q) :=
  HomologicalComplex.isZero_extend_X Rchain ComplexShape.embeddingDownNat q (fun _ hi => by
    simp only [ComplexShape.embeddingDownNat_f] at hi
    omega)

/-- For `q > 0` the `q`-th term of the solid Čech complex vanishes. -/
lemma isZero_Dcpx_of_pos {q : ℤ} (hq : 0 < q) : IsZero (Dcpx.X q) :=
  HomologicalComplex.isZero_extend_X Dchain ComplexShape.embeddingDownNat q (fun _ hi => by
    simp only [ComplexShape.embeddingDownNat_f] at hi
    omega)

/-- In positive degrees the comparison `cmpcpx` is a morphism between zero objects. -/
lemma isIso_cmpcpx_f_of_pos {q : ℤ} (hq : 0 < q) : IsIso (cmpcpx.f q) :=
  ⟨⟨0, (isZero_Rcpx_of_pos hq).eq_of_src _ _, (isZero_Dcpx_of_pos hq).eq_of_tgt _ _⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem solidEquiv_cmpcpx
    (h : ∀ T : LightProfinite.{0}, Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        (Work.ANALYTIC.CechPt.doubleDualUnit (Work.ANALYTIC.CechPt.zf T)))) :
    Submission.Blueprint.SolidEquiv
      (DerivedCategory.Q.map Work.ANALYTIC.CechPt.cmpcpx) := by
  refine Work.TOOLKIT.solidEquiv_levelwise Rcpx Dcpx cmpcpx
    (fun q hq => isZero_Rcpx_of_pos hq) (fun q hq => isZero_Dcpx_of_pos hq) ?_
  intro q
  by_cases hq : q ≤ 0
  · -- In nonpositive degrees, `q = -(p : ℤ)` and the component is the double-dual unit at
    -- `ℤ[T_p]`, conjugated by isomorphisms.
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = -(p : ℤ) :=
      ⟨(-q).natAbs, by have h := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ -q by omega); omega⟩
    rw [cmpcpx_f_neg p]
    -- split the `map` of the composite into the composite of the maps
    simp only [Functor.map_comp]
    refine (Work.TOOLKIT.Levelwise.solidEquiv_iso_conj
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        (HomologicalComplex.extendXIso Rchain ComplexShape.embeddingDownNat
          (ComplexShape.embeddingDownNat_f p)).hom)
      ((DerivedCategory.singleFunctor LightCondAb 0).map (doubleDualUnit (zf (cechTerm p))))
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        (HomologicalComplex.extendXIso Dchain ComplexShape.embeddingDownNat
          (ComplexShape.embeddingDownNat_f p)).inv)
      (by infer_instance) (by infer_instance)).mpr (h (cechTerm p))
  · -- In positive degrees both sides vanish.
    have hq' : 0 < q := not_le.mp hq
    haveI : IsIso (cmpcpx.f q) := isIso_cmpcpx_f_of_pos hq'
    exact Work.TOOLKIT.solidEquiv_of_iso _ inferInstance

end Work.ANALYTIC.CechPt
