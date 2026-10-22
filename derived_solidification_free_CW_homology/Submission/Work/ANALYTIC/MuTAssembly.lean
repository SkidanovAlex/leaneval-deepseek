import Submission.Work.ANALYTIC.HaarDefs
import Submission.Work.ANALYTIC.SolidDual
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.solidEquiv_biprod
import Submission.Work.ATOM.Main
import Submission.Work.ATOM.zfree_iso_pt_biprod_zred
import Submission.Work.ATOM.projective_P

/-!
# AN3 assembly (`exists_muT`) from the pieces

This file records the *assembly* of `Work.ANALYTIC.exists_muT` from the pieces isolated in
`Submission/Work/ANALYTIC/MuT_Route.lean`, as a lemma taking those pieces as hypotheses.  This
separates the (pure category theory) assembly, verified here, from the analytic/algebraic pieces
(proved in their own modules).

The pieces are
* `hbasis` — `haar_basisIso`: `LC T ≅ (JIdx →₀ ℤ)` with `λ ↦ (phiJ j λ)_j` (the Haar/Schauder basis);
* `hdual` — `solidDual_iso_biprod` (built from `hbasis`, `ihom_coprod_iso`, the fact that the
  `LocallyConstant` functor is a left adjoint, and `MonoidalClosed.unitIsoSelf`):
  `solidDual T ≅ Z ⊞ ∏ℤ`;
* `hk` — `exists_kTilde`: a map `ℤ̃[T] ⟶ ∏ℤ` which is a solid-equivalence (obtained from ATOM's
  reduced null sequence `gRed` and AN1 + AN2 by two-out-of-three);
* `Work.ATOM.zfree_iso_pt_biprod_zred` — the splitting `ℤ[T] ≅ ℤ[pt] ⊞ ℤ̃[T]`;
* `Work.ATOM.unitIso` — `ℤ[pt] ≅ Z`;
* `solidEquiv_biprod` — closure of solid-equivalences under biproducts.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

attribute [local instance] Classical.propDecidable

/-- **The assembly of AN3 for infinite `T`**, from the three pieces. -/
theorem exists_muT_of_pieces (T : LightProfinite.{0}) [Infinite T]
    (hTK : Submission.Blueprint.ToolkitProp)
    (hbasis : ∃ e : CategoryTheory.Iso (ModuleCat.of ℤ (Haar.LC T))
        (ModuleCat.of ℤ (Haar.JIdx →₀ ℤ)),
      (∀ (lam : Haar.LC T) (j : Haar.JIdx), e.hom.hom lam j = Haar.phiJ T j lam) ∧
      (∀ j : Haar.JIdx, e.inv.hom (Finsupp.single j 1) = Haar.fJ T j))
    (hdual : Nonempty (solidDual T ≅ CategoryTheory.Limits.biprod Z prodZ))
    (hk : ∃ k : Work.ATOM.zred T (Work.ATOM.levelData T).s₀ ⟶ prodZ,
      Submission.Blueprint.SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map k)) :
    ∃ mu : (LightCondensed.free (R := ℤ)).obj T.toCondensed ⟶ solidDual T,
      Submission.Blueprint.SolidEquiv
        ((DerivedCategory.singleFunctor LightCondAb 0).map mu) := by
  obtain ⟨θ⟩ := hdual
  obtain ⟨k, hk⟩ := hk
  obtain ⟨η⟩ := Work.ATOM.zfree_iso_pt_biprod_zred T (Work.ATOM.levelData T).s₀
  let κ : Work.ATOM.zfree Work.ATOM.pt ⟶ Z := Work.ATOM.unitIso.inv
  let kb : (Work.ATOM.zfree Work.ATOM.pt ⊞ Work.ATOM.zred T (Work.ATOM.levelData T).s₀) ⟶
      (Z ⊞ prodZ) := CategoryTheory.Limits.biprod.map κ k
  have hκ : IsIso κ := Work.ATOM.unitIso.isIso_inv
  have h₁ : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map η.hom) :=
    hTK.of_iso _ ((DerivedCategory.singleFunctor LightCondAb 0).mapIso η).isIso_hom
  have h₂ : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map kb) := by
    have h := solidEquiv_biprod hTK _ _ _ _ κ k
      (hTK.of_iso _ ((DerivedCategory.singleFunctor LightCondAb 0).mapIso
        Work.ATOM.unitIso).isIso_inv) hk
    simpa only [kb, κ] using h
  have h₃ : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map θ.inv) :=
    hTK.of_iso _ ((DerivedCategory.singleFunctor LightCondAb 0).mapIso θ).isIso_inv
  have h₄ := hTK.comp ((DerivedCategory.singleFunctor LightCondAb 0).map η.hom)
    ((DerivedCategory.singleFunctor LightCondAb 0).map kb) h₁ h₂
  have h₅ := hTK.comp (((DerivedCategory.singleFunctor LightCondAb 0).map η.hom) ≫
    ((DerivedCategory.singleFunctor LightCondAb 0).map kb))
    ((DerivedCategory.singleFunctor LightCondAb 0).map θ.inv) h₄ h₃
  have heq : (DerivedCategory.singleFunctor LightCondAb 0).map (η.hom ≫ kb ≫ θ.inv) =
      (((DerivedCategory.singleFunctor LightCondAb 0).map η.hom) ≫
        ((DerivedCategory.singleFunctor LightCondAb 0).map kb)) ≫
        ((DerivedCategory.singleFunctor LightCondAb 0).map θ.inv) := by
    simp only [Functor.map_comp, Category.assoc]
  refine ⟨η.hom ≫ kb ≫ θ.inv, ?_⟩
  rw [heq]
  exact h₅

/-- **The finite case**: there is an isomorphism `ℤ[T] ≅ ℤ■[T]`, hence a (trivial) solid
equivalence. -/
theorem exists_muT_finite (T : LightProfinite.{0}) [Finite T]
    (hTK : Submission.Blueprint.ToolkitProp)
    (h : Nonempty ((LightCondensed.free (R := ℤ)).obj T.toCondensed ≅ solidDual T)) :
    ∃ mu : (LightCondensed.free (R := ℤ)).obj T.toCondensed ⟶ solidDual T,
      Submission.Blueprint.SolidEquiv
        ((DerivedCategory.singleFunctor LightCondAb 0).map mu) := by
  obtain ⟨e⟩ := h
  exact ⟨e.hom, hTK.of_iso ((DerivedCategory.singleFunctor LightCondAb 0).map e.hom)
    ((DerivedCategory.singleFunctor LightCondAb 0).mapIso e).isIso_hom⟩

/-- **AN3, existence form**, assembled from the pieces (the final target `exists_muT` is this
statement with the pieces replaced by the proved lemmas of the modules listed at the top). -/
theorem exists_muT_of_pieces_all (T : LightProfinite.{0})
    (hTK : Submission.Blueprint.ToolkitProp)
    (hbasis : ∀ (_ : Infinite T), ∃ e : CategoryTheory.Iso (ModuleCat.of ℤ (Haar.LC T))
        (ModuleCat.of ℤ (Haar.JIdx →₀ ℤ)),
      (∀ (lam : Haar.LC T) (j : Haar.JIdx), e.hom.hom lam j = Haar.phiJ T j lam) ∧
      (∀ j : Haar.JIdx, e.inv.hom (Finsupp.single j 1) = Haar.fJ T j))
    (hdual : ∀ (_ : Infinite T), Nonempty (solidDual T ≅ CategoryTheory.Limits.biprod Z prodZ))
    (hk : ∀ (_ : Infinite T), ∃ k : Work.ATOM.zred T (Work.ATOM.levelData T).s₀ ⟶ prodZ,
      Submission.Blueprint.SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map k))
    (hfin : ∀ (_ : Finite T),
      Nonempty ((LightCondensed.free (R := ℤ)).obj T.toCondensed ≅ solidDual T)) :
    ∃ mu : (LightCondensed.free (R := ℤ)).obj T.toCondensed ⟶ solidDual T,
      Submission.Blueprint.SolidEquiv
        ((DerivedCategory.singleFunctor LightCondAb 0).map mu) := by
  by_cases hT : Finite T
  · haveI : Finite T := hT
    exact exists_muT_finite T hTK (hfin hT)
  · have hInf : Infinite T := not_finite_iff_infinite.mp hT
    haveI : Infinite T := hInf
    exact exists_muT_of_pieces T hTK (hbasis hInf) (hdual hInf) (hk hInf)

end Work.ANALYTIC
