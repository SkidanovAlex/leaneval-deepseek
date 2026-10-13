import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.exists_lift_of_quasiIso
import Submission.Work.DSEQ0.finFreeResolution_of_isRegularLocalRing
import Submission.Work.DSEQ0.exists_cech_cup
import Submission.Work.DSEQ0.exists_cechZ_cup_extension
import Submission.Work.DSEQ0.TensorCpx.exists_leibnizProduct_of_quasiIso
import Submission.Work.DSEQ0.FFR.boundedFinFreeComplex_of_pdLE
import Submission.Work.DSEQ0Norm.ChartFinite
import Submission.Work.DSEQ0.boundedModelU_of_resolutions
import Submission.Work.DSG4a.CechBaseChange

/-!
# `Work.DSEQ0.exists_unitalModel` — D1 of the EQ0 area

**D1** (see `Submission/Work/DSEQ0/NEXT_input4.md`): a *bounded* finite free model `F` of the
Čech complex `cechZ A X f U` of the given finite affine cover, carrying the coaugmentation `ε`,
a window `[lo,hi]`, a bilinear family `μ` satisfying the strict Leibniz rule, and a homotopy
making `μ 0 (j+1) (ε 1)` homotopic to the identity.

## The proof

* `exists_finFreeResolution_serre`: Serre's theorem `gl.dim A ≤ dim A` in the form consumed by
  the bounded model (the `FFR` files).
* `exists_boundedModelU_final`: the bounded finite free model `P` of `cechZ` with its
  coaugmentation `ε`, from bounded free resolutions of the cohomology modules.  Its inputs are
  the finiteness and vanishing of the Čech cohomology
  (`Work.DSEQ0.cechZ_homology_finite_of_isProjOver`) and the splicing
  `Work.DSEQ0.boundedModelU_of_resolutions`.
* the Leibniz product: the *homotopy transfer* of the Čech cup product along the
  quasi-isomorphism `φ : P ⟶ cechZ`.  The transferred family is
  `ψ i j x y := ψZ i j ((φ.f i) x) ((φ.f j) y)`, where `ψZ` is the `ℤ`-indexed extension of the
  cup product (`Work.DSEQ0.exists_cechZ_cup_extension`, built from
  `Work.DSEQ0.exists_cech_cup`); the engine is
  `Work.DSEQ0.TensorCpx.exists_leibnizProduct_of_quasiIso`, whose proof is the standard
  derived-category argument: `P ⊗ P` is K-projective (bounded above and free), the class of
  `φ⁻¹ ∘ ψ` is realized by an honest chain map `μ`, and `μ (e ⊗ −)` is homotopic to the identity
  because `ψ (e ⊗ −) = φ` (strict unitality of the cup product) and `Q(φ)` is invertible.

## Remaining inputs of the area (not proved here)

* `Work.DSEQ0.exists_cech_cup` (the Čech cup product with its Leibniz rule, its strict
  unitality and its associativity) — in flight in `Submission/Work/DSEQ0Cup/`.
* `Work.DSEQ0.cechZ_homology_finite_of_isProjOver` consumes two still-`sorry` bridge lemmas of
  `Submission/Work/DSEQ0/` (`subCech_chartCover_chartCech`,
  `cechZ_homology_equiv_of_affine_covers`) — equivalent statements are being delivered
  sorry-free by the sibling areas `Work.DSCOH` (`cechZ_homology_iso_chartCech`) and `DSF1`.
-/

namespace Work.DSEQ0

universe a

open CategoryTheory AlgebraicGeometry

/-! ## Serre's theorem, in the form consumed by the bounded model -/

/-- **Serre's theorem** (`gl.dim A ≤ dim A`): every finitely generated module `M` over a
Noetherian regular local ring `A`, in every degree `i`, has a *bounded* complex of finitely
generated free `A`-modules quasi-isomorphic to `M` concentrated in degree `i`.

This is the assembly of `Work.DSEQ0.hasProjectiveDimensionLT_of_isRegularLocalRing` (induction on
the embedding dimension) with `Work.DSEQ0.FFR.boundedFinFreeComplex_of_pdLE` (projective-dimension
bound ↦ bounded free resolution); the same one-line proof is left `sorry` in
`Submission/Work/DSEQ0/finFreeResolution_of_isRegularLocalRing.lean`, which is not ours to edit. -/
theorem exists_finFreeResolution_serre (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsNoetherianRing A] (i : ℤ) {M : Type a} [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    ∃ (G : CochainComplex (ModuleCat.{a} A) ℤ),
      (∀ j, Module.Finite A (G.X j)) ∧ (∀ j, Module.Free A (G.X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (G.X j)) ∧
      ∃ g : G ⟶ (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) i).obj
          (ModuleCat.of A M),
        QuasiIso g := by
  have hpd : CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of A M)
      (IsLocalRing.maximalIdeal A).spanFinrank :=
    Work.DSEQ0.hasProjectiveDimensionLT_of_isRegularLocalRing _ A rfl (ModuleCat.of A M)
      inferInstance
  exact Work.DSEQ0.FFR.boundedFinFreeComplex_of_pdLE A _ (ModuleCat.of A M) i hpd

/-! ## The bounded finite free model with its coaugmentation -/

/-- **Input (3) of area `EQ0`.**  For `A` a Noetherian regular local ring, `f : X ⟶ Spec A`
proper and projective, and a finite affine cover `U` of `X`, there is a *bounded* finite free
model `(P, ε)` of the Čech complex `cechZ A X f U` with the coaugmentation compatibility of
`DSMap.Mix2.IsFinFreeModelU`. -/
theorem exists_boundedModelU_final (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsNoetherianRing A]
    (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    [AlgebraicGeometry.IsProper f] (hp : DSMap.IsProjOver A f) {ι : Type a} [Finite ι]
    (U : ι → X.Opens)
    (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    ∃ (a b : ℤ) (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0),
      DSMap.Mix2.IsFinFreeModelU A X f U P ε ∧
        (∀ i : ℤ, i < a ∨ b < i → CategoryTheory.Limits.IsZero (P.X i)) := by
  obtain ⟨N, hN⟩ :=
    Work.DSEQ0Norm.cechZ_homology_finite_v2 (A := A) X f hp U hU hcov
  have hex : ∀ i : ℤ, ∃ (G : CochainComplex (ModuleCat.{a} A) ℤ),
      (∀ j, Module.Finite A (G.X j)) ∧ (∀ j, Module.Free A (G.X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (G.X j)) ∧
      ∃ g : G ⟶ (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) i).obj
        ((DSMap.cechZ A X f U).homology i), QuasiIso g := by
    intro i
    haveI : Module.Finite A ↥((DSMap.cechZ A X f U).homology i) := (hN i).1
    exact exists_finFreeResolution_serre (A := A) i
      (M := ↥((DSMap.cechZ A X f U).homology i))
  choose G hrest using hex
  exact Work.DSEQ0.boundedModelU_of_resolutions A X f U hU hcov N (fun i hi => (hN i).2 hi) G
    (fun i j => (hrest i).1 j) (fun i j => (hrest i).2.1 j) (fun i => (hrest i).2.2.1)
    (fun i => (hrest i).2.2.2)

theorem exists_unitalModel (A : Type a) [CommRing A] [IsRegularLocalRing A] [IsNoetherianRing A]
    (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    [AlgebraicGeometry.IsProper f] (hp : DSMap.IsProjOver A f) {ι : Type a} [Finite ι]
    (U : ι → X.Opens)
    (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    ∃ (F : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ F.X 0) (lo hi : ℤ)
      (μ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(F.X (i + j))),
      DSMap.Mix2.IsFinFreeModelU A X f U F ε ∧
      (∀ i : ℤ, i < lo ∨ hi < i → CategoryTheory.Limits.IsZero (F.X i)) ∧
      (∀ (i j : ℤ) (x : ↥(F.X i)) (y : ↥(F.X j)),
        (F.d (i + j) (i + j + 1)).hom ((μ i j x) y) =
          (F.XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
              (((μ (i + 1) j) ((F.d i (i + 1)).hom x)) y)
          + (-1 : A) ^ i.natAbs •
              ((F.XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
                ((μ i (j + 1) x) ((F.d j (j + 1)).hom y)))) ∧
      (∃ H : ∀ j : ℤ, ↥(F.X (j + 1)) →ₗ[A] ↥(F.X j),
        ∀ (j : ℤ) (y : ↥(F.X (j + 1))),
          (F.XIsoOfEq (by omega : 0 + (j + 1) = j + 1)).hom ((μ 0 (j + 1) (ε.hom 1)) y) - y =
            (F.d j (j + 1)).hom (H j y) + H (j + 1) ((F.d (j + 1) ((j + 1) + 1)).hom y)) := by
  obtain ⟨lo, hi, P, ε, hP, hbdd⟩ := exists_boundedModelU_final A X f hp U hU hcov
  obtain ⟨φ, hφ, hcompat⟩ := hP.2.2
  haveI hPfree : ∀ i : ℤ, Module.Free A (P.X i) := fun i => (hP.1.1 i).1
  haveI hPfin : ∀ i : ℤ, Module.Finite A (P.X i) := fun i => (hP.1.1 i).2
  -- the Čech cup product, extended to the `ℤ`-indexed Čech complex
  obtain ⟨cup, hleib, hunitC, hassoc⟩ := Work.DSEQ0.exists_cech_cup A X f U
  obtain ⟨ψZ, hψZ_leib, hψZ_unit, hψZ_link⟩ :=
    Work.DSEQ0.exists_cechZ_cup_extension (A := A) X f U cup hleib hunitC
  -- the coaugmentation of `cechZ` is the image of `ε 1` under `φ`
  have hφe : (φ.f 0) (ε.hom 1) = Work.DSG4a.coaugZElem A X f U := by
    set E := (DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl with hE
    have h1 : E.toLinearEquiv ((φ.f 0) (ε.hom 1)) = (DSMap.coaug0 A X f U).hom 1 := by
      change E.hom ((φ.f 0) (ε.hom 1)) = (DSMap.coaug0 A X f U).hom 1
      have h := congrArg (fun (g : ModuleCat.of A A ⟶ (DSMap.cech A X f U).X 0) => g 1) hcompat
      simp only [E, ModuleCat.hom_comp, ModuleCat.comp_apply, LinearMap.comp_apply] at h
      exact h
    have hcz : E.toLinearEquiv.symm ((DSMap.coaug0 A X f U).hom 1) =
        Work.DSG4a.coaugZElem A X f U := by
      change E.inv ((DSMap.coaug0 A X f U).hom 1) = Work.DSG4a.coaugZElem A X f U
      rw [Work.DSG4a.coaugZElem, Work.DSG4a.coaugZ]
      rfl
    have h2 : (φ.f 0) (ε.hom 1) = E.toLinearEquiv.symm ((DSMap.coaug0 A X f U).hom 1) := by
      have h3 : (φ.f 0) (ε.hom 1) =
          E.toLinearEquiv.symm (E.toLinearEquiv ((φ.f 0) (ε.hom 1))) :=
        (LinearEquiv.symm_apply_apply E.toLinearEquiv ((φ.f 0) (ε.hom 1))).symm
      rw [h1] at h3
      exact h3
    exact h2.trans hcz
  -- the transferred product
  obtain ⟨μ, H, hLeib, hunit⟩ :=
    Work.DSEQ0.TensorCpx.exists_leibnizProduct_of_quasiIso (A := A) P (DSMap.cechZ A X f U)
      ⟨hi, fun i hi' => hbdd i (Or.inr hi')⟩ φ hφ
      (fun i j => LinearMap.compl₁₂ (ψZ i j) (φ.f i).hom (φ.f j).hom)
      (by
        intro i j x y
        simp only [LinearMap.compl₁₂_apply]
        have h2 : ((DSMap.cechZ A X f U).d i (i + 1)).hom ((φ.f i) x) =
            (φ.f (i + 1)) ((P.d i (i + 1)).hom x) := by
          have hc := HomologicalComplex.Hom.comm φ i (i + 1)
          have hc' := congrArg (fun (g : P.X i ⟶ (DSMap.cechZ A X f U).X (i + 1)) => g x) hc
          simp only [ModuleCat.hom_comp, ModuleCat.comp_apply, LinearMap.comp_apply] at hc'
          exact hc'
        have h3 : ((DSMap.cechZ A X f U).d j (j + 1)).hom ((φ.f j) y) =
            (φ.f (j + 1)) ((P.d j (j + 1)).hom y) := by
          have hc := HomologicalComplex.Hom.comm φ j (j + 1)
          have hc' := congrArg (fun (g : P.X j ⟶ (DSMap.cechZ A X f U).X (j + 1)) => g y) hc
          simp only [ModuleCat.hom_comp, ModuleCat.comp_apply, LinearMap.comp_apply] at hc'
          exact hc'
        have h := hψZ_leib i j ((φ.f i) x) ((φ.f j) y)
        rw [h2] at h
        rw [h3] at h
        exact h)
      (ε.hom 1)
      (by
        intro k
        have h := congrArg (fun (g : ModuleCat.of A A ⟶ P.X k) => g 1) (hP.2.1 k)
        simp only [ModuleCat.hom_comp, ModuleCat.comp_apply, LinearMap.comp_apply,
          ModuleCat.hom_zero] at h
        exact h)
      (by
        intro j y
        simp only [LinearMap.compl₁₂_apply]
        rw [hφe]
        exact hψZ_unit j ((φ.f j) y))
  exact ⟨P, ε, lo, hi, μ, hP, hbdd, hLeib, H, hunit⟩

end Work.DSEQ0
