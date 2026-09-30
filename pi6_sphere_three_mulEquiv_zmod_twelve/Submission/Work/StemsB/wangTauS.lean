import Mathlib
import Submission.Work.StemsB.wangCollarDerivDefs
import Submission.Work.StemsB.wangTrivExc_delta
import Submission.Work.StemsB.wangTriv_isIso
import Submission.Work.StemsB.wangExc_isIso
import Submission.Work.StemsB.collarLambdaOatIso
import Submission.Work.StemsB.wangGammaExplicit

/-!
# The target isomorphism `τS` of the Wang transgression

This file builds the isomorphism

`τS_n : H^{n+b+1}(E, E|_O) ≅ H^{n+1}(F)`

of the Wang sequence as the composite of the four transport isomorphisms of the derivation
argument: excision, the trivialisation over the inner cube, the degree transport to the collar
degree, the inverse of the Thom isomorphism of the collar, and the clutching identification `ρ`.
It then computes its value on `δ (γ⁻¹ a)`:

`τS_n (δ (γ⁻¹ a)) = θ_n (a)`,  `θ = ρ ∘ Σ ∘ λ_G^*`,
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.StemsB

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- The degree transport `(n + b) + 1 ↦ (n + 1) + b` of the relative cohomology of the collar
pair, as an isomorphism of `ModuleCat ℤ`. -/
noncomputable def wangRelEqIso (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b)) (n : ℕ) :
    (Work.Cohomology.relComplex ℤ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
      (wangCQ b p d_G)).homology (n + b + 1) ≅
    (Work.Cohomology.relComplex ℤ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
      (wangCQ b p d_G)).homology ((n + 1) + b) :=
  (collarRelEq b (wangFY b p d_G) n).toModuleIso

/-- The Thom isomorphism of the collar pair, as an isomorphism of `ModuleCat ℤ`. -/
noncomputable def collarPhiIso (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ) (m : ℕ) :
    Work.Thom.Coh ℤ m Y ≅
      Work.Thom.RelCoh ℤ (m + b) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
  (LinearEquiv.ofBijective (collarPhi (Y := Y) b τ m) (hτ m)).toModuleIso

@[simp] theorem collarPhiIso_hom (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ) (m : ℕ) :
    (collarPhiIso b hb Y τ hτ m).hom = ModuleCat.ofHom (collarPhi (Y := Y) b τ m) := rfl

/-- Excision, as an isomorphism. -/
noncomputable def wangExcIso (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (k : ℕ) :
    (Work.Cohomology.relComplex ℤ (TopCat.of E) (wangA b p)).homology k ≅
      (Work.Cohomology.relComplex ℤ (wangEG b p) (wangA1 b p)).homology k := by
  haveI := wangExc_isIso b hb E p k
  exact asIso (wangExc b p k)

/-- The trivialisation comparison, as an isomorphism. -/
noncomputable def wangTrivIso (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (k : ℕ) :
    (Work.Cohomology.relComplex ℤ (wangEG b p) (wangA1 b p)).homology k ≅
      (Work.Cohomology.relComplex ℤ
        (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (wangCQ b p d_G)).homology k := by
  haveI := wangTriv_isIso b hb E p d_G hT_G k
  exact asIso (wangTriv b p d_G hT_G k)

/-- The clutching identification `ρ = λ_O-pt^*`, as an isomorphism. -/
noncomputable def rhoIso (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    Work.Thom.Coh ℤ k (wangFY b p d_G) ≅
      Work.Cohomology.singularCohomology ℤ k (wangCohFsp b p) := by
  haveI := collarLambdaOat_isIso b hb p d_G hT_G hT_O k
  exact asIso (rhoCoh b hb p d_G hT_G hT_O k)

/-- **The target transport `τS` of the Wang transgression**: excision, the trivialisation, the
degree transport, the inverse Thom isomorphism of the collar and the clutching identification. -/
noncomputable def wangTauS (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    (Work.Cohomology.relComplex ℤ (TopCat.of E) (wangA b p)).homology (n + b + 1) ≅
      Work.Cohomology.singularCohomology ℤ (n + 1) (wangCohFsp b p) :=
  wangExcIso b (by omega) E p (n + b + 1) ≪≫
    wangTrivIso b (by omega) E p d_G hT_G (n + b + 1) ≪≫
    wangRelEqIso b p d_G n ≪≫
    (collarPhiIso b (by omega) (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
      (wangSusT_thom b hb (wangFY b p d_G)) (n + 1)).symm ≪≫
    rhoIso b (by omega) E p d_G hT_G hT_O (n + 1)

/-- **The computation rule of `τS`**: applying `τS_n` to a class factors through the five maps of
which it is composed. -/
theorem wangTauS_hom_apply (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ)
    (z : (Work.Cohomology.relComplex ℤ (TopCat.of E) (wangA b p)).homology (n + b + 1)) :
    (wangTauS b hb E p hT_O d_G hT_G n).hom z =
      (rhoCoh b (by omega) p d_G hT_G hT_O (n + 1)).hom
        ((collarPhiIso b (by omega) (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
            (wangSusT_thom b hb (wangFY b p d_G)) (n + 1)).inv
          ((wangRelEqIso b p d_G n).hom
            ((wangTriv b p d_G hT_G (n + b + 1)).hom
              ((wangExc b p (n + b + 1)).hom z)))) := by
  simp only [wangTauS, wangExcIso, wangTrivIso, rhoIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, ModuleCat.hom_comp]
  rfl

/-- **The value of `τS`**: on the image of the connecting homomorphism of the source
identification, `τS` is the geometric transgression `θ = ρ ∘ Σ ∘ λ_G^*`. -/
theorem wangTauS_value (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ)
    (a : Work.Cohomology.singularCohomology ℤ (n + b) (wangCohFsp b p)) :
    (wangCohShiftθ (TopCat.of E) (wangA b p) (wangCohFsp b p) b
      (wangGammaExplicit b p hT_O) (wangTauS b hb E p hT_O d_G hT_G) n).hom a
      = wangTheta b hb p d_G hT_G hT_O n a := by
  have hb1 : 1 ≤ b := by omega
  change (wangTauS b hb E p hT_O d_G hT_G n).hom
      ((Work.Cohomology.pairδ ℤ (TopCat.of E) (wangA b p) (n + b)).hom
        ((wangGammaExplicit b p hT_O (n + b)).inv a)) = wangTheta b hb p d_G hT_G hT_O n a
  rw [wangGammaExplicit_inv]
  rw [wangTauS_hom_apply]
  rw [wangTrivExc_delta b hb E p d_G hT_G hT_O n a]
  have htrans_gen : ∀ x : (Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of ↥(sphLoopCollarProd b (wangFY b p d_G)))).homology (n + b),
      (collarRelEq b (wangFY b p d_G) n) ((collarDelta b (wangFY b p d_G) n) x)
        = (collarPhiIso b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
            (wangSusT_thom b hb (wangFY b p d_G)) (n + 1)).hom
          (collarSigma b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
            (wangSusT_thom b hb (wangFY b p d_G)) n x) := by
    intro x
    show (collarRelEq b (wangFY b p d_G) n) ((collarDelta b (wangFY b p d_G) n) x)
      = collarPhi b (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) (n + 1)
          (collarSigma b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
            (wangSusT_thom b hb (wangFY b p d_G)) n x)
    rw [collarSigma_spec b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
      (wangSusT_thom b hb (wangFY b p d_G)) n x]
  rw [show (wangRelEqIso b p d_G n).hom
        ((collarDelta b (wangFY b p d_G) n) ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom a))
      = (collarRelEq b (wangFY b p d_G) n)
          ((collarDelta b (wangFY b p d_G) n) ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom a))
      from rfl]
  rw [htrans_gen ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom a)]
  have hiso : (collarPhiIso b (by omega) (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
        (wangSusT_thom b hb (wangFY b p d_G)) (n + 1))
      = (collarPhiIso b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
        (wangSusT_thom b hb (wangFY b p d_G)) (n + 1)) := rfl
  rw [hiso, Iso.hom_inv_id_apply]
  rw [wangTheta_apply]

end

end Work.StemsB
