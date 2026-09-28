import Mathlib
import Submission.Work.StemsB.Rat.CollarSigmaLow
import Submission.Work.StemsB.Rat.WangTauS
import Submission.Work.StemsB.WangSequenceShiftedR
import Submission.Work.StemsB.Rat.WangThetaCup

/-!
# The Wang transgression in the top degree of the fibre

The Wang transgression of a fibration over the sphere is formalised in
`Submission/Work/StemsB/WangSequenceShiftedR.lean` in the **shifted** presentation

  `θ_n : H^{n+b}(F) → H^{n+1}(F)`,  `n ≥ 0`,

i.e. only for classes of degree `≥ b`.  The blueprint's `C2` odd step
(`Submission/Work/Stems/EM_C2_RANGE_FINDING.md` §3/§5) needs the transgression of the
**fundamental class of the fibre**, of degree `b - 1`, together with its multiplicativity
`θ(x ⌣ x) = 2 · x ⌣ θ(x)` (the two are what kill the exceptional degrees `2n-2`, `2n-1` of the
`K(ℤ,n)` computation, `n` odd).

This file provides that degree:

* `wangCohAlphaLowR` / `wangCohThetaLowR` / `wangCohExactLowR` — the **abstract** low-degree Wang
  sequence (exactness at the top fibre degree), over any commutative ring;
* `wangCohThetaLowR_ne_zero` — the consequence used by `C2` odd: a class not in the image of the
  restriction has non-zero transgression (in particular, for a `b`-connected total space every
  non-zero class has non-zero transgression);
* `wangRelEqIsoLow`, `wangTauSLow`, `wangThetaLow` — the **geometric** versions for the sphere
  model, with `wangThetaLow = ρ ∘ Σ ∘ λ_G^*` the low-degree transgression;
* `wangCohExactSphereLow` — exactness of the low-degree Wang sequence over the sphere.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.StemsB.Rat

noncomputable section

/-! ## The abstract low-degree Wang sequence -/

section Abstract

variable (R : Type) [CommRing R] (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)

/-- The restriction `H^{m-1}(X) → H^{m-1}(Fsp)` of the low-degree Wang sequence. -/
def wangCohAlphaLowR
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp) :
    Work.Cohomology.singularCohomology R (m - 1) X ⟶
      Work.Cohomology.singularCohomology R (m - 1) Fsp :=
  HomologicalComplex.homologyMap (Work.Cohomology.restr R X A) (m - 1) ≫ (γ (m - 1)).hom

/-- The low-degree transgression `H^{m-1}(Fsp) → H^0(Fsp)`. -/
def wangCohThetaLowR
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : (Work.Cohomology.relComplex R X A).homology ((m - 1) + 1) ≅
      Work.Cohomology.singularCohomology R 0 Fsp) :
    Work.Cohomology.singularCohomology R (m - 1) Fsp ⟶
      Work.Cohomology.singularCohomology R 0 Fsp :=
  (γ (m - 1)).inv ≫ Work.Cohomology.pairδ R X A (m - 1) ≫ τS.hom

/-- **Exactness of the low-degree Wang sequence**: the image of the restriction is the kernel of
the transgression. -/
theorem wangCohExactLowR
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : (Work.Cohomology.relComplex R X A).homology ((m - 1) + 1) ≅
      Work.Cohomology.singularCohomology R 0 Fsp) :
    Function.Exact (wangCohAlphaLowR R X A Fsp m γ) (wangCohThetaLowR R X A Fsp m γ τS) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₃ R X A (m - 1))
  exact functionExact_conj_R R _ _ (Iso.refl _) (γ (m - 1)) τS h

/-- **A class outside the image of the restriction has non-zero transgression.** -/
theorem wangCohThetaLowR_ne_zero
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : (Work.Cohomology.relComplex R X A).homology ((m - 1) + 1) ≅
      Work.Cohomology.singularCohomology R 0 Fsp)
    (x : Work.Cohomology.singularCohomology R (m - 1) Fsp)
    (hx : x ∉ Set.range (wangCohAlphaLowR R X A Fsp m γ)) :
    (wangCohThetaLowR R X A Fsp m γ τS).hom x ≠ 0 :=
  fun h0 => hx ((wangCohExactLowR R X A Fsp m γ τS x).mp h0)

/-- **A non-zero class of a `b`-connected total space has non-zero transgression.**  If
`H^{m-1}(X) = 0` (the total space is `m`-connected), the image of the restriction is trivial, so
every non-zero class of `H^{m-1}(Fsp)` has non-zero low-degree transgression. -/
theorem wangCohThetaLowR_ne_zero_of_subsingleton
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : (Work.Cohomology.relComplex R X A).homology ((m - 1) + 1) ≅
      Work.Cohomology.singularCohomology R 0 Fsp)
    (hX : Subsingleton (Work.Cohomology.singularCohomology R (m - 1) X))
    {x : Work.Cohomology.singularCohomology R (m - 1) Fsp} (hx : x ≠ 0) :
    (wangCohThetaLowR R X A Fsp m γ τS).hom x ≠ 0 := by
  refine wangCohThetaLowR_ne_zero R X A Fsp m γ τS x (fun hmem => hx ?_)
  obtain ⟨y, hy⟩ := hmem
  rw [← hy, Subsingleton.elim y 0, map_zero]

end Abstract

/-! ## The geometric version over the sphere -/

variable {E : Type} [TopologicalSpace E]

/-- The degree transport `(b - 1) + 1 ↦ 0 + b` of the relative cohomology of the collar pair. -/
noncomputable def wangRelEqIsoLow (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b)) :
    (Work.Cohomology.relComplex ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
      (wangCQ b p d_G)).homology ((b - 1) + 1) ≅
    (Work.Cohomology.relComplex ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
      (wangCQ b p d_G)).homology (0 + b) :=
  ((eqToIso (congrArg (fun t => (Work.Cohomology.relComplex ℚ
      (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (wangCQ b p d_G)).homology t)
      ((lowCast b hb).trans (Nat.zero_add b).symm))).toLinearEquiv).toModuleIso

/-- **The target transport `τS` of the low-degree Wang transgression**: excision, the
trivialisation, the degree transport, the inverse Thom isomorphism of the collar and the
clutching identification, in degree `(b-1)+1 ↦ 0`. -/
noncomputable def wangTauSLow (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    (Work.Cohomology.relComplex ℚ (TopCat.of E) (wangA b p)).homology ((b - 1) + 1) ≅
      Work.Cohomology.singularCohomology ℚ 0 (wangCohFsp b p) :=
  wangExcIso b (by omega) E p ((b - 1) + 1) ≪≫
    wangTrivIso b (by omega) E p d_G hT_G ((b - 1) + 1) ≪≫
    wangRelEqIsoLow b (by omega) E p d_G ≪≫
    (collarPhiIso b (by omega) (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
      (wangSusT_thom b hb (wangFY b p d_G)) 0).symm ≪≫
    rhoIso b (by omega) E p d_G hT_G hT_O 0

/-- **The low-degree Wang transgression**, `ρ ∘ Σ ∘ λ_G^*` on classes of degree `b - 1`. -/
noncomputable def wangThetaLow (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    Work.Cohomology.singularCohomology ℚ (b - 1) (wangCohFsp b p) →ₗ[ℚ]
      Work.Cohomology.singularCohomology ℚ 0 (wangCohFsp b p) :=
  ((rhoCoh b (by omega) p d_G hT_G hT_O 0).hom).comp
    ((collarSigmaLow b (by omega) (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
      (wangSusT_thom b hb (wangFY b p d_G))).comp
      (collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom)

/-- The computation rule of `wangThetaLow`. -/
theorem wangThetaLow_apply (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (a : Work.Cohomology.singularCohomology ℚ (b - 1) (wangCohFsp b p)) :
    wangThetaLow b hb E p d_G hT_G hT_O a =
      (rhoCoh b (by omega) p d_G hT_G hT_O 0).hom
        (collarSigmaLow b (by omega) (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
          (wangSusT_thom b hb (wangFY b p d_G))
          ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom a)) := rfl

/-- **Exactness of the low-degree Wang sequence over the sphere.** -/
theorem wangCohExactSphereLow (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    Function.Exact
      (wangCohAlphaLowR ℚ (TopCat.of E) (wangA b p) (wangCohFsp b p) b
        (wangGammaExplicit b p hT_O))
      (wangCohThetaLowR ℚ (TopCat.of E) (wangA b p) (wangCohFsp b p) b
        (wangGammaExplicit b p hT_O) (wangTauSLow b hb E p hT_O d_G hT_G)) :=
  wangCohExactLowR ℚ (TopCat.of E) (wangA b p) (wangCohFsp b p) b
    (wangGammaExplicit b p hT_O) (wangTauSLow b hb E p hT_O d_G hT_G)

end

end Work.StemsB.Rat
