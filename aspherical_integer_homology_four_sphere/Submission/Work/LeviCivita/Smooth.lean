/-
# Smoothness of the Levi-Civita connection

This file proves the last defining property of `Work.LeviCivita.lcConn`:
`CovariantDerivative.ContMDiffCovariantDerivative lcConn ∞`.

Mathlib proves the existence of the Levi-Civita connection (`leviCivitaConnection`) together with
torsion-freeness and metric compatibility, but *not* its smoothness ("Future PRs" in
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`).  This is that proof.

## The idea

Let `σ` be a `C^∞` section.  We must show that the section `x ↦ ⟨x, lcConn σ x⟩` of the bundle
`Hom(TM, TM)` is `C^∞`.  By `Trivialization.contMDiffWithinAt_section` it suffices to show that the
coordinate representative of `lcConn σ` in the tangent trivialisation at `x₀`,

    A x := inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x x₀ x (lcConn σ x),

is `C^∞` as an `E →L[ℝ] E`-valued function near `x₀`.

Two facts make this computable.

* **The Koszul formula** (`Work.LeviCivita.lcConn_apply_inner`) expresses
  `⟪∇_X σ, Z⟫` for smooth fields `X, Z` as a sum of derivatives of smooth functions and Lie
  brackets; each is smooth in `x`.  So `x ↦ ⟪lcConn σ x (X x), Z x⟫` is smooth
  (`Work.LeviCivita.contMDiffAt_lcConn_pairing`).
* **The chart metric** `Ĝ x := chartGramCLM x₀ x` is a smooth family of positive definite forms on
  the finite dimensional space `E`.  Its *inverse Riesz maps* `x ↦ (Ĝ x).inverse` are smooth
  (`Work.LeviCivita.contMDiffAt_chartGramCLM_inverse`).

Taking the chart frame `b` of `E` and globally smooth fields `smoothFrameField x₀ (b i)` agreeing
with the frame near `x₀`, define the *coordinate Koszul pairing*

    P x := Σ_{i} bᵢ* ⊗ (Σ_{j} bⱼ* ⊗ ⟪lcConn σ x (smoothFrameField x₀ (b i) x),
                                    (smoothFrameField x₀ (b j) x)⟫)

(`chartPairing`, an `E →L[ℝ] E →L[ℝ] ℝ`-valued smooth function) and set

    A' x := (Ĝ x).inverse ∘L (P x).

Then `A' x u` is the unique vector whose `Ĝ x`-pairings with all `w` match `P x u w`.  On the one
hand `Ĝ x ≫ A x` has exactly those pairings, because
`Ĝ x (A x u) w = ⟪lcConn σ x (frameVector x₀ x u), frameVector x₀ x w⟫`
(`chartGram_inCoordinates`) and the chosen fields agree with the frame near `x₀`.  Hence
`A =ᶠ[𝓝 x₀] A'` (`chartLCcoords_eventuallyEq`), and `A` — being eventually equal to a smooth
function — is smooth, which is `contMDiffCovariantDerivative_lcConn` (in `Submission.Work.LeviCivita.Main`).

The comparison `A =ᶠ A'` is `Work.LeviCivita.chartLCcoords_eventuallyEq`, proved in
`Submission/Work/LeviCivita/chartLCcoords_eventuallyEq.lean`.
-/
import Submission.Work.LeviCivita.Defs
import Submission.Work.LeviCivita.ChartMetric
import Submission.Work.LeviCivita.FrameField
import Submission.Work.LeviCivita.Koszul
import Submission.Work.LeviCivita.isInvertible_of_posDef
import Submission.Work.LeviCivita.contMDiffAt_lcConn_pairing
import Submission.Work.LeviCivita.contMDiffAt_chartGramCLM_inverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic

namespace Work.LeviCivita

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

/-! ## §1  The Koszul pairing in coordinates -/

/-- The coordinate Koszul pairing of `∇σ` with the chart frame: an
`E →L[ℝ] E →L[ℝ] ℝ`-valued function of `x`, whose value at `(u, w)` is
`Σ_{ij} uᵢ wⱼ ⟪∇σ, σ_{b j}⟫` in the basis `b` of `E` — that is, the pairing of the coordinate
vector `u` with the coordinate vector `w`, as read through `∇`. -/
noncomputable def chartPairing (x₀ : M) (σ : Π x : M, TangentSpace I x) (x : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
      ((Module.finBasis ℝ E).coord i).toContinuousLinearMap
      (∑ j : Fin (Module.finrank ℝ E),
        ContinuousLinearMap.smulRightL ℝ E ℝ
          ((Module.finBasis ℝ E).coord j).toContinuousLinearMap
          (inner ℝ (lcConn (I := I) (M := M) σ x (smoothFrameField (I := I) x₀
              ((Module.finBasis ℝ E) i) x))
            (smoothFrameField (I := I) x₀ ((Module.finBasis ℝ E) j) x)))

/-- Evaluation of the Koszul pairing. -/
lemma chartPairing_apply (x₀ : M) (σ : Π x : M, TangentSpace I x) (x : M) (u w : E) :
    chartPairing (I := I) x₀ σ x u w =
      ∑ i : Fin (Module.finrank ℝ E),
        ((Module.finBasis ℝ E).coord i) u *
          ∑ j : Fin (Module.finrank ℝ E),
            ((Module.finBasis ℝ E).coord j) w *
              inner ℝ (lcConn (I := I) (M := M) σ x
                  (smoothFrameField (I := I) x₀ ((Module.finBasis ℝ E) i) x))
                (smoothFrameField (I := I) x₀ ((Module.finBasis ℝ E) j) x) := by
  simp only [chartPairing, sum_apply, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
    LinearMap.coe_toContinuousLinearMap']

/-! ## §2  Smoothness of the Koszul pairing -/

/-- A finite sum of `C^n` maps into a normed space is `C^n`. -/
lemma contMDiffAt_finset_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}
    (s : Finset ι) {g : ι → M → F} {n : ℕ∞ω} (x : M)
    (h : ∀ i ∈ s, ContMDiffAt I 𝓘(ℝ, F) n (g i) x) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun y ↦ ∑ i ∈ s, g i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contMDiffAt_const (c := (0 : F)) (x := x)
  | insert a s ha ih =>
      have h1 := h a (Finset.mem_insert_self a s)
      have h2 := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
      have h3 : ContMDiffAt I 𝓘(ℝ, F) n (fun y ↦ g a y + ∑ i ∈ s, g i y) x := h1.add h2
      simpa only [Finset.sum_insert ha] using h3

/-- Precomposition of a smooth family by the rank-one operator `smulRightL ψ`, target `ℝ`. -/
lemma contMDiffAt_smulRightL_real (ψ : E →L[ℝ] ℝ) {A : M → ℝ} {x : M}
    (hA : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ A x) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (fun y ↦ ContinuousLinearMap.smulRightL ℝ E ℝ ψ (A y)) x := by
  have hL : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] ℝ) ∞ (ContinuousLinearMap.smulRightL ℝ E ℝ ψ) :=
    ContinuousLinearMap.contMDiff (𝕜 := ℝ) (n := ∞) _
  exact hL.contMDiffAt.comp x hA

/-- Precomposition of a smooth family by the rank-one operator `smulRightL φ`. -/
lemma contMDiffAt_smulRightL (φ : E →L[ℝ] ℝ) {A : M → E →L[ℝ] ℝ} {x : M}
    (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ∞ A x) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) ∞
      (fun y ↦ ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ) φ (A y)) x := by
  have hL : ContMDiff 𝓘(ℝ, E →L[ℝ] ℝ) 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) ∞
      (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ) φ) :=
    ContinuousLinearMap.contMDiff (𝕜 := ℝ) (n := ∞) _
  exact hL.contMDiffAt.comp x hA

/-- The coordinate Koszul pairing is `C^∞` in `x`. -/
theorem contMDiffAt_chartPairing (x₀ : M) {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I I.tangent ∞ (T% σ)) (x : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) ∞ (chartPairing (I := I) x₀ σ) x := by
  classical
  change ContMDiffAt I 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) ∞
    (fun y ↦ ∑ i : Fin (Module.finrank ℝ E),
      ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
        ((Module.finBasis ℝ E).coord i).toContinuousLinearMap
        (∑ j : Fin (Module.finrank ℝ E),
          ContinuousLinearMap.smulRightL ℝ E ℝ
            ((Module.finBasis ℝ E).coord j).toContinuousLinearMap
            (inner ℝ (lcConn (I := I) (M := M) σ y (smoothFrameField (I := I) x₀
                ((Module.finBasis ℝ E) i) y))
              (smoothFrameField (I := I) x₀ ((Module.finBasis ℝ E) j) y)))) x
  refine contMDiffAt_finset_sum _ x (fun i _ ↦ ?_)
  refine contMDiffAt_smulRightL ((Module.finBasis ℝ E).coord i).toContinuousLinearMap ?_
  refine contMDiffAt_finset_sum _ x (fun j _ ↦ ?_)
  refine contMDiffAt_smulRightL_real ((Module.finBasis ℝ E).coord j).toContinuousLinearMap ?_
  exact contMDiffAt_lcConn_pairing (I := I) hσ
    (smoothFrameField_contMDiff (I := I) x₀ ((Module.finBasis ℝ E) i))
    (smoothFrameField_contMDiff (I := I) x₀ ((Module.finBasis ℝ E) j)) x

/-! ## §3  The candidate coordinate representative -/

/-- The candidate for the coordinate representative of `lcConn σ`: raise the Koszul pairing with
the inverse chart metric. -/
noncomputable def chartLCcoords (x₀ : M) (σ : Π x : M, TangentSpace I x) (x : M) :
    E →L[ℝ] E :=
  (chartGramCLM (I := I) x₀ x).inverse ∘L chartPairing (I := I) x₀ σ x

/-- The candidate coordinate representative is `C^∞` near any point of the chart at `x₀`. -/
theorem contMDiffAt_chartLCcoords (x₀ : M) {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I I.tangent ∞ (T% σ)) (p : M) (hp : p ∈ (chartAt H x₀).source) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (chartLCcoords (I := I) x₀ σ) p := by
  have hInv : ContMDiffAt I 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E) ∞
      (fun x : M ↦ (chartGramCLM (I := I) x₀ x).inverse) p :=
    contMDiffAt_chartGramCLM_inverse (I := I) x₀ p hp
  have hP : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) ∞ (chartPairing (I := I) x₀ σ) p :=
    contMDiffAt_chartPairing (I := I) x₀ hσ p
  exact ContMDiffAt.clm_comp (𝕜 := ℝ) (F₁ := E →L[ℝ] ℝ) (F₂ := E) (F₃ := E) (n := ∞) hInv hP

end

end Work.LeviCivita
