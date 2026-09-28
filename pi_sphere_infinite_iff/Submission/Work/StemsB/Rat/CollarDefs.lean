import Mathlib
import Submission.Work.StemsB.collarThomRat
import Submission.Work.StemsB.serreSphere_collar_les_degenerates
import Submission.Work.Cohomology.RelCup

/-!
# The transgression coefficient map of the collar pair, and the `s`-splitting

Definitions for the derivation property of the Wang transgression (`D2_PLAN.md`,
`D2_STATUS_LEMMA_AGENT.md`), for the collar pair

  `Q = ↥(sphLoopBig b) × Y`,  `C = sphLoopCollarProd b Y`

of the sphere model (`b ≥ 1`, `Y` an arbitrary space).

* `collarPhi b Y τ m : H^m(Y;ℚ) →ₗ H^{m+b}(Q,C;ℚ)`, `x ↦ π^*(x) ⌣ τ` — the **Thom map**;
  `CollarThom b Y τ` is the **Thom property**, and `exists_collarThom` produces a Thom class.
* `collarRestr`, `collarRestr_injective`, `collarProjC` — the restriction `H^*(Q) → H^*(C)`, its
  injectivity (the degeneration of the collar long exact sequence), and the projection
  `H^*(Y) → H^*(C)`.
* `collarRelEq`, `collarRelEqS` — the comparison of the arithmetic degree expressions that occur
  (`(m+b)+1` vs `(m+1)+b`, and `(m+1)+(b-1)` vs `m+b`), as linear equivalences.
* `collarSigma b hb Y τ hτ m : H^{m+b}(C;ℚ) →ₗ H^{m+1}(Y;ℚ)` — the **transgression coefficient
  map** `Σ = Φ⁻¹ ∘ δ`, of degree `-(b-1)`, with `collarSigma_spec` as its defining property.
* `CollarSSq s` — the statement `s ⌣ s = 0`.

The two lemmas the derivation argument needs on top of these — the **splitting**
`x - π^*(Σ x) ⌣ s ∈ im i^*` and the **derivation core** — are the next hand-offs.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB.Rat

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- The projection `↥(sphLoopBig b) × Y → Y`. -/
def collarProjY (b : ℕ) : C(↥(sphLoopBig b) × Y, Y) :=
  ⟨fun p => p.2, by fun_prop⟩

/-- **The Thom map of the collar pair**: `x ↦ π^*(x) ⌣ τ`. -/
def collarPhi (b : ℕ) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) (m : ℕ) :
    Work.Thom.Coh ℚ m Y →ₗ[ℚ]
      Work.Thom.RelCoh ℚ (m + b) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
  ((LinearMap.applyₗ τ).comp (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) m b)).comp
    (Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ m).hom

@[simp] theorem collarPhi_apply (b : ℕ) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) (m : ℕ)
    (x : Work.Thom.Coh ℚ m Y) :
    collarPhi (Y := Y) b τ m x =
      (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) m b)
        ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ m).hom x) τ := rfl

/-- **The Thom property** of a class `τ` of the collar pair: the Thom map is bijective in every
degree. -/
def CollarThom (b : ℕ) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) : Prop :=
  ∀ m : ℕ, Function.Bijective (collarPhi (Y := Y) b τ m)

/-- **The collar pair carries a Thom class** (`Work.StemsB.collar_thomClass`). -/
theorem exists_collarThom (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] :
    ∃ τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y),
      CollarThom (Y := Y) b τ := by
  obtain ⟨τ, hτ⟩ := collarThomRat b hb Y
  refine ⟨τ, fun m => ?_⟩
  have heq : (⇑(collarPhi (Y := Y) b τ m)) = (fun x : Work.Thom.Coh ℚ m Y =>
      (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) m b)
        ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ m).hom x) τ) :=
    funext (fun x => collarPhi_apply b Y τ m x)
  rw [heq]
  exact hτ m

/-- The restriction `H^m(Q;ℚ) → H^m(C;ℚ)` of the collar pair, as a linear map. -/
def collarRestr (b : ℕ) (Y : Type) [TopologicalSpace Y] (m : ℕ) :
    Work.Cohomology.singularCohomology ℚ m (TopCat.of (↥(sphLoopBig b) × Y)) →ₗ[ℚ]
      Work.Cohomology.singularCohomology ℚ m (TopCat.of ↥(sphLoopCollarProd b Y)) :=
  (HomologicalComplex.homologyMap
    (Work.Cohomology.restr ℚ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y)) m).hom

/-- The restriction `H^m(Q;ℚ) → H^m(C;ℚ)` is injective (the collar long exact sequence
degenerates). -/
theorem collarRestr_injective (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (m : ℕ) :
    Function.Injective (collarRestr (Y := Y) b m) :=
  serreSphere_collar_restriction_injective (R := ℚ) (Y := Y) b hb m

/-- The projection `H^m(Y;ℚ) → H^m(C;ℚ)` on cohomology (the collar as a subspace of `Q`). -/
def collarProjC (b : ℕ) (Y : Type) [TopologicalSpace Y] (m : ℕ) :
    Work.Thom.Coh ℚ m Y →ₗ[ℚ]
      Work.Cohomology.singularCohomology ℚ m (TopCat.of ↥(sphLoopCollarProd b Y)) :=
  (Work.Thom.CohMap
    (⟨fun q : ↥(sphLoopCollarProd b Y) => q.1.2, by fun_prop⟩ :
      C(↥(sphLoopCollarProd b Y), Y)) ℚ m).hom

/-- The connecting homomorphism of the collar pair in degree `m + b`, as a linear map. -/
def collarDelta (b : ℕ) (Y : Type) [TopologicalSpace Y] (m : ℕ) :
    (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b) →ₗ[ℚ]
      (Work.Cohomology.relComplex ℚ (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y)).homology ((m + b) + 1) :=
  (Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × Y))
    (sphLoopCollarProd b Y) (m + b)).hom

/-- The comparison of the degrees `(m + b) + 1` and `(m + 1) + b` for the relative cohomology of
the collar pair. -/
noncomputable def collarRelEq (b : ℕ) (Y : Type) [TopologicalSpace Y] (m : ℕ) :
    (Work.Cohomology.relComplex ℚ (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y)).homology ((m + b) + 1) ≃ₗ[ℚ]
      (Work.Cohomology.relComplex ℚ (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y)).homology ((m + 1) + b) :=
  (eqToIso (congrArg (fun t => (Work.Cohomology.relComplex ℚ
    (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)).homology t)
    (by omega : (m + b) + 1 = (m + 1) + b))).toLinearEquiv

/-- The comparison of the degrees `(m + 1) + (b - 1)` and `m + b` for the cohomology of the
collar. -/
noncomputable def collarRelEqS (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (m : ℕ) :
    Work.Cohomology.singularCohomology ℚ ((m + 1) + (b - 1))
        (TopCat.of ↥(sphLoopCollarProd b Y)) ≃ₗ[ℚ]
      Work.Cohomology.singularCohomology ℚ (m + b)
        (TopCat.of ↥(sphLoopCollarProd b Y)) :=
  (eqToIso (congrArg (fun t => Work.Cohomology.singularCohomology ℚ t
    (TopCat.of ↥(sphLoopCollarProd b Y)))
    (by omega : (m + 1) + (b - 1) = m + b))).toLinearEquiv

/-- **The transgression coefficient map of the collar pair**: `Σ x` is the class of the base with
`π^*(Σ x) ⌣ τ = δ x`, the connecting homomorphism `δ` of the pair `(Q,C)` in degree `m + b` being
compared to the degree `(m+1)+b` of the Thom map by `collarRelEq`.  It has degree `-(b-1)`: it
takes `H^{m+b}(C)` to `H^{m+1}(Y)`. -/
noncomputable def collarSigma (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ) (m : ℕ) :
    (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b) →ₗ[ℚ]
      Work.Thom.Coh ℚ (m + 1) Y :=
  ((LinearEquiv.ofBijective (collarPhi (Y := Y) b τ (m + 1)) (hτ (m + 1))).symm.toLinearMap).comp
    (((collarRelEq (Y := Y) b m).toLinearMap).comp (collarDelta (Y := Y) b m))

/-- **The defining property of the transgression coefficient map.** -/
theorem collarSigma_spec (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ) (m : ℕ)
    (x : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b)) :
    collarPhi (Y := Y) b τ (m + 1) (collarSigma b hb (Y := Y) τ hτ m x) =
      collarRelEq (Y := Y) b m (collarDelta (Y := Y) b m x) := by
  show (LinearEquiv.ofBijective (collarPhi (Y := Y) b τ (m + 1)) (hτ (m + 1)))
      ((LinearEquiv.ofBijective (collarPhi (Y := Y) b τ (m + 1)) (hτ (m + 1))).symm
        (collarRelEq (Y := Y) b m (collarDelta (Y := Y) b m x))) =
      collarRelEq (Y := Y) b m (collarDelta (Y := Y) b m x)
  exact LinearEquiv.apply_symm_apply _ _

/-- **The transgression coefficient map exists** (the existential form of `collarSigma`). -/
theorem collarSigma_exists (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ) (m : ℕ) :
    ∃ S : (Work.Cohomology.singularCochainComplex ℚ
          (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b) →ₗ[ℚ]
        Work.Thom.Coh ℚ (m + 1) Y,
      ∀ x : (Work.Cohomology.singularCochainComplex ℚ
          (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b),
        collarPhi (Y := Y) b τ (m + 1) (S x)
          = collarRelEq (Y := Y) b m (collarDelta (Y := Y) b m x) :=
  ⟨collarSigma b hb (Y := Y) τ hτ m, fun x => collarSigma_spec b hb (Y := Y) τ hτ m x⟩

/-- The `s`-part of a class of the collar: `π^*(Σ x) ⌣ s`, where `s` is the suspension class
(`Work.StemsB.Rat.collarSuspensionClass`). -/
noncomputable def collarSPart (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : Work.Cohomology.singularCohomology ℚ (b - 1) (TopCat.of ↥(sphLoopCollarProd b Y)))
    (m : ℕ) :
    (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b) →ₗ[ℚ]
      (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b) :=
  let cupPart : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b) →ₗ[ℚ]
      Work.Cohomology.singularCohomology ℚ ((m + 1) + (b - 1))
        (TopCat.of ↥(sphLoopCollarProd b Y)) :=
    ((LinearMap.applyₗ (R := ℚ)
        (M := Work.Cohomology.singularCohomology ℚ (b - 1)
          (TopCat.of ↥(sphLoopCollarProd b Y)))
        (M₂ := Work.Cohomology.singularCohomology ℚ ((m + 1) + (b - 1))
          (TopCat.of ↥(sphLoopCollarProd b Y))) s).comp
      (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of ↥(sphLoopCollarProd b Y)))
        (m + 1) (b - 1))).comp
      ((collarProjC (Y := Y) b (m + 1)).comp (collarSigma b hb (Y := Y) τ hτ m))
  let signPart : Work.Cohomology.singularCohomology ℚ ((m + 1) + (b - 1))
        (TopCat.of ↥(sphLoopCollarProd b Y)) →ₗ[ℚ]
      Work.Cohomology.singularCohomology ℚ ((m + 1) + (b - 1))
        (TopCat.of ↥(sphLoopCollarProd b Y)) :=
    ((-1 : ℚ) ^ (m + 1)) •
      (LinearMap.id : Work.Cohomology.singularCohomology ℚ ((m + 1) + (b - 1))
          (TopCat.of ↥(sphLoopCollarProd b Y)) →ₗ[ℚ]
        Work.Cohomology.singularCohomology ℚ ((m + 1) + (b - 1))
          (TopCat.of ↥(sphLoopCollarProd b Y)))
  ((collarRelEqS (Y := Y) b hb m).toLinearMap).comp (signPart.comp cupPart)

/-- **The computation rule of the `s`-part**: `(-1)^{m+1} · (π^*(Σ x) ⌣ s)`.  The sign is the
Koszul sign carried by `Work.Sph3Disc.pairDelta_mixedCup_general` (see
`D2_STATUS_LEMMA_AGENT.md` §4sexies): with it, the connecting homomorphism of `collarSPart x` is
`collarDelta x`, which is exactly the hypothesis of `Work.StemsB.Rat.collarSplit_of_delta`. -/
theorem collarSPart_apply (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : Work.Cohomology.singularCohomology ℚ (b - 1) (TopCat.of ↥(sphLoopCollarProd b Y)))
    (m : ℕ)
    (x : (Work.Cohomology.singularCochainComplex ℚ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b)) :
    collarSPart b hb (Y := Y) τ hτ s m x =
      (collarRelEqS (Y := Y) b hb m)
        (((-1 : ℚ) ^ (m + 1)) •
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of ↥(sphLoopCollarProd b Y)))
              (m + 1) (b - 1))
            ((collarProjC (Y := Y) b (m + 1)) (collarSigma b hb (Y := Y) τ hτ m x)) s)) := by
  unfold collarSPart
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap]
  rfl

end

end Work.StemsB.Rat
