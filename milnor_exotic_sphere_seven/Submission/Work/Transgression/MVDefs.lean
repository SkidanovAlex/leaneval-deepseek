import Mathlib
import Submission.Work.Transgression.Pieces
import Submission.Work.Transgression.Algebra
import Submission.Work.Agree.kunnethInj
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.sphereCohomologyTop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The vocabulary of the transgression (Mayer–Vietoris) assembly

This module fixes the objects and the maps through which the remaining input
`Work.Transgression.PuncturedCohCard` of the chapter is computed:

* `MV.XT a b` — the punctured total space `E ∖ 0` of `clutchBundle a b` as a `TopCat`;
* `MV.iotaU`, `MV.iotaV` — the inclusions of the overlap `pW = pU ∩ pV` into the two pieces;
* `MV.s3Iso`, `MV.gen3` — a fixed isomorphism `H³(S³;ℤ) ≅ ℤ` in the quaternionic model and the
  corresponding generator (any generator works, but it is convenient to fix one);
* `MV.alpha`, `MV.beta`, `MV.psiGen` — the three classes of `H³(S³ × S³;ℤ)` in terms of which the
  transgression class is expressed: `α = prjA^* gen`, `β = prjB^* gen`, and the class of the
  clutching map `ψ (u,v) = uᵃ v uᵇ`, which is `(a+b) α + β` (`Work.Transgression.PsiClass`);
* the four pairings between the factor pullbacks and the factor inclusions, which say that
  `sectA^*`, `sectB^*` detect the two summands.

The reason `pU`, `pV` and `pW` are each homotopy equivalent to a sphere product is that they are
the (fibrewise) products of a chart of `S⁴` with the punctured fibre `ℝ⁴ ∖ 0`; the maps
`rhoU`, `rhoV`, `rhoW` of `Submission/Work/Transgression/Pieces.lean` are the resulting retractions.
-/

namespace Work.Transgression

open Work.TangentClasses Work.Thom CategoryTheory Limits

noncomputable section

namespace MV

/-- The quaternionic sphere `S³ = Sp(1)`, the model in which `rhoU`, `rhoV`, `rhoW`, `psi`,
`sectA`, `sectB` are stated. -/
abbrev S3Q : Type := Work.CharacteristicClasses.S3

/-- The product `S³ × S³`, the target of `rhoW`. -/
abbrev S3Q2 : Type := Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3

/-- The punctured total space of `clutchBundle a b`, as a topological space. -/
abbrev XT (a b : ℤ) : TopCat := TopCat.of ↥(Work.Thom.zeroComplement (Zb a b))

/-- The inclusion of the overlap `pW = pU ∩ pV` into the piece `pU`. -/
def iotaU (a b : ℤ) : C(↥(pW a b), ↥(pU a b)) :=
  ⟨fun p => ⟨p.1, p.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The inclusion of the overlap `pW = pU ∩ pV` into the piece `pV`. -/
def iotaV (a b : ℤ) : C(↥(pW a b), ↥(pV a b)) :=
  ⟨fun p => ⟨p.1, p.2.2⟩, continuous_subtype_val.subtype_mk _⟩

@[simp] lemma iotaU_apply (a b : ℤ) (p : ↥(pW a b)) :
    ((iotaU a b p : ↥(pU a b)) : ↥(Work.Thom.zeroComplement (Zb a b))) = p.1 := rfl

@[simp] lemma iotaV_apply (a b : ℤ) (p : ↥(pW a b)) :
    ((iotaV a b p : ↥(pV a b)) : ↥(Work.Thom.zeroComplement (Zb a b))) = p.1 := rfl

/-! ## The fixed generator of `H³(S³;ℤ)` -/

/-- **`H³(S³;ℤ) ≅ ℤ`** in the quaternionic model, through the Euclidean model `S³ ⊆ ℝ⁴`
(`Work.CharacteristicClasses.s3Homeo`) and the computation `Work.Cohomology.sphereCohomologyTop`. -/
def s3Iso : ↥(Coh ℤ 3 S3Q) ≃ₗ[ℤ] ℤ :=
  ((Work.Cohomology.cohomologyIso_of_homotopyEquiv
      (Work.CharacteristicClasses.s3Homeo.toHomotopyEquiv) 3).some ≪≫
    (Work.Cohomology.sphereCohomologyTop 3 (by norm_num)).some).toLinearEquiv

/-- The chosen generator of `H³(S³;ℤ)`: the class sent to `1` by `s3Iso`. -/
def gen3 : ↥(Coh ℤ 3 S3Q) := s3Iso.symm 1

@[simp] lemma s3Iso_gen3 : s3Iso gen3 = 1 := s3Iso.apply_symm_apply 1

/-- `gen3` generates `H³(S³;ℤ)`. -/
lemma gen3_generates (x : ↥(Coh ℤ 3 S3Q)) : ∃ k : ℤ, x = k • gen3 := by
  refine ⟨s3Iso x, s3Iso.injective ?_⟩
  rw [map_zsmul, s3Iso_gen3]
  simp

/-- The `ℤ`-linear functional `φ = s3Iso` evaluated, in the form used by the pairings. -/
lemma s3Iso_apply (x : ↥(Coh ℤ 3 S3Q)) :
    s3Iso x = s3Iso.toLinearMap x := rfl

/-! ## The three classes of `H³(S³ × S³;ℤ)` -/

/-- `α = prjA^* gen`, the pullback of the generator along the first projection. -/
def alpha : ↥(Coh ℤ 3 S3Q2) := (HMap prjA 3).hom gen3

/-- `β = prjB^* gen`, the pullback of the generator along the second projection. -/
def beta : ↥(Coh ℤ 3 S3Q2) := (HMap prjB 3).hom gen3

/-- The class of the clutching map `ψ (u,v) = uᵃ v uᵇ`.  By `Work.Transgression.PsiClass` it is
`(a+b) • α + β`. -/
def psiGen (a b : ℤ) : ↥(Coh ℤ 3 S3Q2) := (HMap (psi a b) 3).hom gen3

/-! ## The four pairings of the factor projections and inclusions -/

lemma prjA_comp_sectA : prjA.comp sectA = ContinuousMap.id S3Q := by
  apply ContinuousMap.ext; intro v; rfl

lemma prjB_comp_sectB : prjB.comp sectB = ContinuousMap.id S3Q := by
  apply ContinuousMap.ext; intro v; rfl

lemma prjB_comp_sectA :
    prjB.comp sectA = ContinuousMap.const S3Q (Work.CharacteristicClasses.s3One) := by
  apply ContinuousMap.ext; intro v; rfl

lemma prjA_comp_sectB :
    prjA.comp sectB = ContinuousMap.const S3Q (Work.CharacteristicClasses.s3One) := by
  apply ContinuousMap.ext; intro v; rfl

/-- `sectA^* ∘ prjA^* = id`. -/
theorem sectA_comp_prjA :
    (HMap sectA 3).hom.comp (HMap prjA 3).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp,
    ← HMap_comp (B₁ := (Work.CharacteristicClasses.S3))
      (B₂ := (Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3))
      (B₃ := (Work.CharacteristicClasses.S3)) sectA prjA 3,
    prjA_comp_sectA, HMap_id]
  rfl

/-- `sectB^* ∘ prjB^* = id`. -/
theorem sectB_comp_prjB :
    (HMap sectB 3).hom.comp (HMap prjB 3).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp,
    ← HMap_comp (B₁ := (Work.CharacteristicClasses.S3))
      (B₂ := (Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3))
      (B₃ := (Work.CharacteristicClasses.S3)) sectB prjB 3,
    prjB_comp_sectB, HMap_id]
  rfl

/-- `sectA^* ∘ prjB^* = 0`: the composite `prjB ∘ sectA` is constant. -/
theorem sectA_prjB_zero :
    (HMap sectA 3).hom.comp (HMap prjB 3).hom = 0 := by
  apply LinearMap.ext
  intro x
  have hcomp := HMap_comp sectA prjB 3
  rw [prjB_comp_sectA] at hcomp
  rw [← ModuleCat.hom_comp, ← hcomp]
  exact Work.Agree.HMap_const_eq_zero (Work.CharacteristicClasses.s3One) 2 x

/-- `sectB^* ∘ prjA^* = 0`: the composite `prjA ∘ sectB` is constant. -/
theorem sectB_prjA_zero :
    (HMap sectB 3).hom.comp (HMap prjA 3).hom = 0 := by
  apply LinearMap.ext
  intro x
  have hcomp := HMap_comp sectB prjA 3
  rw [prjA_comp_sectB] at hcomp
  rw [← ModuleCat.hom_comp, ← hcomp]
  exact Work.Agree.HMap_const_eq_zero (Work.CharacteristicClasses.s3One) 2 x

/-- `gen3` generates `H³(S³;ℤ)`, as a submodule statement. -/
theorem span_gen3 : Submodule.span ℤ ({gen3} : Set ↥(Coh ℤ 3 S3Q)) = ⊤ :=
  (span_singleton_eq_top_iff' gen3).mpr gen3_generates

/-- The image of `⊤` under `prjB^*` is spanned by `β`. -/
theorem map_prjB_top : Submodule.map (HMap prjB 3).hom (⊤ : Submodule ℤ ↥(Coh ℤ 3 S3Q))
    = Submodule.span ℤ ({beta} : Set ↥(Coh ℤ 3 S3Q2)) := by
  calc Submodule.map (HMap prjB 3).hom (⊤ : Submodule ℤ ↥(Coh ℤ 3 S3Q))
      = Submodule.map (HMap prjB 3).hom (Submodule.span ℤ ({gen3} : Set ↥(Coh ℤ 3 S3Q))) := by
        rw [span_gen3]
    _ = Submodule.span ℤ ((HMap prjB 3).hom '' ({gen3} : Set ↥(Coh ℤ 3 S3Q))) :=
        Submodule.map_span _ _
    _ = Submodule.span ℤ ({beta} : Set ↥(Coh ℤ 3 S3Q2)) := by
        rw [Set.image_singleton]; rfl

/-- The image of `⊤` under `prjA^*` is spanned by `α`. -/
theorem map_prjA_top : Submodule.map (HMap prjA 3).hom (⊤ : Submodule ℤ ↥(Coh ℤ 3 S3Q))
    = Submodule.span ℤ ({alpha} : Set ↥(Coh ℤ 3 S3Q2)) := by
  calc Submodule.map (HMap prjA 3).hom (⊤ : Submodule ℤ ↥(Coh ℤ 3 S3Q))
      = Submodule.map (HMap prjA 3).hom (Submodule.span ℤ ({gen3} : Set ↥(Coh ℤ 3 S3Q))) := by
        rw [span_gen3]
    _ = Submodule.span ℤ ((HMap prjA 3).hom '' ({gen3} : Set ↥(Coh ℤ 3 S3Q))) :=
        Submodule.map_span _ _
    _ = Submodule.span ℤ ({alpha} : Set ↥(Coh ℤ 3 S3Q2)) := by
        rw [Set.image_singleton]; rfl

end MV

end

end Work.Transgression
