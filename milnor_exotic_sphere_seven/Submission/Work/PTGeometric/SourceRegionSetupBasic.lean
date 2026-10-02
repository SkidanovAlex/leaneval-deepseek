import Mathlib
import Submission.Work.PTGeometric.SourceAssembly
import Submission.Work.PTGeometric.SourceRegionPhiSign
import Submission.Work.PTGeometric.RegionManifoldNCWeak
import Submission.Work.PTGeometric.RawAmbientData
import Submission.Work.PTGeometric.SourceZero
import Submission.Work.PTGeometric.sourceZeroSet_boundary_homeo
import Submission.Work.PTGeometric.WeakRegion.Setup
import Submission.Work.PTGeometric.WeakRegion.Manifold
import Submission.Work.PTGeometric.WeakRegion.Properties
import Submission.Work.PTGeometric.regionManifoldTheorem_of_isCompact_weak
import Submission.Work.PTGeometric.contMDiffOn_coord_flatSource_collar
import Submission.Work.PTGeometric.flatCoordModel
import Submission.Work.PTGeometric.mfderiv_ne_zero_of_phi_zero
import Submission.Work.PTGeometric.nonempty_rawAmbientData_of_isEmpty_index
import Submission.Work.PTGeometric.isOpen_setOf_injOn_gr

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000


set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

/-!
# PTGEOMETRIC: the basic definitions of the source region of the null-homotopy

This file collects the definitions shared between `Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion`
and the lemmas proved about it:

* `Work.PTGeometric.sourceBasepoint`, `Work.PTGeometric.sourcePhi`, `Work.PTGeometric.sourcePhi_spec`:
  the base-point preimage to be avoided by the source region and the defining function `Φ` of the
  region (`Classical.choose` of the hypothesis `hphi`) together with its clauses;
* `Work.PTGeometric.t2Space_halfSpace`, `Work.PTGeometric.mem_boundary_halfSpace_iff`: the `T2Space`
  instance of the half-space model and the description of its boundary;
* `Work.PTGeometric.sourceRegionSetup`: the region structure `M = {Φ ≤ 0}` of the source;
* `Work.PTGeometric.regionStraightChart`: the straightening chart of the region in the *identity*
  coordinates of the half-space, whose inverse is an explicit map of the ambient Euclidean space
  (this is what makes the model function of the submersion argument available).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom
open Work.PTGeometric.WeakRegion

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- The set to be avoided by the source region: the preimage of the base point of the Thom space. -/
def sourceBasepoint {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    Set (EuclideanHalfSpace ((8 + k) + 1)) :=
  {x | flatSourceHomotopy8 (k := k) (familySource G m hpow).H (familySource G m hpow).φ x.1 = D.t₀}

/-- **The defining function of the source region** (the witness of the hypothesis `hphi`). -/
def sourcePhi {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : SourceRegionPhiInteriorSign k (sourceZeroSet G m hpow)
      (sourceBasepoint (D := D) (Fam := Fam) G m hpow)) :
    EuclideanHalfSpace ((8 + k) + 1) → ℝ :=
  Classical.choose hphi

/-- **The clauses of the defining function.** -/
theorem sourcePhi_spec {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : SourceRegionPhiInteriorSign k (sourceZeroSet G m hpow)
      (sourceBasepoint (D := D) (Fam := Fam) G m hpow)) :
    ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) (modelWithCornersSelf ℝ ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (sourcePhi G m hpow hphi) ∧
      sourceZeroSet G m hpow ⊆ {x | sourcePhi G m hpow hphi x ≤ 0} ∧
      ({x | sourcePhi G m hpow hphi x ≤ 0} ∩ sourceBasepoint (D := D) (Fam := Fam) G m hpow) = ∅ ∧
      IsCompact {x | sourcePhi G m hpow hphi x ≤ 0} ∧
      (sourceZeroSet G m hpow ∩ {x | sourcePhi G m hpow hphi x = 0} ⊆ {x | x.1 0 = 0}) ∧
      (∀ x : EuclideanHalfSpace ((8 + k) + 1), sourcePhi G m hpow hphi x = 0 → x.1 0 ≠ 0 →
        IsSubmersionAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
          (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (sourcePhi G m hpow hphi) x) ∧
      (∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (EuclideanHalfSpace ((8 + k) + 1)), sourcePhi G m hpow hphi x = 0 →
        ∃ (e : OpenPartialHomeomorph (EuclideanHalfSpace ((8 + k) + 1))
              (EuclideanHalfSpace ((8 + k) + 1))) (c : ℝ),
          e ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
                ((⊤ : ℕ∞) : WithTop ℕ∞) (EuclideanHalfSpace ((8 + k) + 1)) ∧
          x ∈ e.source ∧ c < 0 ∧
          (∀ y ∈ e.source, (e y).1 0 = 0 ↔
            y ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
              (EuclideanHalfSpace ((8 + k) + 1))) ∧
          mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
              (modelWithCornersSelf ℝ ℝ) (sourcePhi G m hpow hphi) x
            = c • mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
                (modelWithCornersSelf ℝ ℝ)
                (fun y : EuclideanHalfSpace ((8 + k) + 1) => (e y).1 0) x) ∧
      (∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (EuclideanHalfSpace ((8 + k) + 1)), sourcePhi G m hpow hphi x = 0 →
        ∀ᶠ y in 𝓝 x, y ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (EuclideanHalfSpace ((8 + k) + 1)) → 0 ≤ sourcePhi G m hpow hphi y) :=
  Classical.choose_spec hphi

/-- The instance `T2Space` of the half-space model (not found by `inferInstance` because
`EuclideanHalfSpace` is an irreducible definition). -/
theorem t2Space_halfSpace (n : ℕ) [NeZero n] : T2Space (EuclideanHalfSpace n) := by
  change T2Space {x : EuclideanSpace ℝ (Fin n) // 0 ≤ x 0}
  infer_instance

/-- **The boundary of the half-space model is the hyperplane `{x | x.1 0 = 0}`.** -/
theorem mem_boundary_halfSpace_iff (n : ℕ) [NeZero n] {x : EuclideanHalfSpace n} :
    x ∈ (modelWithCornersEuclideanHalfSpace n).boundary (EuclideanHalfSpace n) ↔ x.1 0 = 0 := by
  have hmem : (OpenPartialHomeomorph.refl (EuclideanHalfSpace n)) ∈
      IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace n)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (EuclideanHalfSpace n) :=
    IsManifold.chart_mem_maximalAtlas (I := modelWithCornersEuclideanHalfSpace n) (x := x)
  rw [Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
    hmem (mem_univ x)]
  have hcoe : (OpenPartialHomeomorph.refl (EuclideanHalfSpace n)).extend
      (modelWithCornersEuclideanHalfSpace n) x = x.1 := by
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      OpenPartialHomeomorph.refl_apply, modelWithCornersEuclideanHalfSpace_apply]
    rfl
  rw [hcoe]

/-- **The region structure of the source.**  The manifold `M := {x | Φ x ≤ 0}` with the weak
region-charting structure of `Work.PTGeometric.WeakRegion`. -/
def sourceRegionSetup {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : SourceRegionPhiInteriorSign k (sourceZeroSet G m hpow)
      (sourceBasepoint (D := D) (Fam := Fam) G m hpow))
    (hweak : ∀ x : EuclideanHalfSpace ((8 + k) + 1), sourcePhi G m hpow hphi x = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) (sourcePhi G m hpow hphi) x ≠ 0) :
    RegionSetupWeak k :=
  letI := t2Space_halfSpace ((8 + k) + 1)
  { A := EuclideanHalfSpace ((8 + k) + 1)
    Φ := sourcePhi G m hpow hphi
    hΦ := (sourcePhi_spec G m hpow hphi).1
    hweak := hweak
    hsign := (sourcePhi_spec G m hpow hphi).2.2.2.2.2.2.2
    hone := (sourcePhi_spec G m hpow hphi).2.2.2.2.2.2.1
    hK := (sourcePhi_spec G m hpow hphi).2.2.2.1 }


/-! ## The straightening of the model space -/

variable {k : ℕ}

/-- The graph straightening `z ↦ (z 0 - ψ (tail z), tail z)`. -/
noncomputable def strAux (ψ : Mod k → ℝ) (z : Mod k) : Mod k :=
  consVec (z.ofLp 0 - ψ (tailVec z)) (tailVec z)

/-- The inverse graph straightening `z ↦ (z 0 + ψ (tail z), tail z)`. -/
noncomputable def unstrAux (ψ : Mod k → ℝ) (z : Mod k) : Mod k :=
  consVec (z.ofLp 0 + ψ (tailVec z)) (tailVec z)

theorem strAux_apply (ψ : Mod k → ℝ) (z : Mod k) :
    strAux ψ z = consVec (z.ofLp 0 - ψ (tailVec z)) (tailVec z) := rfl

theorem unstrAux_apply (ψ : Mod k → ℝ) (z : Mod k) :
    unstrAux ψ z = consVec (z.ofLp 0 + ψ (tailVec z)) (tailVec z) := rfl

theorem strAux_ofLp_zero (ψ : Mod k → ℝ) (z : Mod k) :
    (strAux ψ z).ofLp 0 = z.ofLp 0 - ψ (tailVec z) := by
  rw [strAux_apply, consVec_apply_zero, tailVec_apply_zero, add_zero]

theorem unstrAux_ofLp_zero (ψ : Mod k → ℝ) (z : Mod k) :
    (unstrAux ψ z).ofLp 0 = z.ofLp 0 + ψ (tailVec z) := by
  rw [unstrAux_apply, consVec_apply_zero, tailVec_apply_zero, add_zero]

theorem tailVec_strAux (ψ : Mod k → ℝ) (z : Mod k) :
    tailVec (strAux ψ z) = tailVec z := by
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [tailVec_apply_zero, tailVec_apply_zero]
  · rw [tailVec_ofLp_ne_zero hi, strAux_apply, consVec_ofLp_ne_zero _ _ hi]

theorem tailVec_unstrAux (ψ : Mod k → ℝ) (z : Mod k) :
    tailVec (unstrAux ψ z) = tailVec z := by
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [tailVec_apply_zero, tailVec_apply_zero]
  · rw [tailVec_ofLp_ne_zero hi, unstrAux_apply, consVec_ofLp_ne_zero _ _ hi]

theorem unstrAux_strAux (ψ : Mod k → ℝ) (z : Mod k) :
    unstrAux ψ (strAux ψ z) = z := by
  rw [unstrAux_apply, strAux_ofLp_zero, tailVec_strAux]
  have h : z.ofLp 0 - ψ (tailVec z) + ψ (tailVec z) = z.ofLp 0 := sub_add_cancel _ _
  rw [h, consVec_tailVec]

theorem strAux_unstrAux (ψ : Mod k → ℝ) (z : Mod k) :
    strAux ψ (unstrAux ψ z) = z := by
  rw [strAux_apply, unstrAux_ofLp_zero, tailVec_unstrAux]
  have h : z.ofLp 0 + ψ (tailVec z) - ψ (tailVec z) = z.ofLp 0 := add_sub_cancel_right _ _
  rw [h, consVec_tailVec]

theorem unstrAux_mem_halfSpace {ψ : Mod k → ℝ} (hψnn : ∀ u, 0 ≤ ψ u) {z : Half k} :
    (0 : ℝ) ≤ (unstrAux ψ z.1).ofLp 0 := by
  rw [unstrAux_ofLp_zero]
  linarith [z.2, hψnn (tailVec z.1)]

end

end Work.PTGeometric
