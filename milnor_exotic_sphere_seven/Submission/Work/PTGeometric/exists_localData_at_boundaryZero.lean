import Mathlib
import Submission.Work.PTGeometric.SourceRegionSetupBasic
import Submission.Work.PTGeometric.exists_model_tube_data_strong
import Submission.Work.PTGeometric.exists_epigraph_at_boundaryPoint
import Submission.Work.PTGeometric.regionStraightChart_exists
import Submission.Work.PTGeometric.isSubmersionAt_and_boundary_of_chartModel
import Submission.Work.PTGeometric.isOpen_setOf_injOn_gr
import Submission.Work.PTGeometric.TubeAmbientGr
import Submission.Work.PTGeometric.fderiv_tubeCoord_surjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.PTGeometric.WeakRegion

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8}


/-! ## Auxiliary lemmas about the tube chart, the padding and the straightening -/

/-- **The foot of the tube chart at a point of the embedded manifold is that point.** -/
theorem tubeFoot_e {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    tubeFoot E C (E.e x) = x := by
  show (C.inv (E.e x)).1.1 = x
  have h2 : C.inv (E.e x) = (⟨(x, 0), by simp⟩ : Work.Tubular.NormalTotal E) := by
    rw [← Work.Tubular.tubeMap_zeroSection E x]
    exact C.inv_tubeMap _ (by simpa using C.eps_pos.le)
  rw [h2]

/-- **The tube projection fixes the normal space at its foot.** -/
theorem tubeNormalProj_fixes_of_mem {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (q z : Work.Tubular.Euc (8 + k))
    (hz : z ∈ Work.Tubular.normalSpace E (tubeFoot E C q)) :
    tubeNormalProj E C q z = z := by
  show ((Work.Tubular.normalSpace E (tubeFoot E C q)).subtypeL)
      ((Work.Tubular.normalSpace E (tubeFoot E C q)).orthogonalProjectionOnto z) = z
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨z, hz⟩]
  rfl

/-- **The tube projection lands in the normal space at its foot.** -/
theorem tubeNormalProj_apply_mem_normalSpace {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (q w : Work.Tubular.Euc (8 + k)) :
    tubeNormalProj E C q w ∈ Work.Tubular.normalSpace E (tubeFoot E C q) := by
  show ((Work.Tubular.normalSpace E (tubeFoot E C q)).subtypeL)
      ((Work.Tubular.normalSpace E (tubeFoot E C q)).orthogonalProjectionOnto w) ∈ _
  exact ((Work.Tubular.normalSpace E (tubeFoot E C q)).orthogonalProjectionOnto w).2

/-- **The normal space at the foot of a point of the zero section.** -/
theorem tubeNormalProj_normalSpace_e {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Work.Tubular.normalSpace E (tubeFoot E C (E.e x))
      = Work.Tubular.normalSpace E x := by
  rw [tubeFoot_e E C x]

/-- **Injectivity on the planes in padded form.**  If `ℓ₀` is injective on the plane of the
projection `Q`, then the padded linear map `ℓ₀ ∘ projEuc` is injective on the plane of the padded
projection `padEndEuc k m hm Q`. -/
theorem padEndEuc_inj_of_fixes {k m : ℕ} (hm : 8 ≤ m) {Q : EndOp (8 + k)}
    (hQ : Q ∈ Gr (8 + k) k)
    {ℓ₀ : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    (hinj : ∀ w : EuclideanSpace ℝ (Fin (8 + k)), Q w = w → ℓ₀ w = 0 → w = 0) :
    ∀ z : Amb (k + m), padEndEuc k m hm Q z = z → ℓ₀ (projEuc k m hm z) = 0 → z = 0 := by
  intro z hz hℓ
  rw [padEndEuc_apply] at hz
  set w : EuclideanSpace ℝ (Fin (8 + k)) := Q (projEuc k m hm z) with hw
  have hQw : Q w = w := by
    rw [hw]
    exact mem_Gr_apply_apply hQ (projEuc k m hm z)
  have hℓw : ℓ₀ w = 0 := by
    have h2 : w = projEuc k m hm z := by
      rw [hw]
      have h3 := congrArg (projEuc k m hm) hz
      rwa [projEuc_padEuc] at h3
    rw [h2, hℓ]
  have hw0 : w = 0 := hinj w hQw hℓw
  rw [← hz, hw0, map_zero]

/-- **The inverse straightening is `u ↦ u + ψ (tail u) • e₀`.** -/
theorem unstrAux_eq_add_smul_eZero {k : ℕ} (ψ : Mod k → ℝ) (u : Mod k) :
    unstrAux ψ u = u + ψ (tailVec u) • eZero := by
  rw [unstrAux_apply]
  show consVec (u.ofLp 0 + ψ (tailVec u)) (tailVec u) = u + ψ (tailVec u) • eZero
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [consVec_apply_zero, PiLp.add_apply, PiLp.smul_apply, eZero_apply, tailVec_apply_zero]
    ring
  · rw [consVec_ofLp_ne_zero _ _ hi, PiLp.add_apply, PiLp.smul_apply, eZero_apply_ne hi, smul_zero,
      add_zero, tailVec_ofLp_ne_zero hi]

/-- **The inverse straightening is affine in the direction `e₀`.** -/
theorem unstrAux_add_smul_eZero {k : ℕ} (ψ : Mod k → ℝ) (u : Mod k) (t : ℝ) :
    unstrAux ψ (u + t • eZero) = unstrAux ψ u + t • eZero := by
  rw [unstrAux_eq_add_smul_eZero, unstrAux_eq_add_smul_eZero, tailVec_add_smul_eZero]
  module

/-- **The derivative of the inverse straightening in the direction `e₀`.** -/
theorem fderiv_unstrAux_eZero {k : ℕ} (ψ : Mod k → ℝ) (u : Mod k)
    (hu : DifferentiableAt ℝ (unstrAux ψ) u) :
    (fderiv ℝ (unstrAux ψ) u) eZero = eZero := by
  have hpt : u + (0 : ℝ) • (eZero : Mod k) = u := by simp
  have hc : HasDerivAt (fun t : ℝ => u + t • (eZero : Mod k)) eZero 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • (eZero : Mod k)) ((1 : ℝ) • eZero) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const eZero
    simpa using h1.const_add u
  have h1 : HasDerivAt (fun t : ℝ => unstrAux ψ (u + t • (eZero : Mod k)))
      ((fderiv ℝ (unstrAux ψ) (u + (0 : ℝ) • eZero)) eZero) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => u + t • (eZero : Mod k))
      (f' := (eZero : Mod k)) (l := unstrAux ψ)
      (l' := fderiv ℝ (unstrAux ψ) (u + (0 : ℝ) • eZero)) (0 : ℝ)
      ((hpt.symm ▸ hu).hasFDerivAt) hc
  have h2 : HasDerivAt (fun t : ℝ => unstrAux ψ u + t • (eZero : Mod k)) eZero 0 := by
    have h3 : HasDerivAt (fun t : ℝ => t • (eZero : Mod k)) ((1 : ℝ) • eZero) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const eZero
    simpa using h3.const_add (unstrAux ψ u)
  have h3 : (fun t : ℝ => unstrAux ψ (u + t • eZero))
      = fun t : ℝ => unstrAux ψ u + t • eZero :=
    funext (fun t => unstrAux_add_smul_eZero ψ u t)
  rw [h3] at h1
  exact hpt ▸ h1.unique h2

/-- **The derivative of the inverse straightening**, in explicit form. -/
theorem hasFDerivAt_unstrAux {k : ℕ} (ψ : Mod k → ℝ) (u : Mod k)
    (hu : DifferentiableAt ℝ (fun z : Mod k => ψ (tailVec z)) u) :
    HasFDerivAt (unstrAux ψ)
      ((1 : Mod k →L[ℝ] Mod k)
        + (fderiv ℝ (fun z : Mod k => ψ (tailVec z)) u).smulRight (eZero : Mod k)) u := by
  have h1 : HasFDerivAt (fun z : Mod k => z) (1 : Mod k →L[ℝ] Mod k) u := hasFDerivAt_id u
  have h2 : HasFDerivAt (fun z : Mod k => ψ (tailVec z))
      (fderiv ℝ (fun z : Mod k => ψ (tailVec z)) u) u := hu.hasFDerivAt
  have h3 : HasFDerivAt (fun z : Mod k => ψ (tailVec z) • (eZero : Mod k))
      ((fderiv ℝ (fun z : Mod k => ψ (tailVec z)) u).smulRight (eZero : Mod k)) u :=
    h2.smul_const (eZero : Mod k)
  have h4 : HasFDerivAt (fun z : Mod k => z + ψ (tailVec z) • (eZero : Mod k))
      ((1 : Mod k →L[ℝ] Mod k)
        + (fderiv ℝ (fun z : Mod k => ψ (tailVec z)) u).smulRight (eZero : Mod k)) u :=
    h1.add h3
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards with z
  exact unstrAux_eq_add_smul_eZero ψ z

/-- **The derivative of the inverse straightening is onto**: the extra term only moves the `0`-th
coordinate, so the derivative differs from the identity by a map into `ℝ • e₀`. -/
theorem surjective_fderiv_unstrAux {k : ℕ} (ψ : Mod k → ℝ) {u : Mod k}
    (hu : DifferentiableAt ℝ (fun z : Mod k => ψ (tailVec z)) u) :
    Function.Surjective (fderiv ℝ (unstrAux ψ) u) := by
  set c : Mod k →L[ℝ] ℝ := fderiv ℝ (fun z : Mod k => ψ (tailVec z)) u with hcdef
  have hf := hasFDerivAt_unstrAux ψ u hu
  have hfderiv : fderiv ℝ (unstrAux ψ) u
      = (1 : Mod k →L[ℝ] Mod k) + c.smulRight (eZero : Mod k) := by
    rw [hf.fderiv, ← hcdef]
  rw [hfderiv]
  have hczero : c (eZero : Mod k) = 0 := by
    have hpt : u + (0 : ℝ) • (eZero : Mod k) = u := by simp
    have hc : HasDerivAt (fun t : ℝ => u + t • (eZero : Mod k)) (eZero : Mod k) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • (eZero : Mod k)) ((1 : ℝ) • eZero) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const (eZero : Mod k)
      simpa using h1.const_add u
    have hder : HasDerivAt (fun t : ℝ => (fun z : Mod k => ψ (tailVec z)) (u + t • eZero))
        ((fderiv ℝ (fun z : Mod k => ψ (tailVec z)) (u + (0 : ℝ) • eZero)) eZero) 0 :=
      HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => u + t • (eZero : Mod k))
        (f' := (eZero : Mod k)) (l := fun z : Mod k => ψ (tailVec z))
        (l' := fderiv ℝ (fun z : Mod k => ψ (tailVec z)) (u + (0 : ℝ) • eZero))
        (0 : ℝ) ((hpt.symm ▸ hu).hasFDerivAt) hc
    have hconst : (fun t : ℝ => (fun z : Mod k => ψ (tailVec z)) (u + t • eZero))
        = fun _ : ℝ => ψ (tailVec u) := by
      funext t
      show ψ (tailVec (u + t • (eZero : Mod k))) = ψ (tailVec u)
      rw [tailVec_add_smul_eZero]
    rw [hconst] at hder
    have hfin := hder.unique (hasDerivAt_const (0 : ℝ) (ψ (tailVec u)))
    simpa [hcdef, hpt] using hfin
  have hLapp : ∀ v : Mod k,
      ((1 : Mod k →L[ℝ] Mod k) + c.smulRight (eZero : Mod k)) v = v + c v • eZero := by
    intro v
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smulRight_apply]
  intro w
  refine ⟨consVec (w.ofLp 0 - c (tailVec w)) (tailVec w), ?_⟩
  have hval : c (consVec (w.ofLp 0 - c (tailVec w)) (tailVec w)) = c (tailVec w) := by
    rw [show consVec (w.ofLp 0 - c (tailVec w)) (tailVec w)
        = tailVec w + (w.ofLp 0 - c (tailVec w)) • (eZero : Mod k) from rfl,
      map_add, map_smul, hczero, smul_zero, add_zero]
  rw [hLapp, hval]
  rw [show consVec (w.ofLp 0 - c (tailVec w)) (tailVec w)
      = tailVec w + (w.ofLp 0 - c (tailVec w)) • (eZero : Mod k) from rfl,
    add_assoc, ← add_smul, sub_add_cancel]
  exact consVec_tailVec w

/-- The identity chart of the half-space is a chart of its maximal atlas. -/
theorem idPH_mem_maximalAtlas (k : ℕ) :
    Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH (Half k)
      ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (8 + k + 1))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (Half k) := by
  have h : Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH (Half k)
      = OpenPartialHomeomorph.refl (Half k) := by
    ext x <;> rfl
  rw [h]
  exact IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) (0 : Half k)

/-- The identity partial homeomorphism of the half-space is a chart of its maximal atlas. -/
theorem refl_mem_maximalAtlas (k : ℕ) :
    OpenPartialHomeomorph.refl (Half k)
      ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (8 + k + 1))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (Half k) := by
  have h : OpenPartialHomeomorph.refl (Half k) = chartAt (Half k) (0 : Half k) := rfl
  rw [h]
  exact IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) (0 : Half k)

/-! ## The pointwise local datum at a boundary zero -/

theorem exists_localData_at_boundaryZero {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
      (Work.PTGeometric.sourceZeroSet G m hpow)
      (Work.PTGeometric.sourceBasepoint (D := D) (Fam := Fam) G m hpow))
    (hweak : ∀ y : EuclideanHalfSpace ((8 + k) + 1),
      Work.PTGeometric.sourcePhi G m hpow hphi y = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) (Work.PTGeometric.sourcePhi G m hpow hphi) y ≠ 0)
    (hne : ∀ y : (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region,
      Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1 ≠ D.t₀)
    (x : (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary
      (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region)
    (hvx : (G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ x.1.1, hne x⟩).2 = 0) :
    ∃ (ℓ : Work.PTGeometric.Amb (k + G.mU) →L[ℝ] Work.PTGeometric.Amb k)
      (U : Set (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region),
      IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior {y : (Work.PTGeometric.sourceRegionSetup
          (D := D) (Fam := Fam) G m hpow hphi hweak).Region | y.1.1 0 ≤ 1 / 4} ∧
      (∀ y ∈ closure U, ∀ z : Work.PTGeometric.Amb (k + G.mU),
        (G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1, hne y⟩).1 z = z →
        ℓ z = 0 → z = 0) ∧
      (∀ y ∈ U, ∀ (hy : y ∈ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary
          (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region),
        (G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1, hne y⟩).2 = 0 →
        Manifold.IsSubmersionAt (modelWithCornersEuclideanHalfSpace (8 + k + 1))
          (modelWithCornersSelf ℝ (Work.PTGeometric.Amb k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region =>
            ℓ ((G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1, hne y⟩).2)) y ∧
        Manifold.IsSubmersionAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (8 + k))))
          (modelWithCornersSelf ℝ (Work.PTGeometric.Amb k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : ↥((modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary
            (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region) =>
            ℓ ((G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1.1,
                hne y.1⟩).2)) ⟨y, hy⟩) := by
  classical
  haveI : NeZero ((8 + k) + 1) := ⟨by omega⟩
  let S : Work.PTGeometric.WeakRegion.RegionSetupWeak k :=
    Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak
  let Hf : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → D.T :=
    Work.PTGeometric.flatSourceHomotopy8 (k := k)
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ
  let v : S.Region → Amb (k + G.mU) := fun y => (G.coord ⟨Hf y.1.1, hne y⟩).2
  let P : S.Region → EndOp (k + G.mU) := fun y => (G.coord ⟨Hf y.1.1, hne y⟩).1
  -- ### Step 0: `x` is a boundary point of the half space
  have hx0 : x.1.1 0 = 0 := by
    have hcore : Hf x.1.1 ∈ G.core := (G.core_iff_vec ⟨Hf x.1.1, hne x⟩).mpr hvx
    have hmemb : x ∈ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary S.Region := hxb
    rw [S.mem_boundary_iff] at hmemb
    rcases hmemb with h | h
    · exact ((Work.PTGeometric.mem_boundary_halfSpace_iff ((8 + k) + 1)).mp h)
    · exact (Work.PTGeometric.sourcePhi_spec G m hpow hphi).2.2.2.2.1 ⟨hcore, h⟩
  have hcore : Hf x.1.1 ∈ G.core := (G.core_iff_vec ⟨Hf x.1.1, hne x⟩).mpr hvx
  -- ### Step 1: the tube model at `x`
  obtain ⟨i, z, ℓ₀, W, p, hWopen, hy₀W, hpsm, hptube, hpz, hℓ₀inj, hpsurj, hpkill, hcoord⟩ :=
    Work.PTGeometric.exists_model_tube_data_strong (D := D) (Fam := Fam) G m hpow x.1.1 hx0 hcore
  -- ### Step 2: the epigraph description of the region at `x`
  obtain ⟨ψ, Wψ, Vψ, hWψopen, htailx, hψsmW, hψnnW, hψ0, hVψopen, hxVψ, hVψsub, hepi⟩ :=
    Work.PTGeometric.exists_epigraph_at_boundaryPoint (D := D) (Fam := Fam) G m hpow hphi x.1 x.2 hx0
  -- ### Step 3: a globally nonnegative variant of `ψ`
  have hVψnn : ∀ z ∈ Vψ, 0 ≤ ψ (tailVec z) := fun z hz => hψnnW (tailVec z) (hVψsub hz)
  let ψv : Mod k → ℝ := fun u => max (ψ u) 0
  have hψv_eq : ∀ z ∈ Vψ, ψv (tailVec z) = ψ (tailVec z) := by
    intro z hz
    show max (ψ (tailVec z)) 0 = ψ (tailVec z)
    exact max_eq_left (hVψnn z hz)
  have hψv_nn : ∀ u : Mod k, 0 ≤ ψv u := fun u => le_max_right _ _
  have hψv_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mod k => ψv (tailVec z)) Vψ :=
    (hψsmW.comp contDiff_tailVec.contDiffOn (fun z hz => hVψsub hz)).congr
      (fun z hz => hψv_eq z hz)
  have hepi' : ∀ (zz : Mod k) (hzV : zz ∈ Vψ) (hz : 0 ≤ zz.ofLp 0),
      (S.Φ ((OpenPartialHomeomorph.refl (Half k)).symm ⟨zz, hz⟩) ≤ 0 ↔
        ψv (tailVec zz) ≤ zz.ofLp 0) := by
    intro zz hzV hz
    have h := hepi zz hzV hz
    rw [← hψv_eq zz hzV] at h
    exact h
  -- ### Step 4: the straightening chart of the region
  obtain ⟨e, he_mem, hxe_src, he_form, he_symm_form⟩ :=
    Work.PTGeometric.regionStraightChart_exists S
      (OpenPartialHomeomorph.refl (Half k))
      (refl_mem_maximalAtlas k) ψv Vψ hVψopen x (Set.mem_univ _) hxVψ hepi' hψv_nn hψv_sm
  -- ### Step 5: the padded linear map
  let ℓ : Amb (k + G.mU) →L[ℝ] Amb k := ℓ₀.comp (projEuc k G.mU G.hmU)
  have hPx : P x = padEndEuc k G.mU G.hmU (tubeNormalProj (G.emb i) (G.chart i) (p x.1.1)) :=
    congrArg Prod.fst (hcoord x.1.1 hy₀W (hne x))
  have hfootx : tubeFoot (G.emb i) (G.chart i) (p x.1.1) = z := by
    rw [hpz]
    exact tubeFoot_e (G.emb i) (G.chart i) z
  have hinj_x : ∀ zz : Amb (k + G.mU), P x zz = zz → ℓ zz = 0 → zz = 0 := by
    rw [hPx]
    refine padEndEuc_inj_of_fixes G.hmU
      (tubeNormalProj_mem_Gr (G.emb i) (G.chart i) (p x.1.1)) ?_
    intro w hw hw0
    have hmem : w ∈ Work.Tubular.normalSpace (G.emb i) z := by
      have h1 : w ∈ Work.Tubular.normalSpace (G.emb i)
          (tubeFoot (G.emb i) (G.chart i) (p x.1.1)) := by
        rw [← hw]
        exact tubeNormalProj_apply_mem_normalSpace (G.emb i) (G.chart i) (p x.1.1) w
      rwa [hfootx] at h1
    exact hℓ₀inj w hmem hw0
  -- ### Step 6: continuity of the ambient field
  have hbase : Continuous fun y : S.Region => Hf y.1.1 :=
    (Work.PTGeometric.continuous_flatSourceHomotopy8 k
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hcont_coord : Continuous fun y : S.Region =>
      (⟨Hf y.1.1, hne y⟩ : {zz : D.T // zz ≠ D.t₀}) :=
    hbase.subtype_mk (fun y => hne y)
  have hPc : Continuous P := (G.continuous_coord.comp hcont_coord).fst
  -- ### Step 7: the open sets and the neighbourhood `U`
  have hcontval : Continuous fun y : S.Region =>
      (y.1.1 : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hcoord0 : Continuous fun y : S.Region => (y.1.1 0 : ℝ) :=
    ((continuous_apply (0 : Fin ((8 + k) + 1))).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin ((8 + k) + 1) => ℝ)).continuous).comp
      hcontval
  have hUinj_open : IsOpen {y : S.Region | ∀ zz : Amb (k + G.mU), P y zz = zz → ℓ zz = 0 → zz = 0} :=
    isOpen_setOf_injOn_gr ℓ hPc (fun y => G.coord_isProj ⟨Hf y.1.1, hne y⟩)
  have hquarter_open : IsOpen {y : S.Region | y.1.1 0 < 1 / 4} :=
    isOpen_lt hcoord0 continuous_const
  have hW_open : IsOpen {y : S.Region | y.1.1 ∈ W} := hWopen.preimage hcontval
  have hVψ_open : IsOpen {y : S.Region | y.1.1 ∈ Vψ} := hVψopen.preimage hcontval
  let Vall : Set S.Region := {y : S.Region | ∀ zz : Amb (k + G.mU), P y zz = zz → ℓ zz = 0 → zz = 0} ∩
      {y : S.Region | y.1.1 0 < 1 / 4} ∩ {y : S.Region | y.1.1 ∈ W} ∩ {y : S.Region | y.1.1 ∈ Vψ} ∩
      e.source
  have hVall_open : IsOpen Vall :=
    (((hUinj_open.inter hquarter_open).inter hW_open).inter hVψ_open).inter e.open_source
  have hxquarter : x.1.1 0 < 1 / 4 := by rw [hx0]; norm_num
  have hxVall : x ∈ Vall :=
    ⟨⟨⟨⟨hinj_x, hxquarter⟩, hy₀W⟩, hxVψ⟩, hxe_src⟩
  obtain ⟨U, hUopen, hxU, hUcl⟩ :=
    normal_exists_closure_subset (isClosed_singleton (x := x)) hVall_open
      (singleton_subset_iff.mpr hxVall)
  refine ⟨ℓ, U, hUopen, hxU (Set.mem_singleton x), ?_, ?_, ?_⟩
  · -- the closure stays inside the collar
    refine (hUcl.trans ?_)
    intro y hy
    have hsub : {y : S.Region | y.1.1 0 < 1 / 4} ⊆ {y : S.Region | y.1.1 0 ≤ 1 / 4} := by
      intro zz hz
      have hz' : zz.1.1 0 < 1 / 4 := by simpa using hz
      simpa using le_of_lt hz'
    exact interior_maximal hsub hquarter_open hy.1.1.1.2
  · -- injectivity on the planes
    intro y hy zz hz hz0
    exact (hUcl hy).1.1.1.1 zz hz hz0
  · -- submersivity
    intro y hyU hyb hvy
    have hyUcl : y ∈ closure U := subset_closure hyU
    have hyin : ∀ zz : Amb (k + G.mU), P y zz = zz → ℓ zz = 0 → zz = 0 := (hUcl hyUcl).1.1.1.1
    have hyW : y.1.1 ∈ W := (hUcl hyUcl).1.1.2
    have hyVψ : y.1.1 ∈ Vψ := (hUcl hyUcl).1.2
    have hye : y ∈ e.source := (hUcl hyUcl).2
    have hcoordy := hcoord y.1.1 hyW (hne y)
    have hPy : P y = padEndEuc k G.mU G.hmU (tubeNormalProj (G.emb i) (G.chart i) (p y.1.1)) :=
      congrArg Prod.fst hcoordy
    have hvy0 : tubeNormalCoord (G.emb i) (G.chart i) (p y.1.1) = 0 := by
      have hs : (G.coord ⟨Hf y.1.1, hne y⟩).2
          = padEuc k G.mU G.hmU (tubeNormalCoord (G.emb i) (G.chart i) (p y.1.1)) :=
        congrArg Prod.snd hcoordy
      have h1 : padEuc k G.mU G.hmU (tubeNormalCoord (G.emb i) (G.chart i) (p y.1.1)) = 0 :=
        hs ▸ hvy
      exact padEuc_injective k G.mU G.hmU (by rw [h1, map_zero])
    have hinj_y : ∀ (x' : (Fam i).pt), (G.emb i).e x' = p y.1.1 →
        ∀ w ∈ Work.Tubular.normalSpace (G.emb i) x', ℓ₀ w = 0 → w = 0 := by
      intro x' hx' w hw hw0
      have hν : Work.Tubular.normalSpace (G.emb i)
          (tubeFoot (G.emb i) (G.chart i) ((G.emb i).e x'))
          = Work.Tubular.normalSpace (G.emb i) x' :=
        tubeNormalProj_normalSpace_e (G.emb i) (G.chart i) x'
      have hfix : tubeNormalProj (G.emb i) (G.chart i) (p y.1.1) w = w := by
        rw [← hx']
        exact tubeNormalProj_fixes_of_mem (G.emb i) (G.chart i) ((G.emb i).e x') w
          (hν.symm ▸ hw)
      have hpad : padEndEuc k G.mU G.hmU (tubeNormalProj (G.emb i) (G.chart i) (p y.1.1))
          (padEuc k G.mU G.hmU w) = padEuc k G.mU G.hmU w := by
        rw [padEndEuc_apply, projEuc_padEuc, hfix]
      have hℓpad : ℓ (padEuc k G.mU G.hmU w) = 0 := by
        show ℓ₀ (projEuc k G.mU G.hmU (padEuc k G.mU G.hmU w)) = 0
        rw [projEuc_padEuc, hw0]
      have h0 := hyin (padEuc k G.mU G.hmU w) (by rw [hPy]; exact hpad) hℓpad
      exact padEuc_injective k G.mU G.hmU (by rw [h0, map_zero])
    have hsurj_y : Function.Surjective
        (fderiv ℝ (fun zz : Mod k => ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p zz))) y.1.1) :=
      Work.PTGeometric.fderiv_tubeCoord_surjective (G.emb i) (G.chart i) ℓ₀ hWopen hpsm hpsurj hyW
        (hptube y.1.1 hyW) hvy0 hinj_y
    let Gfun : Mod k → Amb k := fun zz => ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p zz))
    let gfun : Mod k → Amb k :=
      fun u => ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p (unstrAux ψv u)))
    have hGfun_surj : Function.Surjective (fderiv ℝ Gfun y.1.1) := hsurj_y
    -- differentiability of `Gfun`
    have hp_diff : HasFDerivAt p (fderiv ℝ p y.1.1) y.1.1 :=
      ((hpsm.contDiffAt (hWopen.mem_nhds hyW)).differentiableAt (by simp)).hasFDerivAt
    have htnc_diff : HasFDerivAt (tubeNormalCoord (G.emb i) (G.chart i))
        (fderiv ℝ (tubeNormalCoord (G.emb i) (G.chart i)) (p y.1.1)) (p y.1.1) := by
      have hcd := (contMDiffOn_iff_contDiffOn).mp
        (Work.PTGeometric.contMDiffOn_tubeNormalCoord (G.emb i) (G.chart i))
      exact ((hcd.contDiffAt ((G.chart i).openTube_isOpen.mem_nhds (hptube y.1.1 hyW))).differentiableAt
        (by simp)).hasFDerivAt
    have hGfun_full : HasFDerivAt Gfun
        (ℓ₀.comp ((fderiv ℝ (tubeNormalCoord (G.emb i) (G.chart i)) (p y.1.1)).comp
          (fderiv ℝ p y.1.1))) y.1.1 :=
      (ContinuousLinearMap.hasFDerivAt ℓ₀).comp y.1.1 (htnc_diff.comp y.1.1 hp_diff)
    have hGfun_diff : HasFDerivAt Gfun (fderiv ℝ Gfun y.1.1) y.1.1 :=
      hGfun_full.fderiv.symm ▸ hGfun_full
    have hGfun_eZero : (fderiv ℝ Gfun y.1.1) eZero = 0 := by
      rw [hGfun_full.fderiv]
      show ℓ₀ ((fderiv ℝ (tubeNormalCoord (G.emb i) (G.chart i)) (p y.1.1))
        ((fderiv ℝ p y.1.1) eZero)) = 0
      have hp0 : (fderiv ℝ p y.1.1) eZero = 0 := hpkill y.1.1 hyW
      rw [hp0, map_zero, map_zero]
    -- smoothness of the inverse straightening
    have hψvtail_sm : ContDiffOn ℝ ∞ (fun z : Mod k => ψv (tailVec z)) (tailVec ⁻¹' Wψ) :=
      (hψsmW.comp contDiff_tailVec.contDiffOn (fun z hz => hz)).congr
        (fun z hz => by
          show max (ψ (tailVec z)) 0 = ψ (tailVec z)
          exact max_eq_left (hψnnW (tailVec z) hz))
    have hunstrAux_sm : ContDiffOn ℝ ∞ (unstrAux ψv) (tailVec ⁻¹' Wψ) := by
      have h1 : ContDiffOn ℝ ∞ (fun u : Mod k => u + ψv (tailVec u) • eZero) (tailVec ⁻¹' Wψ) :=
        ContDiffOn.add contDiffOn_id (ContDiffOn.smul hψvtail_sm contDiffOn_const)
      refine h1.congr ?_
      intro u _
      exact unstrAux_eq_add_smul_eZero ψv u
    -- the base point of the chart
    have hu₀ : (e.extend (𝓡∂ (8 + k + 1))) y = strAux ψv y.1.1 := by
      have h1 : (e.extend (𝓡∂ (8 + k + 1))) y = (e y).1 := by
        rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
          modelWithCornersEuclideanHalfSpace_apply]
      have h2 : (e y).1 = strAux ψv y.1.1 := he_form y hye
      rw [h1, h2]
    have hg_unstr : unstrAux ψv ((e.extend (𝓡∂ (8 + k + 1))) y) = y.1.1 := by
      rw [hu₀, unstrAux_strAux]
    have hu₀W : unstrAux ψv ((e.extend (𝓡∂ (8 + k + 1))) y) ∈ W := by
      rw [hg_unstr]
      exact hyW
    have hu₀tail : tailVec ((e.extend (𝓡∂ (8 + k + 1))) y) ∈ Wψ := by
      rw [hu₀, tailVec_strAux]
      exact hVψsub hyVψ
    have hunstrAux_contAt : ContinuousAt (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y) :=
      (hunstrAux_sm.contDiffAt ((hWψopen.preimage continuous_tailVec).mem_nhds hu₀tail)).continuousAt
    have hunstrAux_diff : DifferentiableAt ℝ (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y) :=
      (hunstrAux_sm.differentiableOn (by simp)).differentiableAt
        ((hWψopen.preimage continuous_tailVec).mem_nhds hu₀tail)
    have hψvtail_diff : DifferentiableAt ℝ (fun z : Mod k => ψv (tailVec z))
        ((e.extend (𝓡∂ (8 + k + 1))) y) :=
      (hψvtail_sm.differentiableOn (by simp)).differentiableAt
        ((hWψopen.preimage continuous_tailVec).mem_nhds hu₀tail)
    -- ### the model function
    have hgg : ∃ Ug ∈ 𝓝 ((e.extend (𝓡∂ (8 + k + 1))) y), ContDiffOn ℝ ∞ gfun Ug := by
      refine ⟨(tailVec ⁻¹' Wψ) ∩ (unstrAux ψv ⁻¹' W), Filter.inter_mem
        ((hWψopen.preimage continuous_tailVec).mem_nhds hu₀tail)
        (hunstrAux_contAt.preimage_mem_nhds (hWopen.mem_nhds hu₀W)), ?_⟩
      have h1 : ContDiffOn ℝ ∞ (unstrAux ψv) ((tailVec ⁻¹' Wψ) ∩ (unstrAux ψv ⁻¹' W)) :=
        hunstrAux_sm.mono (fun u hu => hu.1)
      have h2 : ContDiffOn ℝ ∞ (fun u => p (unstrAux ψv u))
          ((tailVec ⁻¹' Wψ) ∩ (unstrAux ψv ⁻¹' W)) :=
        hpsm.comp h1 (fun u hu => hu.2)
      have h3 : ContDiffOn ℝ ∞ (fun u => tubeNormalCoord (G.emb i) (G.chart i) (p (unstrAux ψv u)))
          ((tailVec ⁻¹' Wψ) ∩ (unstrAux ψv ⁻¹' W)) :=
        ((contMDiffOn_iff_contDiffOn).mp
          (Work.PTGeometric.contMDiffOn_tubeNormalCoord (G.emb i) (G.chart i))).comp h2
          (fun u hu => hptube _ hu.2)
      exact (ℓ₀.contDiff.contDiffOn).comp h3 (fun _ _ => Set.mem_univ _)
    -- ### the chain rule
    have hGfun_diff' : HasFDerivAt Gfun (fderiv ℝ Gfun y.1.1)
        (unstrAux ψv ((e.extend (𝓡∂ (8 + k + 1))) y)) := by
      rw [hg_unstr]
      exact hGfun_diff
    have hgfun_diff : HasFDerivAt gfun
        ((fderiv ℝ Gfun y.1.1).comp (fderiv ℝ (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y)))
        ((e.extend (𝓡∂ (8 + k + 1))) y) :=
      hGfun_diff'.comp _ hunstrAux_diff.hasFDerivAt
    have hgfun_fderiv : fderiv ℝ gfun ((e.extend (𝓡∂ (8 + k + 1))) y)
        = (fderiv ℝ Gfun y.1.1).comp (fderiv ℝ (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y)) :=
      hgfun_diff.fderiv
    have hsurjg : Function.Surjective (fderiv ℝ gfun ((e.extend (𝓡∂ (8 + k + 1))) y)) := by
      rw [hgfun_fderiv]
      show Function.Surjective ((fderiv ℝ Gfun y.1.1)
        ∘ (fderiv ℝ (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y)))
      exact Function.Surjective.comp hGfun_surj (surjective_fderiv_unstrAux ψv hψvtail_diff)
    have hnormg : ∃ vv : Mod k, (fderiv ℝ gfun ((e.extend (𝓡∂ (8 + k + 1))) y)) vv = 0 ∧ vv 0 ≠ 0 := by
      refine ⟨eZero, ?_, by rw [eZero_apply]; norm_num⟩
      rw [hgfun_fderiv]
      show (fderiv ℝ Gfun y.1.1)
        ((fderiv ℝ (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y)) eZero) = 0
      rw [fderiv_unstrAux_eZero ψv _ hunstrAux_diff, hGfun_eZero]
    -- ### the agreement of the two maps near `y`
    have hagree : (fun y' : S.Region => ℓ (v y')) =ᶠ[𝓝 y]
        (fun y' : S.Region => gfun ((e.extend (𝓡∂ (8 + k + 1))) y')) := by
      refine Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨e.source ∩ {y' : S.Region | y'.1.1 ∈ W}, ?_, ?_⟩
      · exact Filter.inter_mem (e.open_source.mem_nhds hye) (hW_open.mem_nhds hyW)
      · intro y' hy'
        rcases hy' with ⟨hy'e, hy'W⟩
        have h1 : (e.extend (𝓡∂ (8 + k + 1))) y' = strAux ψv y'.1.1 := by
          have h1a : (e.extend (𝓡∂ (8 + k + 1))) y' = (e y').1 := by
            rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
              modelWithCornersEuclideanHalfSpace_apply]
          have h1b : (e y').1 = strAux ψv y'.1.1 := he_form y' hy'e
          rw [h1a, h1b]
        have h2 : gfun ((e.extend (𝓡∂ (8 + k + 1))) y')
            = ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p y'.1.1)) := by
          show ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i)
            (p (unstrAux ψv ((e.extend (𝓡∂ (8 + k + 1))) y')))) = _
          rw [h1, unstrAux_strAux]
        have hv' : v y' = padEuc k G.mU G.hmU
            (tubeNormalCoord (G.emb i) (G.chart i) (p y'.1.1)) :=
          congrArg Prod.snd (hcoord y'.1.1 hy'W (hne y'))
        have h3 : ℓ (v y') = ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p y'.1.1)) := by
          calc ℓ (v y') = ℓ₀ (projEuc k G.mU G.hmU (v y')) := rfl
            _ = ℓ₀ (projEuc k G.mU G.hmU (padEuc k G.mU G.hmU
                  (tubeNormalCoord (G.emb i) (G.chart i) (p y'.1.1)))) := by rw [hv']
            _ = ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p y'.1.1)) := by rw [projEuc_padEuc]
        show ℓ (v y') = gfun ((e.extend (𝓡∂ (8 + k + 1))) y')
        rw [h2, h3]
    exact isSubmersionAt_and_boundary_of_chartModel (n := 8 + k) he_mem hye hyb hgg hagree hsurjg hnormg


end

end Work.PTGeometric
