import Submission.Work.StemsB.CollarNorm
import Submission.Work.StemsB.CubePairGeom
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.exists_relComplexMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The affine identification of the Euclidean cube with `Iⁿ × Y`

The Euclidean cube `eucCube n = {v | ∀ i, |v i| ≤ 1}` is affinely homeomorphic to the standard cube
`CubeP Y n = (Fin n → unitInterval) × Y` by `x ↦ (x+1)/2`, and the homeomorphism carries the
boundary `eucBdry n = {|v|_∞ = 1}` onto `∂Iⁿ = Cube.boundary (Fin n)`.  This file records the
resulting quasi-isomorphism of *relative* chain complexes, so that the relative Künneth theorem
`Work.StemsB.cubePair_main` can be applied to the Euclidean cube pair.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.StemsB

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y]

theorem eucCube_mem_iff (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ eucCube n ↔ ∀ i, |v i| ≤ 1 := Iff.rfl

/-- The affine map `x ↦ (x+1)/2` from the Euclidean cube to `Iⁿ`. -/
def eucToCubeP (n : ℕ) : ↥(eucCube n) → (Fin n → unitInterval) :=
  fun v i => ⟨((v.1 : EuclideanSpace ℝ (Fin n)) i + 1) / 2,
    Set.mem_Icc.mpr ⟨by linarith [(abs_le.mp (v.2 i)).1], by linarith [(abs_le.mp (v.2 i)).2]⟩⟩

/-- The affine map `t ↦ 2t - 1` from `Iⁿ` to the Euclidean cube. -/
def cubePToEuc (n : ℕ) : (Fin n → unitInterval) → ↥(eucCube n) :=
  fun x => ⟨WithLp.toLp 2 (fun i => 2 * (((x i : unitInterval)) : ℝ) - 1), fun i => by
    rw [WithLp.ofLp_toLp, abs_le]
    have h := (x i).2
    constructor <;> linarith [h.1, h.2]⟩

@[simp] theorem eucToCubeP_apply (n : ℕ) (v : ↥(eucCube n)) (i : Fin n) :
    ((eucToCubeP n v i : unitInterval) : ℝ) = ((v.1 : EuclideanSpace ℝ (Fin n)) i + 1) / 2 := rfl

@[simp] theorem cubePToEuc_apply (n : ℕ) (x : Fin n → unitInterval) (i : Fin n) :
    ((cubePToEuc n x).1 : EuclideanSpace ℝ (Fin n)) i = 2 * (((x i : unitInterval)) : ℝ) - 1 := by
  simp [cubePToEuc, WithLp.ofLp_toLp]

theorem cubePToEuc_eucToCubeP (n : ℕ) (v : ↥(eucCube n)) :
    cubePToEuc n (eucToCubeP n v) = v := by
  apply Subtype.ext
  rw [WithLp.ext_iff]
  funext i
  rw [cubePToEuc_apply, eucToCubeP_apply]
  ring

theorem eucToCubeP_cubePToEuc (n : ℕ) (x : Fin n → unitInterval) :
    eucToCubeP n (cubePToEuc n x) = x := by
  funext i
  apply Subtype.ext
  rw [eucToCubeP_apply, cubePToEuc_apply]
  ring

@[fun_prop]
theorem continuous_eucToCubeP (n : ℕ) : Continuous (eucToCubeP n) := by
  rw [continuous_pi_iff]
  intro i
  have h1 : Continuous fun v : ↥(eucCube n) => ((v.1 : EuclideanSpace ℝ (Fin n))) i :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) i).comp continuous_subtype_val
  have hmem : ∀ v : ↥(eucCube n),
      (((v.1 : EuclideanSpace ℝ (Fin n))) i + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    intro v
    have h := v.2 i
    rw [abs_le] at h
    exact Set.mem_Icc.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  change Continuous fun v : ↥(eucCube n) =>
    (⟨(((v.1 : EuclideanSpace ℝ (Fin n))) i + 1) / 2, hmem v⟩ : unitInterval)
  exact Continuous.subtype_mk ((h1.add continuous_const).div_const (2 : ℝ)) hmem

@[fun_prop]
theorem continuous_cubePToEuc (n : ℕ) : Continuous (cubePToEuc n) := by
  have hmem : ∀ x : (Fin n → unitInterval),
      (WithLp.toLp 2 (fun i : Fin n => 2 * (((x i : unitInterval)) : ℝ) - 1)) ∈ eucCube n := by
    intro x i
    rw [WithLp.ofLp_toLp, abs_le]
    have h := (x i).2
    constructor <;> linarith [h.1, h.2]
  have hcont : Continuous fun x : (Fin n → unitInterval) =>
      WithLp.toLp 2 (fun i : Fin n => 2 * (((x i : unitInterval)) : ℝ) - 1) := by
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n => ℝ)).comp ?_
    rw [continuous_pi_iff]
    intro i
    have hc : Continuous fun x : (Fin n → unitInterval) => (((x i : unitInterval)) : ℝ) :=
      continuous_subtype_val.comp (continuous_apply i)
    exact (continuous_const.mul hc).sub continuous_const
  change Continuous fun x : (Fin n → unitInterval) =>
    (⟨WithLp.toLp 2 (fun i : Fin n => 2 * (((x i : unitInterval)) : ℝ) - 1), hmem x⟩ :
      ↥(eucCube n))
  exact Continuous.subtype_mk hcont hmem

/-! ## The maps on the products -/

/-- The affine homeomorphism of the Euclidean cube with `Iⁿ × Y`. -/
def eucAffineHom (n : ℕ) :
    TopCat.of (↥(eucCube n) × Y) ⟶ TopCat.of (CubeP Y n) :=
  TopCat.ofHom ⟨fun p => (eucToCubeP n p.1, p.2), by
    exact Continuous.prodMk ((continuous_eucToCubeP n).comp continuous_fst) continuous_snd⟩

/-- Its inverse. -/
def eucAffineInvHom (n : ℕ) :
    TopCat.of (CubeP Y n) ⟶ TopCat.of (↥(eucCube n) × Y) :=
  TopCat.ofHom ⟨fun p => (cubePToEuc n p.1, p.2), by
    exact Continuous.prodMk ((continuous_cubePToEuc n).comp continuous_fst) continuous_snd⟩

@[simp] theorem eucAffineHom_apply (n : ℕ) (p : ↥(eucCube n) × Y) :
    eucAffineHom (Y := Y) n p = (eucToCubeP n p.1, p.2) := rfl

@[simp] theorem eucAffineInvHom_apply (n : ℕ) (p : CubeP Y n) :
    eucAffineInvHom (Y := Y) n p = (cubePToEuc n p.1, p.2) := rfl

theorem eucAffineHom_eucAffineInvHom (n : ℕ) :
    eucAffineHom (Y := Y) n ≫ eucAffineInvHom (Y := Y) n
      = 𝟙 (TopCat.of (↥(eucCube n) × Y)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  show (cubePToEuc n (eucToCubeP n p.1), p.2) = p
  rw [cubePToEuc_eucToCubeP]

theorem eucAffineInvHom_eucAffineHom (n : ℕ) :
    eucAffineInvHom (Y := Y) n ≫ eucAffineHom (Y := Y) n
      = 𝟙 (TopCat.of (CubeP Y n)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  show (eucToCubeP n (cubePToEuc n p.1), p.2) = p
  rw [eucToCubeP_cubePToEuc]

/-- The affine map as a homotopy equivalence of the total spaces. -/
theorem isIso_eucAffineHomology (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (↥(eucCube n) × Y)) (TopCat.of (CubeP Y n)) (eucAffineHom (Y := Y) n)) k) := by
  have h1 : TopCat.Homotopy (eucAffineHom (Y := Y) n ≫ eucAffineInvHom (Y := Y) n)
      (𝟙 (TopCat.of (↥(eucCube n) × Y))) := by
    rw [eucAffineHom_eucAffineInvHom]
    exact ContinuousMap.Homotopy.refl _
  have h2 : TopCat.Homotopy (eucAffineInvHom (Y := Y) n ≫ eucAffineHom (Y := Y) n)
      (𝟙 (TopCat.of (CubeP Y n))) := by
    rw [eucAffineInvHom_eucAffineHom]
    exact ContinuousMap.Homotopy.refl _
  exact Work.Cohomology.homologyEquiv ℤ _ _ _ _ h1 h2 k

/-! ## The boundary -/

theorem eucToCubeP_mem_boundary (n : ℕ) {v : ↥(eucCube n)}
    (hv : (v.1 : EuclideanSpace ℝ (Fin n)) ∈ eucBdry n) :
    eucToCubeP n v ∈ Cube.boundary (Fin n) := by
  obtain ⟨i, hi⟩ := hv.2
  refine ⟨i, ?_⟩
  have h := ((abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hi)
  rcases h with h | h
  · right
    apply Subtype.ext
    rw [eucToCubeP_apply, h]
    norm_num
  · left
    apply Subtype.ext
    rw [eucToCubeP_apply, h]
    norm_num

theorem cubePToEuc_mem_eucBdry (n : ℕ) {x : Fin n → unitInterval}
    (hx : x ∈ Cube.boundary (Fin n)) :
    ((cubePToEuc n x).1 : EuclideanSpace ℝ (Fin n)) ∈ eucBdry n := by
  obtain ⟨i, hi | hi⟩ := hx
  · refine ⟨fun j => (cubePToEuc n x).2 j, i, ?_⟩
    rw [cubePToEuc_apply, hi]
    norm_num
  · refine ⟨fun j => (cubePToEuc n x).2 j, i, ?_⟩
    rw [cubePToEuc_apply, hi]
    norm_num

/-- The affine map on the boundary parts. -/
def eucAffineRelHom (n : ℕ) :
    TopCat.of ↥(eucBdryProd n Y) ⟶ TopCat.of ↥(cubeBdryK Y n) :=
  TopCat.ofHom
    ⟨fun p => ⟨(eucToCubeP n p.1.1, p.1.2), eucToCubeP_mem_boundary n p.2⟩,
      by
        refine Continuous.subtype_mk (f := fun p : ↥(eucBdryProd n Y) =>
          (eucToCubeP n p.1.1, p.1.2)) ?_ (fun p => eucToCubeP_mem_boundary n p.2)
        fun_prop⟩

/-- Its inverse. -/
def eucAffineRelInvHom (n : ℕ) :
    TopCat.of ↥(cubeBdryK Y n) ⟶ TopCat.of ↥(eucBdryProd n Y) :=
  TopCat.ofHom
    ⟨fun p => ⟨(cubePToEuc n p.1.1, p.1.2), cubePToEuc_mem_eucBdry n p.2⟩,
      by
        refine Continuous.subtype_mk (f := fun p : ↥(cubeBdryK Y n) =>
          (cubePToEuc n p.1.1, p.1.2)) ?_ (fun p => cubePToEuc_mem_eucBdry n p.2)
        fun_prop⟩

theorem eucAffineRelHom_subtypeIncl (n : ℕ) :
    Work.Cohomology.subtypeIncl (TopCat.of (↥(eucCube n) × Y)) (eucBdryProd n Y)
        ≫ eucAffineHom (Y := Y) n
      = eucAffineRelHom (Y := Y) n
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (CubeP Y n)) (cubeBdryK Y n) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

theorem eucAffineRelInvHom_subtypeIncl (n : ℕ) :
    Work.Cohomology.subtypeIncl (TopCat.of (CubeP Y n)) (cubeBdryK Y n)
        ≫ eucAffineInvHom (Y := Y) n
      = eucAffineRelInvHom (Y := Y) n
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥(eucCube n) × Y)) (eucBdryProd n Y) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

theorem eucAffineRelHom_eucAffineRelInvHom (n : ℕ) :
    eucAffineRelHom (Y := Y) n ≫ eucAffineRelInvHom (Y := Y) n
      = 𝟙 (TopCat.of ↥(eucBdryProd n Y)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Subtype.val (cubePToEuc_eucToCubeP n p.1.1)
  · rfl

theorem eucAffineRelInvHom_eucAffineRelHom (n : ℕ) :
    eucAffineRelInvHom (Y := Y) n ≫ eucAffineRelHom (Y := Y) n
      = 𝟙 (TopCat.of ↥(cubeBdryK Y n)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · exact eucToCubeP_cubePToEuc n p.1.1
  · rfl

/-- The affine map as a homotopy equivalence of the relative parts. -/
theorem isIso_eucAffineRelHomology (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(eucBdryProd n Y)) (TopCat.of ↥(cubeBdryK Y n))
      (eucAffineRelHom (Y := Y) n)) k) := by
  have h1 : TopCat.Homotopy (eucAffineRelHom (Y := Y) n ≫ eucAffineRelInvHom (Y := Y) n)
      (𝟙 (TopCat.of ↥(eucBdryProd n Y))) := by
    rw [eucAffineRelHom_eucAffineRelInvHom]
    exact ContinuousMap.Homotopy.refl _
  have h2 : TopCat.Homotopy (eucAffineRelInvHom (Y := Y) n ≫ eucAffineRelHom (Y := Y) n)
      (𝟙 (TopCat.of ↥(cubeBdryK Y n))) := by
    rw [eucAffineRelInvHom_eucAffineRelHom]
    exact ContinuousMap.Homotopy.refl _
  exact Work.Cohomology.homologyEquiv ℤ _ _ _ _ h1 h2 k

/-- The chain map of relative complexes induced by the affine identification. -/
def eucAffineRelMap (n : ℕ) :
    Work.Cohomology.relChains (TopCat.of (↥(eucCube n) × Y)) (eucBdryProd n Y) ⟶
      Work.Cohomology.relChains (TopCat.of (CubeP Y n)) (cubeBdryK Y n) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (↥(eucCube n) × Y)) (TopCat.of (CubeP Y n))
    (eucBdryProd n Y) (cubeBdryK Y n) (eucAffineHom (Y := Y) n)
    (eucAffineRelHom (Y := Y) n) (eucAffineRelHom_subtypeIncl (Y := Y) n)

/-- **The affine identification is a quasi-isomorphism of the relative chain complexes.** -/
theorem isIso_eucAffineRelChains (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (eucAffineRelMap (Y := Y) n) k) :=
  Work.Cohomology.relChainsMapOf_isIso (X := TopCat.of (↥(eucCube n) × Y))
    (Y := TopCat.of (CubeP Y n)) (eucBdryProd n Y) (cubeBdryK Y n)
    (eucAffineHom (Y := Y) n) (eucAffineRelHom (Y := Y) n)
    (eucAffineRelHom_subtypeIncl (Y := Y) n) k
    (fun m => isIso_eucAffineHomology (Y := Y) n m)
    (fun m => isIso_eucAffineRelHomology (Y := Y) n m)

end

end Work.StemsB
