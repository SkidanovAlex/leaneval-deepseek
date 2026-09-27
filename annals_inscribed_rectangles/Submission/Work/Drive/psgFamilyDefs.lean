import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.coreMeet_ncard_eq_famMeet_gen
import Submission.Work.Drive.germHavoidLoop
import Submission.Work.Drive.germHavoidZc
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.odd_ncard_famMeet_iff
import Submission.Work.Drive.genericRegularizationSquare
import Submission.Work.Drive.avoid_zeroSet_open
import Submission.Work.Drive.meetBoxEngine
import Submission.Work.Drive.geometricLocality

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

variable {m : ℕ}

/-! ## The path family of the parity-locality lemma -/

/-- The `C^∞` ramp `0` on `(-∞,1/3]` and `1` on `[2/3,∞)`. -/
def psgRamp (s : ℝ) : ℝ := Real.smoothTransition (3 * (s - 1 / 3))

lemma psgRamp_zero_of_le {s : ℝ} (hs : s ≤ 1 / 3) : psgRamp s = 0 := by
  rw [psgRamp, Real.smoothTransition.zero_of_nonpos]
  linarith

lemma psgRamp_one_of_le {s : ℝ} (hs : 2 / 3 ≤ s) : psgRamp s = 1 := by
  rw [psgRamp, Real.smoothTransition.one_of_one_le]
  linarith

lemma psgRamp_nonneg (s : ℝ) : 0 ≤ psgRamp s := Real.smoothTransition.nonneg _

lemma psgRamp_le_one (s : ℝ) : psgRamp s ≤ 1 := Real.smoothTransition.le_one _

lemma psgRamp_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psgRamp :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

@[simp] lemma psgRamp_zero : psgRamp 0 = 0 := psgRamp_zero_of_le (by norm_num)

@[simp] lemma psgRamp_one : psgRamp 1 = 1 := psgRamp_one_of_le (by norm_num)

/-- The loop chart parameter along the ramped path from `A.1` to `B.1`. -/
def psgPathL (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  (1 - psgRamp s) • A.1 + psgRamp s • B.1

/-- The sweep chart parameter along the ramped path from `A.2` to `B.2`. -/
def psgPathR (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  (1 - psgRamp s) • A.2 + psgRamp s • B.2

@[simp] lemma psgPathL_zero (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    psgPathL A B 0 = A.1 := by simp [psgPathL]

@[simp] lemma psgPathR_zero (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    psgPathR A B 0 = A.2 := by simp [psgPathR]

@[simp] lemma psgPathL_one (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    psgPathL A B 1 = B.1 := by simp [psgPathL]

@[simp] lemma psgPathR_one (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    psgPathR A B 1 = B.2 := by simp [psgPathR]

lemma psgPathL_zero_of_le (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) {s : ℝ}
    (hs : s ≤ 1 / 3) : psgPathL A B s = A.1 := by
  simp [psgPathL, psgRamp_zero_of_le hs]

lemma psgPathR_zero_of_le (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) {s : ℝ}
    (hs : s ≤ 1 / 3) : psgPathR A B s = A.2 := by
  simp [psgPathR, psgRamp_zero_of_le hs]

lemma psgPathL_one_of_le (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) {s : ℝ}
    (hs : 2 / 3 ≤ s) : psgPathL A B s = B.1 := by
  simp [psgPathL, psgRamp_one_of_le hs]

lemma psgPathR_one_of_le (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) {s : ℝ}
    (hs : 2 / 3 ≤ s) : psgPathR A B s = B.2 := by
  simp [psgPathR, psgRamp_one_of_le hs]

/-- A convex combination of two vectors is bounded by the max of their norms. -/
lemma norm_smul_combo_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • a + t • b‖ ≤ max ‖a‖ ‖b‖ := by
  have h1 : 0 ≤ 1 - t := by linarith
  have h2 : (1 - t) + t = 1 := by ring
  have hle1 : ‖(1 - t) • a‖ = (1 - t) * ‖a‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h1]
  have hle2 : ‖t • b‖ = t * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  calc ‖(1 - t) • a + t • b‖ ≤ ‖(1 - t) • a‖ + ‖t • b‖ := norm_add_le _ _
    _ = (1 - t) * ‖a‖ + t * ‖b‖ := by rw [hle1, hle2]
    _ ≤ (1 - t) * max ‖a‖ ‖b‖ + t * max ‖a‖ ‖b‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h1)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) ht0)
    _ = max ‖a‖ ‖b‖ := by rw [← add_mul, h2, one_mul]

lemma norm_psgPathL_le (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (s : ℝ) : ‖psgPathL A B s‖ ≤ max ‖A.1‖ ‖B.1‖ :=
  norm_smul_combo_le A.1 B.1 (psgRamp_nonneg s) (psgRamp_le_one s)

lemma norm_psgPathR_le (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (s : ℝ) : ‖psgPathR A B s‖ ≤ max ‖A.2‖ ‖B.2‖ :=
  norm_smul_combo_le A.2 B.2 (psgRamp_nonneg s) (psgRamp_le_one s)

/-- The real lift of the angle along the ramped path. -/
def psgAngle (tA tB : ℝ) (s : ℝ) : ℝ := (1 - psgRamp s) * tA + psgRamp s * tB

@[simp] lemma psgAngle_zero (tA tB : ℝ) : psgAngle tA tB 0 = tA := by simp [psgAngle]

@[simp] lemma psgAngle_one (tA tB : ℝ) : psgAngle tA tB 1 = tB := by simp [psgAngle]

lemma psgAngle_zero_of_le (tA tB : ℝ) {s : ℝ} (hs : s ≤ 1 / 3) : psgAngle tA tB s = tA := by
  simp [psgAngle, psgRamp_zero_of_le hs]

lemma psgAngle_one_of_le (tA tB : ℝ) {s : ℝ} (hs : 2 / 3 ≤ s) : psgAngle tA tB s = tB := by
  simp [psgAngle, psgRamp_one_of_le hs]

/-- The class of the lifted angle along the path. -/
def psgAngleClass (tA tB : ℝ) (s : ℝ) : UnitAddCircle := ((psgAngle tA tB s : ℝ) : UnitAddCircle)

lemma psgAngleClass_zero (tA tB : ℝ) : psgAngleClass tA tB 0 = ((tA : ℝ) : UnitAddCircle) := by
  simp [psgAngleClass]

lemma psgAngleClass_one (tA tB : ℝ) : psgAngleClass tA tB 1 = ((tB : ℝ) : UnitAddCircle) := by
  simp [psgAngleClass]

lemma psgAngleClass_zero_of_le (tA tB : ℝ) {s : ℝ} (hs : s ≤ 1 / 3) :
    psgAngleClass tA tB s = ((tA : ℝ) : UnitAddCircle) := by
  simp [psgAngleClass, psgAngle_zero_of_le tA tB hs]

lemma psgAngleClass_one_of_le (tA tB : ℝ) {s : ℝ} (hs : 2 / 3 ≤ s) :
    psgAngleClass tA tB s = ((tB : ℝ) : UnitAddCircle) := by
  simp [psgAngleClass, psgAngle_one_of_le tA tB hs]

/-- **A real lift of a point of the circle, within a prescribed distance of a prescribed lift.**  If
`((wt : ℝ) : UnitAddCircle) = w` and `dist w' w < δ ≤ 1/2`, then `w'` has a real lift `t` with
`|t - wt| = dist w' w`. -/
lemma exists_lift_dist_eq {w w' : UnitAddCircle} {wt δ : ℝ}
    (hw : ((wt : ℝ) : UnitAddCircle) = w) (hδ : dist w' w < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ t : ℝ, ((t : ℝ) : UnitAddCircle) = w' ∧ |t - wt| = dist w' w := by
  classical
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective w'
  set k : ℤ := round (s - wt) with hk
  refine ⟨s - (k : ℝ), ?_, ?_⟩
  · rw [← hs, AddCircle.coe_sub]
    have hk0 : (((k : ℝ) : UnitAddCircle)) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨k, by simp⟩
    rw [hk0, sub_zero]
  · have hdist : dist w' w = ‖(((s - wt : ℝ)) : UnitAddCircle)‖ := by
      rw [dist_eq_norm, ← hs, ← hw, ← AddCircle.coe_sub]
    rw [hdist, AddCircle.norm_eq, inv_one, one_mul, ← hk]
    congr 1
    ring

/-- The `c`-form of the class of a lifted angle: `psgAngleClass tA tB s` is the class of the affine
combination of the two lifted angles. -/
lemma psgAngleClass_apply (tA tB : ℝ) (s : ℝ) :
    psgAngleClass tA tB s = (((1 - psgRamp s) * tA + psgRamp s * tB : ℝ) : UnitAddCircle) := rfl

/-- **The interpolated angle stays within the max of the two endpoint distances of the base angle.** -/
lemma dist_psgAngleClass_le {tA tB wt : ℝ} {s : ℝ} :
    dist (psgAngleClass tA tB s) (((wt : ℝ) : UnitAddCircle)) ≤ max |tA - wt| |tB - wt| := by
  have h1 : 0 ≤ 1 - psgRamp s := by linarith [psgRamp_le_one s]
  have h2 : 0 ≤ psgRamp s := psgRamp_nonneg s
  rw [psgAngleClass, psgAngle]
  have hmem : ((1 - psgRamp s) * tA + psgRamp s * tB : ℝ) ∈
      Metric.closedBall ((1 - psgRamp s) * wt + psgRamp s * wt) (max |tA - wt| |tB - wt|) := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    have : (1 - psgRamp s) * tA + psgRamp s * tB
        - ((1 - psgRamp s) * wt + psgRamp s * wt)
        = (1 - psgRamp s) * (tA - wt) + psgRamp s * (tB - wt) := by ring
    rw [this]
    calc |(1 - psgRamp s) * (tA - wt) + psgRamp s * (tB - wt)|
        ≤ |(1 - psgRamp s) * (tA - wt)| + |psgRamp s * (tB - wt)| := abs_add_le _ _
      _ = (1 - psgRamp s) * |tA - wt| + psgRamp s * |tB - wt| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
      _ ≤ (1 - psgRamp s) * max |tA - wt| |tB - wt|
            + psgRamp s * max |tA - wt| |tB - wt| :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h1)
            (mul_le_mul_of_nonneg_left (le_max_right _ _) h2)
      _ = max |tA - wt| |tB - wt| := by ring
  have hcoe : (1 - psgRamp s) * wt + psgRamp s * wt = (wt : ℝ) := by ring
  rw [hcoe] at hmem
  have hpre := AddCircle.coe_real_preimage_closedBall_eq_iUnion (1 : ℝ) wt
    (max |tA - wt| |tB - wt|)
  have hmem' : ((1 - psgRamp s) * tA + psgRamp s * tB : ℝ)
      ∈ ((fun y : ℝ => (y : UnitAddCircle)) ⁻¹'
        Metric.closedBall ((wt : ℝ) : UnitAddCircle) (max |tA - wt| |tB - wt|)) := by
    rw [hpre]
    exact Set.mem_iUnion.mpr ⟨0, by simpa using hmem⟩
  exact Metric.mem_closedBall.mp hmem'

/-- The chart family of the loop side: the `s`-th chart is the chart at the `s`-th configuration,
perturbed by `τ₁`. -/
def psgQFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) : ℝ → ℂ → CappingSpace :=
  fun s z => Ξ (psgPathL A B s + τ₁) (Q z)

/-- The plane-presentation family of the sweep side, perturbed by `τ₂` and rotated along the angle
path. -/
def psgPFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₂ : EuclideanSpace ℝ (Fin m)) : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun s y => rotPresentation (fun z => Ξ (psgPathR A B s + τ₂) (Q z)) (psgAngleClass tA tB s) y

/-- The loop side of the parity family on the five-box. -/
def psgLoopFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  chartLoopFam (psgQFam Ξ Q A B τ₁)

/-- The chain side of the parity family on the five-box. -/
def psgChainFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₂ : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin 4) → CappingSpace :=
  sweepFam c (fun s => 1 - s) (psgPFam Ξ Q A B tA tB τ₂)

/-! ## Basic identities, smoothness of the family, and the two crossing clauses -/

lemma famPt_succ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    famPt t x i.succ = x i := by
  simp [famPt, Fin.cons_succ]

lemma psgLoopFam_apply (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin 5)) :
    famLoop (psgLoopFam Ξ Q A B τ₁) p
      = Ξ (psgPathL A B (p 0) + τ₁)
          (Q (Complex.exp (↑Real.pi * ((p 1 : ℝ) : ℂ) * Complex.I))) := by
  simp [famLoop, psgLoopFam, chartLoopFam, coreLoop, psgQFam]

lemma psgChainFam_apply (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₂ : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin 5)) :
    famChain (psgChainFam Ξ Q c A B tA tB τ₂) p
      = clampedSweep c (fun s => 1 - s) (psgPFam Ξ Q A B tA tB τ₂ (p 0))
          (famT3 (p 2) (p 3) (p 4)) := by
  rw [famChain, psgChainFam, sweepFam, famPt_apply_zero]
  congr 2

lemma psgChainFam_famPt_apply (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₂ : EuclideanSpace ℝ (Fin m)) (u : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    psgChainFam Ξ Q c A B tA tB τ₂ (famPt u x)
      = clampedSweep c (fun s => 1 - s) (psgPFam Ξ Q A B tA tB τ₂ u) x := by
  rw [psgChainFam, sweepFam, famPt_apply_zero, famT3_famPt_tail]

lemma coreLoop_seam_closed {Q : ℂ → CappingSpace}
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) : coreLoop Q 0 = coreLoop Q 1 := by
  have h0 : Complex.exp (Real.pi * ((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have h1 : Complex.exp (Real.pi * ((1 : ℝ) : ℂ) * Complex.I) = (-1 : ℂ) := by
    rw [show Real.pi * ((1 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
  simp only [coreLoop, h0, h1]
  exact (hQ 1 (by simp)).symm

@[fun_prop]
lemma contDiff_psgRamp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psgRamp := psgRamp_contDiff

lemma contDiff_psgPathL (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psgPathL A B) := by
  unfold psgPathL
  fun_prop

lemma contDiff_psgPathR (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psgPathR A B) := by
  unfold psgPathR
  fun_prop

lemma contMDiff_psgProj (i : Fin 2) :
    ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => p i) :=
  ContinuousLinearMap.contMDiff
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)

lemma contMDiff_psgPathL (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 2) (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => psgPathL A B (p 0) + τ₁) := by
  have h1 : ContMDiff (𝓡 2) (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => psgPathL A B (p 0)) :=
    (contDiff_psgPathL A B).contMDiff.comp (contMDiff_psgProj 0)
  exact h1.add contMDiff_const

lemma contMDiff_psgPathR (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₂ : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 2) (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => psgPathR A B (p 0) + τ₂) := by
  have h1 : ContMDiff (𝓡 2) (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => psgPathR A B (p 0)) :=
    (contDiff_psgPathR A B).contMDiff.comp (contMDiff_psgProj 0)
  exact h1.add contMDiff_const

lemma contMDiff_psgExp (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q) (i : Fin 2) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        Q (Complex.exp (↑Real.pi * ((p i : ℝ) : ℂ) * Complex.I))) := by
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (↑Real.pi : ℂ) * (t : ℂ) * Complex.I) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t : ℂ)) :=
      Complex.ofRealCLM.contDiff
    exact (contDiff_const.mul h1).mul contDiff_const
  have hexp : ContMDiff (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℂ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Complex.exp (↑Real.pi * (t : ℂ) * Complex.I)) :=
    Complex.contDiff_exp.contMDiff.comp hlin.contMDiff
  exact hQ.comp (hexp.comp (contMDiff_psgProj i))

end

end Work.Drive
