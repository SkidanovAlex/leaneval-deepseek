import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.coreCountFam
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.hcRotation

/-!
# The concrete family of the germ route `sideGerm_parity_eq_of_close`

This module holds the *definitions* of the one-parameter family that the parity-locality argument of
`Submission/Work/Drive/sideGerm_parity_eq_of_close.lean` deforms, together with the three clauses
`hloop`, `hseam`, `havoid` of the L6 family engine `Work.Drive.odd_ncard_sideFam_iff` and the
identification of the two end slices with the germ counts at the shifted configurations.

The path joins two configurations `A, B : 𝔼^m × 𝔼^m` (loop chart parameter and sweep chart parameter)
by the straight segment, and two angle *lifts* `t, t' : ℝ` by the linear path of lifts; the Sard
parameter `τ ∈ 𝔼^m` shifts both chart parameters simultaneously.

* `Work.Drive.sideGermLoopFam`, `Work.Drive.sideGermChainFam` — the five-box family (the `famLoop` /
  `famChain` pair of the engine);
* `Work.Drive.sideGermQfam`, `Work.Drive.sideGermPfam` — the one-parameter (path-parameter) data of
  the engine `Work.Drive.odd_ncard_sideFam_iff`;
* `Work.Drive.sideGerm_hloop`, `Work.Drive.sideGerm_hseam`, `Work.Drive.sideGerm_havoid` — the three
  geometric clauses, `havoid` transferred from `Work.Drive.sideGerm_havoid_of_close`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The coordinates of `famPt` -/

@[simp] lemma famPt_apply_one (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : famPt t x 1 = x 0 := rfl

@[simp] lemma famPt_apply_two (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : famPt t x 2 = x 1 := rfl

@[simp] lemma famPt_apply_three (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : famPt t x 3 = x 2 := rfl

/-! ## The family -/

variable {m : ℕ}

/-- The path of the *loop's* chart parameter along the straight segment from `A` to `B`. -/
def sideGermPathL (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  (1 - s) • A.1 + s • B.1

/-- The path of the *sweep's* chart parameter along the straight segment from `A` to `B`. -/
def sideGermPathR (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  (1 - s) • A.2 + s • B.2

/-- The path of angles from the class of `t` to the class of `t'`, along the selected lifts. -/
def sideGermAngle (t t' s : ℝ) : UnitAddCircle :=
  (((1 - s) * t + s * t' : ℝ) : UnitAddCircle)

@[simp] lemma sideGermPathL_zero (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    sideGermPathL A B 0 = A.1 := by simp [sideGermPathL]

@[simp] lemma sideGermPathL_one (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    sideGermPathL A B 1 = B.1 := by simp [sideGermPathL]

@[simp] lemma sideGermPathR_zero (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    sideGermPathR A B 0 = A.2 := by simp [sideGermPathR]

@[simp] lemma sideGermPathR_one (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    sideGermPathR A B 1 = B.2 := by simp [sideGermPathR]

@[simp] lemma sideGermAngle_zero (t t' : ℝ) :
    sideGermAngle t t' 0 = ((t : ℝ) : UnitAddCircle) := by simp [sideGermAngle]

@[simp] lemma sideGermAngle_one (t t' : ℝ) :
    sideGermAngle t t' 1 = ((t' : ℝ) : UnitAddCircle) := by simp [sideGermAngle]

/-- **The loop side of the germ family** at the Sard shift `τ`. -/
def sideGermLoopFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun τ y => coreLoop (fun z => Ξ (sideGermPathL A B (y 0) + τ) (Q z)) (y 1)

/-- **The chain side of the germ family** at the Sard shift `τ`. -/
def sideGermChainFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace :=
  fun τ x => clampedSweep c (fun u => 1 - u)
    (rotPresentation (fun z => Ξ (sideGermPathR A B (x 0) + τ) (Q z))
      (sideGermAngle t t' (x 0))) (famT3 (x 1) (x 2) (x 3))

/-- The one-parameter loop family of the engine: the chart at the `s`-th configuration, shifted. -/
def sideGermQfam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) : ℝ → ℂ → CappingSpace :=
  fun s z => Ξ (sideGermPathL A B s + τ) (Q z)

/-- The one-parameter plane-presentation family of the engine. -/
def sideGermPfam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun s y => rotPresentation (fun z => Ξ (sideGermPathR A B s + τ) (Q z))
    (sideGermAngle t t' s) y

lemma sideGermLoopFam_eq_chartLoopFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) :
    sideGermLoopFam Ξ Q A B τ = chartLoopFam (sideGermQfam Ξ Q A B τ) := rfl

lemma sideGermChainFam_eq_sweepFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) :
    sideGermChainFam Ξ Q c t t' A B τ
      = sweepFam c (fun u => 1 - u) (sideGermPfam Ξ Q t t' A B τ) := rfl

lemma sideGermQfam_zero (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) :
    sideGermQfam Ξ Q A B τ 0 = pertChart Ξ Q (A.1 + τ) := by
  funext z; simp [sideGermQfam, pertChart]

lemma sideGermQfam_one (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) :
    sideGermQfam Ξ Q A B τ 1 = pertChart Ξ Q (B.1 + τ) := by
  funext z; simp [sideGermQfam, pertChart]

lemma sideGermPfam_zero (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) :
    sideGermPfam Ξ Q t t' A B τ 0
      = rotPresentation (pertChart Ξ Q (A.2 + τ)) ((t : ℝ) : UnitAddCircle) := by
  funext y
  simp only [sideGermPfam, sideGermPathR, sideGermAngle, Pi.zero_apply, sub_zero, one_mul,
    zero_mul, one_smul, zero_smul, add_zero]
  rfl

lemma sideGermPfam_one (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) :
    sideGermPfam Ξ Q t t' A B τ 1
      = rotPresentation (pertChart Ξ Q (B.2 + τ)) ((t' : ℝ) : UnitAddCircle) := by
  funext y
  simp only [sideGermPfam, sideGermPathR, sideGermAngle, Pi.one_apply, sub_self, zero_mul,
    one_mul, zero_smul, one_smul, zero_add]
  rfl

/-- **The `s = 0` slice count is the germ count at the shifted configuration `A + (τ,τ)`.** -/
lemma coreSideCount_zero_eq_CntAt (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) :
    coreSideCount (sideGermQfam Ξ Q A B τ 0) c (sideGermPfam Ξ Q t t' A B τ 0)
      = CntAt Ξ Q c (((t : ℝ) : UnitAddCircle)) (A.1 + τ, A.2 + τ) := by
  simp only [coreSideCount, CntAt, sideGermQfam_zero, sideGermPfam_zero, pertChart]

/-- **The `s = 1` slice count is the germ count at the shifted configuration `B + (τ,τ)`.** -/
lemma coreSideCount_one_eq_CntAt (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) :
    coreSideCount (sideGermQfam Ξ Q A B τ 1) c (sideGermPfam Ξ Q t t' A B τ 1)
      = CntAt Ξ Q c (((t' : ℝ) : UnitAddCircle)) (B.1 + τ, B.2 + τ) := by
  simp only [coreSideCount, CntAt, sideGermQfam_one, sideGermPfam_one, pertChart]

/-! ## The three engine clauses -/

/-- **The core loop of a chart with the seam clause is closed.** -/
lemma coreLoop_zero_eq_one_of_seam {Q : ℂ → CappingSpace}
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) : coreLoop Q 0 = coreLoop Q 1 := by
  have h0 : Complex.exp (Real.pi * ((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have h1 : Complex.exp (Real.pi * ((1 : ℝ) : ℂ) * Complex.I) = (-1 : ℂ) := by
    rw [show Real.pi * ((1 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
  simp only [coreLoop, h0, h1]
  exact (hQ 1 (by simp)).symm

/-- The closure `hloop` of the engine for an arbitrary one-parameter chart family with the seam
clause. -/
lemma chartLoopFam_hloop_of_seam {Q : ℝ → ℂ → CappingSpace}
    (hQ : ∀ (s : ℝ) (z : ℂ), ‖z‖ = 1 → Q s (-z) = Q s z) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, chartLoopFam Q (mk2 t 0) = chartLoopFam Q (mk2 t 1) := by
  intro t _
  rw [chartLoopFam, chartLoopFam, mk2_apply_zero, mk2_apply_one]
  exact coreLoop_zero_eq_one_of_seam (hQ t)

/-- **The loop closure `hloop` of the L6 engine** for the germ family. -/
lemma sideGerm_hloop (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hQ : IsChartData Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, chartLoopFam (sideGermQfam Ξ Q A B τ) (mk2 t 0)
      = chartLoopFam (sideGermQfam Ξ Q A B τ) (mk2 t 1) :=
  chartLoopFam_hloop_of_seam (Q := sideGermQfam Ξ Q A B τ)
    (fun s z hz => congrArg (fun p => Ξ (sideGermPathL A B s + τ) p) (hQ.2 z hz))

/-- **The chain seam invariance `hseam` of the L6 engine** for the germ family, in the *unfolded*
form: the presentation of the `s`-th configuration is the rotated presentation of the perturbed chart
`z ↦ Ξ (pathR s + τ) (Q z)` at the angle `sideGermAngle t t' s`.  This is the form in which the
statement is cheap to work with; the `sweepFam`/`sideGermPfam` form consumed by the engine is derived
from it by `sideGerm_hseam`. -/
lemma sideGerm_hseam_raw (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) (hQ : IsChartData Q) :
    ∀ (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)), onSeam x →
      clampedSweep c (fun u => 1 - u)
        (rotPresentation (fun z => Ξ (sideGermPathR A B s + τ) (Q z)) (sideGermAngle t t' s))
        (seamInv x)
      = clampedSweep c (fun u => 1 - u)
        (rotPresentation (fun z => Ξ (sideGermPathR A B s + τ) (Q z))
          (sideGermAngle t t' s)) x := by
  intro s x hx
  exact (clampedSweep_seamInv c (fun u => 1 - u)
    (rotPresentation (fun z => Ξ (sideGermPathR A B s + τ) (Q z)) (sideGermAngle t t' s))
    (fun y hy => (seam_rotPresentation (fun z => Ξ (sideGermPathR A B s + τ) (Q z))
      (sideGermAngle t t' s)
      (fun z hz => congrArg (fun p => Ξ (sideGermPathR A B s + τ) p) (hQ.2 z hz)) hy).symm)
    x hx).symm

/-- **The chain seam invariance `hseam` of the L6 engine** in the form consumed by the engine: the
`seamInv`-invariance of the `sweepFam` of the germ route. -/
lemma sideGerm_hseam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) (hQ : IsChartData Q) :
    ∀ (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)), onSeam x →
      sweepFam c (fun u => 1 - u) (sideGermPfam Ξ Q t t' A B τ) (famPt s (seamInv x))
        = sweepFam c (fun u => 1 - u) (sideGermPfam Ξ Q t t' A B τ) (famPt s x) := by
  intro s x hx
  have hraw := sideGerm_hseam_raw Ξ Q c t t' A B τ hQ s x hx
  have hP : sideGermPfam Ξ Q t t' A B τ s
      = rotPresentation (fun z => Ξ (sideGermPathR A B s + τ) (Q z)) (sideGermAngle t t' s) := by
    funext y
    simp only [sideGermPfam]
  have e1 : famT3 ((famPt s (seamInv x)) 1) ((famPt s (seamInv x)) 2) ((famPt s (seamInv x)) 3)
      = seamInv x := by
    rw [famPt_apply_one, famPt_apply_two, famPt_apply_three]
    exact famT3_eta (seamInv x)
  have e2 : famT3 ((famPt s x) 1) ((famPt s x) 2) ((famPt s x) 3) = x := by
    rw [famPt_apply_one, famPt_apply_two, famPt_apply_three]
    exact famT3_eta x
  simp only [sweepFam, famPt_apply_zero, e1, e2, hP]
  exact hraw

/-- **The radial-face avoidance `havoid` of the L6 engine** for the germ family, transferred from the
geometric statement `Work.Drive.sideGerm_havoid_of_close`. -/
lemma sideGerm_havoid (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t t' : ℝ) (w : UnitAddCircle)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) {ε δ : ℝ}
    (hav : ∀ (a : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
      ‖a‖ < ε → dist w' w < δ →
      ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
        u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
        coreLoop (pertChart Ξ Q a.1) (u 1)
          = clampedSweep c (fun u => 1 - u) (rotPresentation (pertChart Ξ Q a.2) w') x →
        (x 2 = 0 ∨ x 2 = 1) → False)
    (hsmall : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(sideGermPathL A B s + τ, sideGermPathR A B s + τ)‖ < ε)
    (hang : ∀ s ∈ Set.Icc (0 : ℝ) 1, dist (sideGermAngle t t' s) w < δ) :
    ∀ p ∈ Submission.Drive.unitBox 4,
      famLoop (sideGermLoopFam Ξ Q A B τ) p = famChain (sideGermChainFam Ξ Q c t t' A B τ) p →
      (p 4 = 0 ∨ p 4 = 1) → False := by
  intro p hp hmeet hface
  have hp0 : p 0 ∈ Set.Icc (0 : ℝ) 1 := hp 0
  have h1 : (mk2 (p 0) (p 1)) ∈ Submission.Drive.unitBox 1 := by
    intro i
    fin_cases i
    · simpa [mk2] using hp 0
    · simpa [mk2] using hp 1
  have hx : famT3 (p 2) (p 3) (p 4) ∈ Submission.Drive.unitBox 2 := by
    intro i
    fin_cases i
    · simpa [famT3] using hp 2
    · simpa [famT3] using hp 3
    · simpa [famT3] using hp 4
  refine hav _ _ (hsmall (p 0) hp0) (hang (p 0) hp0) (mk2 (p 0) (p 1))
      (famT3 (p 2) (p 3) (p 4)) h1 hx ?_ hface
  have h := hmeet
  simp only [famLoop, famChain, sideGermLoopFam, sideGermChainFam, famPt_apply_zero] at h
  rw [mk2_apply_one]
  exact h

/-! ## The charted-space structure of the capping space, as a *global* instance

The workspace declares the smooth structure of `CappingSpace` as `def`s which the consuming files
register with `attribute [local instance]`.  Statements about `mfderiv`/`chr` on `CappingSpace` can
only be *written* in a file where such an instance is in scope, so the two instances below are declared
globally here (they are definitionally the workspace's `cappingCharted` /
`isManifold_cappingCharted`), which makes the statements of the delegated obligations of
`sideGerm_parity_eq_of_close` expressible in their own files. -/

instance instChartedSpaceCappingSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace :=
  cappingCharted

instance instIsManifoldCappingSpace :
    IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) CappingSpace :=
  isManifold_cappingCharted

instance instT2SpaceCappingSpace : T2Space CappingSpace := t2Space_cappingSpace

end

end Work.Drive
