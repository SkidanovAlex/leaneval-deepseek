import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.famMeetDefs
import Submission.Work.Drive.coreMeet_ncard_eq_famMeet
import Submission.Work.Drive.hcRotation
import Submission.Work.Drive.coreCountFam
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.germHavoidZc
import Submission.Work.Drive.designCountLocalityGen

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 4000000

noncomputable section

/-! ## 1. Angle lifts whose difference is the distance -/

lemma sep_coe_intCast_unitAddCircle (k : ℤ) : ((k : ℝ) : UnitAddCircle) = 0 := by
  have h : (k : ℝ) = k • (1:ℝ) := by simp
  rw [h, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

lemma sep_norm_coe_unitAddCircle_eq (x : ℝ) : |x - (round x : ℝ)| = ‖(x : UnitAddCircle)‖ := by
  rw [AddCircle.norm_eq (1:ℝ)]
  norm_num

lemma sep_norm_coe_unitAddCircle_le (y : ℝ) : ‖((y : ℝ) : UnitAddCircle)‖ ≤ |y| := by
  rw [← sep_norm_coe_unitAddCircle_eq y]
  rcases lt_or_ge (|y|) (1/2 : ℝ) with h | h
  · have h0 : round y = 0 := by
      rw [round_eq_zero_iff]
      exact ⟨by linarith [neg_abs_le y], lt_of_le_of_lt (le_abs_self y) h⟩
    rw [h0]; simp
  · have h' : |y - (round y : ℝ)| ≤ 1/2 := abs_sub_round y
    linarith

lemma sep_dist_coe_coe_le (x y : ℝ) :
    dist ((x : ℝ) : UnitAddCircle) ((y : ℝ) : UnitAddCircle) ≤ |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact sep_norm_coe_unitAddCircle_le _

theorem sep_exists_lift_pair (w w' : UnitAddCircle) :
    ∃ a a' : ℝ, (a : UnitAddCircle) = w ∧ (a' : UnitAddCircle) = w' ∧
      |a' - a| = dist w' w := by
  obtain ⟨a, rfl⟩ := Quotient.mk''_surjective w
  obtain ⟨b, rfl⟩ := Quotient.mk''_surjective w'
  refine ⟨a, b - (round (b - a) : ℤ), rfl, ?_, ?_⟩
  · rw [AddCircle.coe_sub, sep_coe_intCast_unitAddCircle, sub_zero]
  · have h : b - (round (b-a) : ℤ) - a = (b - a) - (round (b - a) : ℝ) := by push_cast; ring
    rw [h, sep_norm_coe_unitAddCircle_eq, AddCircle.coe_sub, dist_eq_norm]

/-! ## 2. The family of the germ route (local copy, under `sep` names) -/

variable {m : ℕ}

/-- The path of the loop's chart parameter along the straight segment from `A` to `B`. -/
def sepPathL (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  (1 - s) • A.1 + s • B.1

/-- The path of the sweep's chart parameter along the straight segment from `A` to `B`. -/
def sepPathR (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  (1 - s) • A.2 + s • B.2

/-- The path of angles from the class of `t` to the class of `t'`, along the selected lifts. -/
def sepAngle (t t' s : ℝ) : UnitAddCircle :=
  (((1 - s) * t + s * t' : ℝ) : UnitAddCircle)

@[simp] lemma sepPathL_zero (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    sepPathL A B 0 = A.1 := by simp [sepPathL]

@[simp] lemma sepPathL_one (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    sepPathL A B 1 = B.1 := by simp [sepPathL]

@[simp] lemma sepPathR_zero (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    sepPathR A B 0 = A.2 := by simp [sepPathR]

@[simp] lemma sepPathR_one (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    sepPathR A B 1 = B.2 := by simp [sepPathR]

@[simp] lemma sep_famPt_apply_one (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : famPt t x 1 = x 0 := rfl

@[simp] lemma sep_famPt_apply_two (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : famPt t x 2 = x 1 := rfl

@[simp] lemma sep_famPt_apply_three (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : famPt t x 3 = x 2 := rfl

@[simp] lemma sepAngle_zero (t t' : ℝ) : sepAngle t t' 0 = ((t : ℝ) : UnitAddCircle) := by
  simp [sepAngle]

@[simp] lemma sepAngle_one (t t' : ℝ) : sepAngle t t' 1 = ((t' : ℝ) : UnitAddCircle) := by
  simp [sepAngle]

/-- The one-parameter loop family of the L6 engine: the chart at the `s`-th configuration, shifted by
`τ₁`.  The two sides of the family carry **independent** shift parameters `τ₁`, `τ₂`: this is what
makes the parameter-derivative of the charted difference map onto at every point (the difference of
two separately onto maps, in the form `(τ₁,τ₂) ↦ A τ₁ - B τ₂`). -/
def sepQfam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) : ℝ → ℂ → CappingSpace :=
  fun s z => Ξ (sepPathL A B s + τ₁) (Q z)

/-- The one-parameter plane-presentation family of the L6 engine. -/
def sepPfam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₂ : EuclideanSpace ℝ (Fin m)) : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun s y => rotPresentation (fun z => Ξ (sepPathR A B s + τ₂) (Q z)) (sepAngle t t' s) y

lemma sepQfam_zero (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) :
    sepQfam Ξ Q A B τ₁ 0 = pertChart Ξ Q (A.1 + τ₁) := by
  funext z; simp [sepQfam, pertChart]

lemma sepQfam_one (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) :
    sepQfam Ξ Q A B τ₁ 1 = pertChart Ξ Q (B.1 + τ₁) := by
  funext z; simp [sepQfam, pertChart]

lemma sepPfam_zero (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₂ : EuclideanSpace ℝ (Fin m)) :
    sepPfam Ξ Q t t' A B τ₂ 0
      = rotPresentation (pertChart Ξ Q (A.2 + τ₂)) ((t : ℝ) : UnitAddCircle) := by
  funext y
  simp only [sepPfam, sepPathR, sepAngle, Pi.zero_apply, sub_zero, one_mul, zero_mul, one_smul,
    zero_smul, add_zero]
  rfl

lemma sepPfam_one (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₂ : EuclideanSpace ℝ (Fin m)) :
    sepPfam Ξ Q t t' A B τ₂ 1
      = rotPresentation (pertChart Ξ Q (B.2 + τ₂)) ((t' : ℝ) : UnitAddCircle) := by
  funext y
  simp only [sepPfam, sepPathR, sepAngle, Pi.one_apply, sub_self, zero_mul, one_mul, zero_smul,
    one_smul, zero_add]
  rfl

/-- **The `s = 0` slice count is the germ count at the shifted configuration `A + (τ,τ)`.** -/
lemma sepCoreSideCount_zero_eq_CntAt
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) :
    coreSideCount (sepQfam Ξ Q A B τ₁ 0) c (sepPfam Ξ Q t t' A B τ₂ 0)
      = CntAt Ξ Q c (((t : ℝ) : UnitAddCircle)) (A.1 + τ₁, A.2 + τ₂) := by
  simp only [coreSideCount, CntAt, sepQfam_zero, sepPfam_zero, pertChart]

/-- **The `s = 1` slice count is the germ count at the shifted configuration `B + (τ,τ)`.** -/
lemma sepCoreSideCount_one_eq_CntAt
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) :
    coreSideCount (sepQfam Ξ Q A B τ₁ 1) c (sepPfam Ξ Q t t' A B τ₂ 1)
      = CntAt Ξ Q c (((t' : ℝ) : UnitAddCircle)) (B.1 + τ₁, B.2 + τ₂) := by
  simp only [coreSideCount, CntAt, sepQfam_one, sepPfam_one, pertChart]

/-! ## 3. The three geometric clauses of the L6 engine -/

/-- **The core loop of a chart with the seam clause is closed.** -/
lemma sep_coreLoop_zero_eq_one_of_seam {Q : ℂ → CappingSpace}
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) : coreLoop Q 0 = coreLoop Q 1 := by
  have h0 : Complex.exp (Real.pi * ((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have h1 : Complex.exp (Real.pi * ((1 : ℝ) : ℂ) * Complex.I) = (-1 : ℂ) := by
    rw [show Real.pi * ((1 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
  simp only [coreLoop, h0, h1]
  exact (hQ 1 (by simp)).symm

/-- **The loop closure `hloop` of the L6 engine** for the germ family. -/
lemma sep_hloop (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hQ : IsChartData Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      chartLoopFam (sepQfam Ξ Q A B τ₁) (mk2 t 0)
        = chartLoopFam (sepQfam Ξ Q A B τ₁) (mk2 t 1) := by
  intro t _
  rw [chartLoopFam, chartLoopFam, mk2_apply_zero, mk2_apply_one]
  exact sep_coreLoop_zero_eq_one_of_seam (fun z hz =>
    congrArg (fun p => Ξ (sepPathL A B t + τ₁) p) (hQ.2 z hz))

/-- **The chain seam invariance `hseam` of the L6 engine** for the germ family. -/
lemma sep_hseam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t t' : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₂ : EuclideanSpace ℝ (Fin m)) (hQ : IsChartData Q) :
    ∀ (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)), onSeam x →
      sweepFam c (fun u => 1 - u) (sepPfam Ξ Q t t' A B τ₂) (famPt s (seamInv x))
        = sweepFam c (fun u => 1 - u) (sepPfam Ξ Q t t' A B τ₂) (famPt s x) := by
  intro s x hx
  have hraw : clampedSweep c (fun u => 1 - u)
        (rotPresentation (fun z => Ξ (sepPathR A B s + τ₂) (Q z)) (sepAngle t t' s)) (seamInv x)
      = clampedSweep c (fun u => 1 - u)
        (rotPresentation (fun z => Ξ (sepPathR A B s + τ₂) (Q z)) (sepAngle t t' s)) x :=
    (clampedSweep_seamInv c (fun u => 1 - u)
      (rotPresentation (fun z => Ξ (sepPathR A B s + τ₂) (Q z)) (sepAngle t t' s))
      (fun y hy => (seam_rotPresentation (fun z => Ξ (sepPathR A B s + τ₂) (Q z))
        (sepAngle t t' s)
        (fun z hz => congrArg (fun p => Ξ (sepPathR A B s + τ₂) p) (hQ.2 z hz)) hy).symm) x hx).symm
  have key : ∀ y : EuclideanSpace ℝ (Fin 3),
      clampedSweep c (fun u => 1 - u)
        (rotPresentation (fun z => Ξ (sepPathR A B s + τ₂) (Q z)) (sepAngle t t' s)) y
      = clampedSweep c (fun u => 1 - u) (sepPfam Ξ Q t t' A B τ₂ s) y := by
    intro y
    rfl
  have hL : sweepFam c (fun u => 1 - u) (sepPfam Ξ Q t t' A B τ₂) (famPt s (seamInv x))
      = clampedSweep c (fun u => 1 - u) (sepPfam Ξ Q t t' A B τ₂ s) (seamInv x) := by
    rw [sweepFam]
    simp only [famPt_apply_zero, sep_famPt_apply_one, sep_famPt_apply_two, sep_famPt_apply_three,
      famT3_eta]
  have hR : sweepFam c (fun u => 1 - u) (sepPfam Ξ Q t t' A B τ₂) (famPt s x)
      = clampedSweep c (fun u => 1 - u) (sepPfam Ξ Q t t' A B τ₂ s) x := by
    rw [sweepFam]
    simp only [famPt_apply_zero, sep_famPt_apply_one, sep_famPt_apply_two, sep_famPt_apply_three,
      famT3_eta]
  rw [hL, hR, ← key (seamInv x), ← key x]
  exact hraw

/-- **The radial-face avoidance `havoid` of the L6 engine** for the germ family. -/
lemma sep_havoid (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ) (w : UnitAddCircle)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) {ε δ : ℝ}
    (hav : ∀ (a : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
      ‖a‖ < ε → dist w' w < δ →
      ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
        u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
        coreLoop (pertChart Ξ Q a.1) (u 1)
          = clampedSweep c (fun u => 1 - u) (rotPresentation (pertChart Ξ Q a.2) w') x →
        (x 2 = 0 ∨ x 2 = 1) → False)
    (hsmall : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(sepPathL A B s + τ₁, sepPathR A B s + τ₂)‖ < ε)
    (hang : ∀ s ∈ Set.Icc (0 : ℝ) 1, dist (sepAngle tR t'R s) w < δ) :
    ∀ p ∈ Submission.Drive.unitBox 4,
      famLoop (chartLoopFam (sepQfam Ξ Q A B τ₁)) p
        = famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂)) p →
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
  simp only [famLoop, famChain, chartLoopFam, sweepFam, sepQfam, sepPfam,
    famPt_apply_zero] at h
  rw [mk2_apply_one]
  exact h


/-! ## 4. The regularity data of the germ family at the Sard shift (the hypotheses of the L6 engine) -/

/-- **The regularity data of the germ family** at the shift `τ`: the smoothness of the two sides of
the five-box family and the two regularity clauses (`htrans`, `hface`) of the parity engine
`Work.Drive.odd_coreSideCount_iff_of_famRegular_gen`. -/
structure SepRegular (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) : Prop where
  hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (chartLoopFam (sepQfam Ξ Q A B τ₁))
  hN : ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂))
  htrans : ∀ p ∈ Submission.Drive.unitBox 4,
    famLoop (chartLoopFam (sepQfam Ξ Q A B τ₁)) p
        = famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂)) p →
    Function.Surjective (fun v : EuclideanSpace ℝ (Fin 5) =>
      (show EuclideanSpace ℝ (Fin 4) from
          mfderiv (𝓡 5) (𝓡 4) (famLoop (chartLoopFam (sepQfam Ξ Q A B τ₁))) p v)
        - (show EuclideanSpace ℝ (Fin 4) from
          mfderiv (𝓡 5) (𝓡 4)
            (famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂))) p v))
  hface : ∀ p ∈ Submission.Drive.unitBox 4,
    famLoop (chartLoopFam (sepQfam Ξ Q A B τ₁)) p
        = famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂)) p →
    p ∈ Submission.Drive.unitBoxBdry 4 →
    ∃ i : Fin 5, (p i = 0 ∨ p i = 1) ∧ (∀ j : Fin 5, j ≠ i → p j ∈ Set.Ioo (0 : ℝ) 1) ∧
      ∃ σ : EuclideanSpace ℝ (Fin 5),
        mfderiv (𝓡 5) (𝓡 4) (famLoop (chartLoopFam (sepQfam Ξ Q A B τ₁))) p σ
          = mfderiv (𝓡 5) (𝓡 4)
              (famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂))) p σ ∧
        σ i ≠ 0

/-! ## 4bis. The three pieces of `SepRegular`, as separate structures

`SepRegular` is the *conjunction* of three independent obligations; splitting it lets each be proved
(or delegated) on its own:

* `SepSmooth` — the smoothness of the two sides of the family (pure bookkeeping);
* `SepTrans` — the *transversality* clause of the engine (the parametric Sard on the charted
  difference system, whose parameter-derivative is onto because the two chart perturbations are
  independent);
* `SepFace` — the *face* clause of the engine (no meet on two faces, and every meet on one face is
  crossed: a genericity statement, produced on the codimension-`2` corners by the avoidance machinery
  and on the single faces by the square Sard for the face-restricted system). -/

/-- **The smoothness clauses** of the parity family. -/
structure SepSmooth (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) : Prop where
  hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (chartLoopFam (sepQfam Ξ Q A B τ₁))
  hN : ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂))

/-- **The transversality clause** of the parity engine for the germ family. -/
structure SepTrans (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) : Prop where
  htrans : ∀ p ∈ Submission.Drive.unitBox 4,
    famLoop (chartLoopFam (sepQfam Ξ Q A B τ₁)) p
        = famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂)) p →
    Function.Surjective (fun v : EuclideanSpace ℝ (Fin 5) =>
      (show EuclideanSpace ℝ (Fin 4) from
          mfderiv (𝓡 5) (𝓡 4) (famLoop (chartLoopFam (sepQfam Ξ Q A B τ₁))) p v)
        - (show EuclideanSpace ℝ (Fin 4) from
          mfderiv (𝓡 5) (𝓡 4)
            (famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂))) p v))

/-- **The face clause** of the parity engine for the germ family. -/
structure SepFace (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) : Prop where
  hface : ∀ p ∈ Submission.Drive.unitBox 4,
    famLoop (chartLoopFam (sepQfam Ξ Q A B τ₁)) p
        = famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂)) p →
    p ∈ Submission.Drive.unitBoxBdry 4 →
    ∃ i : Fin 5, (p i = 0 ∨ p i = 1) ∧ (∀ j : Fin 5, j ≠ i → p j ∈ Set.Ioo (0 : ℝ) 1) ∧
      ∃ σ : EuclideanSpace ℝ (Fin 5),
        mfderiv (𝓡 5) (𝓡 4) (famLoop (chartLoopFam (sepQfam Ξ Q A B τ₁))) p σ
          = mfderiv (𝓡 5) (𝓡 4)
              (famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂))) p σ ∧
        σ i ≠ 0

/-- **`SepRegular` from its three pieces.** -/
theorem SepRegular.of_pieces {Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace}
    {Q : ℂ → CappingSpace} {c : ℝ} {tR t'R : ℝ}
    {A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)}
    {τ₁ τ₂ : EuclideanSpace ℝ (Fin m)}
    (hs : SepSmooth Ξ Q c tR t'R A B τ₁ τ₂) (ht : SepTrans Ξ Q c tR t'R A B τ₁ τ₂)
    (hf : SepFace Ξ Q c tR t'R A B τ₁ τ₂) : SepRegular Ξ Q c tR t'R A B τ₁ τ₂ :=
  ⟨hs.hL, hs.hN, ht.htrans, hf.hface⟩

end

end Work.Drive
