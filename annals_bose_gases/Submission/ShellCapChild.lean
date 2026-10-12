import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.ShellGeom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Task: prove the latitude/projection measure of the unit sphere

GOAL (`shell_proj_measure`): with `ShellS2 := Metric.sphere (0 : ℝ³) 1`
(`ℝ³ := EuclideanSpace ℝ (Fin 3)`), the push-forward of the sphere measure
`volume.toSphere` (total mass `4π`) under the first-coordinate map
`u ↦ (u : ℝ³) 0` is `2π` times Lebesgue measure restricted to `[−1,1]`:

    (volume.toSphere).map (fun u : ShellS2 => (u : ℝ³) 0)
        = ENNReal.ofReal (2 * π) • (volume.restrict (Set.Icc (-1) 1) : Measure ℝ)

Proof structure:
1. cap geometry: cone over a cap; `toSphere (cap) = 3 * volume (cone)`.
2. the volume of the cone is computed by slicing the coordinate `x0`.
3. extension from positive caps to the full measure equality.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real ENNReal NNReal BigOperators Pointwise

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ### Cap geometry -/

/-- Pushforward measure of the first-coordinate map on the unit sphere. -/
noncomputable def shellProjMu : Measure ℝ :=
  (volume.toSphere : Measure ShellS2).map (fun u : ShellS2 => (u : ℝ³) 0)

/-- The target measure: `2π` times Lebesgue measure on `[−1,1]`. -/
noncomputable def shellProjNu : Measure ℝ :=
  ENNReal.ofReal (2 * π) • (volume.restrict (Set.Icc (-1) 1) : Measure ℝ)

/-- A cap of the unit sphere: latitudes `≥ c`. -/
def shellCap (c : ℝ) : Set ShellS2 := {u : ShellS2 | c ≤ (u : ℝ³) 0}

/-- The cone over the cap: points `x` with `0 < ‖x‖ < 1` in the direction of the cap. -/
def shellCone3 (c : ℝ) : Set ℝ³ := {x : ℝ³ | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ c ≤ (x : ℝ³) 0 / ‖x‖}

/-- The cone with the linear form of the direction condition. -/
def shellCone3' (c : ℝ) : Set ℝ³ := {x : ℝ³ | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ c * ‖x‖ ≤ (x : ℝ³) 0}

lemma mem_sphere_norm {x : ℝ³} (hx : x ∈ Metric.sphere (0 : ℝ³) 1) : ‖x‖ = 1 := by
  simpa [Metric.mem_sphere, dist_zero_right] using hx

lemma shell_cone_smul_cap (c : ℝ) :
    (Set.Ioo (0 : ℝ) 1 • ((↑) '' (shellCap c))) = shellCone3 c := by
  ext x
  constructor
  · rintro ⟨a, ha, v, hv, hx⟩
    rcases hv with ⟨w, hw, rfl⟩
    have hnorm : ‖(w : ℝ³)‖ = 1 := mem_sphere_norm w.2
    have hx0 : (x : ℝ³) 0 = a * ((w : ℝ³) 0) := by
      rw [← hx]
      simp [PiLp.smul_apply]
    have hnormx : ‖x‖ = a := by
      rw [← hx, norm_smul, hnorm]
      simp [abs_of_nonneg (le_of_lt ha.1)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hnormx]; exact ha.1
    · rw [hnormx]; exact ha.2
    · rw [hx0, hnormx]
      have ha' : a ≠ 0 := ha.1.ne'
      have hc : (a * ((w : ℝ³) 0)) / a = (w : ℝ³) 0 := by field_simp [ha']
      rw [hc]
      exact hw
  · intro hx
    rcases hx with ⟨h1, h2, h3⟩
    let u : ShellS2 := ⟨‖x‖⁻¹ • x, by
      have hnormu : ‖(‖x‖⁻¹ • x : ℝ³)‖ = 1 := by
        rw [norm_smul]
        rw [Real.norm_eq_abs, abs_inv, abs_of_pos h1]
        field_simp [h1.ne']
      simpa [Metric.mem_sphere, dist_zero_right] using hnormu⟩
    refine ⟨‖x‖, ⟨h1, h2⟩, (u : ℝ³), ?_, ?_⟩
    · refine ⟨u, ?_, rfl⟩
      change c ≤ ((u : ℝ³) 0)
      have hu0 : ((u : ℝ³) 0) = (x : ℝ³) 0 / ‖x‖ := by
        simp [u, PiLp.smul_apply]
        field_simp
      rw [hu0]; exact h3
    · ext i
      simp [u]
      field_simp [h1.ne']

lemma shell_cone3_eq (c : ℝ) : shellCone3 c = shellCone3' c := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [le_div_iff₀ h1] at h3
    simpa [mul_comm] using h3
  · intro hx
    rcases hx with ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [le_div_iff₀ h1]
    simpa [mul_comm] using h3

lemma shellCap_measurable (c : ℝ) : MeasurableSet (shellCap c) := by
  unfold shellCap
  have hf : Measurable (fun u : ShellS2 => (u : ℝ³) 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).measurable.comp measurable_subtype_coe
  exact hf measurableSet_Ici

lemma shellCone3_measurable (c : ℝ) : MeasurableSet (shellCone3 c) := by
  rw [shell_cone3_eq]
  rw [show shellCone3' c =
      ({x : ℝ³ | 0 < ‖x‖} ∩ {x : ℝ³ | ‖x‖ < 1}) ∩ {x : ℝ³ | c * ‖x‖ ≤ (x : ℝ³) 0} by
    ext x; simp [shellCone3', and_assoc]]
  have h1 : MeasurableSet {x : ℝ³ | 0 < ‖x‖} := continuous_norm.measurable measurableSet_Ioi
  have h2 : MeasurableSet {x : ℝ³ | ‖x‖ < 1} := by
    rw [show {x : ℝ³ | ‖x‖ < 1} = Metric.ball (0 : ℝ³) 1 by ext x; simp]
    exact Metric.isOpen_ball.measurableSet
  have h3 : MeasurableSet {x : ℝ³ | c * ‖x‖ ≤ (x : ℝ³) 0} := by
    have hcont : Continuous (fun x : ℝ³ => (x : ℝ³) 0 - c * ‖x‖) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).sub (continuous_const.mul continuous_norm)
    have hset : {x : ℝ³ | c * ‖x‖ ≤ (x : ℝ³) 0} = {x : ℝ³ | (x : ℝ³) 0 - c * ‖x‖ ∈ Set.Ici (0 : ℝ)} := by
      ext x; simp
    rw [hset]
    exact hcont.measurable measurableSet_Ici
  exact (h1.inter h2).inter h3

/-- Cap measure by `toSphere_apply'`: the sphere-cap measure is `3` times the cone volume. -/
lemma shell_toSphere_cap (c : ℝ) :
    (volume.toSphere : Measure ShellS2) (shellCap c) =
      (3 : ℝ≥0∞) * (volume : Measure ℝ³) (shellCone3 c) := by
  have h := Measure.toSphere_apply' (μ := (volume : Measure ℝ³)) (s := shellCap c)
    (shellCap_measurable c)
  rw [h]
  rw [shell_cone_smul_cap]
  rw [finrank_r3]
  norm_num

/-- The measurable equivalence `ShellX3 ≃ᵐ ℝ³` given by `WithLp.toLp`, measure preserving. -/
lemma toLp3_measurePreserving : MeasurePreserving (WithLp.toLp 2 : ShellX3 → ℝ³) volume volume := by
  have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm
  convert h using 1 <;> rfl

/-- The measurable equivalence `ShellX2 ≃ᵐ ℝ²` given by `WithLp.toLp`, measure preserving. -/
lemma toLp2_measurePreserving :
    MeasurePreserving (WithLp.toLp 2 : ShellX2 → EuclideanSpace ℝ (Fin 2)) volume volume := by
  have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).symm
  convert h using 1 <;> rfl

/-! ### The analytic core: volume of the cone over a cap, by slices -/

/-- Euclidean norm on the 2D coordinate space. -/
noncomputable def wnorm (w : ShellX2) : ℝ := ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2))‖

/-- Euclidean norm on the 3D coordinate space. -/
noncomputable def n3 (x : ShellX3) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖

lemma n3_sq (x : ShellX3) : n3 x ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
  unfold n3
  rw [shell_sq_norm3]

lemma wnorm_sq (w : ShellX2) : wnorm w ^ 2 = ∑ j : Fin 2, (w j) ^ 2 := by
  unfold wnorm
  rw [shell_sq_norm2 (w := (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)))]

lemma sq_norm_insert (t : ℝ) (w : ShellX2) :
    n3 (shellInsert0 t w) ^ 2 = t ^ 2 + wnorm w ^ 2 := by
  unfold n3 wnorm
  rw [shell_sq_norm3]
  rw [Fin.sum_univ_succ]
  simp [shellInsert0]
  rw [shell_sq_norm2 (w := (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)))]
  simp

lemma n3_nonneg (x : ShellX3) : 0 ≤ n3 x := by
  unfold n3; exact norm_nonneg _

lemma wnorm_nonneg (w : ShellX2) : 0 ≤ wnorm w := by
  unfold wnorm; exact norm_nonneg _

/-- The cone in squared form (equivalent to `shellCone3'` for `0 ≤ c`). -/
def shellCone3sq (c : ℝ) : Set ℝ³ :=
  {x : ℝ³ | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ 0 ≤ (x : ℝ³) 0 ∧ c ^ 2 * ‖x‖ ^ 2 ≤ ((x : ℝ³) 0) ^ 2}

/-- The cone in `ShellX3` coordinates (preimage of `shellCone3sq` under `WithLp.toLp`). -/
def preconeSq (c : ℝ) : Set ShellX3 :=
  {x : ShellX3 | 0 < n3 x ∧ n3 x < 1 ∧ 0 ≤ x 0 ∧ c ^ 2 * n3 x ^ 2 ≤ (x 0) ^ 2}

lemma shell_cone3'_eq_sq (c : ℝ) (hc0 : 0 ≤ c) : shellCone3' c = shellCone3sq c := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨h1, h2, h3⟩
    have hle : 0 ≤ c * ‖x‖ := mul_nonneg hc0 (le_of_lt h1)
    have h3' : (c * ‖x‖) ^ 2 ≤ ((x : ℝ³) 0) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg hle, abs_of_nonneg (le_trans hle h3)]
      exact h3
    refine ⟨h1, h2, ?_, ?_⟩
    · linarith
    · simpa [mul_pow] using h3'
  · intro hx
    rcases hx with ⟨h1, h2, hzero, h3⟩
    refine ⟨h1, h2, ?_⟩
    have h3' : (c * ‖x‖) ^ 2 ≤ ((x : ℝ³) 0) ^ 2 := by
      ring_nf at h3 ⊢
      exact h3
    have habs : |c * ‖x‖| ≤ |(x : ℝ³) 0| := sq_le_sq.mp h3'
    have hcp : 0 ≤ c * ‖x‖ := mul_nonneg hc0 (le_of_lt h1)
    rwa [abs_of_nonneg hcp, abs_of_nonneg hzero] at habs

lemma shellCone3sq_measurable (c : ℝ) : MeasurableSet (shellCone3sq c) := by
  unfold shellCone3sq
  measurability

lemma preconeSq_eq_preimage (c : ℝ) : preconeSq c = (WithLp.toLp 2) ⁻¹' (shellCone3sq c) := by
  ext x
  constructor
  · intro hx
    change (WithLp.toLp 2 x : ℝ³) ∈ shellCone3sq c
    rcases hx with ⟨h1, h2, h3, h4⟩
    unfold shellCone3sq
    refine ⟨h1, h2, ?_, ?_⟩
    · change (0 : ℝ) ≤ ((WithLp.toLp 2 x : ℝ³) 0)
      simpa using h3
    · change c ^ 2 * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ≤
          ((WithLp.toLp 2 x : ℝ³) 0) ^ 2
      simpa [n3] using h4
  · intro hx
    change (WithLp.toLp 2 x : ℝ³) ∈ shellCone3sq c at hx
    rcases hx with ⟨h1, h2, h3, h4⟩
    unfold preconeSq
    refine ⟨h1, h2, ?_, ?_⟩
    · change (0 : ℝ) ≤ x 0
      simpa using h3
    · change c ^ 2 * n3 x ^ 2 ≤ (x 0) ^ 2
      simpa [n3] using h4

lemma preconeSq_measurable (c : ℝ) : MeasurableSet (preconeSq c) := by
  rw [preconeSq_eq_preimage]
  exact toLp3_measurePreserving.measurable (shellCone3sq_measurable c)

/-! #### Real area of 2D disks, expressed as integrals over `ShellX2` -/

/-- Real measure of a 2D ball of radius `r`. -/
lemma realArea_ball2 (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r) =
      π * r ^ 2 := by
  rw [measureReal_def]
  rw [EuclideanSpace.volume_ball_fin_two]
  rw [ENNReal.toReal_mul]
  have hpow : ((ENNReal.ofReal r) ^ 2).toReal = r ^ 2 := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  rw [hpow]
  have hpi : (ENNReal.ofReal π).toReal = π := ENNReal.toReal_ofReal (by positivity)
  rw [hpi]
  ring

/-- Real measure of a 2D closed ball of radius `r`. -/
lemma realArea_closedBall2 (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure (EuclideanSpace ℝ (Fin 2))).real
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r) =
      π * r ^ 2 := by
  rw [measureReal_def]
  rw [EuclideanSpace.volume_closedBall_fin_two]
  rw [ENNReal.toReal_mul]
  have hpow : ((ENNReal.ofReal r) ^ 2).toReal = r ^ 2 := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  rw [hpow]
  have hpi : (ENNReal.ofReal π).toReal = π := ENNReal.toReal_ofReal (by positivity)
  rw [hpi]
  ring

lemma wnorm_eq_sqrt (w : ShellX2) : wnorm w = Real.sqrt (wnorm w ^ 2) := by
  calc wnorm w = |wnorm w| := (abs_of_nonneg (wnorm_nonneg w)).symm
       _ = Real.sqrt (wnorm w ^ 2) := (Real.sqrt_sq_eq_abs (wnorm w)).symm

lemma wnorm_eq_sqrt_sum (w : ShellX2) :
    wnorm w = Real.sqrt (∑ j : Fin 2, (w j) ^ 2) := by
  rw [wnorm_eq_sqrt, wnorm_sq]

/-- `w` lies in the radius-`s` disk iff its `ShellX2` norm squared is `≤ s` (for `0 ≤ s`). -/
lemma wnorm_sq_le_iff (w : ShellX2) {s : ℝ} (hs : 0 ≤ s) :
    wnorm w ^ 2 ≤ s ↔ wnorm w ≤ Real.sqrt s := by
  constructor
  · intro h
    have hsq : wnorm w ^ 2 ≤ Real.sqrt s ^ 2 := by rwa [Real.sq_sqrt hs]
    have habs : |wnorm w| ≤ |Real.sqrt s| := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (wnorm_nonneg w), abs_of_nonneg (Real.sqrt_nonneg s)] at habs
  · intro h
    have hsq : wnorm w ^ 2 ≤ Real.sqrt s ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (wnorm_nonneg w), abs_of_nonneg (Real.sqrt_nonneg s)]
      exact h
    rwa [Real.sq_sqrt hs] at hsq

/-- A `ShellX2`-disk of radius-squared `s` is the preimage of a 2D closed ball (for `0 ≤ s`). -/
lemma disk_sq_eq_preimage (s : ℝ) (hs : 0 ≤ s) :
    {w : ShellX2 | wnorm w ^ 2 ≤ s} =
      (WithLp.toLp 2) ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)) := by
  ext w
  change (wnorm w ^ 2 ≤ s) ↔
      (WithLp.toLp 2 w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s))
  rw [wnorm_sq_le_iff (w := w) hs]
  unfold wnorm
  rw [Metric.mem_closedBall, dist_zero_right]

/-- `w` lies in the radius-`s` open disk iff its norm squared `< s` (for `0 ≤ s`). -/
lemma wnorm_sq_lt_iff (w : ShellX2) {s : ℝ} (hs : 0 ≤ s) :
    wnorm w ^ 2 < s ↔ wnorm w < Real.sqrt s := by
  constructor
  · intro h
    have hsq : wnorm w ^ 2 < Real.sqrt s ^ 2 := by rwa [Real.sq_sqrt hs]
    have habs : |wnorm w| < |Real.sqrt s| := sq_lt_sq.mp hsq
    rwa [abs_of_nonneg (wnorm_nonneg w), abs_of_nonneg (Real.sqrt_nonneg s)] at habs
  · intro h
    have hsq : wnorm w ^ 2 < Real.sqrt s ^ 2 := by
      apply sq_lt_sq.mpr
      rw [abs_of_nonneg (wnorm_nonneg w), abs_of_nonneg (Real.sqrt_nonneg s)]
      exact h
    rwa [Real.sq_sqrt hs] at hsq

/-- A `ShellX2` open disk of radius-squared `s` is the preimage of a 2D open ball (for `0 ≤ s`). -/
lemma disk_lt_eq_preimage (s : ℝ) (hs : 0 ≤ s) :
    {w : ShellX2 | wnorm w ^ 2 < s} =
      (WithLp.toLp 2) ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)) := by
  ext w
  change (wnorm w ^ 2 < s) ↔
      (WithLp.toLp 2 w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s))
  rw [wnorm_sq_lt_iff (w := w) hs]
  unfold wnorm
  rw [Metric.mem_ball, dist_zero_right]

/-- The `ShellX2`-integral over the open radius-`s` disk equals `π·s` (for `0 ≤ s`). -/
lemma shellX2_disk_lt_area (s : ℝ) (hs : 0 ≤ s) :
    (∫ w : ShellX2, {z : ShellX2 | wnorm z ^ 2 < s}.indicator (fun _ : ShellX2 => (1 : ℝ)) w) =
      π * s := by
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  let G : EuclideanSpace ℝ (Fin 2) → ℝ :=
    (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)).indicator (fun _ => (1 : ℝ))
  have hG : (fun w : ShellX2 =>
      {z : ShellX2 | wnorm z ^ 2 < s}.indicator (fun _ : ShellX2 => (1 : ℝ)) w)
      = fun w : ShellX2 => G (WithLp.toLp 2 w) := by
    funext w
    unfold G
    rw [disk_lt_eq_preimage s hs]
    by_cases hmem : (WithLp.toLp 2 w) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)
    · have hwmem : w ∈ (WithLp.toLp 2 ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)) := by
        simpa using hmem
      simp [hwmem, hmem]
    · have hwnmem : w ∉ (WithLp.toLp 2 ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)) := by
        simpa using hmem
      simp [hwnmem, hmem]
  rw [hG]
  calc
    (∫ w : ShellX2, G (WithLp.toLp 2 w)) = ∫ z : EuclideanSpace ℝ (Fin 2), G z := by
      have h := shell_integral_coords2 (f := fun c : ShellX2 => G (WithLp.toLp 2 c))
      simpa using h.symm
    _ = π * s := by
      unfold G
      have hInt : (∫ z : EuclideanSpace ℝ (Fin 2),
            (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)).indicator
              (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) z)
          = (volume : Measure (EuclideanSpace ℝ (Fin 2))).real
              (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)) := by
        exact integral_indicator_one (s := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)) Metric.isOpen_ball.measurableSet
      rw [hInt]
      rw [realArea_ball2 (Real.sqrt s) (Real.sqrt_nonneg s)]
      rw [hsq]

/-- The `ShellX2`-integral over the radius-`s` disk equals `π·s` (for `0 ≤ s`). -/
lemma shellX2_disk_le_area (s : ℝ) (hs : 0 ≤ s) :
    (∫ w : ShellX2, {z : ShellX2 | wnorm z ^ 2 ≤ s}.indicator (fun _ : ShellX2 => (1 : ℝ)) w) =
      π * s := by
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  let G : EuclideanSpace ℝ (Fin 2) → ℝ :=
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)).indicator (fun _ => (1 : ℝ))
  have hG : (fun w : ShellX2 =>
      {z : ShellX2 | wnorm z ^ 2 ≤ s}.indicator (fun _ : ShellX2 => (1 : ℝ)) w)
      = fun w : ShellX2 => G (WithLp.toLp 2 w) := by
    funext w
    unfold G
    rw [disk_sq_eq_preimage s hs]
    by_cases hmem : (WithLp.toLp 2 w) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)
    · have hwmem : w ∈ (WithLp.toLp 2 ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)) := by
        simpa using hmem
      simp [hwmem, hmem]
    · have hwnmem : w ∉ (WithLp.toLp 2 ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)) := by
        simpa using hmem
      simp [hwnmem, hmem]
  rw [hG]
  calc
    (∫ w : ShellX2, G (WithLp.toLp 2 w)) = ∫ z : EuclideanSpace ℝ (Fin 2), G z := by
      have h := shell_integral_coords2 (f := fun c : ShellX2 => G (WithLp.toLp 2 c))
      simpa using h.symm
    _ = π * s := by
      unfold G
      have hInt : (∫ z : EuclideanSpace ℝ (Fin 2),
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)).indicator
              (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) z)
          = (volume : Measure (EuclideanSpace ℝ (Fin 2))).real
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)) := by
        exact integral_indicator_one (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt s)) measurableSet_closedBall
      rw [hInt]
      rw [realArea_closedBall2 (Real.sqrt s) (Real.sqrt_nonneg s)]
      rw [hsq]


/-! #### Fiber sets of the cone at fixed latitude `t` -/

/-- The set of `w`'s such that `insert 0 t w` lies in the cone. -/
def fiberSet (c t : ℝ) : Set ShellX2 := {w : ShellX2 | shellInsert0 t w ∈ preconeSq c}

/-- The `ShellX2`-area (as an integral) of the fiber at latitude `t`. -/
def fiberArea (c t : ℝ) : ℝ :=
  ∫ w : ShellX2, (fiberSet c t).indicator (fun _ : ShellX2 => (1 : ℝ)) w

lemma fiber_mem (c t : ℝ) (w : ShellX2) :
    w ∈ fiberSet c t ↔
      0 < n3 (shellInsert0 t w) ∧ n3 (shellInsert0 t w) < 1 ∧ 0 ≤ t ∧
        c ^ 2 * n3 (shellInsert0 t w) ^ 2 ≤ t ^ 2 := by
  rfl

/-- auxiliary: square inequalities for nonnegative numbers. -/
lemma sq_le_sq_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ≤ b ↔ a ^ 2 ≤ b ^ 2 := by
  constructor
  · intro h
    exact sq_le_sq.mpr (by rw [abs_of_nonneg ha, abs_of_nonneg hb]; exact h)
  · intro h
    have habs : |a| ≤ |b| := sq_le_sq.mp h
    rwa [abs_of_nonneg ha, abs_of_nonneg hb] at habs

lemma sq_lt_sq_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a < b ↔ a ^ 2 < b ^ 2 := by
  constructor
  · intro h
    exact sq_lt_sq.mpr (by rw [abs_of_nonneg ha, abs_of_nonneg hb]; exact h)
  · intro h
    have habs : |a| < |b| := sq_lt_sq.mp h
    rwa [abs_of_nonneg ha, abs_of_nonneg hb] at habs


/-- For `t > 0` the condition `0 < n3 (insert t w)` is automatic. -/
lemma insert_n3_pos {t : ℝ} (ht : 0 < t) (w : ShellX2) : 0 < n3 (shellInsert0 t w) := by
  have hsq : 0 < n3 (shellInsert0 t w) ^ 2 := by
    rw [sq_norm_insert]
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    nlinarith [sq_nonneg (wnorm w)]
  by_contra h
  have hz : n3 (shellInsert0 t w) = 0 := le_antisymm (le_of_not_gt h) (n3_nonneg _)
  have : (0 : ℝ) < 0 := by simpa [hz] using hsq
  norm_num at this

/-- The fiber at `t` is described by quadratic conditions only (for `0 < t`). -/
lemma fiberSet_eq_cond (c t : ℝ) (hc0 : 0 ≤ c) (ht0 : 0 < t) :
    fiberSet c t =
      {w : ShellX2 | t ^ 2 + wnorm w ^ 2 < 1 ∧ c ^ 2 * (t ^ 2 + wnorm w ^ 2) ≤ t ^ 2} := by
  ext w
  rw [fiber_mem]
  have hn : n3 (shellInsert0 t w) ^ 2 = t ^ 2 + wnorm w ^ 2 := sq_norm_insert t w
  have hn3 : 0 ≤ n3 (shellInsert0 t w) := n3_nonneg _
  constructor
  · intro hw
    rcases hw with ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_⟩
    · have h2' : n3 (shellInsert0 t w) ^ 2 < 1 := by
        simpa using (sq_lt_sq_iff_of_nonneg (a := n3 (shellInsert0 t w)) (b := 1) hn3 zero_le_one).mp h2
      rw [hn] at h2'
      exact h2'
    · rw [hn] at h4
      exact h4
  · intro hw
    rcases hw with ⟨h1, h2⟩
    have h2' : n3 (shellInsert0 t w) ^ 2 < 1 := by rwa [hn]
    refine ⟨insert_n3_pos ht0 w, ?_, le_of_lt ht0, ?_⟩
    · have hlt1 : n3 (shellInsert0 t w) < 1 ↔ n3 (shellInsert0 t w) ^ 2 < 1 := by
        simpa using (sq_lt_sq_iff_of_nonneg (a := n3 (shellInsert0 t w)) (b := 1) hn3 zero_le_one)
      exact hlt1.mpr h2'
    · rwa [hn]


/-- `t²(1−c²)/c² < 1 − t²` for `0 < t < c` (and `0 < c`). -/
lemma s1_small_lt_s2 (c t : ℝ) (hc0 : 0 < c) (ht0 : 0 < t) (htc : t < c) :
    t ^ 2 * (1 - c ^ 2) / c ^ 2 < 1 - t ^ 2 := by
  have htsq : t ^ 2 < c ^ 2 :=
    (sq_lt_sq_iff_of_nonneg (le_of_lt ht0) (le_of_lt hc0)).mp htc
  have hnum : t ^ 2 * (1 - c ^ 2) < c ^ 2 * (1 - t ^ 2) := by nlinarith [htsq]
  have hc2pos : 0 < c ^ 2 := sq_pos_of_pos hc0
  have hdiv : t ^ 2 * (1 - c ^ 2) / c ^ 2 < c ^ 2 * (1 - t ^ 2) / c ^ 2 := by
    exact div_lt_div_of_pos_right hnum hc2pos
  have hright : c ^ 2 * (1 - t ^ 2) / c ^ 2 = 1 - t ^ 2 := by
    field_simp [ne_of_gt hc2pos]
  rwa [hright] at hdiv

/-- `0 ≤ t²(1−c²)/c²` for `0 < t`, `0 < c ≤ 1`. -/
lemma s1_small_nonneg (c t : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (ht0 : 0 < t) :
    0 ≤ t ^ 2 * (1 - c ^ 2) / c ^ 2 := by
  have h1 : 0 ≤ t ^ 2 := sq_nonneg t
  have h1mc : 0 ≤ 1 - c ^ 2 := by
    have hcsq : c ^ 2 ≤ 1 := by
      simpa using (sq_le_sq_iff_of_nonneg (a := c) (b := 1) (le_of_lt hc0) zero_le_one).mp hc1
    nlinarith
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc0
  positivity

/-- `1 − t² ≥ 0` for `0 ≤ t < 1`. -/
lemma s2_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 ≤ 1 - t ^ 2 := by
  have htsq : t ^ 2 < 1 := by
    simpa using (sq_lt_sq_iff_of_nonneg (a := t) (b := 1) ht0 zero_le_one).mp ht1
  nlinarith

/-- For `0 < t < c`, the fiber is the closed disk of radius-squared `s = t²(1-c²)/c²`. -/
lemma fiber_small_disk (c t : ℝ) (hc0 : 0 < c) (ht0 : 0 < t) (htc : t < c) :
    fiberSet c t = {w : ShellX2 | wnorm w ^ 2 ≤ t ^ 2 * (1 - c ^ 2) / c ^ 2} := by
  rw [fiberSet_eq_cond c t (le_of_lt hc0) ht0]
  ext w
  constructor
  · intro hw
    rcases hw with ⟨hA, hB⟩
    have hc2pos : 0 < c ^ 2 := sq_pos_of_pos hc0
    have h1 : c ^ 2 * wnorm w ^ 2 ≤ t ^ 2 - c ^ 2 * t ^ 2 := by nlinarith
    have hdiv : (c ^ 2 * wnorm w ^ 2) / c ^ 2 ≤ (t ^ 2 - c ^ 2 * t ^ 2) / c ^ 2 := by
      exact div_le_div_of_nonneg_right h1 (le_of_lt hc2pos)
    have hleft : (c ^ 2 * wnorm w ^ 2) / c ^ 2 = wnorm w ^ 2 := by
      field_simp [ne_of_gt hc2pos]
    have hright : (t ^ 2 - c ^ 2 * t ^ 2) / c ^ 2 = t ^ 2 * (1 - c ^ 2) / c ^ 2 := by ring
    rwa [hleft, hright] at hdiv
  · intro hw
    have hs1lt : t ^ 2 * (1 - c ^ 2) / c ^ 2 < 1 - t ^ 2 := s1_small_lt_s2 c t hc0 ht0 htc
    have hw1 : wnorm w ^ 2 < 1 - t ^ 2 := lt_of_le_of_lt hw hs1lt
    have hA : t ^ 2 + wnorm w ^ 2 < 1 := by nlinarith
    have hc2pos : 0 < c ^ 2 := sq_pos_of_pos hc0
    have hc2s : c ^ 2 * (t ^ 2 * (1 - c ^ 2) / c ^ 2) = t ^ 2 * (1 - c ^ 2) := by
      field_simp [ne_of_gt hc2pos]
    have hmul : c ^ 2 * wnorm w ^ 2 ≤ c ^ 2 * (t ^ 2 * (1 - c ^ 2) / c ^ 2) :=
      mul_le_mul_of_nonneg_left hw (le_of_lt hc2pos)
    have hmul' : c ^ 2 * wnorm w ^ 2 ≤ t ^ 2 * (1 - c ^ 2) := by simpa [hc2s] using hmul
    have hB : c ^ 2 * (t ^ 2 + wnorm w ^ 2) ≤ t ^ 2 := by nlinarith
    exact ⟨hA, hB⟩

/-- Fiber area on `0 < t < c`. -/
lemma fiberArea_small (c t : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (ht0 : 0 < t) (htc : t < c) :
    fiberArea c t = π * (t ^ 2 * (1 - c ^ 2) / c ^ 2) := by
  rw [fiberArea]
  rw [fiber_small_disk c t hc0 ht0 htc]
  exact shellX2_disk_le_area (t ^ 2 * (1 - c ^ 2) / c ^ 2) (s1_small_nonneg c t hc0 hc1 ht0)

/-- For `0 < c`, `c ≤ t < 1`, the fiber is the open disk of radius-squared `s = 1-t²`. -/
lemma fiber_large_disk (c t : ℝ) (hc0 : 0 < c) (htc : c ≤ t) (ht1 : t < 1) :
    fiberSet c t = {w : ShellX2 | wnorm w ^ 2 < 1 - t ^ 2} := by
  have ht0 : 0 < t := lt_of_lt_of_le hc0 htc
  rw [fiberSet_eq_cond c t (le_of_lt hc0) ht0]
  ext w
  constructor
  · intro hw
    rcases hw with ⟨hA, hB⟩
    exact (by nlinarith : wnorm w ^ 2 < 1 - t ^ 2)
  · intro hw
    have htsq : c ^ 2 ≤ t ^ 2 := by
      simpa using (sq_le_sq_iff_of_nonneg (a := c) (b := t) (le_of_lt hc0) (le_of_lt ht0)).mp htc
    have hnum : c ^ 2 * (1 - t ^ 2) ≤ t ^ 2 * (1 - c ^ 2) := by nlinarith [htsq]
    have hc2pos : 0 < c ^ 2 := sq_pos_of_pos hc0
    have hleft : c ^ 2 * (1 - t ^ 2) / c ^ 2 = 1 - t ^ 2 := by
      field_simp [ne_of_gt hc2pos]
    have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt hc2pos)
    have hs : 1 - t ^ 2 ≤ t ^ 2 * (1 - c ^ 2) / c ^ 2 := by
      rwa [hleft] at hdiv
    have hw2 : wnorm w ^ 2 < 1 - t ^ 2 := hw
    have hle : wnorm w ^ 2 ≤ t ^ 2 * (1 - c ^ 2) / c ^ 2 := le_trans (le_of_lt hw2) hs
    have hc2s : c ^ 2 * (t ^ 2 * (1 - c ^ 2) / c ^ 2) = t ^ 2 * (1 - c ^ 2) := by
      field_simp [ne_of_gt hc2pos]
    have hmul : c ^ 2 * wnorm w ^ 2 ≤ c ^ 2 * (t ^ 2 * (1 - c ^ 2) / c ^ 2) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hc2pos)
    have hmul' : c ^ 2 * wnorm w ^ 2 ≤ t ^ 2 * (1 - c ^ 2) := by simpa [hc2s] using hmul
    have hB : c ^ 2 * (t ^ 2 + wnorm w ^ 2) ≤ t ^ 2 := by nlinarith
    have hw2 : wnorm w ^ 2 < 1 - t ^ 2 := hw
    exact ⟨(by nlinarith : t ^ 2 + wnorm w ^ 2 < 1), hB⟩

/-- Fiber area on `0 < c`, `c ≤ t < 1`. -/
lemma fiberArea_large (c t : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (htc : c ≤ t) (ht1 : t < 1) :
    fiberArea c t = π * (1 - t ^ 2) := by
  rw [fiberArea]
  rw [fiber_large_disk c t hc0 htc ht1]
  exact shellX2_disk_lt_area (1 - t ^ 2) (s2_nonneg (le_of_lt (lt_of_lt_of_le hc0 htc)) ht1)

/-- Fiber is empty for `t ≤ 0` (when `0 < c`). -/
lemma fiber_zero_nonpos (c t : ℝ) (hc0 : 0 < c) (ht : t ≤ 0) : fiberArea c t = 0 := by
  unfold fiberArea
  -- the fiber set is empty
  have hempty : fiberSet c t = ∅ := by
    ext w
    constructor
    · intro hw
      rw [fiber_mem] at hw
      rcases hw with ⟨h1, h2, h3, h4⟩
      exfalso
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
      have hc2pos : 0 < c ^ 2 := sq_pos_of_pos hc0
      -- 0 < n3 and c²·n3² ≤ t² ≤ 0 impossible
      have hz : n3 (shellInsert0 t w) = 0 := by
        have hle : c ^ 2 * n3 (shellInsert0 t w) ^ 2 ≤ 0 := by nlinarith
        have hnn : 0 ≤ n3 (shellInsert0 t w) ^ 2 := sq_nonneg _
        have hcnn : 0 ≤ c ^ 2 * n3 (shellInsert0 t w) ^ 2 := mul_nonneg (le_of_lt hc2pos) hnn
        have hz' : c ^ 2 * n3 (shellInsert0 t w) ^ 2 = 0 := le_antisymm hle hcnn
        have hz'' : n3 (shellInsert0 t w) ^ 2 = 0 := by
          exact (mul_eq_zero.mp hz').resolve_left (ne_of_gt hc2pos)
        exact sq_eq_zero_iff.mp hz''
      linarith
    · intro hw
      exact False.elim hw
  rw [hempty]
  simp


/-- Fiber is empty for `t ≥ 1`. -/
lemma fiber_zero_ge (c t : ℝ) (ht : 1 ≤ t) : fiberArea c t = 0 := by
  unfold fiberArea
  have hempty : fiberSet c t = ∅ := by
    ext w
    constructor
    · intro hw
      rw [fiber_mem] at hw
      rcases hw with ⟨h1, h2, h3, h4⟩
      exfalso
      have hn1 : n3 (shellInsert0 t w) ≥ t := by
        -- n3² = t² + wnorm² ≥ t² and t ≥ 1 ≥ 0 gives n3 ≥ t
        have hsq1 : t ^ 2 ≤ n3 (shellInsert0 t w) ^ 2 := by
          rw [sq_norm_insert]
          nlinarith [sq_nonneg (wnorm w)]
        have ht1 : 0 ≤ t := le_trans zero_le_one ht
        have ht' : t ≥ 1 := ht
        have hb : |t| ≤ |n3 (shellInsert0 t w)| := by
          rw [abs_of_nonneg ht1, abs_of_nonneg (n3_nonneg _)]
          rw [sq_le_sq_iff_of_nonneg (a := t) (b := n3 (shellInsert0 t w)) ht1 (n3_nonneg _)]
          exact hsq1
        rwa [abs_of_nonneg ht1, abs_of_nonneg (n3_nonneg _)] at hb
      linarith
    · intro hw
      exact False.elim hw
  rw [hempty]
  simp


/-! #### The outer integral over the latitude -/

/-- The piecewise latitude-area function (coincides with `fiberArea` pointwise for `0 < c ≤ 1`). -/
def sliceFun (c : ℝ) : ℝ → ℝ :=
  fun t => (Set.Ioc (0 : ℝ) c).indicator (fun t => π * (t ^ 2 * (1 - c ^ 2) / c ^ 2)) t +
           (Set.Ioc c 1).indicator (fun t => π * (1 - t ^ 2)) t

/-- value of `sliceFun` in the middle region (`0 < t ≤ c`) -/
lemma sliceFun_small (c t : ℝ) (ht0 : 0 < t) (htc : t ≤ c) :
    sliceFun c t = π * (t ^ 2 * (1 - c ^ 2) / c ^ 2) := by
  unfold sliceFun
  simp [ht0, htc]

/-- value of `sliceFun` in the large region (`c < t ≤ 1`) -/
lemma sliceFun_large (c t : ℝ) (hctl : c < t) (ht1 : t ≤ 1) :
    sliceFun c t = π * (1 - t ^ 2) := by
  unfold sliceFun
  simp [hctl, ht1]

/-- value of `sliceFun` at `t = c` -/
lemma sliceFun_at_c (c : ℝ) (hc0 : 0 < c) : sliceFun c c = π * (1 - c ^ 2) := by
  rw [sliceFun_small c c hc0 (le_refl c)]
  field_simp [ne_of_gt hc0]

/-- value of `sliceFun` for `t ≤ 0` (and `0 < c`) -/
lemma sliceFun_le0 (c t : ℝ) (hc0 : 0 < c) (ht : t ≤ 0) : sliceFun c t = 0 := by
  unfold sliceFun
  have hnot1 : ¬ 0 < t := by linarith
  have hnot2 : ¬ c < t := by linarith
  simp [hnot1, hnot2]

/-- value of `sliceFun` for `t ≥ 1` -/
lemma sliceFun_ge1 (c t : ℝ) (hc1 : c ≤ 1) (ht : 1 ≤ t) : sliceFun c t = 0 := by
  unfold sliceFun
  by_cases hteq : t = 1
  · subst t
    by_cases hcl : c < 1
    · simp [hcl]
    · have h1le : 1 ≤ c := le_of_not_gt hcl
      have hceq : c = 1 := le_antisymm hc1 h1le
      simp [hceq]
  · have hgt : 1 < t := lt_of_le_of_ne ht (Ne.symm hteq)
    have hnot1 : ¬ t ≤ c := by linarith
    have hnot2 : ¬ t ≤ 1 := by linarith
    simp [hnot1, hnot2]

/-- `fiberArea` equals the piecewise function pointwise (for `0 < c ≤ 1`). -/
lemma fiberArea_eq_sliceFun (c t : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    fiberArea c t = sliceFun c t := by
  by_cases ht0 : t ≤ 0
  · rw [sliceFun_le0 c t hc0 ht0]
    exact fiber_zero_nonpos c t hc0 ht0
  · have htpos : 0 < t := lt_of_not_ge ht0
    by_cases ht1 : t < 1
    · by_cases htc : t < c
      · rw [sliceFun_small c t htpos (le_of_lt htc)]
        exact fiberArea_small c t hc0 hc1 htpos htc
      · have hct : c ≤ t := le_of_not_gt htc
        rcases lt_or_eq_of_le hct with hctl | hteq
        · rw [sliceFun_large c t hctl (le_of_lt ht1)]
          exact fiberArea_large c t hc0 hc1 (le_of_lt hctl) ht1
        · subst t
          rw [sliceFun_at_c c hc0]
          exact fiberArea_large c c hc0 hc1 (le_refl c) ht1
    · have htge : 1 ≤ t := le_of_not_gt ht1
      rw [sliceFun_ge1 c t hc1 htge]
      exact fiber_zero_ge c t htge

/-- The latitude integral of the slice area. -/
lemma sliceFun_integral (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (∫ t : ℝ, sliceFun c t) = 2 * π / 3 * (1 - c) := by
  -- support of sliceFun lies in (0,1], so the full integral equals the interval integral 0..1
  have hsupp : Function.support (sliceFun c) ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro t ht
    -- ht : sliceFun c t ≠ 0: from lemmas: t not ≤ 0 and not > 1.
    have hle0 : ¬ t ≤ 0 := by
      intro hz
      have : sliceFun c t = 0 := sliceFun_le0 c t hc0 hz
      exact ht this
    have hgt1 : ¬ 1 < t := by
      intro hg
      have : sliceFun c t = 0 := by
        unfold sliceFun
        have hnot1 : ¬ t ≤ c := by linarith
        have hnot2 : ¬ t ≤ 1 := by linarith
        simp [hnot1, hnot2]
      exact ht this
    exact ⟨lt_of_not_ge hle0, le_of_not_gt hgt1⟩
  have hint01 : (∫ t : ℝ, sliceFun c t) = ∫ t in (0 : ℝ)..1, sliceFun c t :=
    (intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hsupp).symm
  -- split 0..1 at c
  have hcont0 : ContinuousOn (sliceFun c) (Set.Icc (0 : ℝ) c) := by
    let r0 : ℝ := π * (1 - c ^ 2) / c ^ 2
    have hA2 : ContinuousOn (fun t : ℝ => r0 * t ^ 2) (Set.Icc (0 : ℝ) c) :=
      (by fun_prop : Continuous (fun t : ℝ => r0 * t ^ 2)).continuousOn
    have hEq0 : Set.EqOn (sliceFun c) (fun t : ℝ => r0 * t ^ 2) (Set.Icc (0:ℝ) c) := by
      intro t ht
      rcases ht with ⟨h0, hc⟩
      by_cases htz : t = 0
      · subst t
        rw [sliceFun_le0 c 0 hc0 (le_refl 0)]
        simp [r0]
      · have htpos : 0 < t := lt_of_le_of_ne h0 (Ne.symm htz)
        have hv := sliceFun_small c t htpos hc
        rw [hv]
        unfold r0
        ring
    exact hA2.congr hEq0
  have hcont1 : ContinuousOn (sliceFun c) (Set.Icc c 1) := by
    have hEq1 : Set.EqOn (sliceFun c) (fun t : ℝ => π * (1 - t ^ 2)) (Set.Icc c 1) := by
      intro t ht
      rcases ht with ⟨hct, ht1⟩
      by_cases hteq : t = c
      · subst t
        exact sliceFun_at_c c hc0
      · have hctl : c < t := lt_of_le_of_ne hct (Ne.symm hteq)
        exact sliceFun_large c t hctl ht1
    have hBc : ContinuousOn (fun t : ℝ => π * (1 - t ^ 2)) (Set.Icc c 1) :=
      (by fun_prop : Continuous (fun t : ℝ => π * (1 - t ^ 2))).continuousOn
    exact hBc.congr hEq1
  have hfi0 : IntervalIntegrable (sliceFun c) volume (0 : ℝ) c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt hc0)]
    exact hcont0
  have hfic : IntervalIntegrable (sliceFun c) volume c 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hc1]
    exact hcont1
  have hsplit : (∫ t in (0 : ℝ)..1, sliceFun c t) =
      (∫ t in (0 : ℝ)..c, sliceFun c t) + ∫ t in c..1, sliceFun c t := by
    exact (intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := (0:ℝ)) (b := c) hfi0 hfic).symm
  -- congr to polynomial A on (0,c] and B on (c,1]
  have hA : ∀ᵐ t : ℝ ∂volume, t ∈ Set.uIoc (0:ℝ) c →
      sliceFun c t = π * (t ^ 2 * (1 - c ^ 2) / c ^ 2) := by
    filter_upwards with t ht
    rw [Set.uIoc_of_le (le_of_lt hc0)] at ht
    exact sliceFun_small c t ht.1 ht.2
  have hB : ∀ᵐ t : ℝ ∂volume, t ∈ Set.uIoc c 1 →
      sliceFun c t = π * (1 - t ^ 2) := by
    filter_upwards with t ht
    rw [Set.uIoc_of_le hc1] at ht
    exact sliceFun_large c t ht.1 ht.2
  have hInt0 : (∫ t in (0 : ℝ)..c, sliceFun c t) =
      (∫ t in (0 : ℝ)..c, π * (t ^ 2 * (1 - c ^ 2) / c ^ 2)) := by
    exact intervalIntegral.integral_congr_ae hA
  have hIntc : (∫ t in c..1, sliceFun c t) = (∫ t in c..1, π * (1 - t ^ 2)) := by
    exact intervalIntegral.integral_congr_ae hB
  rw [hint01, hsplit, hInt0, hIntc]
  -- evaluate the two polynomial interval integrals
  have hval0 : (∫ t in (0 : ℝ)..c, π * (t ^ 2 * (1 - c ^ 2) / c ^ 2)) =
      π * (1 - c ^ 2) / c ^ 2 * (c ^ 3 / 3) := by
    have hpoly : (fun t : ℝ => π * (t ^ 2 * (1 - c ^ 2) / c ^ 2)) =
        fun t : ℝ => (π * (1 - c ^ 2) / c ^ 2) * t ^ 2 := by
      funext t; ring
    rw [hpoly]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_pow]
    norm_num
  have hval1 : (∫ t in c..1, π * (1 - t ^ 2)) = π * ((1 - c) - (1 - c ^ 3) / 3) := by
    rw [intervalIntegral.integral_const_mul]
    have hf : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume c 1 := intervalIntegrable_const
    have hg : IntervalIntegrable (fun x : ℝ => x ^ 2) volume c 1 := by
      exact (by fun_prop : Continuous (fun x : ℝ => x ^ 2)).intervalIntegrable c 1
    have hform : (∫ t in c..1, (1 : ℝ) - t ^ 2) =
        (∫ t in c..1, (fun _ : ℝ => (1 : ℝ)) t - (fun t : ℝ => t ^ 2) t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rfl
    rw [hform]
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t ^ 2) hf hg]
    rw [intervalIntegral.integral_const]
    simp
    norm_num
  have hsum : π * (1 - c ^ 2) / c ^ 2 * (c ^ 3 / 3) + π * ((1 - c) - (1 - c ^ 3) / 3) =
      π * (2 / 3) * (1 - c) := by
    have hcne : c ≠ 0 := ne_of_gt hc0
    field_simp [hcne]
    ring
  rw [hval0, hval1, hsum]
  ring

/-- The region `n3 < 1` has finite ShellX3 measure (transferred from the unit ball of `ℝ³`). -/
lemma n3_lt_one_volume_finite :
    (volume : Measure ShellX3) {x : ShellX3 | n3 x < 1} < ⊤ := by
  let B : Set ℝ³ := Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
  have hset : {x : ShellX3 | n3 x < 1} = (WithLp.toLp 2) ⁻¹' B := by
    ext x
    change n3 x < 1 ↔ (WithLp.toLp 2 x) ∈ B
    unfold n3
    rw [Metric.mem_ball, dist_zero_right]
  rw [hset]
  -- volume of preimage equals volume of the ball
  have hvol : (volume : Measure ShellX3) ((WithLp.toLp 2) ⁻¹' B) = (volume : Measure ℝ³) B :=
    toLp3_measurePreserving.measure_preimage (Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  rw [hvol]
  rw [EuclideanSpace.volume_ball_fin_three]
  exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

/-- The cone (ShellX3 version) has finite measure. -/
lemma preconeSq_finite (c : ℝ) : (volume : Measure ShellX3) (preconeSq c) < ⊤ := by
  exact lt_of_le_of_lt
    (measure_mono (fun x hx => by rcases hx with ⟨h1, h2, h3, h4⟩; exact h2))
    (n3_lt_one_volume_finite)

/-- Cone indicator is integrable over ShellX3. -/
lemma preconeSq_indicator_integrable (c : ℝ) :
    Integrable ((preconeSq c).indicator (fun _ : ShellX3 => (1 : ℝ))) := by
  rw [integrable_indicator_iff (preconeSq_measurable c)]
  exact integrableOn_const (hs := (preconeSq_finite c).ne)

/-- The real volume of the cone (ShellX3-coordinates). -/
lemma shell_cone_volreal (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (∫ x : ShellX3, (preconeSq c).indicator (fun _ : ShellX3 => (1 : ℝ)) x) =
      2 * π / 3 * (1 - c) := by
  let f : ShellX3 → ℝ := (preconeSq c).indicator (fun _ : ShellX3 => (1 : ℝ))
  have hint : Integrable f := by simpa [f] using preconeSq_indicator_integrable c
  have hii : (fun t : ℝ => ∫ w : ShellX2, f (shellInsert0 t w)) = fun t : ℝ => fiberArea c t := by
    funext t
    unfold fiberArea f
    exact congrArg (fun g : ShellX2 → ℝ => ∫ w : ShellX2, g w) (funext (fun w => by rfl))
  calc
    (∫ x : ShellX3, f x) = (∫ t : ℝ, ∫ w : ShellX2, f (shellInsert0 t w)) :=
      shell_integral_peel0 f hint
    _ = (∫ t : ℝ, fiberArea c t) := by rw [hii]
    _ = (∫ t : ℝ, sliceFun c t) := by
      exact congrArg (fun g : ℝ → ℝ => ∫ t : ℝ, g t) (funext fun t => fiberArea_eq_sliceFun c t hc0 hc1)
    _ = 2 * π / 3 * (1 - c) := sliceFun_integral c hc0 hc1


/-! ### From cone volumes to cap measures -/

/-- Real measure of the cone equals the ENNReal measure value. -/
lemma preconeSq_volume_ofReal (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (volume : Measure ShellX3) (preconeSq c) = ENNReal.ofReal (2 * π / 3 * (1 - c)) := by
  rw [← ENNReal.ofReal_toReal (preconeSq_finite c).ne]
  congr 1
  rw [← measureReal_def]
  rw [← integral_indicator_one (preconeSq_measurable c)]
  exact shell_cone_volreal c hc0 hc1

/-- Volume of the cone equals the ShellX3-volume of `preconeSq` (for `0 ≤ c`). -/
lemma shell_cone_volume_eq (c : ℝ) (hc0 : 0 ≤ c) :
    (volume : Measure ℝ³) (shellCone3 c) = (volume : Measure ShellX3) (preconeSq c) := by
  rw [shell_cone3_eq, shell_cone3'_eq_sq c hc0]
  rw [preconeSq_eq_preimage]
  exact (toLp3_measurePreserving.measure_preimage
    (shellCone3sq_measurable c).nullMeasurableSet).symm

/-- Cap measure for `0 < c < 1`. -/
lemma shell_cap_measure_pos (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (volume.toSphere : Measure ShellS2) (shellCap c) = ENNReal.ofReal (2 * π * (1 - c)) := by
  calc
    (volume.toSphere : Measure ShellS2) (shellCap c) =
        (3 : ℝ≥0∞) * (volume : Measure ℝ³) (shellCone3 c) := shell_toSphere_cap c
    _ = (3 : ℝ≥0∞) * ENNReal.ofReal (2 * π / 3 * (1 - c)) := by
      rw [shell_cone_volume_eq c (le_of_lt hc0)]
      rw [preconeSq_volume_ofReal c hc0 (le_of_lt hc1)]
    _ = ENNReal.ofReal (2 * π * (1 - c)) := by
      have hnn : 0 ≤ 2 * π / 3 * (1 - c) := by positivity
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring

/-- Total mass of the sphere measure is `4π` (ENNReal version). -/
lemma shell_toSphere_total_enn :
    (volume.toSphere : Measure ShellS2) Set.univ = ENNReal.ofReal (4 * π) := by
  have htop : (volume.toSphere : Measure ShellS2) Set.univ ≠ (∞ : ℝ≥0∞) :=
    shell_toSphere_finite.measure_univ_lt_top.ne
  rw [← ENNReal.ofReal_toReal htop]
  congr 1
  exact shell_toSphere_total

/-- Negation of sphere points, an ambient-linear-isometry action. -/
noncomputable def shellNegS2 (u : ShellS2) : ShellS2 :=
  ⟨- (u : ℝ³), by
    have hu : (u : ℝ³) ∈ Metric.sphere (0 : ℝ³) 1 := u.2
    rw [Metric.mem_sphere, dist_zero_right] at hu
    rw [Metric.mem_sphere, dist_zero_right]
    simp [hu]⟩

/-- Ambient negation is a linear isometry (measure preserving). -/
noncomputable def negLIE : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  { toLinearEquiv := (LinearEquiv.neg ℝ (M := EuclideanSpace ℝ (Fin 3))),
    norm_map' := by intro x; simp }

/-- Ambient negation preserves the volume on `ℝ³`. -/
lemma neg_volume_preserving : MeasurePreserving (fun x : ℝ³ => -x) volume volume := by
  exact negLIE.measurePreserving

lemma shellNegS2_measurable : Measurable shellNegS2 := by
  unfold shellNegS2
  fun_prop

/-- Negation maps the shell preimage of a cap to the mirrored set. -/
lemma coe_image_neg_preimage (s : Set ShellS2) :
    ((↑) '' (shellNegS2 ⁻¹' s)) = (fun x : ℝ³ => -x) ⁻¹' ((↑) '' s) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨shellNegS2 u, ?_, ?_⟩
    · simpa [shellNegS2] using hu
    · simp [shellNegS2]
  · intro hx
    change -x ∈ ((↑) '' s) at hx
    rcases hx with ⟨w, hw, hxw⟩
    refine ⟨shellNegS2 w, ?_, ?_⟩
    · simpa [shellNegS2] using hw
    · have h := congrArg Neg.neg hxw
      simpa [shellNegS2] using h

/-- Positive scalars commute with negation (set form). -/
lemma neg_smul_set (S : Set ℝ³) :
    (fun x : ℝ³ => -x) ⁻¹' (Set.Ioo (0 : ℝ) 1 • S) =
      Set.Ioo (0 : ℝ) 1 • ((fun x : ℝ³ => -x) ⁻¹' S) := by
  ext x
  constructor
  · intro hx
    change -x ∈ Set.Ioo (0 : ℝ) 1 • S at hx
    rcases hx with ⟨a, ha, z, hz, hxz⟩
    refine ⟨a, ha, -z, ?_, ?_⟩
    · simpa [Set.mem_preimage] using hz
    · have h := congrArg Neg.neg hxz
      simp at h
      rw [← smul_neg] at h
      exact h
  · rintro ⟨a, ha, z, hz, hxz⟩
    change -x ∈ Set.Ioo (0 : ℝ) 1 • S
    refine ⟨a, ha, -z, ?_, ?_⟩
    · simpa [Set.mem_preimage] using hz
    · rw [← hxz]
      exact smul_neg a z

/-- `toSphere` is invariant under negation (for cap-shaped measurable sets). -/
lemma toSphere_neg_cap (a : ℝ) :
    (volume.toSphere : Measure ShellS2) {u : ShellS2 | (u : ℝ³) 0 ≤ -a} =
      (volume.toSphere : Measure ShellS2) (shellCap a) := by
  have hpre : {u : ShellS2 | (u : ℝ³) 0 ≤ -a} = shellNegS2 ⁻¹' (shellCap a) := by
    ext u
    simp [shellCap, shellNegS2, le_neg]
  rw [hpre]
  have hset : Set.Ioo (0 : ℝ) 1 • ((↑) '' (shellNegS2 ⁻¹' (shellCap a))) =
      (fun x : ℝ³ => -x) ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' (shellCap a))) := by
    rw [coe_image_neg_preimage]
    exact (neg_smul_set ((↑) '' (shellCap a))).symm
  rw [Measure.toSphere_apply' (μ := (volume : Measure ℝ³))
    (s := shellNegS2 ⁻¹' (shellCap a))
    (shellNegS2_measurable (shellCap_measurable a))]
  rw [Measure.toSphere_apply' (μ := (volume : Measure ℝ³)) (s := shellCap a) (shellCap_measurable a)]
  rw [finrank_r3]
  congr 1
  rw [hset]
  rw [show Set.Ioo (0 : ℝ) 1 • ((↑) '' (shellCap a)) = shellCone3 a by
    exact shell_cone_smul_cap a]
  exact (neg_volume_preserving.measure_preimage (shellCone3_measurable a).nullMeasurableSet)


/-! ### Open caps, hemisphere and negative latitudes -/

/-- Approximating thresholds for an open cap `{u₀ > b}`. -/
def capSeq (b : ℝ) (n : ℕ) : ℝ := b + (1 - b) / ((n : ℝ) + 2)

lemma capSeq_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (n : ℕ) : 0 < capSeq b n := by
  unfold capSeq
  by_cases hb : b = 0
  · subst b
    positivity
  · have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    have h2 : 0 ≤ (1 - b) / ((n : ℝ) + 2) :=
      div_nonneg (sub_nonneg.2 (le_of_lt hb1)) (by positivity)
    nlinarith

lemma capSeq_lt_one {b : ℝ} (hb1 : b < 1) (n : ℕ) : capSeq b n < 1 := by
  unfold capSeq
  have hb1b : 0 < 1 - b := sub_pos.2 hb1
  have hn2p : 0 < (n : ℝ) + 2 := by positivity
  have hn2 : 1 < (n : ℝ) + 2 := by
    have : (1 : ℕ) < n + 2 := by omega
    exact_mod_cast this
  have hf : (1 - b) / ((n : ℝ) + 2) < 1 - b := by
    exact (div_lt_iff₀ hn2p).mpr (by
      have h1 := mul_lt_mul_of_pos_left hn2 hb1b
      simpa using h1)
  nlinarith

lemma capSeq_antitone {b : ℝ} (hb1 : b ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    capSeq b n ≤ capSeq b m := by
  unfold capSeq
  have hmnr : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
    exact_mod_cast (by omega : m + 2 ≤ n + 2)
  have h1b : 0 ≤ 1 - b := sub_nonneg.2 hb1
  have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hm2, hn2]
  nlinarith [hmnr, h1b]

/-- `{u₀ > b}` is covered by the approximating closed caps. -/
lemma openCap_eq_iUnion {b : ℝ} (hb1 : b < 1) :
    {u : ShellS2 | b < (u : ℝ³) 0} = ⋃ n : ℕ, shellCap (capSeq b n) := by
  ext u
  constructor
  · intro hu
    have hpos : 0 < (u : ℝ³) 0 - b := sub_pos.2 hu
    have h1b : 0 < 1 - b := sub_pos.2 hb1
    rcases exists_nat_gt ((1 - b) / ((u : ℝ³) 0 - b) - 2) with ⟨N, hN⟩
    rw [Set.mem_iUnion]
    refine ⟨N, ?_⟩
    change capSeq b N ≤ (u : ℝ³) 0
    unfold capSeq
    have hNpos : 0 < (N : ℝ) + 2 := by positivity
    have hc : (1 - b) / ((u : ℝ³) 0 - b) < (N : ℝ) + 2 := by nlinarith
    have hA : (1 - b) < ((u : ℝ³) 0 - b) * ((N : ℝ) + 2) := by
      have hmm := (div_lt_iff₀ hpos).mp hc
      nlinarith
    have g2 : (1 - b) / ((N : ℝ) + 2) ≤ (u : ℝ³) 0 - b :=
      (div_le_iff₀ hNpos).mpr (le_of_lt hA)
    set q : ℝ := (1 - b) / ((N : ℝ) + 2) with hq
    change b + q ≤ (u : ℝ³) 0
    nlinarith
  · intro hu
    rw [Set.mem_iUnion] at hu
    rcases hu with ⟨n, hn⟩
    have hn' : capSeq b n ≤ (u : ℝ³) 0 := by simpa [shellCap] using hn
    have hbpos : 0 < (1 - b) / ((n : ℝ) + 2) := by
      exact div_pos (sub_pos.2 hb1) (by positivity)
    have hbl : b < b + (1 - b) / ((n : ℝ) + 2) := by nlinarith
    exact lt_of_lt_of_le hbl hn

/-- Measure of an open cap: `σ{u₀ > b} = 2π(1-b)` for `0 ≤ b < 1`. -/
lemma shell_cap_open (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (volume.toSphere : Measure ShellS2) {u : ShellS2 | b < (u : ℝ³) 0} =
      ENNReal.ofReal (2 * π * (1 - b)) := by
  have hmono : Monotone (fun n : ℕ => shellCap (capSeq b n)) := by
    intro m n hmn x hx
    unfold shellCap at hx ⊢
    exact le_trans (capSeq_antitone (le_of_lt hb1) hmn) hx
  have htend := tendsto_measure_iUnion_atTop (μ := (volume.toSphere : Measure ShellS2)) hmono
  have hval : Tendsto (fun n : ℕ =>
      (volume.toSphere : Measure ShellS2) (shellCap (capSeq b n)))
      atTop (𝓝 (ENNReal.ofReal (2 * π * (1 - b)))) := by
    have hpts : ∀ n, (volume.toSphere : Measure ShellS2) (shellCap (capSeq b n)) =
        ENNReal.ofReal (2 * π * (1 - capSeq b n)) := by
      intro n
      exact shell_cap_measure_pos (capSeq b n) (capSeq_pos hb0 hb1 n) (capSeq_lt_one hb1 n)
    have hrew : (fun n : ℕ => (volume.toSphere : Measure ShellS2) (shellCap (capSeq b n))) =
        fun n : ℕ => ENNReal.ofReal (2 * π * (1 - capSeq b n)) := by
      funext n
      exact hpts n
    rw [hrew]
    have hsum : (fun n : ℕ => ENNReal.ofReal (2 * π * (1 - capSeq b n))) =
        fun n : ℕ => ENNReal.ofReal ((2 * π * (1 - b)) * (1 - 1 / ((n : ℝ) + 2))) := by
      funext n
      congr 1
      unfold capSeq
      ring
    rw [hsum]
    have hrec : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
        have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
        simpa [Function.comp_def, Nat.cast_add] using h
      simpa using (tendsto_const_nhds.sub h2)
    have hreal : Tendsto (fun n : ℕ => (2 * π * (1 - b)) * (1 - 1 / ((n : ℝ) + 2)))
        atTop (𝓝 (2 * π * (1 - b))) := by
      have hmul : Tendsto (fun n : ℕ => (2 * π * (1 - b)) * (1 - 1 / ((n : ℝ) + 2)))
          atTop (𝓝 ((2 * π * (1 - b)) * 1)) :=
        (tendsto_const_nhds (x := (2 * π * (1 - b)))).mul hrec
      convert hmul using 1
      ring
    exact (ENNReal.continuous_ofReal.tendsto (2 * π * (1 - b))).comp hreal
  rw [← openCap_eq_iUnion hb1] at htend
  exact tendsto_nhds_unique htend hval





/-! ### Cap measures across the range, and the pushforward equality -/

/-- Measure continuity from below applied to the sphere measure. -/
lemma toSphere_iUnion_of_tendsto {s : ℕ → Set ShellS2} (hmono : Monotone s)
    {v : ℝ≥0∞} (hval : Tendsto (fun n => (volume.toSphere : Measure ShellS2) (s n)) atTop (𝓝 v)) :
    (volume.toSphere : Measure ShellS2) (⋃ n, s n) = v := by
  have htend := tendsto_measure_iUnion_atTop (μ := (volume.toSphere : Measure ShellS2)) hmono
  exact tendsto_nhds_unique htend hval

/-- The measure of `{u₀ < 0}` is `2π`. -/
lemma shell_neghemisphere : (volume.toSphere : Measure ShellS2) {u : ShellS2 | (u : ℝ³) 0 < 0} =
    ENNReal.ofReal (2 * π) := by
  let s : ℕ → Set ShellS2 := fun n => {u : ShellS2 | (u : ℝ³) 0 ≤ -(1 / ((n : ℝ) + 2))}
  have hmono : Monotone s := by
    intro m n hmn x hx
    have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) := by
      have hm2 : (0:ℝ) < (m : ℝ) + 2 := by positivity
      have hnn : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
        exact_mod_cast (by omega : m + 2 ≤ n + 2)
      exact one_div_le_one_div_of_le hm2 hnn
    have hleq : -(1 / ((m : ℝ) + 2)) ≤ -(1 / ((n : ℝ) + 2)) := by nlinarith
    unfold s at hx ⊢
    exact le_trans hx hleq
  have hset : {u : ShellS2 | (u : ℝ³) 0 < 0} = ⋃ n, s n := by
    ext u
    constructor
    · intro hu
      rw [Set.mem_iUnion]
      have hup : (u : ℝ³) 0 < 0 := hu
      have hA0 : 0 < -(u : ℝ³) 0 := by nlinarith
      rcases exists_nat_gt (1 / (-(u : ℝ³) 0)) with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      have hposN : 0 < (N : ℝ) + 2 := by positivity
      have h1m : 1 < (-(u : ℝ³) 0) * ((N : ℝ) + 2) := by
        have hN2 : (N : ℝ) ≤ (N : ℝ) + 2 := by nlinarith
        have hc : 1 / (-(u : ℝ³) 0) < (N : ℝ) + 2 := by nlinarith [hN2]
        have hmm := (div_lt_iff₀ hA0).mp hc
        nlinarith
      have hgoal : (u : ℝ³) 0 ≤ -1 / ((N : ℝ) + 2) := by
        rw [le_div_iff₀ hposN]
        nlinarith [h1m]
      unfold s
      change (u : ℝ³) 0 ≤ -(1 / ((N : ℝ) + 2))
      have hring : -1 / ((N : ℝ) + 2) = -(1 / ((N : ℝ) + 2)) := by ring
      rwa [hring] at hgoal
    · intro hu
      rw [Set.mem_iUnion] at hu
      rcases hu with ⟨n, hn⟩
      unfold s at hn
      have hdiv : 0 < (1 / ((n : ℝ) + 2)) := by positivity
      have hneg : -(1 / ((n : ℝ) + 2)) < 0 := by
        have : (0 : ℝ) < (1 / ((n : ℝ) + 2)) := hdiv
        nlinarith
      exact lt_of_le_of_lt hn hneg
  -- value limit
  have hval : Tendsto (fun n : ℕ => (volume.toSphere : Measure ShellS2) (s n))
      atTop (𝓝 (ENNReal.ofReal (2 * π))) := by
    have hpts : ∀ n, (volume.toSphere : Measure ShellS2) (s n) =
        ENNReal.ofReal (2 * π * (1 - 1 / ((n : ℝ) + 2))) := by
      intro n
      have hneg := toSphere_neg_cap (1 / ((n : ℝ) + 2))
      -- hneg : toSphere {u | u0 ≤ -(1/(n+2))} = toSphere (cap (1/(n+2)))
      change (volume.toSphere : Measure ShellS2) {u : ShellS2 | (u : ℝ³) 0 ≤ -(1 / ((n : ℝ) + 2))} =
          ENNReal.ofReal (2 * π * (1 - 1 / ((n : ℝ) + 2)))
      rw [hneg]
      have hlt1 : 1 / ((n : ℝ) + 2) < 1 := by
        have h12 : (1 : ℝ) < (n : ℝ) + 2 := by
          have : (1 : ℕ) < n + 2 := by omega
          exact_mod_cast this
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
        nlinarith
      rw [shell_cap_measure_pos (1 / ((n : ℝ) + 2)) (by positivity) hlt1]
    have hrew : (fun n : ℕ => (volume.toSphere : Measure ShellS2) (s n)) =
        fun n : ℕ => ENNReal.ofReal (2 * π * (1 - 1 / ((n : ℝ) + 2))) := by
      funext n
      exact hpts n
    rw [hrew]
    have hrec : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
        have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
        simpa [Function.comp_def, Nat.cast_add] using h
      simpa using (tendsto_const_nhds.sub h2)
    have hreal : Tendsto (fun n : ℕ => (2 * π) * (1 - 1 / ((n : ℝ) + 2)))
        atTop (𝓝 (2 * π)) := by
      have hmul : Tendsto (fun n : ℕ => (2 * π) * (1 - 1 / ((n : ℝ) + 2)))
          atTop (𝓝 ((2 * π) * 1)) :=
        (tendsto_const_nhds (x := (2 * π))).mul hrec
      convert hmul using 1
      ring
    exact (ENNReal.continuous_ofReal.tendsto (2 * π)).comp hreal
  rw [hset]
  exact toSphere_iUnion_of_tendsto hmono hval




/-- ENNReal: bounded above by a sequence tending to zero. -/
lemma ennreal_le_of_tendsto_of_le {x : ℝ≥0∞} {f : ℕ → ℝ≥0∞}
    (hf : Tendsto f atTop (𝓝 (0 : ℝ≥0∞))) (hle : ∀ n, x ≤ f n) : x = 0 := by
  have hx0 : x ≤ 0 := by
    apply ge_of_tendsto hf
    filter_upwards with n
    exact hle n
  exact le_antisymm hx0 bot_le

/-- The north pole (cap at `1`) has measure zero. -/
lemma shell_cap_one_zero : (volume.toSphere : Measure ShellS2) (shellCap 1) = 0 := by
  have hle : ∀ n : ℕ, (volume.toSphere : Measure ShellS2) (shellCap 1) ≤
      ENNReal.ofReal (2 * π / ((n : ℝ) + 2)) := by
    intro n
    have hsub : shellCap 1 ⊆ shellCap (1 - 1 / ((n : ℝ) + 2)) := by
      intro u hu
      unfold shellCap at hu ⊢
      have h : (1 : ℝ) ≤ (u : ℝ³) 0 := hu
      have hc : 1 - 1 / ((n : ℝ) + 2) ≤ 1 := by
        have hdiv : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
        nlinarith
      exact le_trans hc h
    refine le_trans (measure_mono hsub) ?_
    have hval : (volume.toSphere : Measure ShellS2) (shellCap (1 - 1 / ((n : ℝ) + 2))) =
        ENNReal.ofReal (2 * π / ((n : ℝ) + 2)) := by
      have hpos : 0 < 1 - 1 / ((n : ℝ) + 2) := by
        have h12 : (1 : ℝ) < (n : ℝ) + 2 := by
          have : (1 : ℕ) < n + 2 := by omega
          exact_mod_cast this
        have hlt1 : 1 / ((n : ℝ) + 2) < 1 := by
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
          nlinarith
        nlinarith
      have hlt : 1 - 1 / ((n : ℝ) + 2) < 1 := by
        have hdiv : 0 < 1 / ((n : ℝ) + 2) := by positivity
        nlinarith
      rw [shell_cap_measure_pos (1 - 1 / ((n : ℝ) + 2)) hpos hlt]
      congr 1
      field_simp [show ((n : ℝ) + 2) ≠ 0 by positivity]
      ring
    exact hval.le
  apply ennreal_le_of_tendsto_of_le
  · -- ofReal (2π/(n+2)) → 0
    have hreal : Tendsto (fun n : ℕ => (2 * π / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
        have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
        simpa [Function.comp_def, Nat.cast_add] using h
      have hmul : Tendsto (fun n : ℕ => (2 * π) * ((n : ℝ) + 2)⁻¹)
          atTop (𝓝 ((2 * π) * 0)) :=
        (tendsto_const_nhds (x := (2 * π))).mul h2
      convert hmul using 1 <;> ring
    simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  · exact hle

/-- The measure of the hemisphere `{u₀ ≥ 0}` is `2π`. -/
lemma shell_cap_zero : (volume.toSphere : Measure ShellS2) (shellCap 0) = ENNReal.ofReal (2 * π) := by
  have htotal := shell_toSphere_total_enn
  have hd : (shellCap 0) ∪ {u : ShellS2 | (u : ℝ³) 0 < 0} = Set.univ := by
    ext u
    by_cases h : 0 ≤ (u : ℝ³) 0
    · simp [shellCap, h]
    · simp [shellCap, h, lt_of_not_ge h]
  have hdisj : Disjoint (shellCap 0) {u : ShellS2 | (u : ℝ³) 0 < 0} := by
    rw [Set.disjoint_left]
    intro u hu hlt
    change 0 ≤ (u : ℝ³) 0 at hu
    exact (not_le_of_gt hlt) hu
  have hneg_m : MeasurableSet {u : ShellS2 | (u : ℝ³) 0 < 0} := by
    have hf : Measurable (fun u : ShellS2 => (u : ℝ³) 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).measurable.comp measurable_subtype_coe
    exact hf measurableSet_Iio
  have hadd : (volume.toSphere : Measure ShellS2) ((shellCap 0) ∪ {u : ShellS2 | (u : ℝ³) 0 < 0}) =
      (volume.toSphere : Measure ShellS2) (shellCap 0) +
        (volume.toSphere : Measure ShellS2) {u : ShellS2 | (u : ℝ³) 0 < 0} := by
    exact measure_union hdisj hneg_m
  have htot : (volume.toSphere : Measure ShellS2) (shellCap 0) +
        (volume.toSphere : Measure ShellS2) {u : ShellS2 | (u : ℝ³) 0 < 0} =
      ENNReal.ofReal (4 * π) := by
    rw [← htotal, ← hd, ← hadd]
  have hneg := shell_neghemisphere
  have hc : ENNReal.ofReal (4 * π) - ENNReal.ofReal (2 * π) = ENNReal.ofReal (2 * π) := by
    rw [← ENNReal.ofReal_sub (4 * π) (by positivity : (0 : ℝ) ≤ 2 * π)]
    congr 1
    ring
  calc
    (volume.toSphere : Measure ShellS2) (shellCap 0)
        = ENNReal.ofReal (4 * π) - ENNReal.ofReal (2 * π) := by
          have hsum : (volume.toSphere : Measure ShellS2) (shellCap 0) + ENNReal.ofReal (2 * π) =
              ENNReal.ofReal (4 * π) := by
            simpa [hneg] using htot
          have hfin : ENNReal.ofReal (2 * π) ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
          rw [← hsum]
          rw [add_comm]
          rw [ENNReal.add_sub_cancel_left hfin]
    _ = ENNReal.ofReal (2 * π) := hc



/-- Coordinates of sphere points satisfy `-1 ≤ u₀`. -/
lemma sphere_coord0_ge (u : ShellS2) : -1 ≤ (u : ℝ³) 0 := by
  have hb : |(u : ℝ³) 0| ≤ (1 : ℝ) := by
    have hu : ‖(u : ℝ³)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using u.2
    have hsq : ((u : ℝ³) 0) ^ 2 ≤ ‖(u : ℝ³)‖ ^ 2 := by
      rw [shell_sq_norm3]; rw [Fin.sum_univ_three]; simp
      nlinarith [sq_nonneg ((u : ℝ³) 1), sq_nonneg ((u : ℝ³) 2)]
    have habs : |(u : ℝ³) 0| ≤ |‖(u : ℝ³)‖| := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _), hu] at habs
  have h := abs_le.mp hb
  linarith

/-- Cap with latitude `≤ -1` is the whole sphere: `4π`. -/
lemma shell_cap_low (a : ℝ) (ha : a ≤ -1) :
    (volume.toSphere : Measure ShellS2) (shellCap a) = ENNReal.ofReal (4 * π) := by
  have hset : shellCap a = Set.univ := by
    ext u
    constructor
    · intro hu
      trivial
    · intro _
      unfold shellCap
      have hge : -1 ≤ (u : ℝ³) 0 := sphere_coord0_ge u
      exact le_trans ha hge
  rw [hset]
  exact shell_toSphere_total_enn

/-- Cap measures for `-1 < a < 0`. -/
lemma shell_cap_neg (a : ℝ) (hlo : -1 < a) (hhi : a < 0) :
    (volume.toSphere : Measure ShellS2) (shellCap a) = ENNReal.ofReal (2 * π * (1 - a)) := by
  let b : ℝ := -a
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  have ha : a = -b := by dsimp [b]; ring
  have hneq := toSphere_neg_cap (-b)
  -- hneq : toSphere {u0 ≤ -(-b)} = toSphere cap(-b): u0 ≤ b
  have hcomp : (volume.toSphere : Measure ShellS2) {u : ShellS2 | b < (u : ℝ³) 0}ᶜ =
      (volume.toSphere : Measure ShellS2) Set.univ -
        (volume.toSphere : Measure ShellS2) {u : ShellS2 | b < (u : ℝ³) 0} := by
    have hmeas : MeasurableSet {u : ShellS2 | b < (u : ℝ³) 0} := by
      have hf : Measurable (fun u : ShellS2 => (u : ℝ³) 0) :=
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).measurable.comp measurable_subtype_coe
      exact hf measurableSet_Ioi
    have hfin : (volume.toSphere : Measure ShellS2) {u : ShellS2 | b < (u : ℝ³) 0} ≠ (∞ : ℝ≥0∞) := by
      refine lt_top_iff_ne_top.mp ?_
      have hbnd : (volume.toSphere : Measure ShellS2) {u : ShellS2 | b < (u : ℝ³) 0} ≤
          (volume.toSphere : Measure ShellS2) Set.univ := measure_mono (by intro x hx; trivial)
      exact lt_of_le_of_lt hbnd shell_toSphere_finite.measure_univ_lt_top
    exact measure_compl hmeas hfin
  have hsouth : (volume.toSphere : Measure ShellS2) {u : ShellS2 | (u : ℝ³) 0 ≤ b} =
      ENNReal.ofReal (2 * π * (1 + b)) := by
    -- complement relation: {u0 ≤ b} = {u0 > b}ᶜ
    have hcomp2 : (volume.toSphere : Measure ShellS2) {u : ShellS2 | (u : ℝ³) 0 ≤ b} =
        (volume.toSphere : Measure ShellS2) Set.univ -
          (volume.toSphere : Measure ShellS2) {u : ShellS2 | b < (u : ℝ³) 0} := by
      rw [← hcomp]
      congr 1
      ext u
      simp
    have hopen := shell_cap_open b (le_of_lt hb0) hb1
    rw [hcomp2]
    rw [shell_toSphere_total_enn, hopen]
    rw [← ENNReal.ofReal_sub (4 * π) (by positivity : (0 : ℝ) ≤ 2 * π * (1 - b))]
    congr 1
    ring
  calc
    (volume.toSphere : Measure ShellS2) (shellCap a) = ENNReal.ofReal (2 * π * (1 + b)) := by
      rw [ha]
      have hcap : (volume.toSphere : Measure ShellS2) (shellCap (-b)) =
          (volume.toSphere : Measure ShellS2) {u : ShellS2 | (u : ℝ³) 0 ≤ b} := by
        simpa using (toSphere_neg_cap (-b)).symm
      rw [hcap, hsouth]
    _ = ENNReal.ofReal (2 * π * (1 - a)) := by
      dsimp [b]
      ring

/-- Cap measures on the whole interval `[-1,1]`. -/
lemma shell_cap_interval (a : ℝ) (hlo : -1 ≤ a) (hhi : a ≤ 1) :
    (volume.toSphere : Measure ShellS2) (shellCap a) = ENNReal.ofReal (2 * π * (1 - a)) := by
  by_cases h0 : a < 0
  · -- either -1 < a or a = -1
    rcases lt_or_eq_of_le hlo with hlt | heq
    · exact shell_cap_neg a hlt h0
    · subst a
      rw [show ENNReal.ofReal (2 * π * (1 - (-1 : ℝ))) = ENNReal.ofReal (4 * π) by ring]
      exact shell_cap_low (-1) (le_refl (-1))
  · have hge0 : 0 ≤ a := le_of_not_gt h0
    rcases lt_or_eq_of_le hhi with hlt | heq
    · -- a < 1
      rcases eq_or_lt_of_le hge0 with hz | hpos
      · subst a
        simpa using shell_cap_zero
      · exact shell_cap_measure_pos a hpos hlt
    · subst a
      simpa using shell_cap_one_zero



/-- Coordinates of sphere points satisfy `u₀ ≤ 1`. -/
lemma sphere_coord0_le (u : ShellS2) : (u : ℝ³) 0 ≤ 1 := by
  have hb : |(u : ℝ³) 0| ≤ (1 : ℝ) := by
    have hu : ‖(u : ℝ³)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using u.2
    have hsq : ((u : ℝ³) 0) ^ 2 ≤ ‖(u : ℝ³)‖ ^ 2 := by
      rw [shell_sq_norm3]; rw [Fin.sum_univ_three]; simp
      nlinarith [sq_nonneg ((u : ℝ³) 1), sq_nonneg ((u : ℝ³) 2)]
    have habs : |(u : ℝ³) 0| ≤ |‖(u : ℝ³)‖| := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _), hu] at habs
  have h := abs_le.mp hb
  linarith

/-- Caps at latitude `≥ 1` have measure zero. -/
lemma shell_cap_high_zero (a : ℝ) (ha : 1 ≤ a) :
    (volume.toSphere : Measure ShellS2) (shellCap a) = 0 := by
  rcases lt_or_eq_of_le ha with hgt | heq
  · -- a > 1: cap empty
    have hempty : shellCap a = ∅ := by
      ext u
      constructor
      · intro hu
        change a ≤ (u : ℝ³) 0 at hu
        have hle : (u : ℝ³) 0 ≤ 1 := sphere_coord0_le u
        exfalso
        linarith
      · intro hx
        exact False.elim hx
    rw [hempty]
    simp
  · subst a
    exact shell_cap_one_zero


/-- Scalar multiplication of a measure applied to a set. -/
lemma smul_measure_apply (c : ℝ≥0∞) (ν : Measure ℝ) (s : Set ℝ) : (c • ν) s = c * ν s := by
  simp [Measure.smul_apply]

/-- The interval `[-1,1] ∩ [a,∞)` is `[max a (-1), 1]`. -/
lemma Icc_inter_Ici_eq (a : ℝ) : Set.Icc (-1) 1 ∩ Set.Ici a = Set.Icc (max a (-1)) 1 := by
  ext x
  constructor
  · intro hx
    change ((-1 ≤ x ∧ x ≤ 1) ∧ a ≤ x) at hx
    change (max a (-1) ≤ x ∧ x ≤ 1)
    exact ⟨max_le hx.2 hx.1.1, hx.1.2⟩
  · intro hx
    change (max a (-1) ≤ x ∧ x ≤ 1) at hx
    change ((-1 ≤ x ∧ x ≤ 1) ∧ a ≤ x)
    exact ⟨⟨le_trans (le_max_right a (-1)) hx.1, hx.2⟩, le_trans (le_max_left a (-1)) hx.1⟩

/-- Cap measure value for every latitude (clamped form). -/
lemma shell_cap_value (a : ℝ) :
    (volume.toSphere : Measure ShellS2) (shellCap a) =
      ENNReal.ofReal (2 * π * (1 - max a (-1))) := by
  by_cases h1 : 1 ≤ a
  · rw [shell_cap_high_zero a h1]
    have hmax : max a (-1) = a := max_eq_left (le_trans (by norm_num : (-1 : ℝ) ≤ 1) h1)
    rw [hmax]
    have hle0 : 2 * π * (1 - a) ≤ 0 := by
      have hnon : 1 - a ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hnon
    exact (ENNReal.ofReal_eq_zero.mpr hle0).symm
  · have ha1' : a < 1 := lt_of_not_ge h1
    by_cases h2 : a ≤ -1
    · rw [shell_cap_low a h2]
      have hmax : max a (-1) = -1 := max_eq_right h2
      rw [hmax]
      congr 1
      ring
    · have hlo : -1 ≤ a := le_of_not_ge h2
      rw [shell_cap_interval a hlo (le_of_lt ha1')]
      have hmax : max a (-1) = a := max_eq_left hlo
      rw [hmax]

/-- The pushforward on the interval `Ici a`. -/
lemma shellProj_Ici (a : ℝ) : shellProjMu (Set.Ici a) = shellProjNu (Set.Ici a) := by
  unfold shellProjMu shellProjNu
  have hm : Measurable (fun u : ShellS2 => (u : ℝ³) 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).measurable.comp measurable_subtype_coe
  rw [Measure.map_apply hm measurableSet_Ici]
  change (volume.toSphere : Measure ShellS2) (shellCap a) =
      (ENNReal.ofReal (2 * π) • (volume.restrict (Set.Icc (-1) 1) : Measure ℝ)) (Set.Ici a)
  rw [smul_measure_apply]
  rw [Measure.restrict_apply measurableSet_Ici]
  rw [Set.inter_comm, Icc_inter_Ici_eq]
  rw [Real.volume_Icc]
  rw [shell_cap_value a]
  have hprod : ENNReal.ofReal (2 * π) * ENNReal.ofReal (1 - max a (-1)) =
      ENNReal.ofReal (2 * π * (1 - max a (-1))) := by
    by_cases hle : max a (-1) ≤ 1
    · have hnn : 0 ≤ 1 - max a (-1) := by linarith
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
    · have hgt : 1 < max a (-1) := lt_of_not_ge hle
      have hneg : 1 - max a (-1) < 0 := by linarith
      have h0 : ENNReal.ofReal (1 - max a (-1)) = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_lt hneg)
      rw [h0]
      rw [mul_zero]
      have hneg2 : 2 * π * (1 - max a (-1)) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) hneg
      exact (ENNReal.ofReal_eq_zero.mpr (le_of_lt hneg2)).symm
  rw [hprod]

/-- Finite measure instance for the pushforward. -/
lemma shellProjMu_finite : IsFiniteMeasure shellProjMu := by
  unfold shellProjMu
  refine ⟨?_⟩
  have hm : Measurable (fun u : ShellS2 => (u : ℝ³) 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).measurable.comp measurable_subtype_coe
  rw [Measure.map_apply hm MeasurableSet.univ]
  exact shell_toSphere_finite.measure_univ_lt_top

/-- Pushforward of the unit-sphere measure under the first coordinate is `2π`-times
Lebesgue measure on `[−1,1]`. -/
theorem shell_proj_measure :
    (volume.toSphere : Measure ShellS2).map (fun u : ShellS2 => (u : ℝ³) 0) =
      ENNReal.ofReal (2 * π) • (volume.restrict (Set.Icc (-1) 1) : Measure ℝ) := by
  rw [show (volume.toSphere : Measure ShellS2).map (fun u : ShellS2 => (u : ℝ³) 0) = shellProjMu by rfl]
  rw [show ENNReal.ofReal (2 * π) • (volume.restrict (Set.Icc (-1) 1) : Measure ℝ) = shellProjNu by rfl]
  haveI : IsFiniteMeasure shellProjMu := shellProjMu_finite
  exact Measure.ext_of_Ici shellProjMu shellProjNu shellProj_Ici

