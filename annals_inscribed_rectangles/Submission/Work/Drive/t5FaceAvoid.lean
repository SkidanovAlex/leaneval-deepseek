import Mathlib
import Submission.Work.Drive.collapseT5
import Submission.Work.Drive.loopFamMeet_boxHavoid
import Submission.Work.Drive.contMDiff_loopFam

/-!
# The avoidance hypothesis of T5, and T5 with the box-restricted avoidance

`Submission/Work/Drive/collapseT5.lean` proves the two parity comparisons of the radial-collapse
transport (T5) as instances of the loop-deformation engine `Work.Drive.odd_ncard_loopFamMeet_iff`, with
the engine's regularity data (`hseam`, `havoid`, `htrans`, `hface`) carried as explicit hypotheses.  The
engine's `havoid` asks that the loop `L` meet the chain `N` nowhere on the chain's two *level* faces
(`x 2 ∈ {0,1}`), quantified over **all** loop parameters `u : ℝ²`.

This file does two things.

1. **It discharges the (box-restricted) avoidance** for the two concrete T5 families
   `diamFam Q t` and `arcFam Q t` against a clamped sweep `clampedSweep c ψ P`, from the two honest
   geometric hypotheses of the design:
   * the **plane disjointness** `Q '' {‖z‖ = 1} ∩ P '' □ = ∅` (the chart's curve misses the sweep's
     plane — the top face `x 2 = 1`) and, for `diamFam`, its closed-disk form
     `Q '' {‖z‖ ≤ 1} ∩ P '' □ = ∅`;
   * the **level bound** `levelOf (Q z) > c` on the closed disk (the floor `x 2 = 0`).
   The proof is the same as in `Submission/Work/Drive/collapseFaceAvoid.lean`: `diamFam Q t u` is
   `Q z` with `‖z‖ ≤ 1` for `u ∈ [0,1]²`, `arcFam Q t u` is `Q z` with `‖z‖ = 1` for every `u`, the
   sequence `x ↦ shadow c (P (mk2 (x 0) (x 1)))` lies in the level `c` (`levelOf_shadow`), and the top
   face is `P (mk2 (x 0) (x 1))` (`clampedSweep_face_one`).

2. **It restates T5 with the box-restricted avoidance**, using
   `Work.Drive.odd_ncard_loopFamMeet_iff_box` (the engine whose `havoid` is required only at loop
   parameters inside `unitBox 1`).  The two statements `odd_ncard_diamMeet_iff_arcMeet_box` and
   `odd_ncard_arcMeet_iff_core_box` are the versions a consumer should use with the proved avoidance
   above.

## Why the restriction is not a convenience

The unrestricted `havoid` quantifies over loop parameters `u` *outside* the box.  For the concrete
families that is a statement about `Q z` for `‖z‖` large (`diamFam`) or for `z` on the whole circle
(`arcFam`), and `IsPlaneChart` constrains `Q` only on the closed unit disk (strip clause on the annulus
`1/2 < ‖z‖ ≤ 1`, cap clause on `‖z‖ < 1/2`).  So the data the design has do **not** imply the
unrestricted form, while they do imply the restricted one — the memberships
`diamFam_mem_closedDisk` / `arcFam_mem_circle` below are exactly the passage.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

/-! ## 1. Where the two T5 families take their values -/

/-- The argument of `diamInterp` has norm at most `1` for parameters in the square. -/
lemma norm_diamInterp_arg_le (t a σ : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖((((1 - a) * (1 - 2 * σ) : ℝ)) : ℂ) * colCirclePt t
      + ((a : ℂ) * colCirclePt (t + σ))‖ ≤ 1 := by
  have h1 : ‖((((1 - a) * (1 - 2 * σ) : ℝ)) : ℂ) * colCirclePt t‖
      = |(1 - a) * (1 - 2 * σ)| := by
    rw [norm_mul, norm_colCirclePt, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖((a : ℂ) * colCirclePt (t + σ))‖ = |a| := by
    rw [norm_mul, norm_colCirclePt, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have ha' : (0 : ℝ) ≤ 1 - a := by linarith [ha.2]
  have hσ' : |1 - 2 * σ| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have h3 : |(1 - a) * (1 - 2 * σ)| = (1 - a) * |1 - 2 * σ| := by
    rw [abs_mul, abs_of_nonneg ha']
  calc ‖((((1 - a) * (1 - 2 * σ) : ℝ)) : ℂ) * colCirclePt t
        + ((a : ℂ) * colCirclePt (t + σ))‖
      ≤ ‖((((1 - a) * (1 - 2 * σ) : ℝ)) : ℂ) * colCirclePt t‖
        + ‖((a : ℂ) * colCirclePt (t + σ))‖ := norm_add_le _ _
    _ = |(1 - a) * (1 - 2 * σ)| + |a| := by rw [h1, h2]
    _ = (1 - a) * |1 - 2 * σ| + a := by rw [h3, abs_of_nonneg ha.1]
    _ ≤ (1 - a) * 1 + a := by
        have := mul_le_mul_of_nonneg_left hσ' ha'
        linarith
    _ = 1 := by ring

/-- **The diameter family takes its values in the chart's image of the closed disk**, for loop
parameters in the square. -/
lemma diamFam_mem_closedDisk {Q : ℂ → CappingSpace} (t : ℝ)
    {u : EuclideanSpace ℝ (Fin 2)} (hu : u ∈ Submission.Drive.unitBox 1) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ diamFam Q t u = Q z :=
  ⟨_, norm_diamInterp_arg_le t (u 0) (u 1) ⟨(hu 0).1, (hu 0).2⟩ ⟨(hu 1).1, (hu 1).2⟩, rfl⟩

/-- The argument of `arcRot` lies on the unit circle. -/
lemma norm_arcRot_arg (t τ σ : ℝ) : ‖colCirclePt ((1 - τ) * t + σ)‖ = 1 := norm_colCirclePt _

/-- **The rotation family takes its values in the chart's image of the boundary circle**, for *every*
loop parameter. -/
lemma arcFam_mem_circle {Q : ℂ → CappingSpace} (t : ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ arcFam Q t u = Q z :=
  ⟨_, norm_arcRot_arg t (u 0) (u 1), rfl⟩

/-! ## 2. The avoidances -/

/-- **The top face of a clamped sweep does not meet the rotation family.**  The rotation family is the
chart's curve `Q '' {‖z‖ = 1}`, the top face of the sweep is the plane `P` evaluated on the square, and
the plane disjointness excludes the equation. -/
theorem arcFam_ne_clampedSweep_top {c : ℝ} {ψ : ℝ → ℝ} (hψ1 : ψ 1 = 0)
    {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hdisj : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ = 1 → Q z ≠ P y)
    (t : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)) (hx2 : x 2 = 1) :
    arcFam Q t u ≠ clampedSweep c ψ P x := by
  intro h
  rw [clampedSweep_face_one c ψ P hψ1 x hx2] at h
  obtain ⟨z, hz, hzq⟩ := arcFam_mem_circle (Q := Q) t u
  rw [hzq] at h
  exact hdisj z _ hz h

/-- **The floor of a clamped sweep does not meet the rotation family.**  The floor lies in the level
`c`, the rotation family's level is the level of `Q` on the circle, and the level bound excludes the
equation. -/
theorem arcFam_ne_clampedSweep_floor {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1)
    {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (t : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)) (hx2 : x 2 = 0) :
    arcFam Q t u ≠ clampedSweep c ψ P x := by
  intro h
  rw [clampedSweep_face_zero c hc ψ P hψ0 x hx2] at h
  have hlv : levelOf (arcFam Q t u) = c := by rw [h, levelOf_shadow c hc]
  rw [show arcFam Q t u = Q (colCirclePt ((1 - u 0) * t + u 1)) from rfl] at hlv
  exact hlev _ (le_of_eq (norm_colCirclePt _)) hlv

/-- **The top face of a clamped sweep does not meet the diameter family**, for loop parameters in the
square (where the family is a value of `Q` on the closed disk). -/
theorem diamFam_ne_clampedSweep_top {c : ℝ} {ψ : ℝ → ℝ} (hψ1 : ψ 1 = 0)
    {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hdisj : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 → Q z ≠ P y)
    (t : ℝ) {u : EuclideanSpace ℝ (Fin 2)} (hu : u ∈ Submission.Drive.unitBox 1)
    (x : EuclideanSpace ℝ (Fin 3)) (hx2 : x 2 = 1) :
    diamFam Q t u ≠ clampedSweep c ψ P x := by
  intro h
  rw [clampedSweep_face_one c ψ P hψ1 x hx2] at h
  obtain ⟨z, hz, hzq⟩ := diamFam_mem_closedDisk (Q := Q) t hu
  rw [hzq] at h
  exact hdisj z _ hz h

/-- **The floor of a clamped sweep does not meet the diameter family**, for loop parameters in the
square. -/
theorem diamFam_ne_clampedSweep_floor {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1)
    {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (t : ℝ) {u : EuclideanSpace ℝ (Fin 2)} (hu : u ∈ Submission.Drive.unitBox 1)
    (x : EuclideanSpace ℝ (Fin 3)) (hx2 : x 2 = 0) :
    diamFam Q t u ≠ clampedSweep c ψ P x := by
  intro h
  rw [clampedSweep_face_zero c hc ψ P hψ0 x hx2] at h
  obtain ⟨z, hz, hzq⟩ := diamFam_mem_closedDisk (Q := Q) t hu
  have hlv : levelOf (Q z) = c := by
    rw [hzq] at h
    rw [h, levelOf_shadow c hc]
  exact hlev z hz hlv

/-! ## 3. The two `havoid` forms for T5 -/

/-- **The avoidance hypothesis of T5(a)** (`diamFam`, box-restricted): the engine's `havoid` for the
diameter family, from the plane disjointness and the level bound. -/
theorem havoid_diamFam {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hdisj : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 → Q z ≠ P y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (t : ℝ) : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = clampedSweep c ψ P x → u ∈ Submission.Drive.unitBox 1 →
      x ∈ Submission.Drive.unitBox 2 → (x 2 = 0 ∨ x 2 = 1) → False := by
  intro u x hmeet hu _ hb
  rcases hb with h2 | h2
  · exact diamFam_ne_clampedSweep_floor hc hψ0 hlev t hu x h2 hmeet
  · exact diamFam_ne_clampedSweep_top hψ1 hdisj t hu x h2 hmeet

/-- **The avoidance hypothesis of T5(b)** (`arcFam`): the engine's `havoid` for the rotation family,
from the curve/plane disjointness and the level bound. -/
theorem havoid_arcFam {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hdisj : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ = 1 → Q z ≠ P y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (t : ℝ) : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c ψ P x → u ∈ Submission.Drive.unitBox 1 →
      x ∈ Submission.Drive.unitBox 2 → (x 2 = 0 ∨ x 2 = 1) → False := by
  intro u x hmeet _ _ hb
  rcases hb with h2 | h2
  · exact arcFam_ne_clampedSweep_floor hc hψ0 hlev t u x h2 hmeet
  · exact arcFam_ne_clampedSweep_top hψ1 hdisj t u x h2 hmeet

/-! ## 4. T5 with the box-restricted avoidance -/

/-- **T5(a) with the box-restricted avoidance**: the same statement as
`Work.Drive.odd_ncard_diamMeet_iff_arcMeet`, but consuming the provable form of `havoid` (only at loop
parameters in `unitBox 1`). -/
theorem odd_ncard_diamMeet_iff_arcMeet_box (Q : ℂ → CappingSpace) (t : ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (diamFam Q t))
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hseam : ∀ x : EuclideanSpace ℝ (Fin 3), onSeam x → W (seamInv x) = W x)
    (havoid : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = W x → u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
        (x 2 = 0 ∨ x 2 = 1) → False)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = W x →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) W x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = W x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ = mfderiv (𝓡 3) (𝓡 4) W x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ = mfderiv (𝓡 3) (𝓡 4) W x τ ∧ τ j ≠ 0)) :
    Odd (diamMeet Q t W).ncard ↔ Odd (arcMeet Q t W).ncard := by
  have hloop : ∀ a ∈ Set.Icc (0 : ℝ) 1, diamFam Q t (mk2 a 0) = diamFam Q t (mk2 a 1) := by
    intro a _
    show diamInterp Q t a 0 = diamInterp Q t a 1
    exact (diamInterp_loop hQseam t a).symm
  have he := odd_ncard_loopFamMeet_iff_box CappingSpace (diamFam Q t) W hL hN hloop hseam
    havoid htrans hface
  rw [diamMeet_ncard_eq_loopFamMeet_zero Q t W, ← loopFamMeet_one_eq_arcMeet Q t W]
  exact he

/-- **T5(b) with the box-restricted avoidance**: the same statement as
`Work.Drive.odd_ncard_arcMeet_iff_core`, with the provable form of `havoid`. -/
theorem odd_ncard_arcMeet_iff_core_box (Q : ℂ → CappingSpace) (t c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (arcFam Q t))
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (clampedSweep c (fun s => 1 - s) P))
    (hseam : ∀ x : EuclideanSpace ℝ (Fin 3), onSeam x →
      clampedSweep c (fun s => 1 - s) P (seamInv x) = clampedSweep c (fun s => 1 - s) P x)
    (havoid : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x → u ∈ Submission.Drive.unitBox 1 →
        x ∈ Submission.Drive.unitBox 2 → (x 2 = 0 ∨ x 2 = 1) → False)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
                = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ τ j ≠ 0)) :
    Odd (arcMeet Q t (clampedSweep c (fun s => 1 - s) P)).ncard
      ↔ Odd (coreSideCount Q c P) := by
  have hloop : ∀ a ∈ Set.Icc (0 : ℝ) 1, arcFam Q t (mk2 a 0) = arcFam Q t (mk2 a 1) := by
    intro a _
    show arcRot Q t a 0 = arcRot Q t a 1
    exact (arcRot_loop hQseam t a).symm
  have he := odd_ncard_loopFamMeet_iff_box CappingSpace (arcFam Q t)
    (clampedSweep c (fun s => 1 - s) P) hL hN hloop hseam havoid htrans hface
  change Odd (arcMeet Q t (clampedSweep c (fun s => 1 - s) P)).ncard
      ↔ Odd ((coreMeet Q c P).ncard)
  rw [arcMeet_ncard_eq_loopFamMeet_zero, ← arcMeet_zero_eq_coreMeet,
    ← loopFamMeet_one_eq_arcMeet_zero]
  exact he

/-! ## 5. T5 for the concrete clamped sweep, with the analytic hypotheses discharged -/

/-- **T5(a) for a clamped sweep**, with the smoothness of the two loop families
(`contMDiff_diamFam`), the smoothness of the sweep (`contMDiff_clampedSweep`), its seam invariance
(`clampedSweep_seamInv`) and the avoidance (`havoid_diamFam`) all discharged: what is left to the design
is the chart's data (`hQ`, `hQseam`), the sweep's data (`hψ`, `hP`, `hPseam`, `hψ0`, `hψ1`, `hc`), the
plane disjointness, the level bound, and the two genericity fields `htrans`/`hface`. -/
theorem odd_ncard_diamMeet_iff_arcMeet_clampedSweep (Q : ℂ → CappingSpace) (t c : ℝ)
    (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hPseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P y = P (seamInv2 y))
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hc : 0 < c)
    (hdisj : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 → Q z ≠ P y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = clampedSweep c ψ P x →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c ψ P) x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = clampedSweep c ψ P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c ψ P) x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ
                = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c ψ P) x τ ∧ τ j ≠ 0)) :
    Odd (diamMeet Q t (clampedSweep c ψ P)).ncard
      ↔ Odd (arcMeet Q t (clampedSweep c ψ P)).ncard :=
  odd_ncard_diamMeet_iff_arcMeet_box Q t (clampedSweep c ψ P) hQseam
    (contMDiff_diamFam hQ t) (contMDiff_clampedSweep c ψ P hψ hP)
    (fun x hx => (clampedSweep_seamInv c ψ P hPseam x hx).symm)
    (havoid_diamFam hc hψ0 hψ1 hdisj hlev t) htrans hface

/-- **T5(b) for the clamped sweep `clampedSweep c (1 - ·) P`**, with the smoothness of the rotation
family, the smoothness and the seam invariance of the sweep, and the avoidance (`havoid_arcFam`) all
discharged. -/
theorem odd_ncard_arcMeet_iff_core_clampedSweep (Q : ℂ → CappingSpace) (t c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hPseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P y = P (seamInv2 y))
    (hc : 0 < c)
    (hdisj : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ = 1 → Q z ≠ P y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
                = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ τ j ≠ 0)) :
    Odd (arcMeet Q t (clampedSweep c (fun s => 1 - s) P)).ncard
      ↔ Odd (coreSideCount Q c P) :=
  odd_ncard_arcMeet_iff_core_box Q t c P hQseam (contMDiff_arcFam hQ t)
    (contMDiff_clampedSweep c (fun s => 1 - s) P (by fun_prop) hP)
    (fun x hx => (clampedSweep_seamInv c (fun s => 1 - s) P hPseam x hx).symm)
    (havoid_arcFam hc (by norm_num) (by norm_num) hdisj hlev t) htrans hface

end

end Work.Drive
