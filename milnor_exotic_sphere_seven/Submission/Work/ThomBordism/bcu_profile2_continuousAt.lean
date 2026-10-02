import Mathlib
import Submission.Work.ThomBordism.BCUProfile
import Submission.Work.ThomBordism.bcu_profile2_properties

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Continuity of the seam-free boundary-collapse profile as a function of `(t, v)`

`Work.ThomBordism.BCU.profile2 e t v` (`Submission/Work/ThomBordism/BCUProfile.lean`) is the
seam-free three-phase profile of the boundary collapse `Φ`.  What the boundary-sign construction
needs is that `profile2 0 · ·` is continuous *at a pair* `(t₀, v₀)` which is the limit of the
bump/chart values `(χ z, eNorm z)`.  This file provides exactly that:

* if `v₀ ≠ 0` it is joint continuity of `(t, v) ↦ profile2 e t v` off the origin
  (`continuousOn_profile2_ne`), obtained by gluing the three phases along the seams
  `t = 1/2` and `t = 3/4` (the seam identities are `sphPhase_pi_div_two`, `sphPhase_zero` and
  `shiftPhase2_one`), together with continuity of the radial clamp (`clampBall_continuous`);
* if `t₀ = 1`, `v₀ = 0` it is the limit `profile2 e t v → 0` as `(t, v) → (1, 0)`
  (`tendsto_profile2_zero`): along the third phase the argument
  `shift2Arg ((1-t)*4) 0 v` is squeezed by `|1-t|*4 + |4t-3|▪‖v‖`, and the radial clamp never
  increases the norm.

The auxiliary lemmas are kept in the namespace `Work.ThomBordism.BCUP2` (rather than being taken
from `bcu_PhiE2_continuous_and_mem`, where they also appear) so that this module imports only
`BCUProfile` and `bcu_profile2_properties` and can therefore be imported next to `BCUDefs` without
a declaration clash.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.ThomBordism

open Work.ThomBordism.BCU
open Filter
open scoped Topology

namespace BCUP2

/-! ## The radial clamp -/

/-- The radial clamp `w ↦ min 1 ‖w‖⁻¹ • w` is continuous. -/
theorem clampBall_continuous (m : ℕ) :
    Continuous (fun w : EuclideanSpace ℝ (Fin (m + 1)) => BCU.clampBall w) := by
  have hEq : (fun w : EuclideanSpace ℝ (Fin (m + 1)) => BCU.clampBall w)
      = fun w => if ‖w‖ ≤ 1 then w else ‖w‖⁻¹ • w := by
    funext w
    by_cases hw : ‖w‖ ≤ 1
    · rw [if_pos hw, bcu_clampBall_eq_self w hw]
    · rw [if_neg hw, BCU.clampBall,
        min_eq_right (inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hw)))]
  rw [hEq]
  refine continuous_if ?_ continuous_id.continuousOn ?_
  · intro a ha
    have hsub : frontier {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ 1} ⊆ {x | ‖x‖ = 1} := by
      intro x hx
      have hclosed : IsClosed {y : EuclideanSpace ℝ (Fin (m+1)) | ‖y‖ ≤ 1} :=
        isClosed_le (continuous_norm : Continuous fun y : EuclideanSpace ℝ (Fin (m+1)) => ‖y‖)
          (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin (m+1)) => (1:ℝ))
      have h2 : ‖x‖ ≤ 1 := hclosed.frontier_subset hx
      have h1 : (1:ℝ) ≤ ‖x‖ := by
        have hcompl : ({y : EuclideanSpace ℝ (Fin (m+1)) | ‖y‖ ≤ 1}ᶜ)
            = {y : EuclideanSpace ℝ (Fin (m+1)) | (1:ℝ) < ‖y‖} := by
          ext y; simp [not_le]
        have hfr : frontier {y : EuclideanSpace ℝ (Fin (m+1)) | ‖y‖ ≤ 1}
            = frontier {y : EuclideanSpace ℝ (Fin (m+1)) | (1:ℝ) < ‖y‖} := by
          rw [← frontier_compl, hcompl]
        have hx' : x ∈ closure {y : EuclideanSpace ℝ (Fin (m+1)) | (1:ℝ) < ‖y‖} :=
          frontier_subset_closure (hfr ▸ hx)
        exact closure_lt_subset_le
          (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin (m+1)) => (1:ℝ))
          (continuous_norm : Continuous fun y : EuclideanSpace ℝ (Fin (m+1)) => ‖y‖) hx'
      exact le_antisymm h2 h1
    have h1 : ‖a‖ = 1 := hsub ha
    show a = ‖a‖⁻¹ • a
    rw [h1, inv_one, one_smul]
  · have hinv : ContinuousOn (fun w : EuclideanSpace ℝ (Fin (m + 1)) => ‖w‖⁻¹)
        {x | (1:ℝ) ≤ ‖x‖} :=
      ContinuousOn.inv₀ continuous_norm.continuousOn
        (fun x hx => by
          have hx' : (1:ℝ) ≤ ‖x‖ := hx
          exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx'))
    have hg : ContinuousOn (fun w : EuclideanSpace ℝ (Fin (m + 1)) => ‖w‖⁻¹ • w)
        {x | (1:ℝ) ≤ ‖x‖} := hinv.smul continuousOn_id
    have hsub : closure {x : EuclideanSpace ℝ (Fin (m + 1)) | ¬ ‖x‖ ≤ 1} ⊆ {x | (1:ℝ) ≤ ‖x‖} := by
      have h1 : {x : EuclideanSpace ℝ (Fin (m + 1)) | ¬ ‖x‖ ≤ 1} = {x | (1:ℝ) < ‖x‖} := by
        ext x; simp [not_le]
      rw [h1]
      exact closure_lt_subset_le continuous_const continuous_norm
    exact hg.mono hsub

/-! ## Continuity of the individual phases off the origin -/

/-- `sphPhase` is continuous on the set where its second argument is nonzero, for any continuous
phase function of the first coordinate. -/
theorem continuousOn_sphPhase (m : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => BCU.sphPhase (φ p.1) p.2)
      {p | p.2 ≠ 0} := by
  have hnorminv : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (m+1)) => ‖p.2‖⁻¹)
      {p | p.2 ≠ 0} :=
    ContinuousOn.inv₀ (continuous_norm.comp continuous_snd).continuousOn
      (fun p hp => norm_ne_zero_iff.mpr hp)
  have hφc : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (m+1)) => φ p.1) {p | p.2 ≠ 0} :=
    hφ.comp_continuousOn continuousOn_fst
  have hA : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (m+1)) =>
      Real.cos (φ p.1) • (‖p.2‖⁻¹ • p.2) + Real.sin (φ p.1) • BCU.northPole m)
      {p | p.2 ≠ 0} := by
    refine ContinuousOn.add ?_ ?_
    · exact ((Real.continuous_cos.comp_continuousOn hφc).smul (hnorminv.smul continuousOn_snd))
    · exact (Real.continuous_sin.comp_continuousOn hφc).smul continuousOn_const
  exact (clampBall_continuous m).comp_continuousOn hA

/-- `shiftPhase2` is continuous on the set where its second argument is nonzero, for any continuous
function of the phase. -/
theorem continuousOn_shiftPhase2 (m : ℕ) (e : EuclideanSpace ℝ (Fin (m+1))) {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => BCU.shiftPhase2 (ψ p.1) e p.2)
      {p | p.2 ≠ 0} := by
  have hψc : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (m+1)) => ψ p.1) {p | p.2 ≠ 0} :=
    hψ.comp_continuousOn continuousOn_fst
  have hdiv : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (m+1)) => ψ p.1 / ‖p.2‖)
      {p | p.2 ≠ 0} :=
    ContinuousOn.div₀ hψc (continuous_norm.comp continuous_snd).continuousOn
      (fun p hp => norm_ne_zero_iff.mpr hp)
  have hA : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (m+1)) =>
      (ψ p.1 / ‖p.2‖ + (1 - ψ p.1)) • p.2 + (ψ p.1 * (1 - ψ p.1)) • e) {p | p.2 ≠ 0} := by
    refine ContinuousOn.add ?_ ?_
    · exact (hdiv.add (continuousOn_const.sub hψc)).smul continuousOn_snd
    · exact (hψc.mul (continuousOn_const.sub hψc)).smul continuousOn_const
  exact (clampBall_continuous m).comp_continuousOn hA

/-! ## The seams of the profile -/

/-- At the phase `π/2` the spherical phase is the north pole. -/
theorem sphPhase_pi_div_two (m : ℕ) (v : EuclideanSpace ℝ (Fin (m+1))) :
    BCU.sphPhase (Real.pi / 2) v = BCU.northPole m := by
  rw [BCU.sphPhase, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp [BCU.clampBall, bcu_northPole_norm]

/-- At phase `0` the spherical phase is the normalisation `clampBall (‖v‖⁻¹ • v)`. -/
theorem sphPhase_zero (m : ℕ) (v : EuclideanSpace ℝ (Fin (m+1))) :
    BCU.sphPhase 0 v = BCU.clampBall (‖v‖⁻¹ • v) := by
  rw [BCU.sphPhase, Real.cos_zero, Real.sin_zero]
  simp

/-- At phase `1` the seam-free shift phase is the normalisation `clampBall (‖v‖⁻¹ • v)`. -/
theorem shiftPhase2_one (m : ℕ) (e v : EuclideanSpace ℝ (Fin (m+1))) :
    BCU.shiftPhase2 1 e v = BCU.clampBall (‖v‖⁻¹ • v) := by
  rw [BCU.shiftPhase2]
  simp

/-- The seam-free profile at time `1` and value `0` is `0`. -/
theorem profile2_one_zero (m : ℕ) (e : EuclideanSpace ℝ (Fin (m+1))) :
    BCU.profile2 e 1 0 = 0 := by
  rw [BCU.profile2]
  norm_num
  rw [BCU.shiftPhase2]
  norm_num
  rw [BCU.clampBall]
  simp

/-! ## Joint continuity of the seam-free profile off `v = 0` -/

/-- The seam-free profile is continuous at every pair `(t, v)` with `v ≠ 0`. -/
theorem continuousOn_profile2_ne (m : ℕ) (e : EuclideanSpace ℝ (Fin (m + 1))) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => BCU.profile2 e p.1 p.2)
      {p | p.2 ≠ 0} := by
  change ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) =>
    if p.1 ≤ 1 / 2 then BCU.northPole m
    else if p.1 ≤ 3 / 4 then BCU.sphPhase ((3 / 4 - p.1) * 2 * Real.pi) p.2
    else BCU.shiftPhase2 ((1 - p.1) * 4) e p.2) {p | p.2 ≠ 0}
  refine ContinuousOn.if ?_ continuousOn_const ?_
  · intro a ha
    have ha1 : a.1 = 1 / 2 := frontier_le_subset_eq continuous_fst continuous_const ha.2
    rw [ha1, if_pos (by norm_num : (1/2:ℝ) ≤ 3/4)]
    have harg : (3 / 4 - 1 / 2 : ℝ) * 2 * Real.pi = Real.pi / 2 := by ring
    rw [harg, sphPhase_pi_div_two]
  · refine ContinuousOn.if ?_ ?_ ?_
    · intro a ha
      have ha1 : a.1 = 3 / 4 := frontier_le_subset_eq continuous_fst continuous_const ha.2
      rw [ha1]
      have h1 : (3 / 4 - 3 / 4 : ℝ) * 2 * Real.pi = 0 := by ring
      have h2 : (1 - 3 / 4 : ℝ) * 4 = 1 := by norm_num
      rw [h1, h2, sphPhase_zero, shiftPhase2_one]
    · exact (continuousOn_sphPhase m
        (by fun_prop : Continuous fun t : ℝ => (3 / 4 - t) * 2 * Real.pi)).mono
        (by intro a ha; exact ha.1.1)
    · exact (continuousOn_shiftPhase2 m e
        (by fun_prop : Continuous fun t : ℝ => (1 - t) * 4)).mono
        (by intro a ha; exact ha.1.1)

/-! ## The limit of the profile at `(1, 0)` -/

/-- A norm bound for the argument of the second shift phase with `e = 0`. -/
theorem norm_shift2Arg_zero_le (m : ℕ) (p : ℝ) (v : EuclideanSpace ℝ (Fin (m+1))) :
    ‖BCU.shift2Arg p (0 : EuclideanSpace ℝ (Fin (m+1))) v‖ ≤ |p| + |1 - p| * ‖v‖ := by
  have h1 : ‖(‖v‖⁻¹ : ℝ) • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    rcases eq_or_lt_of_le (norm_nonneg v) with h | h
    · rw [← h]; simp
    · rw [inv_mul_cancel₀ (ne_of_gt h)]
  have hsplit : BCU.shift2Arg p (0 : EuclideanSpace ℝ (Fin (m+1))) v
      = p • ((‖v‖⁻¹ : ℝ) • v) + (1 - p) • v := by
    rw [BCU.shift2Arg, div_eq_mul_inv, add_smul, mul_smul]
    simp
  rw [hsplit]
  calc ‖p • ((‖v‖⁻¹ : ℝ) • v) + (1 - p) • v‖
      ≤ ‖p • ((‖v‖⁻¹ : ℝ) • v)‖ + ‖(1 - p) • v‖ := norm_add_le _ _
    _ ≤ |p| + |1 - p| * ‖v‖ := by
        have h2 : ‖p • ((‖v‖⁻¹ : ℝ) • v)‖ ≤ |p| := by
          rw [norm_smul, Real.norm_eq_abs]
          calc |p| * ‖(‖v‖⁻¹ : ℝ) • v‖ ≤ |p| * 1 :=
                mul_le_mul_of_nonneg_left h1 (abs_nonneg p)
            _ = |p| := mul_one _
        have h3 : ‖(1 - p) • v‖ = |1 - p| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
        linarith

/-- The seam-free profile `profile2 0` tends to `0` at `(1, 0)`. -/
theorem tendsto_profile2_zero (m : ℕ) :
    Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) =>
      BCU.profile2 (0 : EuclideanSpace ℝ (Fin (m + 1))) p.1 p.2) (𝓝 (1, 0)) (𝓝 0) := by
  have hU : {p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) | (3:ℝ)/4 < p.1} ∈
      𝓝 ((1:ℝ), (0 : EuclideanSpace ℝ (Fin (m + 1)))) :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (by norm_num)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (f := fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) =>
      ‖BCU.profile2 (0 : EuclideanSpace ℝ (Fin (m + 1))) p.1 p.2‖)
    (g := fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) =>
      |(1 - p.1) * 4| + |1 - (1 - p.1) * 4| * ‖p.2‖)
    (Eventually.of_forall fun p => norm_nonneg _) ?_ ?_
  · filter_upwards [hU] with p hp
    rw [BCU.profile2, if_neg (by linarith : ¬ p.1 ≤ 1/2),
      if_neg (by linarith : ¬ p.1 ≤ 3/4)]
    have hclamp : ‖BCU.shiftPhase2 ((1 - p.1) * 4) (0 : EuclideanSpace ℝ (Fin (m+1))) p.2‖
        = min 1 ‖BCU.shift2Arg ((1 - p.1) * 4) (0 : EuclideanSpace ℝ (Fin (m+1))) p.2‖ := by
      rw [BCU.shiftPhase2_eq_clampBall, bcu_clampBall_norm]
    rw [hclamp]
    exact (min_le_right _ _).trans (norm_shift2Arg_zero_le m ((1 - p.1) * 4) p.2)
  · have hc : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) =>
        |(1 - p.1) * 4| + |1 - (1 - p.1) * 4| * ‖p.2‖ := by fun_prop
    have h := hc.tendsto ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (m + 1))))
    simpa using h

end BCUP2

/-- The seam-free profile `profile2 0` is continuous at `(t₀, v₀)` whenever `v₀ ≠ 0` or
`t₀ = 1` (with `0 ≤ t₀ ≤ 1`). -/
theorem bcu_profile2_continuousAt (m : ℕ) (t₀ : ℝ) (v₀ : EuclideanSpace ℝ (Fin (m + 1)))
    (ht0 : 0 ≤ t₀) (ht1 : t₀ ≤ 1) (hv : v₀ ≠ 0 ∨ t₀ = 1) :
    ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) =>
      Work.ThomBordism.BCU.profile2 (0 : EuclideanSpace ℝ (Fin (m + 1))) p.1 p.2) (t₀, v₀) := by
  by_cases hv0 : v₀ = 0
  · have ht : t₀ = 1 := hv.resolve_left (fun h => h hv0)
    subst ht
    subst hv0
    change Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin (m + 1)) =>
      Work.ThomBordism.BCU.profile2 (0 : EuclideanSpace ℝ (Fin (m + 1))) p.1 p.2)
      (𝓝 ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (m + 1)))))
      (𝓝 (Work.ThomBordism.BCU.profile2 (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 0))
    rw [BCUP2.profile2_one_zero m (0 : EuclideanSpace ℝ (Fin (m + 1)))]
    exact BCUP2.tendsto_profile2_zero m
  · exact (BCUP2.continuousOn_profile2_ne m (0 : EuclideanSpace ℝ (Fin (m + 1)))).continuousAt
      ((isOpen_ne.preimage continuous_snd).mem_nhds hv0)

end Work.ThomBordism
