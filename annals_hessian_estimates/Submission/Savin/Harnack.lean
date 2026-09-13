/-
# The Harnack inequality: the propagation estimate

The Harnack inequality is proved, following Imbert--Silvestre (*Estimates on elliptic equations
that hold only where the gradient is large*, JEMS 18 (2016), Section 7), from the two measure
estimates of the from-below sliding-paraboloid method:

* the "propagation" estimate (their Corollary 4.3): a non-negative solution that is `≤ 1` at one
  point of a small ball cannot exceed the large level `33` on more than a `(1-μ)`-fraction of
  `closedBall 0 (1/2)`; this is `density_contactPt` combined with the level-set inclusion
  `contactPt_le_value`;
* the decay/weak-`L^ε` estimate (`Submission.weak_Leps`), which turns this base case into
  `|{φ > t}| ≤ C t^{-κ}`.

Both are consequences of the *from-below* (supersolution) side only, so no from-above measure
estimates are needed for the Harnack inequality.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Density
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_comp_add_linear_of_contDiffAt

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- **The propagation estimate** (base case of the Harnack lower bound; Imbert--Silvestre,
Corollary 4.3 in the normalised constants of this formalisation).  If `φ ≥ 0` solves
`Fop C ε = 0` on `ball 0 (3/2)`, `φ x₁ ≤ 1` at some point `x₁ ∈ closedBall 0 (1/16)` and the
opening `16` is admissible (`3 ε · 16 ≤ c/2`), then the superlevel set `{φ > 33}` occupies at most
a `(1-μ)`-fraction of `closedBall 0 (1/2)`, where `μ = (1/8)^4 / (1 + 2 tr C / c + 3)^4` is the
density constant of `Submission.density_contactPt`. -/
theorem measure_superlevel_le {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) {ε : ℝ} (hε : 0 < ε)
    (heq : ∀ x ∈ ball 0 (3 / 2), Fop C ε (hessOp φ x) = 0) (hε16 : 3 * ε * 16 ≤ c / 2)
    (hpos : ∀ x ∈ closedBall 0 1, 0 ≤ φ x)
    (hinf : ∃ x₁ ∈ closedBall 0 (1 / 16), φ x₁ ≤ 1) :
    volume ({x : ℝ⁴ | 33 < φ x} ∩ closedBall (0 : ℝ⁴) (1 / 2)) ≤
      ENNReal.ofReal (1 - ((1 / 8 : ℝ) ^ 4 / (1 + (2 * trOp C / c + 3)) ^ 4))
        * volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
  have htrC : 0 ≤ trOp C := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 := hcq (stdB4 i)
    have h3 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h3] at h2
    nlinarith [h2]
  set μ : ℝ := (1 / 8 : ℝ) ^ 4 / (1 + (2 * trOp C / c + 3)) ^ 4 with hμdef
  have h2c : 0 ≤ 2 * trOp C / c := div_nonneg (by linarith) hc.le
  have hKpos : 0 < 1 + (2 * trOp C / c + 3) := by linarith
  have hμpos : 0 < μ := by
    rw [hμdef]
    exact div_pos (by norm_num) (pow_pos hKpos 4)
  have hμle1 : μ ≤ 1 := by
    rw [hμdef, div_le_one (pow_pos hKpos 4)]
    have h1 : (1 / 8 : ℝ) ^ 4 ≤ 1 := by norm_num
    have h2 : (1 : ℝ) ≤ (1 + (2 * trOp C / c + 3)) ^ 4 :=
      one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + (2 * trOp C / c + 3))
    linarith
  -- the density estimate, with the level-set inclusion
  have hdens := density_contactPt hφ hC hc hcq hε heq hε16 hpos hinf
  have hlevel : contactPt 16 φ ⊆ {x : ℝ⁴ | φ x ≤ 33} := by
    intro x hx
    obtain ⟨x₁, hx₁, hle₁⟩ := hinf
    have h := contactPt_le_value (a := 16) (by norm_num)
      (closedBall_subset_closedBall (by norm_num : (1 : ℝ) / 16 ≤ 1) hx₁) hle₁ hx
    have h2 : (1 : ℝ) + 2 * 16 = 33 := by norm_num
    rw [h2] at h
    exact h
  have hcl : IsClosed (contactPt 16 φ) :=
    isClosed_contactPt ((hφ.of_le (m := 1) (by norm_num)).mono (ball_subset_ball (by norm_num)))
  have hfin : volume (closedBall (0 : ℝ⁴) (1 / 2)) ≠ ⊤ := by
    rw [Measure.addHaar_closedBall_eq_addHaar_ball]
    exact measure_ball_lt_top.ne
  have hfinT : volume (contactPt 16 φ) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono contactPt_subset_closedBall)
  have hsub : {x : ℝ⁴ | 33 < φ x} ∩ closedBall (0 : ℝ⁴) (1 / 2)
      ⊆ closedBall (0 : ℝ⁴) (1 / 2) \ contactPt 16 φ := by
    intro x hx
    obtain ⟨hxφ, hxS⟩ := hx
    have hxφ' : 33 < φ x := hxφ
    refine ⟨hxS, fun hxT => ?_⟩
    have : φ x ≤ 33 := hlevel hxT
    linarith
  have hmsdiff : volume (closedBall (0 : ℝ⁴) (1 / 2) \ contactPt 16 φ)
      = volume (closedBall (0 : ℝ⁴) (1 / 2)) - volume (contactPt 16 φ) :=
    measure_sdiff contactPt_subset_closedBall hcl.nullMeasurableSet hfinT
  have hdensT : ENNReal.ofReal μ * volume (closedBall (0 : ℝ⁴) (1 / 2))
      ≤ volume (contactPt 16 φ) := by
    rw [hμdef]
    have heq : contactPt 16 φ ∩ closedBall (0 : ℝ⁴) (1 / 2) = contactPt 16 φ := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, contactPt_subset_closedBall h⟩⟩
    rwa [heq] at hdens
  have hsum : ENNReal.ofReal μ * volume (closedBall (0 : ℝ⁴) (1 / 2))
      + ENNReal.ofReal (1 - μ) * volume (closedBall (0 : ℝ⁴) (1 / 2))
      = volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
    rw [← add_mul, ← ENNReal.ofReal_add hμpos.le (by linarith), show μ + (1 - μ) = 1 by ring]
    simp
  have hkey : volume (closedBall (0 : ℝ⁴) (1 / 2)) - ENNReal.ofReal μ * volume (closedBall (0 : ℝ⁴) (1 / 2))
      ≤ ENNReal.ofReal (1 - μ) * volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
    rw [tsub_le_iff_right]
    rw [add_comm, hsum]
  rw [hμdef] at hkey
  calc volume ({x : ℝ⁴ | 33 < φ x} ∩ closedBall (0 : ℝ⁴) (1 / 2))
      ≤ volume (closedBall (0 : ℝ⁴) (1 / 2) \ contactPt 16 φ) := measure_mono hsub
    _ = volume (closedBall (0 : ℝ⁴) (1 / 2)) - volume (contactPt 16 φ) := hmsdiff
    _ ≤ volume (closedBall (0 : ℝ⁴) (1 / 2))
          - ENNReal.ofReal μ * volume (closedBall (0 : ℝ⁴) (1 / 2)) :=
        tsub_le_tsub_left hdensT _
    _ ≤ ENNReal.ofReal (1 - μ) * volume (closedBall (0 : ℝ⁴) (1 / 2)) := hkey

/-- **The maximal flatness point.**  A non-negative continuous function on `closedBall 0 (3/4)`
attains its maximum of `x ↦ φ x * (3/4 - ‖x‖)^β` at an *interior* point (unless the maximum is
`0`).  This is the contact point of the barrier family `t * (3/4 - ‖x‖)^{-β}` used in the proof of
the Harnack inequality. -/
theorem exists_max_flatness {φ : ℝ⁴ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hcont : ContinuousOn φ (closedBall 0 (3 / 4)))
    (hpos : ∀ x ∈ closedBall 0 (3 / 4), 0 ≤ φ x) :
    ∃ x₀ ∈ ball 0 (3 / 4), ∀ x ∈ closedBall 0 (3 / 4),
      φ x * (3 / 4 - ‖x‖) ^ β ≤ φ x₀ * (3 / 4 - ‖x₀‖) ^ β := by
  have hGcont : ContinuousOn (fun x : ℝ⁴ => φ x * (3 / 4 - ‖x‖) ^ β) (closedBall 0 (3 / 4)) := by
    refine hcont.mul ?_
    refine (continuous_const.sub continuous_norm).continuousOn.rpow_const ?_
    intro x hx
    right
    have h := mem_closedBall.mp hx
    rw [dist_zero_right] at h
    linarith
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := (isCompact_closedBall (0 : ℝ⁴) (3 / 4)).exists_isMaxOn
    ⟨0, by rw [mem_closedBall, dist_zero_right]; norm_num⟩ hGcont
  have hmaxle : ∀ x ∈ closedBall (0 : ℝ⁴) (3 / 4),
      φ x * (3 / 4 - ‖x‖) ^ β ≤ φ x₀ * (3 / 4 - ‖x₀‖) ^ β := fun x hx => hx₀max hx
  have hGnonneg : ∀ x ∈ closedBall (0 : ℝ⁴) (3 / 4), 0 ≤ φ x * (3 / 4 - ‖x‖) ^ β := by
    intro x hx
    refine mul_nonneg (hpos x hx) ?_
    refine Real.rpow_nonneg ?_ β
    have h := mem_closedBall.mp hx
    rw [dist_zero_right] at h
    linarith
  have hx₀nn : ‖x₀‖ ≤ 3 / 4 := by
    have h := mem_closedBall.mp hx₀mem
    rwa [dist_zero_right] at h
  by_cases hbnd : ‖x₀‖ = 3 / 4
  · -- the maximum equals `0`, so any interior point works
    have hzero : ∀ x ∈ closedBall (0 : ℝ⁴) (3 / 4), φ x * (3 / 4 - ‖x‖) ^ β = 0 := by
      intro x hx
      have h1 := hmaxle x hx
      have h2 := hGnonneg x hx
      have h3 : φ x₀ * (3 / 4 - ‖x₀‖) ^ β = 0 := by
        rw [hbnd, show (3 : ℝ) / 4 - 3 / 4 = 0 by norm_num, Real.zero_rpow hβ.ne', mul_zero]
      rw [h3] at h1
      exact le_antisymm h1 h2
    refine ⟨0, by rw [mem_ball, dist_zero_right]; norm_num, fun x hx => ?_⟩
    rw [hzero x hx, hzero 0 (by rw [mem_closedBall, dist_zero_right]; norm_num)]
  · refine ⟨x₀, ?_, fun x hx => hx₀max hx⟩
    rw [mem_ball, dist_zero_right]
    exact lt_of_le_of_ne hx₀nn hbnd

/-- **The Hessian under an affine self-map.**  `hessOp` scales by `r²` under
`y ↦ φ (x₀ + r • y)`. -/
theorem hessOp_comp_affine {φ : ℝ⁴ → ℝ} {x₀ x : ℝ⁴} {r : ℝ}
    (hφ : ContDiffAt ℝ 2 φ (x₀ + r • x)) :
    hessOp (fun y => φ (x₀ + r • y)) x = (r * r) • hessOp φ (x₀ + r • x) := by
  have hcont : ContDiffAt ℝ 2 (fun y : ℝ⁴ => φ (x₀ + r • y)) x :=
    hφ.comp x ((contDiffAt_const (c := x₀)).add (contDiffAt_id.const_smul r))
  have hsym1 : (hessOp (fun y => φ (x₀ + r • y)) x).IsSymmetric :=
    hessOp_symm_of_contDiffAt hcont
  have hsym2 : ((r * r) • hessOp φ (x₀ + r • x)).IsSymmetric :=
    LinearMap.IsSymmetric.smul (by simp) (hessOp_symm_of_contDiffAt hφ)
  refine clm_eq_of_inner_self_eq hsym1 hsym2 fun v => ?_
  have h1 : ⟪hessOp (fun y => φ (x₀ + r • y)) x v, v⟫
      = (fderiv ℝ (fderiv ℝ (fun y => φ (x₀ + r • y))) x) v v :=
    InnerProductSpace.continuousLinearMapOfBilin_apply _ v v
  have h2 : ⟪hessOp φ (x₀ + r • x) v, v⟫
      = (fderiv ℝ (fderiv ℝ φ) (x₀ + r • x)) v v :=
    InnerProductSpace.continuousLinearMapOfBilin_apply _ v v
  calc ⟪hessOp (fun y => φ (x₀ + r • y)) x v, v⟫
      = (fderiv ℝ (fderiv ℝ (fun y => φ (x₀ + r • y))) x) v v := h1
    _ = (fderiv ℝ (fderiv ℝ φ) (x₀ + r • x)) (r • v) (r • v) :=
        Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_comp_add_linear_of_contDiffAt
          (L := r • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) x₀ φ x v v hφ
    _ = (r * r) * (fderiv ℝ (fderiv ℝ φ) (x₀ + r • x)) v v := by
        simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
    _ = (r * r) * ⟪hessOp φ (x₀ + r • x) v, v⟫ := by rw [h2]
    _ = ⟪((r * r) • hessOp φ (x₀ + r • x)) v, v⟫ := by
        rw [ContinuousLinearMap.smul_apply, real_inner_smul_left]

/-- **The small-perturbation equation is preserved by affine rescalings**, with the perturbation
parameter rescaled by `k²`: if `φ` solves `Fop C ε (D²φ) = 0` at `x₀ + k • x` then
`y ↦ φ (x₀ + k • y)` solves `Fop C (ε / k²) (D²·) = 0` at `x`. -/
theorem Fop_hessOp_comp_affine {φ : ℝ⁴ → ℝ} {C : ℝ⁴ →L[ℝ] ℝ⁴} {ε k : ℝ} {x₀ x : ℝ⁴}
    (hk : k ≠ 0) (hφ : ContDiffAt ℝ 2 φ (x₀ + k • x))
    (heq : Fop C ε (hessOp φ (x₀ + k • x)) = 0) :
    Fop C (ε / k ^ 2) (hessOp (fun y => φ (x₀ + k • y)) x) = 0 := by
  rw [hessOp_comp_affine hφ]
  rw [Fop_smul]
  have hk2 : (ε / k ^ 2) * (k * k) = ε := by
    field_simp
  rw [hk2, heq, mul_zero]

end

end Submission
