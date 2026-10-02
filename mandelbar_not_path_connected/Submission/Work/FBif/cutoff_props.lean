import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The radial cutoff of the gluing construction: analytic properties

This file proves `Work.FBif.cutoff_props`: the smooth radial cutoff `cutoff c` used to glue the
perturbation `perturb c q ε` to the model `Tantibar c` is `C¹`, equal to `1` on the closed ball of
radius `innerRad c`, equal to `0` outside the open ball of radius `cutRad c`, takes values in
`[0,1]`, has vanishing Wirtinger derivative `dz` in both regions where it is locally constant, and
has *globally bounded* Wirtinger derivatives `dz`, `dzbar`.

The last point is the analytic content: `cutoff c` is a compactly supported `C¹` function, so its
Fréchet derivative is continuous and compactly supported (it vanishes outside the cut ball), hence
bounded by `Continuous.bounded_above_of_compact_support`; the Wirtinger derivatives are explicit
linear combinations of values of the Fréchet derivative at `1` and `I`, so they inherit the bound.
-/

open Filter
open scoped Topology

noncomputable section

namespace Work.FBif

/- Auxiliary lemmas for `cutoff_props`, kept in their own namespace to avoid
name collisions with the rest of the area. -/
namespace cutoffAux

/-! ## Elementary inequalities between the radii -/

theorem farRad_pos (c : ℂ) : 0 < farRad c := by
  have h : (16 : ℝ) ≤ farRad c := le_max_left _ _
  linarith

theorem innerRad_pos (c : ℂ) : 0 < innerRad c := by
  unfold innerRad
  have := farRad_pos c
  linarith

theorem cutRad_pos (c : ℂ) : 0 < cutRad c := by
  unfold cutRad
  have := farRad_pos c
  linarith

theorem innerRad_lt_cutRad (c : ℂ) : innerRad c < cutRad c := by
  unfold innerRad cutRad
  have := farRad_pos c
  linarith

theorem cutRad_sq_sub_innerRad_sq_pos (c : ℂ) : 0 < cutRad c ^ 2 - innerRad c ^ 2 := by
  have h1 : 0 < innerRad c := innerRad_pos c
  have h2 : innerRad c < cutRad c := innerRad_lt_cutRad c
  nlinarith

/-! ## The value of the cutoff -/

theorem cutoff_eq_one_of_norm_le (c : ℂ) {z : ℂ} (hz : ‖z‖ ≤ innerRad c) : cutoff c z = 1 := by
  rw [cutoff_apply]
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (cutRad_sq_sub_innerRad_sq_pos c)]
  have h : ‖z‖ ^ 2 ≤ innerRad c ^ 2 := by
    nlinarith [innerRad_pos c, norm_nonneg z]
  linarith

theorem cutoff_eq_zero_of_cutRad_le (c : ℂ) {z : ℂ} (hz : cutRad c ≤ ‖z‖) : cutoff c z = 0 := by
  rw [cutoff_apply]
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt (cutRad_sq_sub_innerRad_sq_pos c))
  have h := pow_le_pow_left₀ (le_of_lt (cutRad_pos c)) hz 2
  linarith

theorem cutoff_nonneg (c : ℂ) (z : ℂ) : 0 ≤ cutoff c z := by
  rw [cutoff_apply]
  exact Real.smoothTransition.nonneg _

theorem cutoff_le_one (c : ℂ) (z : ℂ) : cutoff c z ≤ 1 := by
  rw [cutoff_apply]
  exact Real.smoothTransition.le_one _

/-! ## Local constancy of the cutoff in the two regions where it is constant -/

theorem eventually_cutoff_eq_one (c : ℂ) {z : ℂ} (hz : ‖z‖ < innerRad c) :
    ∀ᶠ w in 𝓝 z, cutoff c w = 1 := by
  have hr : 0 < innerRad c := innerRad_pos c
  have hball : Metric.ball z (innerRad c - ‖z‖) ∈ 𝓝 z :=
    Metric.ball_mem_nhds z (by linarith)
  filter_upwards [hball] with w hw
  have hw' : ‖w‖ < innerRad c := by
    have h1 : ‖w - z‖ < innerRad c - ‖z‖ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h2 : ‖w‖ ≤ ‖z‖ + ‖z - w‖ := norm_le_norm_add_norm_sub z w
    have h3 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
    linarith
  exact cutoff_eq_one_of_norm_le c (le_of_lt hw')

theorem eventually_cutoff_eq_zero (c : ℂ) {z : ℂ} (hz : cutRad c < ‖z‖) :
    ∀ᶠ w in 𝓝 z, cutoff c w = 0 := by
  have hr : 0 < cutRad c := cutRad_pos c
  have hball : Metric.ball z (‖z‖ - cutRad c) ∈ 𝓝 z :=
    Metric.ball_mem_nhds z (by linarith)
  filter_upwards [hball] with w hw
  have hw' : cutRad c < ‖w‖ := by
    have h1 : ‖w - z‖ < ‖z‖ - cutRad c := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h2 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := norm_le_norm_add_norm_sub w z
    linarith
  exact cutoff_eq_zero_of_cutRad_le c (le_of_lt hw')

/-! ## Smoothness -/

theorem contDiff_normSq_complex (n : ℕ∞) : ContDiff ℝ n (fun z : ℂ => Complex.normSq z) := by
  simp only [Complex.normSq_apply]
  exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))

theorem contDiff_norm_sq_complex (n : ℕ∞) : ContDiff ℝ n (fun z : ℂ => ‖z‖ ^ 2) := by
  rw [show (fun z : ℂ => ‖z‖ ^ 2) = fun z => Complex.normSq z from
    funext fun z => Complex.sq_norm z]
  exact contDiff_normSq_complex n

theorem contDiff_cutoffArg (c : ℂ) (n : ℕ∞) :
    ContDiff ℝ n (fun z : ℂ => (cutRad c ^ 2 - ‖z‖ ^ 2) / (cutRad c ^ 2 - innerRad c ^ 2)) := by
  have h : ContDiff ℝ n (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq_complex n
  exact (contDiff_const.sub h).div_const _

theorem contDiff_cutoff (c : ℂ) : ContDiff ℝ 1 (cutoff c) := by
  unfold cutoff radialCut
  exact Real.smoothTransition.contDiff.comp (contDiff_cutoffArg c 1)

theorem contDiff_realCoe_cutoff (c : ℂ) : ContDiff ℝ 1 (realCoe (cutoff c)) := by
  unfold realCoe
  exact Complex.ofRealCLM.contDiff.comp (contDiff_cutoff c)

/-! ## The Wirtinger derivatives -/

/-- A function which is eventually equal to a constant at `z` has vanishing Fréchet derivative. -/
theorem fderiv_eq_zero_of_eventuallyEq_const {F : ℂ → ℂ} {z : ℂ} {v : ℂ}
    (h : F =ᶠ[𝓝 z] fun _ => v) : fderiv ℝ F z = 0 := by
  have h' : HasFDerivAt F (0 : ℂ →L[ℝ] ℂ) z :=
    (hasFDerivAt_const v z).congr_of_eventuallyEq h
  simpa using h'.fderiv

theorem realCoe_eventually_eq_one (c : ℂ) {z : ℂ} (hz : ‖z‖ < innerRad c) :
    realCoe (cutoff c) =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
  filter_upwards [eventually_cutoff_eq_one c hz] with w hw
  change ((cutoff c w : ℝ) : ℂ) = 1
  rw [hw]
  norm_num

theorem realCoe_eventually_eq_zero (c : ℂ) {z : ℂ} (hz : cutRad c < ‖z‖) :
    realCoe (cutoff c) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
  filter_upwards [eventually_cutoff_eq_zero c hz] with w hw
  change ((cutoff c w : ℝ) : ℂ) = 0
  rw [hw]
  norm_num

theorem dz_realCoe_cutoff_eq_zero_of_norm_lt_innerRad (c : ℂ) {z : ℂ} (hz : ‖z‖ < innerRad c) :
    Work.MRMT.dz (realCoe (cutoff c)) z = 0 := by
  have hf : fderiv ℝ (realCoe (cutoff c)) z = 0 :=
    fderiv_eq_zero_of_eventuallyEq_const (realCoe_eventually_eq_one c hz)
  show ((fderiv ℝ (realCoe (cutoff c)) z 1
    - Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I) / 2) = 0
  rw [hf]
  simp

theorem dz_realCoe_cutoff_eq_zero_of_cutRad_lt_norm (c : ℂ) {z : ℂ} (hz : cutRad c < ‖z‖) :
    Work.MRMT.dz (realCoe (cutoff c)) z = 0 := by
  have hf : fderiv ℝ (realCoe (cutoff c)) z = 0 :=
    fderiv_eq_zero_of_eventuallyEq_const (realCoe_eventually_eq_zero c hz)
  show ((fderiv ℝ (realCoe (cutoff c)) z 1
    - Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I) / 2) = 0
  rw [hf]
  simp

/-! ## Global boundedness of the Wirtinger derivatives -/

theorem support_fderiv_realCoe_cutoff_subset (c : ℂ) :
    Function.support (fderiv ℝ (realCoe (cutoff c))) ⊆ Metric.closedBall 0 (cutRad c) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_contra h
  exact hz (fderiv_eq_zero_of_eventuallyEq_const
    (realCoe_eventually_eq_zero c (not_le.mp h)))

theorem hasCompactSupport_fderiv_realCoe_cutoff (c : ℂ) :
    HasCompactSupport (fderiv ℝ (realCoe (cutoff c))) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) (cutRad c))
    (support_fderiv_realCoe_cutoff_subset c)

theorem exists_bound_dz_dzbar_cutoff (c : ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ,
      ‖Work.MRMT.dz (realCoe (cutoff c)) z‖ ≤ K ∧
      ‖Work.MRMT.dzbar (realCoe (cutoff c)) z‖ ≤ K := by
  obtain ⟨K, hK⟩ := (contDiff_realCoe_cutoff c).continuous_fderiv (by norm_num :
      (1 : WithTop ℕ∞) ≠ 0) |>.bounded_above_of_compact_support
        (hasCompactSupport_fderiv_realCoe_cutoff c)
  refine ⟨K, le_trans (norm_nonneg _) (hK 0), fun z => ⟨?_, ?_⟩⟩
  · have hA : ‖fderiv ℝ (realCoe (cutoff c)) z 1‖ ≤ K := by
      have h := ContinuousLinearMap.le_opNorm (fderiv ℝ (realCoe (cutoff c)) z) (1 : ℂ)
      simp only [norm_one, mul_one] at h
      exact le_trans h (hK z)
    have hB : ‖fderiv ℝ (realCoe (cutoff c)) z Complex.I‖ ≤ K := by
      have h := ContinuousLinearMap.le_opNorm (fderiv ℝ (realCoe (cutoff c)) z) Complex.I
      simp only [Complex.norm_I, mul_one] at h
      exact le_trans h (hK z)
    have hsplit : ‖fderiv ℝ (realCoe (cutoff c)) z 1
        - Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I‖
        ≤ ‖fderiv ℝ (realCoe (cutoff c)) z 1‖
          + ‖fderiv ℝ (realCoe (cutoff c)) z Complex.I‖ := by
      have h := norm_sub_le (fderiv ℝ (realCoe (cutoff c)) z 1)
        (Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I)
      rwa [norm_mul, Complex.norm_I, one_mul] at h
    have hnorm : ‖(fderiv ℝ (realCoe (cutoff c)) z 1
        - Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I) / 2‖
        = ‖fderiv ℝ (realCoe (cutoff c)) z 1
        - Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I‖ / 2 := by
      rw [norm_div]
      norm_num
    show ‖(fderiv ℝ (realCoe (cutoff c)) z 1
      - Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I) / 2‖ ≤ K
    rw [hnorm]
    linarith
  · have hA : ‖fderiv ℝ (realCoe (cutoff c)) z 1‖ ≤ K := by
      have h := ContinuousLinearMap.le_opNorm (fderiv ℝ (realCoe (cutoff c)) z) (1 : ℂ)
      simp only [norm_one, mul_one] at h
      exact le_trans h (hK z)
    have hB : ‖fderiv ℝ (realCoe (cutoff c)) z Complex.I‖ ≤ K := by
      have h := ContinuousLinearMap.le_opNorm (fderiv ℝ (realCoe (cutoff c)) z) Complex.I
      simp only [Complex.norm_I, mul_one] at h
      exact le_trans h (hK z)
    have hsplit : ‖fderiv ℝ (realCoe (cutoff c)) z 1
        + Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I‖
        ≤ ‖fderiv ℝ (realCoe (cutoff c)) z 1‖
          + ‖fderiv ℝ (realCoe (cutoff c)) z Complex.I‖ := by
      have h := norm_add_le (fderiv ℝ (realCoe (cutoff c)) z 1)
        (Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I)
      rwa [norm_mul, Complex.norm_I, one_mul] at h
    have hnorm : ‖(fderiv ℝ (realCoe (cutoff c)) z 1
        + Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I) / 2‖
        = ‖fderiv ℝ (realCoe (cutoff c)) z 1
        + Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I‖ / 2 := by
      rw [norm_div]
      norm_num
    show ‖(fderiv ℝ (realCoe (cutoff c)) z 1
      + Complex.I * fderiv ℝ (realCoe (cutoff c)) z Complex.I) / 2‖ ≤ K
    rw [hnorm]
    linarith

end cutoffAux

open cutoffAux

/-! ## The statement -/

theorem cutoff_props (c : ℂ) :
    ContDiff ℝ 1 (Work.FBif.cutoff c) ∧
      (∀ z : ℂ, ‖z‖ ≤ Work.FBif.innerRad c → Work.FBif.cutoff c z = 1) ∧
      (∀ z : ℂ, Work.FBif.cutRad c ≤ ‖z‖ → Work.FBif.cutoff c z = 0) ∧
      (∀ z : ℂ, 0 ≤ Work.FBif.cutoff c z ∧ Work.FBif.cutoff c z ≤ 1) ∧
      (∀ z : ℂ, ‖z‖ < Work.FBif.innerRad c →
        Work.MRMT.dz (Work.FBif.realCoe (Work.FBif.cutoff c)) z = 0) ∧
      (∀ z : ℂ, Work.FBif.cutRad c < ‖z‖ →
        Work.MRMT.dz (Work.FBif.realCoe (Work.FBif.cutoff c)) z = 0) ∧
      (∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ,
        ‖Work.MRMT.dz (Work.FBif.realCoe (Work.FBif.cutoff c)) z‖ ≤ K ∧
        ‖Work.MRMT.dzbar (Work.FBif.realCoe (Work.FBif.cutoff c)) z‖ ≤ K) :=
  ⟨contDiff_cutoff c,
   fun _ hz => cutoff_eq_one_of_norm_le c hz,
   fun _ hz => cutoff_eq_zero_of_cutRad_le c hz,
   fun z => ⟨cutoff_nonneg c z, cutoff_le_one c z⟩,
   fun _ hz => dz_realCoe_cutoff_eq_zero_of_norm_lt_innerRad c hz,
   fun _ hz => dz_realCoe_cutoff_eq_zero_of_cutRad_lt_norm c hz,
   exists_bound_dz_dzbar_cutoff c⟩

end Work.FBif

end
