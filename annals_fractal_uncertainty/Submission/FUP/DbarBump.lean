import Submission.FUP.DbarDbarPos
import Submission.Commons.Analysis.Calculus.fderiv_fderiv_swap

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# Closedness of `∂̄` for the bump function of §5

Cohen's §5 takes a smooth bump `h : ℂᵈ → ℂ` with `h = 1` on `B_{1/2}` and `supp h ⊆ B_1`, sets
`η = ∂̄h` and applies Hörmander's theorem, whose hypothesis is `∂̄η = 0`.

This module proves `∂̄(∂̄h) = 0` for every `C²` function `h` (the mixed second derivatives of a `C²`
function commute, which is `Commons.Analysis.Calculus.fderiv_fderiv_swap`, applied to the two real
Wirtinger derivatives), and packages the bump function used in §5 as `bumpC`.
-/

namespace Submission.FUP

section Commute

/-- The derivative of `∂̄_j h` in the direction `u`, in terms of the mixed second derivatives of
`h`. -/
lemma fderiv_partialZbar_apply {h : ℂᵈ → ℂ} (hh : ContDiff ℝ 2 h) (j : Fin d) (z u : ℂᵈ) :
    fderiv ℝ (fun w => partialZbar j h w) z u
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z u
          + Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z u) := by
  have hfd : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have happ : ∀ a : ℂᵈ, DifferentiableAt ℝ (fun w : ℂᵈ => fderiv ℝ h w a) z := by
    intro a
    have h := ((ContinuousLinearMap.apply ℝ ℂ a).differentiableAt).comp z hfd.differentiableAt
    simpa [Function.comp_def] using h
  have hG : DifferentiableAt ℝ (fun w : ℂᵈ => fderiv ℝ h w (Pi.single j (1:ℂ))
      + Complex.I * fderiv ℝ h w (Pi.single j Complex.I)) z :=
    (happ (Pi.single j (1:ℂ))).add ((happ (Pi.single j Complex.I)).const_mul Complex.I)
  have h1 : (fun w : ℂᵈ => partialZbar j h w)
      = fun w : ℂᵈ => (1/2 : ℂ) * (fderiv ℝ h w (Pi.single j (1:ℂ))
          + Complex.I * fderiv ℝ h w (Pi.single j Complex.I)) := by
    funext w; rw [partialZbar]; ring
  have hsplit : fderiv ℝ (fun w : ℂᵈ => fderiv ℝ h w (Pi.single j (1:ℂ))
        + Complex.I * fderiv ℝ h w (Pi.single j Complex.I)) z
      = fderiv ℝ (fun w : ℂᵈ => fderiv ℝ h w (Pi.single j (1:ℂ))) z
        + fderiv ℝ (fun w : ℂᵈ => Complex.I * fderiv ℝ h w (Pi.single j Complex.I)) z := by
    rw [show (fun w : ℂᵈ => fderiv ℝ h w (Pi.single j (1:ℂ))
          + Complex.I * fderiv ℝ h w (Pi.single j Complex.I))
        = (fun w : ℂᵈ => fderiv ℝ h w (Pi.single j (1:ℂ)))
          + (fun w : ℂᵈ => Complex.I * fderiv ℝ h w (Pi.single j Complex.I)) from by
            funext w; rfl]
    exact fderiv_add (happ _) ((happ _).const_mul Complex.I)
  rw [h1, fderiv_const_mul hG (1/2 : ℂ), hsplit,
    fderiv_const_mul (happ (Pi.single j Complex.I)) Complex.I]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The two real Wirtinger derivatives commute for a `C²` function. -/
lemma partialZbar_comm {h : ℂᵈ → ℂ} (hh : ContDiff ℝ 2 h) (j k : Fin d) (z : ℂᵈ) :
    partialZbar k (fun w => partialZbar j h w) z
      = partialZbar j (fun w => partialZbar k h w) z := by
  have hj := fderiv_partialZbar_apply hh j z
  have hk := fderiv_partialZbar_apply hh k z
  have hj1 : fderiv ℝ (fun w => partialZbar j h w) z (Pi.single k (1:ℂ))
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k 1)
          + Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z
              (Pi.single k 1)) := hj _
  have hj2 : fderiv ℝ (fun w => partialZbar j h w) z (Pi.single k Complex.I)
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k Complex.I)
          + Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z
              (Pi.single k Complex.I)) := hj _
  have hk1 : fderiv ℝ (fun w => partialZbar k h w) z (Pi.single j (1:ℂ))
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j 1)
          + Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z
              (Pi.single j 1)) := hk _
  have hk2 : fderiv ℝ (fun w => partialZbar k h w) z (Pi.single j Complex.I)
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j Complex.I)
          + Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z
              (Pi.single j Complex.I)) := hk _
  rw [partialZbar, partialZbar, hj1, hj2, hk1, hk2]
  have e1 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k 1)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j 1) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  have e2 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z (Pi.single k 1)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j Complex.I) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  have e3 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k Complex.I)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z (Pi.single j 1) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  have e4 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z (Pi.single k Complex.I)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z (Pi.single j Complex.I) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  rw [e1, e2, e3, e4]
  ring

/-- **`∂̄(∂̄h) = 0`** for every `C²` function `h`. -/
theorem dbarClosed_dbarFun {h : ℂᵈ → ℂ} (hh : ContDiff ℝ 2 h) : DbarClosed (dbarFun h) := by
  funext z j k
  simp only [dbarForm, dbarFun, Pi.zero_apply]
  exact sub_eq_zero.mpr (partialZbar_comm hh j k z)

end Commute

section Bump

/-- The bump function of §5: a smooth bump on `ℂᵈ` which is `1` on `B_{1/2}` and supported in
`B_1`. -/
noncomputable def unitBump : ContDiffBump (0 : ℂᵈ) := ⟨1/2, 1, by norm_num, by norm_num⟩

/-- The bump of §5, as a `ℂ`-valued function. -/
noncomputable def bumpC (z : ℂᵈ) : ℂ := ((unitBump (d := d) z : ℝ) : ℂ)

lemma contDiff_bumpC : ContDiff ℝ 2 (bumpC (d := d)) := by
  have h : ContDiff ℝ 2 ((fun r : ℝ => (r : ℂ)) ∘ (↑(unitBump (d := d)) : ℂᵈ → ℝ)) :=
    Complex.ofRealCLM.contDiff.comp (unitBump (d := d)).contDiff
  convert h using 1
  funext z
  simp only [Function.comp_def, bumpC, Complex.ofRealCLM_apply]

lemma contDiff_bumpC_top : ContDiff ℝ ∞ (bumpC (d := d)) := by
  have h : ContDiff ℝ ∞ ((fun r : ℝ => (r : ℂ)) ∘ (↑(unitBump (d := d)) : ℂᵈ → ℝ)) :=
    Complex.ofRealCLM.contDiff.comp (unitBump (d := d)).contDiff
  convert h using 1
  funext z
  simp only [Function.comp_def, bumpC, Complex.ofRealCLM_apply]

lemma contDiff_dbarFun_bumpC : ContDiff ℝ ∞ (dbarFun (bumpC (d := d))) :=
  contDiff_dbarFun contDiff_bumpC_top

lemma support_bumpC_subset : Function.support (bumpC (d := d)) ⊆ Metric.closedBall (0 : ℂᵈ) 1 := by
  have hb : Function.support (bumpC (d := d)) ⊆ Metric.ball (0 : ℂᵈ) 1 := by
    intro z hz
    have hz' : (unitBump (d := d) z : ℝ) ≠ 0 := by
      simpa [bumpC, Function.mem_support] using hz
    have hmem : z ∈ Function.support (↑(unitBump (d := d)) : ℂᵈ → ℝ) := by
      simpa [Function.mem_support] using hz'
    rw [(unitBump (d := d)).support_eq] at hmem
    exact hmem
  exact fun z hz => Metric.ball_subset_closedBall (hb hz)

lemma tsupport_bumpC_subset : tsupport (bumpC (d := d)) ⊆ Metric.closedBall (0 : ℂᵈ) 1 :=
  closure_minimal (support_bumpC_subset (d := d)) Metric.isClosed_closedBall

lemma bumpC_eq_one {x : ℂᵈ} (hx : ‖x‖ ≤ 1/2) : bumpC (d := d) x = 1 := by
  have hmem : x ∈ Metric.closedBall (0 : ℂᵈ) (unitBump (d := d)).rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx
  have h : (unitBump (d := d) x : ℝ) = 1 := (unitBump (d := d)).one_of_mem_closedBall hmem
  rw [bumpC, h]
  norm_num

lemma bumpC_eq_zero_of_one_lt {x : ℂᵈ} (hx : 1 < ‖x‖) : bumpC (d := d) x = 0 := by
  by_contra hne
  have hmem : x ∈ Function.support (bumpC (d := d)) := by simpa [Function.mem_support] using hne
  have h1 := support_bumpC_subset (d := d) hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  linarith

/-- `∂̄ h = 0` on `B_{1/2}`, where `h = 1`. -/
lemma dbarFun_bumpC_eq_zero_of_lt_half {x : ℂᵈ} (hx : ‖x‖ < 1/2) :
    dbarFun (bumpC (d := d)) x = 0 := by
  have hnb : Metric.ball (0 : ℂᵈ) (1/2) ∈ 𝓝 x :=
    Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hx)
  have hev : (bumpC (d := d)) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
    filter_upwards [hnb] with y hy
    exact bumpC_eq_one (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hy))
  have hfd : fderiv ℝ (bumpC (d := d)) x = 0 := by
    have h1 : HasFDerivAt (bumpC (d := d)) (0 : ℂᵈ →L[ℝ] ℂ) x :=
      (hasFDerivAt_const (𝕜 := ℝ) (c := (1:ℂ)) (x := x)).congr_of_eventuallyEq hev
    exact h1.fderiv
  funext j
  simp only [dbarFun, partialZbar, hfd, ContinuousLinearMap.zero_apply, mul_zero, add_zero,
    zero_div, Pi.zero_apply]

/-- Outside `B_1` the bump vanishes identically, so its derivative vanishes. -/
lemma fderiv_bumpC_eq_zero_of_one_lt {x : ℂᵈ} (hx : 1 < ‖x‖) :
    fderiv ℝ (bumpC (d := d)) x = 0 := by
  have hnb : (tsupport (bumpC (d := d)))ᶜ ∈ 𝓝 x :=
    (isClosed_tsupport _).isOpen_compl.mem_nhds (fun hmem => by
      have h1 := tsupport_bumpC_subset (d := d) hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      linarith)
  have hev : (bumpC (d := d)) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hnb] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have h1 : HasFDerivAt (bumpC (d := d)) (0 : ℂᵈ →L[ℝ] ℂ) x :=
    (hasFDerivAt_const (𝕜 := ℝ) (c := (0:ℂ)) (x := x)).congr_of_eventuallyEq hev
  exact h1.fderiv

/-- `∂̄ h = 0` outside `B_1`, where `h = 0`. -/
lemma dbarFun_bumpC_eq_zero_of_one_lt {x : ℂᵈ} (hx : 1 < ‖x‖) :
    dbarFun (bumpC (d := d)) x = 0 := by
  have hfd := fderiv_bumpC_eq_zero_of_one_lt (d := d) hx
  funext j
  simp only [dbarFun, partialZbar, hfd, ContinuousLinearMap.zero_apply, mul_zero, add_zero,
    zero_div, Pi.zero_apply]

/-- The derivative of the bump is uniformly bounded. -/
lemma exists_bound_fderiv_bumpC :
    ∃ B : ℝ, ∀ z : ℂᵈ, ‖fderiv ℝ (bumpC (d := d)) z‖ ≤ B := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ (bumpC (d := d))) :=
    contDiff_bumpC.fderiv_right (m := 1) (by norm_num)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂᵈ) 1).exists_bound_of_continuousOn
    hfd.continuous.continuousOn
  refine ⟨max B 0, fun z => ?_⟩
  by_cases hz : z ∈ Metric.closedBall (0 : ℂᵈ) 1
  · exact le_trans (hB z hz) (le_max_left _ _)
  · rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    rw [fderiv_bumpC_eq_zero_of_one_lt (d := d) hz, norm_zero]
    exact le_max_right _ _

/-- **`∂̄(∂̄ h) = 0` for the bump of §5.** -/
theorem dbarClosed_bumpC : DbarClosed (dbarFun (bumpC (d := d))) :=
  dbarClosed_dbarFun contDiff_bumpC

end Bump

end Submission.FUP
