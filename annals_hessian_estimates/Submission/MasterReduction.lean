/-
The final reduction of the challenge statement to the "master estimate" -- the a priori bound on
`Delta u(0)` in terms of the `C^1` norm which is the content of Section 5 of Shankar--Yuan.

This file currently contains:
* the statement of the master estimate and its use for the Frobenius bound
  (`frobeniusNorm_hessian_le_laplacian`);
* the design of the reduction (see `Submission/Roadmap.md`, section "SESSION 5").

The master estimate is stated in the "Skolemised" form: a bound function `B : ℝ → ℝ` such that
every solution whose `C^1` norm on `closedBall 0 3` is bounded by `Γ` satisfies `Δu 0 ≤ B Γ`.
The reduction (to be completed) is:

  rescale `ũ(x) = 16 * u (x/4)` (so `a * b^2 = 1` with `a = 16`, `b = 1/4`, which preserves `Δ`
  and `σ₂`), obtain the `C^1` bounds of `ũ` on `closedBall 0 3` from the `L^∞` norms of `u` and
  `fderiv ℝ u` on `ball 0 1` (`Commons.Measure.LpSeminorm.norm_le_toReal_eLpNorm_top`), apply the
  master estimate, and finish with `‖H u (ball 0 1) 0‖_F ≤ Δu 0` and
  `C e = B (16 * (e.toReal + 1) + 4)`.
-/
import ChallengeDeps
import Submission.DoublingMovingCenter
import Submission.Commons.Measure.LpSeminorm.norm_le_toReal_eLpNorm_top
import Submission.Commons.Analysis.Sigma2.frobenius_le_trace_of_sigma2_one
import Submission.Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues
import Submission.Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv
import Submission.Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian

open HessianEstimates
open Commons.Analysis.Calculus.FDeriv
open Commons.Analysis.Sigma2
open Commons.Analysis.InnerProductSpace
open Commons.Measure.LpSeminorm
open Laplacian Metric MeasureTheory
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

local notation "‖" f "‖_C¹(" s ")" => eC1NormOn f s volume
local notation "‖" T "‖_F" => frobeniusNorm T

/-! ## The master estimate (Section 5) -/

/-- The `C^1`-type bound function of the master estimate: `B Γ` bounds `Δu(0)` for every solution
of `σ₂(D²u) = 1` with `Δu > 0` and `|u|, ‖Du‖ ≤ Γ - 4` on `closedBall 0 3`. -/
def IsMasterBound (B : ℝ → ℝ) : Prop :=
  ∀ Γ : ℝ, 4 ≤ Γ → ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴),
    IsOpen s → closedBall 0 3 ⊆ s → ContDiffOn ℝ 4 u s →
    (∀ y ∈ s, σ₂ (H u s y) = 1) → (∀ y ∈ s, 0 < (Δ u) y) →
    (∀ z ∈ closedBall 0 3, |u z| ≤ Γ - 4) →
    (∀ z ∈ closedBall 0 3, ‖fderiv ℝ u z‖ ≤ Γ - 4) →
    (Δ u) 0 ≤ B Γ

/-! ## The Frobenius norm of the Hessian is bounded by the Laplacian -/

/-- For a smooth solution with `σ₂(D²u) = 1` and `Δu > 0` the Frobenius norm of the Hessian
operator at a point is at most `Δu` there.  This is the final step of the proof: it reduces the
Hessian estimate to the Laplacian (trace) estimate. -/
theorem frobeniusNorm_hessian_le_laplacian {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hx : (0 : ℝ⁴) ∈ s) (hu : ContDiffOn ℝ 2 u s) (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1)
    (hΔ : ∀ y ∈ s, 0 < (Δ u) y) :
    ‖H u s 0‖_F ≤ (Δ u) 0 := by
  set T : ℝ⁴ →L[ℝ] ℝ⁴ := H u s 0 with hTdef
  have hTsym : T.IsSymmetric := isSymmetric_hessianWithin hs hx hu
  have hpair : (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i : Fin (Module.finrank ℝ ℝ⁴),
      if i < j then hTsym.eigenvalues rfl i * hTsym.eigenvalues rfl j else 0) = 1 := by
    have h := hσ2 0 hx
    rw [HessianEstimates.σ₂, dif_pos hTsym] at h
    rw [show (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i < j,
          hTsym.eigenvalues rfl i * hTsym.eigenvalues rfl j)
        = (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i : Fin (Module.finrank ℝ ℝ⁴),
            if i < j then hTsym.eigenvalues rfl i * hTsym.eigenvalues rfl j else 0) from
        Finset.sum_congr rfl (fun j _ => by
          show (∑ i ∈ Finset.Iio j, _) = _
          rw [show Finset.Iio j = Finset.univ.filter (fun x => x < j) from by
                ext x; simp [Finset.mem_Iio], Finset.sum_filter])] at h
    exact h
  have htr : LinearMap.trace ℝ ℝ⁴ (T : ℝ⁴ →ₗ[ℝ] ℝ⁴) = (Δ u) 0 := by
    show LinearMap.trace ℝ ℝ⁴ ((InnerProductSpace.continuousLinearMapOfBilin
      (fderivWithin ℝ (fderivWithin ℝ u s) s 0)) : ℝ⁴ →ₗ[ℝ] ℝ⁴) = (Δ u) 0
    rw [← laplacian_eq_trace_hessian (u := u) (s := s) (x := 0) hs hx hu
      (stdOrthonormalBasis ℝ ℝ⁴)]
  have hσ1 : 0 < ∑ i : Fin (Module.finrank ℝ ℝ⁴), hTsym.eigenvalues rfl i := by
    rw [← trace_eq_sum_eigenvalues hTsym, htr]
    exact hΔ 0 hx
  have hF := frobenius_le_trace_of_sigma2_one hTsym hσ1 hpair
  have hsum : (∑ i : Fin (Module.finrank ℝ ℝ⁴), hTsym.eigenvalues rfl i) = (Δ u) 0 := by
    rw [← trace_eq_sum_eigenvalues hTsym, htr]
  rw [hsum] at hF
  exact le_trans hF le_rfl

end Submission


namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable def rescale4 (u : ℝ⁴ → ℝ) : ℝ⁴ → ℝ := fun x => 16 * u ((1 / 4 : ℝ) • x)

theorem preimage_quarter_ball : {x : ℝ⁴ | (1 / 4 : ℝ) • x ∈ ball 0 1} = ball 0 4 := by
  ext x
  simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  constructor <;> intro h <;> linarith

theorem quarter_mem_ball {z : ℝ⁴} (hz : z ∈ ball 0 4) : (1 / 4 : ℝ) • z ∈ ball 0 1 := by
  have h := hz
  rw [← preimage_quarter_ball] at h
  exact h

theorem contDiffOn_rescale4 {u : ℝ⁴ → ℝ} (hu : ContDiffOn ℝ 4 u (ball 0 1)) :
    ContDiffOn ℝ 4 (rescale4 u) (ball 0 4) := by
  have h := contDiffOn_rescale (u := u) (s := ball 0 1) (a := 16) (b := 1 / 4) (y := 0) hu
  have hset : {x : ℝ⁴ | (1 / 4 : ℝ) • x + 0 ∈ ball 0 1} = ball 0 4 := by
    rw [show {x : ℝ⁴ | (1 / 4 : ℝ) • x + 0 ∈ ball 0 1}
        = {x : ℝ⁴ | (1 / 4 : ℝ) • x ∈ ball 0 1} from by ext x; simp]
    exact preimage_quarter_ball
  rw [hset] at h
  change ContDiffOn ℝ 4 (fun x => 16 * u ((1 / 4 : ℝ) • x)) (ball 0 4)
  simpa only [add_zero] using h

theorem laplacian_rescale4 {u : ℝ⁴ → ℝ} (hu : ContDiffOn ℝ 2 u (ball 0 1)) {z : ℝ⁴}
    (hz : z ∈ ball 0 4) : (Δ (rescale4 u)) z = (Δ u) ((1 / 4 : ℝ) • z) := by
  have hz1 := quarter_mem_ball hz
  have huAt : ContDiffAt ℝ 2 u (((1 / 4 : ℝ) • z) + 0) := by
    simpa using hu.contDiffAt (isOpen_ball.mem_nhds hz1)
  have h := laplacian_rescale (u := u) (a := 16) (b := 1 / 4) (y := 0) (z := z) huAt
  rw [show (16 : ℝ) * (1 / 4) ^ 2 = 1 by norm_num] at h
  change (Δ (fun x => 16 * u ((1 / 4 : ℝ) • x))) z = (Δ u) ((1 / 4 : ℝ) • z)
  simpa only [add_zero, one_mul] using h

theorem sigma2_rescale4 {u : ℝ⁴ → ℝ} (hu : ContDiffOn ℝ 2 u (ball 0 1)) {z : ℝ⁴}
    (hz : z ∈ ball 0 4) :
    σ₂ (H (rescale4 u) (ball 0 4) z) = σ₂ (H u (ball 0 1) ((1 / 4 : ℝ) • z)) := by
  have hz1 := quarter_mem_ball hz
  have h := sigma2_rescale (u := u) (s := ball 0 1) (a := 16) (b := 1 / 4) (y := 0) (z := z)
      isOpen_ball hu (by simpa using hz1) (by norm_num)
  have hset : {x : ℝ⁴ | (1 / 4 : ℝ) • x + 0 ∈ ball 0 1} = ball 0 4 := by
    rw [show {x : ℝ⁴ | (1 / 4 : ℝ) • x + 0 ∈ ball 0 1}
        = {x : ℝ⁴ | (1 / 4 : ℝ) • x ∈ ball 0 1} from by ext x; simp]
    exact preimage_quarter_ball
  rw [hset] at h
  change σ₂ (H (fun x => 16 * u ((1 / 4 : ℝ) • x)) (ball 0 4) z)
    = σ₂ (H u (ball 0 1) ((1 / 4 : ℝ) • z))
  simpa only [add_zero] using h

theorem fderiv_rescale4 {u : ℝ⁴ → ℝ} (hu : ContDiffOn ℝ 1 u (ball 0 1)) {z : ℝ⁴}
    (hz : z ∈ ball 0 4) :
    fderiv ℝ (rescale4 u) z = (4 : ℝ) • fderiv ℝ u ((1 / 4 : ℝ) • z) := by
  have hz1 := quarter_mem_ball hz
  have huAt : DifferentiableAt ℝ u (((1 / 4 : ℝ) • z) + 0) := by
    simpa using (hu.contDiffAt (isOpen_ball.mem_nhds hz1)).differentiableAt (by norm_num)
  have h := fderiv_rescale (u := u) (a := 16) (b := 1 / 4) (y := 0) (z := z) huAt
  rw [show (16 : ℝ) * (1 / 4) = 4 by norm_num] at h
  change fderiv ℝ (fun x => 16 * u ((1 / 4 : ℝ) • x)) z
    = (4 : ℝ) • fderiv ℝ u ((1 / 4 : ℝ) • z)
  simpa only [add_zero] using h

theorem norm_fderiv_rescale4 {u : ℝ⁴ → ℝ} (hu : ContDiffOn ℝ 1 u (ball 0 1)) {z : ℝ⁴}
    (hz : z ∈ ball 0 4) :
    ‖fderiv ℝ (rescale4 u) z‖ = (4 : ℝ) * ‖fderiv ℝ u ((1 / 4 : ℝ) • z)‖ := by
  rw [fderiv_rescale4 hu hz, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 4)]

theorem abs_rescale4 {u : ℝ⁴ → ℝ} (z : ℝ⁴) :
    |rescale4 u z| = 16 * |u ((1 / 4 : ℝ) • z)| := by
  change |16 * u ((1 / 4 : ℝ) • z)| = 16 * |u ((1 / 4 : ℝ) • z)|
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 16)]

theorem theorem_1_1_of_master (B : ℝ → ℝ) (hm : IsMasterBound B) (L : WithTop ℕ∞)
    (hL : (4 : WithTop ℕ∞) ≤ L) :
    ∃ C : ℝ≥0∞ → ℝ, ∀ (u : ℝ⁴ → ℝ)
      (_smooth : ContDiffOn ℝ L u (ball 0 1))
      (_bounded : eC1NormOn u (ball 0 1) volume < (∞ : ℝ≥0∞))
      (_positive_branch : ∀ x ∈ ball 0 1, (Δ u) x > 0)
      (_solution : ∀ x ∈ ball 0 1, σ₂ (H u (ball 0 1) x) = 1),
      frobeniusNorm (H u (ball 0 1) 0) ≤ C (eC1NormOn u (ball 0 1) volume) := by
  refine ⟨fun E => B (16 * (E.toReal + 1) + 4), ?_⟩
  intro u hsmooth hbdd hpos hsol
  have hs4 : ContDiffOn ℝ 4 u (ball 0 1) := hsmooth.of_le hL
  have hs2 : ContDiffOn ℝ 2 u (ball 0 1) :=
    hsmooth.of_le (le_trans (by norm_num : (2 : WithTop ℕ∞) ≤ 4) hL)
  have hs1 : ContDiffOn ℝ 1 u (ball 0 1) :=
    hsmooth.of_le (le_trans (by norm_num : (1 : WithTop ℕ∞) ≤ 4) hL)
  set E : ℝ≥0∞ := eC1NormOn u (ball 0 1) volume with hEdef
  have hsum : E = eLpNorm u ⊤ (volume.restrict (ball 0 1))
      + eLpNorm (fderiv ℝ u) ⊤ (volume.restrict (ball 0 1)) := by
    rw [hEdef]; rfl
  have hEl : E < ⊤ := by rw [hEdef]; exact hbdd
  have hEne : E ≠ ⊤ := ne_of_lt hEl
  have hadd : eLpNorm u ⊤ (volume.restrict (ball 0 1))
      + eLpNorm (fderiv ℝ u) ⊤ (volume.restrict (ball 0 1)) < ⊤ := by
    rw [← hsum]; exact hEl
  have hfin1 := (ENNReal.add_lt_top.mp hadd).1
  have hfin2 := (ENNReal.add_lt_top.mp hadd).2
  have hle1 : (eLpNorm u ⊤ (volume.restrict (ball 0 1))).toReal ≤ E.toReal :=
    ENNReal.toReal_mono hEne (by rw [hsum]; exact le_self_add)
  have hle2 : (eLpNorm (fderiv ℝ u) ⊤ (volume.restrict (ball 0 1))).toReal ≤ E.toReal :=
    ENNReal.toReal_mono hEne (by rw [hsum]; exact le_add_self)
  have hu_bound : ∀ x ∈ ball 0 1, |u x| ≤ E.toReal := by
    intro x hx
    have h := norm_le_toReal_eLpNorm_top (f := u) isOpen_ball hsmooth.continuousOn hfin1 hx
    simpa using le_trans h hle1
  have hdu_bound : ∀ x ∈ ball 0 1, ‖fderiv ℝ u x‖ ≤ E.toReal := by
    intro x hx
    have hcont : ContinuousOn (fderiv ℝ u) (ball 0 1) := continuousOn_fderiv isOpen_ball hs1
    have h := norm_le_toReal_eLpNorm_top (f := fderiv ℝ u) isOpen_ball hcont hfin2 hx
    exact le_trans h hle2
  have hG4 : (4 : ℝ) ≤ 16 * (E.toReal + 1) + 4 := by
    linarith [ENNReal.toReal_nonneg (a := E)]
  have hR4 : ContDiffOn ℝ 4 (rescale4 u) (ball 0 4) := contDiffOn_rescale4 hs4
  have hRσ : ∀ z ∈ ball 0 4, σ₂ (H (rescale4 u) (ball 0 4) z) = 1 := by
    intro z hz
    rw [sigma2_rescale4 hs2 hz]
    exact hsol _ (quarter_mem_ball hz)
  have hRΔ : ∀ z ∈ ball 0 4, 0 < (Δ (rescale4 u)) z := by
    intro z hz
    rw [laplacian_rescale4 hs2 hz]
    exact hpos _ (quarter_mem_ball hz)
  have hsub : closedBall (0:ℝ⁴) 3 ⊆ ball (0:ℝ⁴) 4 := closedBall_subset_ball (by norm_num : (3:ℝ) < 4)
  have hRb1 : ∀ z ∈ closedBall 0 3, |rescale4 u z| ≤ 16 * (E.toReal + 1) + 4 - 4 := by
    intro z hz
    have hz4 : z ∈ ball 0 4 := hsub hz
    rw [abs_rescale4]
    have h2 := hu_bound _ (quarter_mem_ball hz4)
    have h3 : (16 : ℝ) * (E.toReal + 1) + 4 - 4 = 16 * (E.toReal + 1) := by ring
    rw [h3]
    nlinarith
  have hRb2 : ∀ z ∈ closedBall 0 3, ‖fderiv ℝ (rescale4 u) z‖ ≤ 16 * (E.toReal + 1) + 4 - 4 := by
    intro z hz
    have hz4 : z ∈ ball 0 4 := hsub hz
    rw [norm_fderiv_rescale4 hs1 hz4]
    have h2 := hdu_bound _ (quarter_mem_ball hz4)
    have h3 : (16 : ℝ) * (E.toReal + 1) + 4 - 4 = 16 * (E.toReal + 1) := by ring
    rw [h3]
    nlinarith
  have hmaster := hm (16 * (E.toReal + 1) + 4) hG4 (rescale4 u) (ball 0 4) isOpen_ball
      hsub hR4 hRσ hRΔ hRb1 hRb2
  have hΔ0 : (Δ (rescale4 u)) 0 = (Δ u) 0 := by
    have hz : (0 : ℝ⁴) ∈ ball 0 4 := by simp
    have h := laplacian_rescale4 hs2 hz
    simpa using h
  have hfrob := frobeniusNorm_hessian_le_laplacian (u := u) (s := ball 0 1) isOpen_ball
      (by simp) hs2 hsol hpos
  have hmain : frobeniusNorm (H u (ball 0 1) 0) ≤ B (16 * (E.toReal + 1) + 4) :=
    le_trans (le_trans hfrob (le_of_eq hΔ0.symm)) hmaster
  rw [hEdef] at hmain
  exact hmain

end Submission
