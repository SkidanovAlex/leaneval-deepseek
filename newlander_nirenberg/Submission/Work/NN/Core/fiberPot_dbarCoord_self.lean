import Mathlib
import Submission.Work.NN.Core.fiberPot
import Submission.Work.NN.Core.fiberPot_eq_shiftIntegral
import Submission.Work.NN.Core.fiberPot_dbarCoord_eq_zero
import Submission.Work.NN.Core.dbarCoord_fiberPot_of_fibreCut
import Submission.Work.CR.Flat.Cauchy.dbarTransform_dbarCoord
import Submission.Work.CR.Flat.Cauchy.contDiff_dbarTransform
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.NN.Core.sharpCut

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Work.NN.Core

/-- The fixed-disc potential of fibre-supported data agrees with the centred Cauchy-type
transform `dbarTransform` near the point of interest.  Both are the integral of
`s ↦ v (y + s e_j)/s` against the kernel `1/s`, so it suffices that the (translated) support of
the integrand is contained in both discs `‖s‖ < R` and `‖s + y j‖ < R`. -/
lemma fiberPot_eq_dbarTransform {n : ℕ} (R : ℝ) (j : Fin n)
    {v : (Fin n → ℂ) → ℂ} (hv : Continuous v) {z y : Fin n → ℂ} {ρ : ℝ}
    (hsupp : ∀ (y : Fin n → ℂ) (w : ℂ), ρ ≤ ‖w - z j‖ → v (Function.update y j w) = 0)
    (h1 : ρ + ‖z j‖ < R) (h2 : ρ + ‖y j - z j‖ < R) :
    fiberPot R j v y = Work.CR.Flat.Cauchy.dbarTransform R j v y := by
  rw [fiberPot_eq_shiftIntegral R j hv y]
  rw [show Work.CR.Flat.Cauchy.dbarTransform R j v y
      = -((Real.pi : ℂ))⁻¹ * ∫ s in Metric.ball (0:ℂ) R,
          v (y + Function.update (0:Fin n→ℂ) j s) / s from rfl]
  congr 1
  have hupd : ∀ s : ℂ, Function.update y j (y j + s) = y + Function.update (0:Fin n→ℂ) j s := by
    intro s; funext l; by_cases hl : l = j <;> simp [hl, Pi.add_apply]
  have hA : ∀ s : ℂ, s ∉ Metric.ball (-(y j)) R →
      v (y + Function.update (0:Fin n→ℂ) j s) / s = 0 := by
    intro s hs
    rw [Metric.mem_ball, not_lt, dist_eq_norm] at hs
    have hsj : ‖s - (-(y j))‖ = ‖y j + s‖ := by rw [sub_neg_eq_add]; ring_nf
    have hRs : R ≤ ‖y j + s‖ := by rw [← hsj]; exact hs
    have hle : ‖y j + s‖ ≤ ‖(y j + s) - z j‖ + ‖z j‖ := by
      calc ‖y j + s‖ = ‖((y j+s) - z j) + z j‖ := by ring_nf
        _ ≤ ‖(y j+s) - z j‖ + ‖z j‖ := norm_add_le _ _
    have hge : ρ ≤ ‖(y j + s) - z j‖ := by linarith
    have hv0 : v (y + Function.update (0:Fin n→ℂ) j s) = 0 := by
      have hh := hsupp y (y j + s) hge
      rwa [hupd s] at hh
    rw [hv0, zero_div]
  have hB : ∀ s : ℂ, s ∉ Metric.ball (0:ℂ) R →
      v (y + Function.update (0:Fin n→ℂ) j s) / s = 0 := by
    intro s hs
    rw [Metric.mem_ball, not_lt, dist_eq_norm, sub_zero] at hs
    have hle : ‖s‖ ≤ ‖(y j + s) - z j‖ + ‖y j - z j‖ := by
      calc ‖s‖ = ‖((y j+s) - z j) - (y j - z j)‖ := by ring_nf
        _ ≤ ‖(y j+s) - z j‖ + ‖y j - z j‖ := norm_sub_le _ _
    have hge : ρ ≤ ‖(y j + s) - z j‖ := by linarith
    have hv0 : v (y + Function.update (0:Fin n→ℂ) j s) = 0 := by
      have hh := hsupp y (y j + s) hge
      rwa [hupd s] at hh
    rw [hv0, zero_div]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hA,
      setIntegral_eq_integral_of_forall_compl_eq_zero hB]

/-- Eventual version of `fiberPot_eq_dbarTransform`. -/
lemma fiberPot_eventuallyEq_dbarTransform {n : ℕ} (R : ℝ) (j : Fin n)
    {v : (Fin n → ℂ) → ℂ} (hv : Continuous v) {z : Fin n → ℂ} {ρ : ℝ}
    (hsupp : ∀ (y : Fin n → ℂ) (w : ℂ), ρ ≤ ‖w - z j‖ → v (Function.update y j w) = 0)
    (h1 : ρ + ‖z j‖ < R) :
    fiberPot R j v =ᶠ[𝓝 z] Work.CR.Flat.Cauchy.dbarTransform R j v := by
  have hpos : 0 < R - ρ - ‖z j‖ := by linarith
  filter_upwards [Metric.ball_mem_nhds z hpos] with y hy
  refine fiberPot_eq_dbarTransform R j hv hsupp h1 ?_
  have hy' : ‖y - z‖ < R - ρ - ‖z j‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
  have h2 : ‖y j - z j‖ ≤ ‖y - z‖ := norm_le_pi_norm (y - z) j
  nlinarith [norm_nonneg (z j)]

/-- `sharpCut` is `C¹`. -/
lemma contDiff_one_of_sharpCut {a b : ℝ} : ContDiff ℝ 1 (Work.NN.Core.sharpCut a b) :=
  (Work.NN.Core.contDiff_sharpCut (a := a) (b := b)).of_le (by simp)

/-- The coordinate map `y ↦ y j - z j` is `C¹`. -/
lemma contDiff_one_apply_sub {n : ℕ} (j : Fin n) (z : Fin n → ℂ) :
    ContDiff ℝ 1 (fun y : Fin n → ℂ => y j - z j) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).contDiff.sub contDiff_const

/-- The fixed-disc potential of data cut off around `z j` (with support radius `ρ` inside the
disc: `ρ + ‖z j‖ < R`) is (real-)differentiable at `z`. -/
lemma differentiableAt_fiberPot_cut {n : ℕ} (R : ℝ) (j : Fin n)
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ 1 u) {z : Fin n → ℂ}
    {c : ℂ → ℂ} (hc : ContDiff ℝ 1 c) {ρ : ℝ} (_hρnn : 0 ≤ ρ)
    (hcsupp : ∀ ζ : ℂ, ρ ≤ ‖ζ‖ → c ζ = 0) (hρR : ρ + ‖z j‖ < R) :
    DifferentiableAt ℝ (fiberPot R j (fun y => u y * c (y j - z j))) z := by
  set v : (Fin n → ℂ) → ℂ := fun y => u y * c (y j - z j) with hvdef
  have hv : ContDiff ℝ 1 v := by
    rw [hvdef]
    exact hu.mul (hc.comp (contDiff_one_apply_sub j z))
  have hsupp : ∀ (y : Fin n → ℂ) (w : ℂ), ρ ≤ ‖w - z j‖ → v (Function.update y j w) = 0 := by
    intro y w hw
    simp only [hvdef]
    rw [Function.update_self, hcsupp (w - z j) hw, mul_zero]
  have hbsupp : ∀ y : Fin n → ℂ, ‖z j‖ + ρ ≤ ‖y j‖ → v y = 0 := by
    intro y hy
    simp only [hvdef]
    have hle : ‖y j - z j‖ ≥ ρ := by
      have h1 : ‖y j‖ ≤ ‖y j - z j‖ + ‖z j‖ := by
        calc ‖y j‖ = ‖(y j - z j) + z j‖ := by ring_nf
          _ ≤ ‖(y j - z j)‖ + ‖z j‖ := norm_add_le _ _
      linarith
    rw [hcsupp (y j - z j) hle, mul_zero]
  have hev := fiberPot_eventuallyEq_dbarTransform R j hv.continuous hsupp (by linarith)
  rw [hev.differentiableAt_iff]
  exact ((Work.CR.Flat.Cauchy.contDiff_dbarTransform
    (by linarith : ‖z j‖ + ρ < R) j 1 hv hbsupp).differentiable one_ne_zero).differentiableAt

/-- **The fixed-disc Cauchy potential in the `j`-th fibre is a right inverse of `∂̄_j`.**

For every `C¹` function `u : ℂⁿ → ℂ` (globally defined, *not* assumed to have any support) and
every `z` with `‖z j‖ < R` one has `∂̄_j (fiberPot R j u) z = u z`, where
`fiberPot R j u z = -(1/π) ∫_{‖w‖ < R} u (z with z j replaced by w) / (w - z j) dw`
(defined in `Submission.Work.NN.Core.fiberPot`).

Two proof routes: (a) prove the mean-value identity and differentiate the *subtracted* potential
under the integral sign; (b) take a smooth cutoff `ψ` in the fibre variable equal to `1` near
`z j` and supported in `‖w‖ < R`, write `u = uψ + u(1-ψ)`: for `uψ` (supported data) the identity
follows from `Work.CR.Flat.Cauchy.pompeiuFormula` / `dbarC_cauchyTransform` (after comparing the
fixed-disc and moving-disc domains of integration), while the second term is holomorphic at `z`. -/
theorem fiberPot_dbarCoord_self {n : ℕ} (R : ℝ) (hR : 0 < R) (j : Fin n)
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ 1 u) {z : Fin n → ℂ} (hz : ‖z j‖ < R) :
    Work.CR.Flat.dbarCoord j (Work.NN.Core.fiberPot R j u) z = u z := by
  set δ : ℝ := (R - ‖z j‖) / 10 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have h3δnn : 0 ≤ 3 * δ := by linarith
  have h36 : 3 * δ < 6 * δ := by linarith
  have hρR : ‖z j‖ + 6 * δ < R := by rw [hδdef]; linarith
  have hρnn : 0 ≤ 6 * δ := by linarith
  have hc_cd : ContDiff ℝ 1 (sharpCut (3 * δ) (6 * δ)) := contDiff_one_of_sharpCut
  have hc_supp : ∀ ζ : ℂ, 6 * δ ≤ ‖ζ‖ → sharpCut (3 * δ) (6 * δ) ζ = 0 :=
    fun ζ hζ => sharpCut_eq_zero h3δnn h36 hζ
  have hc_one : sharpCut (3 * δ) (6 * δ) 0 = 1 :=
    sharpCut_eq_one h3δnn h36 (by rw [norm_zero]; linarith)
  set v₁ : (Fin n → ℂ) → ℂ := fun y => u y * sharpCut (3 * δ) (6 * δ) (y j - z j) with hv1
  set v₂ : (Fin n → ℂ) → ℂ := fun y => u y * (1 - sharpCut (3 * δ) (6 * δ) (y j - z j)) with hv2
  have hsum : ∀ y : Fin n → ℂ, v₁ y + v₂ y = u y := by
    intro y; rw [hv1, hv2]; ring
  have hv1_cont : Continuous v₁ := by
    rw [hv1]
    exact hu.continuous.mul (hc_cd.continuous.comp
      ((continuous_apply j).sub continuous_const))
  have hv2_cont : Continuous v₂ := by
    rw [hv2]
    exact hu.continuous.mul
      (continuous_const.sub (hc_cd.continuous.comp ((continuous_apply j).sub continuous_const)))
  have hv2_cd : ContDiff ℝ 1 v₂ := by
    rw [hv2]
    exact hu.mul (contDiff_const.sub (hc_cd.comp (contDiff_one_apply_sub j z)))
  -- the potential splits
  have hFsplit : fiberPot R j u = fun y => fiberPot R j v₁ y + fiberPot R j v₂ y := by
    funext y
    have h := fiberPot_add R j hv1_cont hv2_cont y
    rw [show (fun y => v₁ y + v₂ y) = u from funext hsum] at h
    exact h
  -- piece 1
  have hF1_diff : DifferentiableAt ℝ (fiberPot R j v₁) z := by
    rw [hv1]
    exact differentiableAt_fiberPot_cut R j hu hc_cd hρnn hc_supp (by linarith)
  have hF1 : Work.CR.Flat.dbarCoord j (fiberPot R j v₁) z = u z := by
    rw [hv1]
    exact dbarCoord_fiberPot_of_fibreCut R hR j hu hz hc_cd hρnn hρR hc_supp hc_one
  -- piece 2
  have hvan : ∀ y : Fin n → ℂ, ‖y - z‖ < δ → ∀ w : ℂ, ‖w - y j‖ < δ →
      v₂ (Function.update y j w) = 0 := by
    intro y hy w hw
    simp only [hv2]
    rw [Function.update_self]
    have hc1 : sharpCut (3 * δ) (6 * δ) (w - z j) = 1 := by
      apply sharpCut_eq_one h3δnn h36
      have h1 : ‖w - z j‖ ≤ ‖w - y j‖ + ‖y j - z j‖ := by
        calc ‖w - z j‖ = ‖(w - y j) + (y j - z j)‖ := by ring_nf
          _ ≤ ‖w - y j‖ + ‖y j - z j‖ := norm_add_le _ _
      have h2 : ‖y j - z j‖ ≤ ‖y - z‖ := norm_le_pi_norm (y - z) j
      linarith
    rw [hc1]; ring
  obtain ⟨hF2_diff, hF2⟩ := fiberPot_dbarCoord_eq_zero R hR j hv2_cd hδpos hvan
  -- assemble
  rw [hFsplit, Work.CR.Flat.Polydisc.dbarCoord_add j (fiberPot R j v₁) (fiberPot R j v₂) z
        hF1_diff hF2_diff, hF1, hF2, add_zero]

end Work.NN.Core
