import Mathlib
import Submission.Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_le_harmonic
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_nonpos_of_isLocalMax

open scoped Topology
open Filter

namespace Commons.Analysis.Complex.Harmonic

/-- The Laplacian of the squared distance to a fixed point of the plane: `Δ ‖z - c‖² = 4`.

This is the two-dimensional case of the general identity `Δ ‖z - c‖² = 2 * finrank ℝ E`; it is
used below to build a strictly subharmonic perturbation of a `C²` function. -/
lemma laplacian_norm_sub_sq_complex (c : ℂ) :
    Laplacian.laplacian (fun z : ℂ => ‖z - c‖ ^ 2) = fun _ => 4 := by
  have h1 : ∀ x : ℂ, fderiv ℝ (fun z : ℂ => ‖z - c‖ ^ 2) x = 2 • innerSL ℝ (x - c) := by
    intro x
    have hcomp : HasFDerivAt (fun z : ℂ => ‖z - c‖ ^ 2)
        ((2 • innerSL ℝ (x - c)) ∘SL (ContinuousLinearMap.id ℝ ℂ)) x := by
      refine HasFDerivAt.comp x (f := fun z : ℂ => z - c) (f' := ContinuousLinearMap.id ℝ ℂ)
        (hasStrictFDerivAt_norm_sq (x - c)).hasFDerivAt ?_
      simpa using (hasFDerivAt_id x).sub_const c
    rw [hcomp.fderiv]
    simp
  have hfd1 : fderiv ℝ (fun z : ℂ => ‖z - c‖ ^ 2) = fun x => 2 • innerSL ℝ (x - c) :=
    funext h1
  have h2 : ∀ x : ℂ, fderiv ℝ (fun x : ℂ => 2 • innerSL ℝ (x - c)) x
      = (2 • innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) := by
    intro x
    have hcomp : HasFDerivAt (fun x : ℂ => 2 • innerSL ℝ (x - c))
        (((2 • innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))) ∘SL (ContinuousLinearMap.id ℝ ℂ)) x := by
      refine HasFDerivAt.comp x (f := fun z : ℂ => z - c) (f' := ContinuousLinearMap.id ℝ ℂ)
        (ContinuousLinearMap.hasFDerivAt ((2 • innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)))) ?_
      simpa using (hasFDerivAt_id x).sub_const c
    rw [hcomp.fderiv]
    simp
  have hfd2 : fderiv ℝ (fderiv ℝ (fun z : ℂ => ‖z - c‖ ^ 2))
      = fun _ : ℂ => (2 • innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) := by
    rw [hfd1]
    funext x
    exact h2 x
  have hinner : ∀ a : ℂ, ((2 • innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) a) a = 2 * ‖a‖ ^ 2 := by
    intro a
    rw [smul_apply, smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq]
    simp
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  funext x
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hfd2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hinner, hinner]
  norm_num [Complex.normSq, Complex.norm_I]

/-- **Maximum principle for functions whose Laplacian is nonnegative.**

Let `φ : ℂ → ℝ` be continuous on the closed ball `closedBall c R` (`R > 0`), twice continuously
differentiable on the open ball, with `0 ≤ Δφ` on the open ball, and `φ ≤ 0` on the sphere
`sphere c R`. Then `φ ≤ 0` on the whole closed ball.

The proof is the classical perturbation argument: for `δ > 0` the function
`ψ = φ + δ‖· - c‖²` has `Δψ ≥ 4δ > 0`, so it cannot attain a maximum at an interior point of the
ball (at an interior local maximum the Laplacian is `≤ 0`, see
`Commons.Analysis.Calculus.Laplacian.laplacian_nonpos_of_isLocalMax`). Hence the maximum of `ψ`
over the closed ball is at most `δR²`, i.e. `φ ≤ δ(R² - ‖z - c‖²)`; letting `δ → 0⁺` gives the
claim. -/
theorem max_principle_laplacian_nonneg {c : ℂ} {R : ℝ} (hR : 0 < R) {φ : ℂ → ℝ}
    (hcont : ContinuousOn φ (Metric.closedBall c R))
    (hdiff : ContDiffOn ℝ 2 φ (Metric.ball c R))
    (hlap : ∀ z ∈ Metric.ball c R, 0 ≤ Laplacian.laplacian φ z)
    (hbd : ∀ z ∈ Metric.sphere c R, φ z ≤ 0) :
    ∀ z ∈ Metric.closedBall c R, φ z ≤ 0 := by
  suffices h : ∀ δ : ℝ, 0 < δ → ∀ z ∈ Metric.closedBall c R, φ z ≤ δ * R ^ 2 by
    intro z hz
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hδ : 0 < ε / (R ^ 2 + 1) := by positivity
    have h1 := h (ε / (R ^ 2 + 1)) hδ z hz
    have h2 : ε / (R ^ 2 + 1) * R ^ 2 ≤ ε := by
      rw [div_mul_eq_mul_div]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg R]
    linarith
  intro δ hδ z hz
  let ψ : ℂ → ℝ := fun z => φ z + δ * ‖z - c‖ ^ 2
  have hne : (Metric.closedBall c R).Nonempty :=
    ⟨c, by rw [Metric.mem_closedBall, dist_self]; exact hR.le⟩
  have hψcont : ContinuousOn ψ (Metric.closedBall c R) := by
    have h1c : Continuous (fun z : ℂ => δ * ‖z - c‖ ^ 2) :=
      continuous_const.mul ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2)
    exact hcont.add h1c.continuousOn
  have hkey : ∀ y ∈ Metric.closedBall c R, ψ y ≤ δ * R ^ 2 := by
    intro y hy
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hqB, hqmax⟩ := (isCompact_closedBall c R).exists_isMaxOn hne hψcont
    have hyq : ψ y ≤ ψ q := hqmax hy
    have hq_gt : δ * R ^ 2 < ψ q := lt_of_lt_of_le hlt hyq
    have hnormq : ‖q - c‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hqB
    rcases lt_or_eq_of_le hnormq with hqint | hqeq
    · have hmem : Metric.closedBall c R ∈ 𝓝 q := by
        have hb : Metric.ball c R ∈ 𝓝 q :=
          Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_eq_norm] using hqint)
        exact Filter.mem_of_superset hb Metric.ball_subset_closedBall
      have hlocalmax : IsLocalMax ψ q := by
        filter_upwards [hmem] with w hw
        exact hqmax hw
      have hqball : q ∈ Metric.ball c R := by simpa [Metric.mem_ball, dist_eq_norm] using hqint
      have hgφ : ContDiffAt ℝ 2 φ q := hdiff.contDiffAt (Metric.isOpen_ball.mem_nhds hqball)
      have hgn2 : ContDiffAt ℝ 2 (fun z : ℂ => ‖z - c‖ ^ 2) q :=
        (contDiffAt_id.sub contDiffAt_const).norm_sq ℝ
      have hgn : ContDiffAt ℝ 2 (fun z : ℂ => δ * ‖z - c‖ ^ 2) q :=
        (hgn2.const_smul δ).congr_of_eventuallyEq
          (by filter_upwards with w; simp [smul_eq_mul])
      have hcdψ : ContDiffAt ℝ 2 ψ q := hgφ.add hgn
      have hnonpos :=
        Commons.Analysis.Calculus.Laplacian.laplacian_nonpos_of_isLocalMax hcdψ hlocalmax
      have hpos : 0 < Laplacian.laplacian ψ q := by
        have h1 : Laplacian.laplacian ψ q
            = Laplacian.laplacian φ q
              + Laplacian.laplacian (fun z : ℂ => δ * ‖z - c‖ ^ 2) q :=
          ContDiffAt.laplacian_add hgφ hgn
        have h2 : Laplacian.laplacian (fun z : ℂ => δ * ‖z - c‖ ^ 2) q = δ * 4 := by
          have heq : (fun z : ℂ => δ * ‖z - c‖ ^ 2) = δ • (fun z : ℂ => ‖z - c‖ ^ 2) := by
            funext w
            simp [smul_eq_mul]
          rw [heq, InnerProductSpace.laplacian_smul δ hgn2, laplacian_norm_sub_sq_complex c]
          simp [smul_eq_mul]
        have h3 : 0 ≤ Laplacian.laplacian φ q := hlap q hqball
        rw [h1, h2]
        nlinarith
      linarith
    · have hqsph : q ∈ Metric.sphere c R := by
        rw [Metric.mem_sphere, dist_eq_norm]
        exact hqeq
      have hφq : φ q ≤ 0 := hbd q hqsph
      have hψq : ψ q = φ q + δ * R ^ 2 := by
        change φ q + δ * ‖q - c‖ ^ 2 = φ q + δ * R ^ 2
        rw [hqeq]
      rw [hψq] at hq_gt
      linarith
  have hz' : ψ z ≤ δ * R ^ 2 := hkey z hz
  change φ z + δ * ‖z - c‖ ^ 2 ≤ δ * R ^ 2 at hz'
  have h2 : 0 ≤ δ * ‖z - c‖ ^ 2 := by positivity
  linarith

/-- **Local circle mean-value inequality for functions with nonnegative Laplacian.**

If `Ω ⊆ ℂ` is open, `g : ℂ → ℝ` is twice continuously real-differentiable on `Ω` and
`Δg ≥ 0` on `Ω` (i.e. `g` is subharmonic in the classical `C²` sense), then every point
`p ∈ Ω` has a neighbourhood `ball p ε ⊆ Ω` in which the circle mean-value inequality
`g p ≤ Real.circleAverage g p r` holds for every radius `r > 0` with
`Metric.closedBall p r ⊆ Metric.ball p ε`.

Proof: `g p ≤ Real.circleAverage g p r` is proved for every closed ball `closedBall p r ⊆ Ω`
using the comparison criterion for subharmonic functions
(`circleAverage_ge_of_le_harmonic`), whose hypothesis — that a `C²` function dominating `g` on a
circle dominates it on the ball — is exactly the maximum principle
`max_principle_laplacian_nonneg` applied to `g - h` for a harmonic Dirichlet solution `h`. -/
theorem localSubMeanValue_of_laplacian_nonneg {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℝ}
    (hg : ContDiffOn ℝ 2 g Ω) (hlap : ∀ z ∈ Ω, 0 ≤ Laplacian.laplacian g z) :
    ∀ p ∈ Ω, ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ Ω ∧
      ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Metric.ball p ε →
        g p ≤ Real.circleAverage g p r := by
  have hcmp : ∀ (p : ℂ) (r : ℝ), 0 < r → Metric.closedBall p r ⊆ Ω → ∀ h : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd h (Metric.ball p r) →
      ContinuousOn h (Metric.closedBall p r) →
      (∀ z ∈ Metric.sphere p r, g z ≤ h z) → ∀ z ∈ Metric.ball p r, g z ≤ h z := by
    intro p r hr hball h hharm hhcont hle z hz
    have hballΩ : Metric.ball p r ⊆ Ω := fun y hy => hball (Metric.ball_subset_closedBall hy)
    have hcontφ : ContinuousOn (fun y : ℂ => g y - h y) (Metric.closedBall p r) :=
      (hg.continuousOn.mono hball).sub hhcont
    have hdiffφ : ContDiffOn ℝ 2 (fun y : ℂ => g y - h y) (Metric.ball p r) :=
      (hg.mono hballΩ).sub hharm.contDiffOn
    have hlapφ : ∀ y ∈ Metric.ball p r, 0 ≤ Laplacian.laplacian (fun y : ℂ => g y - h y) y := by
      intro y hy
      have hyΩ : y ∈ Ω := hballΩ hy
      have hgy : ContDiffAt ℝ 2 g y := hg.contDiffAt (hΩ.mem_nhds hyΩ)
      have hhy : ContDiffAt ℝ 2 h y := (hharm y hy).1
      have hsub : Laplacian.laplacian (fun y : ℂ => g y - h y) y
          = Laplacian.laplacian g y - Laplacian.laplacian h y :=
        ContDiffAt.laplacian_sub hgy hhy
      have hh0 : Laplacian.laplacian h y = 0 := ((hharm y hy).2).eq_of_nhds
      rw [hsub, hh0, sub_zero]
      exact hlap y hyΩ
    have hbd : ∀ y ∈ Metric.sphere p r, (fun y : ℂ => g y - h y) y ≤ 0 := by
      intro y hy
      show g y - h y ≤ 0
      have := hle y hy
      linarith
    have hres := max_principle_laplacian_nonneg hr hcontφ hdiffφ hlapφ hbd z
      (Metric.ball_subset_closedBall hz)
    have hres' : g z - h z ≤ 0 := hres
    linarith
  have hMVP : ∀ p ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω →
      g p ≤ Real.circleAverage g p r := by
    intro p hp r hr hball
    exact Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_le_harmonic
      (v := g) hΩ hg.continuousOn hcmp hr hball
  intro p hp
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hΩ p hp
  exact ⟨ε, hεpos, hεsub, fun r hr hcl => hMVP p hp r hr (hcl.trans hεsub)⟩

end Commons.Analysis.Complex.Harmonic
