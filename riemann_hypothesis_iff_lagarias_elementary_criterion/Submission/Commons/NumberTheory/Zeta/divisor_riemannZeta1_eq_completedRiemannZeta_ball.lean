import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace Commons.NumberTheory.Zeta

open Complex Filter Metric Set
open scoped Real Topology

noncomputable section

/-- A point of the open ball of radius `4` around `2 + i t` (with `5 ≤ |t|`) is different
from `0`, from `1` and from every `-2 n` (the poles of `Gammaℝ`). -/
private lemma ball4_forbidden {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    z ≠ 0 ∧ z ≠ 1 ∧ ∀ n : ℕ, z ≠ -(2 * (n : ℂ)) := by
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have hz' : ‖z - c‖ < (4 : ℝ) := by simpa [c, dist_eq_norm] using hz
  have hkey : ∀ w : ℂ, w.im = 0 → (4 : ℝ) < ‖w - c‖ := by
    intro w hw
    have him := Complex.abs_im_le_norm (w - c)
    have hre : (w - c).im = -t := by
      simp [c, hw]
    rw [hre, abs_neg] at him
    linarith
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun n hn => ?_⟩
  · rw [h0] at hz'
    have := hkey 0 (by simp)
    linarith
  · rw [h1] at hz'
    have := hkey 1 (by simp)
    linarith
  · rw [hn] at hz'
    have := hkey (-(2 * (n : ℂ))) (by simp)
    linarith

/-- On the open ball of radius `4` around `2 + i t` (with `5 ≤ |t|`) the completed zeta function
factors as `Gammaℝ · ζ`. -/
private lemma completedRiemannZeta_eq_mul_Gammaℝ {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    completedRiemannZeta z = z.Gammaℝ * riemannZeta z := by
  obtain ⟨hz0, _, hzG⟩ := ball4_forbidden ht hz
  have hG : z.Gammaℝ ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    exact hzG n hn
  rw [riemannZeta_def_of_ne_zero hz0, mul_div_cancel₀ _ hG]

/-- On the open ball of radius `4` around `2 + i t` (with `5 ≤ |t|`) the entire completion
`riemannZeta₁ = (s-1)·ζ(s) + O((s-1)²)` of `(s-1) ζ(s)` agrees with `(s-1) ζ(s)`. -/
private lemma riemannZeta₁_eq_mul_sub {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    riemannZeta₁ z = (z - 1) * riemannZeta z := by
  obtain ⟨_, hz1, _⟩ := ball4_forbidden ht hz
  rw [riemannZeta_eq_inv_sub_mul hz1,
    mul_inv_cancel_left₀ (sub_ne_zero.mpr hz1)]

/-- `Gammaℝ` is analytic at every point of the open ball of radius `4` around `2 + i t`
(with `5 ≤ |t|`); indeed the only poles of `Gammaℝ` are the points `-2 n`. -/
private lemma analyticAt_Gammaℝ_of_ball4 {t : ℝ} (ht : 5 ≤ |t|) {u : ℂ}
    (hu : u ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    AnalyticAt ℂ (fun z : ℂ => z.Gammaℝ) u := by
  obtain ⟨_, _, huG⟩ := ball4_forbidden ht hu
  have hG : u.Gammaℝ ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    exact huG n hn
  have h1 : AnalyticAt ℂ (fun z : ℂ => (z.Gammaℝ⁻¹)⁻¹) u := by
    have hinv : Differentiable ℂ (fun z : ℂ => z.Gammaℝ⁻¹) := Complex.differentiable_Gammaℝ_inv
    have hz : ((fun z : ℂ => z.Gammaℝ⁻¹) u) ≠ 0 := by
      simpa using inv_ne_zero hG
    exact (hinv.analyticAt u).inv hz
  refine h1.congr ?_
  filter_upwards with z
  simp

/-- On the open ball of radius `4` around `2 + i t` the meromorphic order of the completed zeta
function coincides with that of `ζ` (`Gammaℝ` is analytic and zero-free there). -/
private lemma meromorphicOrderAt_completedRiemannZeta_eq_riemannZeta {t : ℝ} (ht : 5 ≤ |t|)
    {u : ℂ} (hu : u ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    meromorphicOrderAt completedRiemannZeta u = meromorphicOrderAt riemannZeta u := by
  have hball : Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ) ∈ 𝓝 u :=
    Metric.isOpen_ball.mem_nhds hu
  have hev : completedRiemannZeta =ᶠ[𝓝[≠] u]
      ((fun z : ℂ => z.Gammaℝ) * riemannZeta) := by
    filter_upwards [nhdsWithin_le_nhds hball] with z hz
    simpa [Pi.mul_apply] using completedRiemannZeta_eq_mul_Gammaℝ ht hz
  have hg : AnalyticAt ℂ (fun z : ℂ => z.Gammaℝ) u := analyticAt_Gammaℝ_of_ball4 ht hu
  have hg0 : u.Gammaℝ ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    exact (ball4_forbidden ht hu).2.2 n hn
  calc meromorphicOrderAt completedRiemannZeta u
      = meromorphicOrderAt ((fun z : ℂ => z.Gammaℝ) * riemannZeta) u :=
        meromorphicOrderAt_congr hev
    _ = meromorphicOrderAt riemannZeta u := meromorphicOrderAt_mul_of_ne_zero hg hg0

/-- On the open ball of radius `4` around `2 + i t` the meromorphic order of `riemannZeta₁`
coincides with that of `ζ` (`s - 1` is analytic and non-zero there). -/
private lemma meromorphicOrderAt_riemannZeta₁_eq_riemannZeta {t : ℝ} (ht : 5 ≤ |t|)
    {u : ℂ} (hu : u ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    meromorphicOrderAt riemannZeta₁ u = meromorphicOrderAt riemannZeta u := by
  have hball : Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ) ∈ 𝓝 u :=
    Metric.isOpen_ball.mem_nhds hu
  have hev : riemannZeta₁ =ᶠ[𝓝[≠] u] ((fun z : ℂ => z - 1) * riemannZeta) := by
    filter_upwards [nhdsWithin_le_nhds hball] with z hz
    simpa [Pi.mul_apply] using riemannZeta₁_eq_mul_sub ht hz
  have hg : AnalyticAt ℂ (fun z : ℂ => z - 1) u := by fun_prop
  have hg0 : u - 1 ≠ 0 := sub_ne_zero.mpr (ball4_forbidden ht hu).2.1
  calc meromorphicOrderAt riemannZeta₁ u
      = meromorphicOrderAt ((fun z : ℂ => z - 1) * riemannZeta) u :=
        meromorphicOrderAt_congr hev
    _ = meromorphicOrderAt riemannZeta u := meromorphicOrderAt_mul_of_ne_zero hg hg0

theorem divisor_riemannZeta1_eq_completedRiemannZeta_ball {t R : ℝ} (ht : 5 ≤ |t|)
    (hR : 0 < R) (hR4 : R ≤ 4) {u : ℂ}
    (hu : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2)) :
    MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2)) u =
      MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) u := by
  have hRpos : 0 < R := hR
  have hdist : dist u ((2 : ℂ) + Complex.I * (t : ℂ)) ≤ R / 2 := by
    simpa [Metric.mem_closedBall] using hu
  have huU : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ) := by
    simp only [Metric.mem_closedBall]
    linarith [hRpos]
  have hu4 : u ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ) := by
    simp only [Metric.mem_ball]
    linarith
  have hζ1an : AnalyticOnNhd ℂ riemannZeta₁
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2)) :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hΛan : AnalyticOnNhd ℂ completedRiemannZeta
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) := by
    intro z hz
    have hz4 : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ) := by
      simp only [Metric.mem_ball, Metric.mem_closedBall] at hz ⊢
      linarith
    obtain ⟨hz0, hz1, _⟩ := ball4_forbidden ht hz4
    have hS : ({w : ℂ | w ≠ 0 ∧ w ≠ 1} : Set ℂ) ∈ 𝓝 z :=
      (isOpen_compl_singleton.inter isOpen_compl_singleton).mem_nhds ⟨hz0, hz1⟩
    have hd : DifferentiableOn ℂ completedRiemannZeta {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
      intro w hw
      exact (differentiableAt_completedZeta hw.1 hw.2).differentiableWithinAt
    exact hd.analyticAt hS
  have hord : meromorphicOrderAt riemannZeta₁ u = meromorphicOrderAt completedRiemannZeta u :=
    (meromorphicOrderAt_riemannZeta₁_eq_riemannZeta ht hu4).trans
      (meromorphicOrderAt_completedRiemannZeta_eq_riemannZeta ht hu4).symm
  rw [MeromorphicOn.divisor_apply hζ1an.meromorphicOn hu,
    MeromorphicOn.divisor_apply hΛan.meromorphicOn huU]
  exact congrArg (WithTop.untop₀ (α := ℤ)) hord

end

end Commons.NumberTheory.Zeta