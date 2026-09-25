import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth_neg
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
import Submission.Commons.NumberTheory.Zeta.zeta_lower_re_two
import Submission.Commons.NumberTheory.Zeta.zeta_ball3_divisor_le_log

open Complex Filter Metric Set
open scoped Real Topology BigOperators
noncomputable section

namespace Commons.NumberTheory.Zeta
open scoped Topology

/-- points in the open ball of radius 4 around `c = 2 + it` (with `5 ≤ |t|`)
are not in `{0, 1} ∪ {-(2n)}` -/
lemma center_ball_forbidden {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) 4) :
    z ≠ 0 ∧ z ≠ 1 ∧ ∀ n : ℕ, z ≠ -(2 * (n : ℂ)) := by
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have hz' : ‖z - c‖ < 4 := by simpa [c, dist_eq_norm] using hz
  have hct0 : 4 < ‖(0 : ℂ) - c‖ := by
    have hle : 4 < |t| := by linarith
    have hnorm : |((0 : ℂ) - c).im| ≤ ‖(0 : ℂ) - c‖ := Complex.abs_im_le_norm ((0 : ℂ) - c)
    have hre : ((0 : ℂ) - c).im = -t := by simp [c]
    rw [hre] at hnorm
    rw [abs_neg] at hnorm
    linarith
  have hct1 : 4 < ‖(1 : ℂ) - c‖ := by
    have hle : 4 < |t| := by linarith
    have hnorm : |((1 : ℂ) - c).im| ≤ ‖(1 : ℂ) - c‖ := Complex.abs_im_le_norm ((1 : ℂ) - c)
    have hre : ((1 : ℂ) - c).im = -t := by simp [c]
    rw [hre] at hnorm
    rw [abs_neg] at hnorm
    linarith
  have hctn : ∀ n : ℕ, 4 < ‖(-((2 * (n : ℂ))) : ℂ) - c‖ := by
    intro n
    have hle : 4 < |t| := by linarith
    have hnorm : |((-((2 * (n : ℂ))) : ℂ) - c).im| ≤ ‖(-((2 * (n : ℂ))) : ℂ) - c‖ :=
      Complex.abs_im_le_norm ((-((2 * (n : ℂ))) : ℂ) - c)
    have hre : ((-((2 * (n : ℂ))) : ℂ) - c).im = -t := by simp [c]
    rw [hre] at hnorm
    rw [abs_neg] at hnorm
    linarith
  constructor
  · intro h0
    have : ‖(0 : ℂ) - c‖ < 4 := by simpa [h0] using hz'
    linarith
  constructor
  · intro h1
    have : ‖(1 : ℂ) - c‖ < 4 := by simpa [h1] using hz'
    linarith
  · intro n hn
    have hne : (-((2 * (n : ℂ))) : ℂ) - c = z - c := by
      rw [hn]
    have hx : ‖(-((2 * (n : ℂ))) : ℂ) - c‖ < 4 := by simpa [hne] using hz'
    exact (not_lt_of_ge hx.le) (hctn n)

/-- completed zeta equals `Gammaℝ · zeta` pointwise in the open ball radius 4 around `c` -/
lemma completedRiemannZeta_eq_mul_Gammaℝ_of_ball {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) 4) :
    completedRiemannZeta z = z.Gammaℝ * riemannZeta z := by
  have hz0 : z ≠ 0 := (center_ball_forbidden ht hz).1
  have hze : z.Gammaℝ ≠ 0 := by
    intro hzero
    rcases (Complex.Gammaℝ_eq_zero_iff.mp hzero) with ⟨n, hn⟩
    exact ((center_ball_forbidden ht hz).2.2 n) hn
  have hζ : riemannZeta z = completedRiemannZeta z / z.Gammaℝ :=
    riemannZeta_def_of_ne_zero hz0
  calc
    completedRiemannZeta z = (completedRiemannZeta z / z.Gammaℝ) * z.Gammaℝ := by
      field_simp [hze]
    _ = z.Gammaℝ * riemannZeta z := by
      rw [hζ]
      ring

/-- analyticity of `z ↦ z.Gammaℝ` in the open ball radius 4 around `c` -/
lemma analyticAt_Gammaℝ_of_ball {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) 4) : AnalyticAt ℂ (fun s : ℂ => s.Gammaℝ) z := by
  have hz0 : z ≠ 0 := (center_ball_forbidden ht hz).1
  have hze : z.Gammaℝ ≠ 0 := by
    intro hzero
    rcases (Complex.Gammaℝ_eq_zero_iff.mp hzero) with ⟨n, hn⟩
    exact ((center_ball_forbidden ht hz).2.2 n) hn
  have h1 : AnalyticAt ℂ (fun s : ℂ => (s.Gammaℝ⁻¹)⁻¹) z := by
    have hinv : Differentiable ℂ (fun s : ℂ => s.Gammaℝ⁻¹) := Complex.differentiable_Gammaℝ_inv
    have hinvz : ((fun s : ℂ => s.Gammaℝ⁻¹) z) ≠ 0 := by
      dsimp
      exact inv_ne_zero hze
    exact (hinv.analyticAt z).inv hinvz
  refine h1.congr ?_
  filter_upwards with s
  simp

/-- meromorphic order comparison: order of completed zeta at `z` equals order of zeta -/
lemma meromorphicOrderAt_completedRiemannZeta_eq_riemannZeta {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) 4) :
    meromorphicOrderAt completedRiemannZeta z = meromorphicOrderAt riemannZeta z := by
  have hfun0 : completedRiemannZeta =ᶠ[𝓝 z] (fun s : ℂ => s.Gammaℝ * riemannZeta s) := by
    have hball : Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) 4 ∈ 𝓝 z :=
      Metric.isOpen_ball.mem_nhds hz
    filter_upwards [hball] with x hx
    rw [completedRiemannZeta_eq_mul_Gammaℝ_of_ball ht hx]
  have hfun : completedRiemannZeta =ᶠ[𝓝[≠] z] (fun s : ℂ => s.Gammaℝ * riemannZeta s) :=
    hfun0.filter_mono nhdsWithin_le_nhds
  have hg : AnalyticAt ℂ (fun s : ℂ => s.Gammaℝ) z := analyticAt_Gammaℝ_of_ball ht hz
  have hg' : (fun s : ℂ => s.Gammaℝ) z ≠ 0 := by
    dsimp
    by_contra hzero
    rcases (Complex.Gammaℝ_eq_zero_iff.mp hzero) with ⟨n, hn⟩
    exact ((center_ball_forbidden ht hz).2.2 n) hn
  calc
    meromorphicOrderAt completedRiemannZeta z
        = meromorphicOrderAt (fun s : ℂ => s.Gammaℝ * riemannZeta s) z := by
            exact meromorphicOrderAt_congr hfun
    _ = meromorphicOrderAt riemannZeta z := by
            exact meromorphicOrderAt_mul_of_ne_zero hg hg'

/-- divisor equality on the closed ball radius 3 around `c = 2 + it` -/
lemma divisor_completedRiemannZeta_eq_riemannZeta (t : ℝ) (ht : 5 ≤ |t|) :
    ∀ u : ℂ, (MeromorphicOn.divisor completedRiemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u =
      (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u := by
  intro u
  let U : Set ℂ := Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  by_cases hu : u ∈ U
  · have hΛanU : AnalyticOnNhd ℂ completedRiemannZeta U := by
      intro x hx
      have hx4 : x ∈ Metric.ball c 4 := by
        have hd : dist x c ≤ (3 : ℝ) := by simpa [U, c, Metric.mem_closedBall] using hx
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt hd (by norm_num : (3 : ℝ) < 4)
      have hx0 : x ≠ 0 := (center_ball_forbidden ht hx4).1
      have hx1 : x ≠ 1 := (center_ball_forbidden ht hx4).2.1
      let S : Set ℂ := {z : ℂ | z ≠ 0 ∧ z ≠ 1}
      have hSopen : IsOpen S := by
        dsimp [S]
        exact isOpen_compl_singleton.inter isOpen_compl_singleton
      have hdiff : DifferentiableOn ℂ completedRiemannZeta S := by
        intro y hy
        exact (differentiableAt_completedZeta hy.1 hy.2).differentiableWithinAt
      exact hdiff.analyticAt (hSopen.mem_nhds ⟨hx0, hx1⟩)
    have hζanU : AnalyticOnNhd ℂ riemannZeta U := by
      intro x hx
      have hx4 : x ∈ Metric.ball c 4 := by
        have hd : dist x c ≤ (3 : ℝ) := by simpa [U, c, Metric.mem_closedBall] using hx
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt hd (by norm_num : (3 : ℝ) < 4)
      have hx1 : x ≠ 1 := (center_ball_forbidden ht hx4).2.1
      let S : Set ℂ := {z : ℂ | z ≠ 1}
      have hSopen : IsOpen S := isOpen_compl_singleton
      have hdiff : DifferentiableOn ℂ riemannZeta S := by
        intro y hy
        exact (differentiableAt_riemannZeta hy).differentiableWithinAt
      exact hdiff.analyticAt (hSopen.mem_nhds hx1)
    have hz4 : u ∈ Metric.ball c 4 := by
      have hd : dist u c ≤ (3 : ℝ) := by simpa [U, c, Metric.mem_closedBall] using hu
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt hd (by norm_num : (3 : ℝ) < 4)
    have hord : meromorphicOrderAt completedRiemannZeta u = meromorphicOrderAt riemannZeta u :=
      meromorphicOrderAt_completedRiemannZeta_eq_riemannZeta ht hz4
    rw [MeromorphicOn.divisor_apply hΛanU.meromorphicOn hu, MeromorphicOn.divisor_apply hζanU.meromorphicOn hu]
    exact congrArg (WithTop.untop₀ (α := ℤ)) hord
  · simp [U, hu]


/-- **Local zero count of the completed Riemann zeta function in a disk centred on Re = 2.** -/
theorem riemannZeta_local_zeroCount :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 5 ≤ |t| →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor completedRiemannZeta
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ)) ≤
        c * (Real.log (|t| + 6) + 1) := by
  rcases Commons.NumberTheory.Zeta.zeta_ball3_divisor_le_log with ⟨K, hKpos, hK⟩
  refine ⟨K, hKpos, ?_⟩
  intro t ht
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor completedRiemannZeta
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ))
        = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ)) := by
          apply finsum_congr
          intro u
          exact congrArg (fun z : ℤ => (z : ℝ))
            (divisor_completedRiemannZeta_eq_riemannZeta t ht u)
    _ ≤ K * (Real.log (|t| + 6) + 1) := hK t ht

end Commons.NumberTheory.Zeta
