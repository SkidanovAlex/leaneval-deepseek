import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.FatouCH.Ends.Basic
import Submission.Work.FatouCH.Ends.geometry
import Submission.Work.FatouCH.Ends.derivBound
import Submission.Work.FatouCH.Ends.endsPsiFacts
import Submission.Work.FatouCH.Ends.endsPsiSmall
import Submission.Work.FatouCH.Ends.endsRayIntegral
import Submission.Work.FatouCH.Ends.endsTailIntegral
import Submission.Work.FatouCH.Ends.endsVerticalLimit

/-!
# The end asymptotics of a Fatou coordinate

This is the core of `Work.FatouCH.fatouEnds`: for a near-translation `F` on `Qreg b₁ b₂` whose tail
`F z - (z + ρ)` is exponentially small on the balls of radius `T/8` around the points of height
`σ T` (`σ = ±1`), the deviation `devFn Φ ρ = Φ - ·/ρ` tends to a limit `c` along the end
`σ Im z → +∞`, uniformly on vertical windows `|Re z - x| ≤ 2`.

The ingredient is the derivative estimate `endsDerivBound`, which bounds `‖d(devFn Φ ρ)‖` by
`psi K κ T = 2K/T² + 2K exp(-κT/8)` on the region of height `T`; this is integrable in `T`:
(i) the increments along the vertical ray `t ↦ x + σ t i` are bounded by `∫ psi ≤ Psi K κ T`
(FTC + `endsTailIntegral`) and `endsVerticalLimit` gives the limit with that quantitative bound;
(ii) the window `|Re - x| ≤ 2` is covered by the mean value inequality along the horizontal segment
at height `T`; (iii) the limits for different centres `x` agree because the horizontal chords
between the rays have length `|x|`, so their difference is at most `|x| · psi K κ T → 0`.
-/

namespace Work.FatouCH.Ends

open Set Metric Complex Filter
open scoped Topology intervalIntegral

noncomputable section

theorem endsCore {b₁ b₂ : Option ℂ} {F Φ : ℂ → ℂ} {ρ : ℂ} {M κ : ℝ} {R₁ C₁ σ Ts : ℝ}
    (hDiff : DiffEst R₁ C₁) (hC₁ : 0 ≤ C₁) (hσ : σ = 1 ∨ σ = -1) (hκ : 0 < κ)
    (hρ : 1 / 2 ≤ ‖ρ‖)
    (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂))
    (hTs1 : 1 ≤ Ts)
    (hsmall : ∀ T : ℝ, Ts ≤ T → |M| * Real.exp (-(7 * κ * T / 8)) ≤ 1 / 4)
    (htailball : ∀ (T : ℝ) (u : ℂ), Ts ≤ T → u.im = σ * T → |u.re| ≤ T / 4 →
      ∀ ζ ∈ Metric.ball u (T / 8), ‖F ζ - (ζ + ρ)‖ ≤ |M| * Real.exp (-(7 * κ * T / 8))) :
    ∃ c : ℂ, ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ MandelDim.Qreg b₁ b₂, Y' < σ * z.im →
      |z.re - x| ≤ 2 → ‖devFn Φ ρ z - c‖ < ε := by
  obtain ⟨Tg, hTgpos, hmarg⟩ := marginsSafe (b₁ := b₁) (b₂ := b₂)
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  set K : ℝ := Kc C₁ M with hKdef
  have hK0 : 0 ≤ K := Kc_nonneg hC₁
  obtain ⟨hPsinonneg, hPsimono, hPsizero⟩ := endsPsiFacts (K := K) (κ := κ) hK0 hκ
  obtain ⟨hpsinonneg, -, hpsizero⟩ := endsPsiSmall (K := K) (κ := κ) hK0 hκ
  have hQopen : IsOpen (MandelDim.Qreg b₁ b₂) := isOpen_Qreg b₁ b₂
  -- ## The global threshold `Tm`
  set Tm : ℝ := max Ts (max (Tg + 1) (16 * R₁ + 1)) with hTmdef
  have hTm1 : 1 ≤ Tm := le_trans hTs1 (le_max_left _ _)
  have hTm_Ts : Ts ≤ Tm := le_max_left _ _
  have hTm_Tg : Tg ≤ Tm := by
    have h : Tg + 1 ≤ Tm := le_trans (le_max_left (Tg + 1) (16 * R₁ + 1))
      (le_max_right Ts (max (Tg + 1) (16 * R₁ + 1)))
    linarith
  have hTm_R : R₁ ≤ Tm / 16 := by
    have h : 16 * R₁ + 1 ≤ Tm := le_trans (le_max_right (Tg + 1) (16 * R₁ + 1))
      (le_max_right Ts (max (Tg + 1) (16 * R₁ + 1)))
    linarith
  -- ## The pointwise derivative bound
  have hbound : ∀ (T : ℝ) (u : ℂ), Tm ≤ T → u.im = σ * T → |u.re| ≤ T / 4 →
      ‖deriv (devFn Φ ρ) u‖ ≤ psi K κ T := by
    intro T u hTm him hre
    have hT1 : 1 ≤ T := le_trans hTm1 hTm
    have hTsT : Ts ≤ T := le_trans hTm_Ts hTm
    have hTpos : 0 < T := by linarith
    have himT : |u.im| = T := by
      rw [him, abs_mul, hσabs, one_mul, abs_of_nonneg (by linarith)]
    have hm := hmarg T u (le_trans hTm_Tg hTm) himT hre
    exact endsDerivBound (b₁ := b₁) (b₂ := b₂) (F := F) (Φ := Φ) (ρ := ρ) (M := M) (κ := κ)
      hDiff hC₁ hNT hΦ hκ hρ hT1 (le_trans hTm_R (by linarith)) (hsmall T hTsT)
      (ballSubsetSafe hTpos hm.1 hm.2) (htailball T u hTsT him hre)
  -- ## Points of the horizontal segment at height `σ T`
  have hseg_point : ∀ (T : ℝ) (p q : ℂ), p.im = σ * T → q.im = σ * T →
      |p.re| ≤ T / 4 → |q.re| ≤ T / 4 →
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, ((1 - θ) • p + θ • q).im = σ * T ∧
        |((1 - θ) • p + θ • q).re| ≤ T / 4 := by
    intro T p q hp hq hpr hqr θ hθ
    have hθ0 : (0 : ℝ) ≤ θ := hθ.1
    have hθ1 : θ ≤ 1 := hθ.2
    constructor
    · rw [Complex.add_im, Complex.smul_im, Complex.smul_im, hp, hq]
      ring
    · rw [Complex.add_re, Complex.smul_re, Complex.smul_re]
      simp only [smul_eq_mul]
      have h1 : |(1 - θ) * p.re + θ * q.re| ≤ (1 - θ) * |p.re| + θ * |q.re| := by
        have h := abs_add_le ((1 - θ) * p.re) (θ * q.re)
        have h1a : |1 - θ| = 1 - θ := abs_of_nonneg (by linarith)
        have h1b : |θ| = θ := abs_of_nonneg hθ0
        rw [abs_mul, abs_mul, h1a, h1b] at h
        exact h
      have h2 : (1 - θ) * |p.re| + θ * |q.re| ≤ T / 4 := by
        have h3 : (1 - θ) * |p.re| ≤ (1 - θ) * (T / 4) := mul_le_mul_of_nonneg_left hpr (by linarith)
        have h4 : θ * |q.re| ≤ θ * (T / 4) := mul_le_mul_of_nonneg_left hqr hθ0
        nlinarith
      linarith
  -- ## The vertical ray
  have hray : ∀ x : ℝ, ∀ T₂ T₁ : ℝ, max Tm (4 * |x| + 8) ≤ T₁ → T₁ ≤ T₂ →
      ‖devFn Φ ρ (x + ((σ * T₂ : ℝ) : ℂ) * Complex.I) -
        devFn Φ ρ (x + ((σ * T₁ : ℝ) : ℂ) * Complex.I)‖ ≤
        2 * K / T₁ + 16 * K / κ * Real.exp (-(κ * T₁ / 8)) := by
    intro x T₂ T₁ hT₁ h12
    have hTmax1 : 1 ≤ max Tm (4 * |x| + 8) := le_trans hTm1 (le_max_left _ _)
    have hTmax0 : 0 < max Tm (4 * |x| + 8) := by linarith
    have hγderiv : ∀ t : ℝ, max Tm (4 * |x| + 8) ≤ t →
        HasDerivAt (fun s : ℝ => x + ((σ * s : ℝ) : ℂ) * Complex.I)
          ((σ : ℂ) * Complex.I) t := by
      intro t _
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h1 : HasDerivAt (fun s : ℝ => ((σ * s : ℝ) : ℂ)) ((σ : ℂ)) t := by
        have := h0.const_mul (σ : ℂ)
        simpa [Complex.ofReal_mul] using this
      have h2 : HasDerivAt (fun s : ℝ => ((σ * s : ℝ) : ℂ) * Complex.I)
          ((σ : ℂ) * Complex.I) t := h1.mul_const Complex.I
      exact h2.const_add (x : ℂ)
    have hσnorm : ‖(σ : ℂ)‖ = 1 := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
      exact hσabs
    have hγnorm : ∀ t : ℝ, max Tm (4 * |x| + 8) ≤ t → ‖(σ : ℂ) * Complex.I‖ = 1 := by
      intro t _
      rw [Complex.norm_mul, Complex.norm_I, mul_one]
      exact hσnorm
    have hpt : ∀ t : ℝ, (x + ((σ * t : ℝ) : ℂ) * Complex.I).im = σ * t ∧
        (x + ((σ * t : ℝ) : ℂ) * Complex.I).re = x := by
      intro t
      constructor
      · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
    have hinQ : ∀ t : ℝ, max Tm (4 * |x| + 8) ≤ t →
        x + ((σ * t : ℝ) : ℂ) * Complex.I ∈ MandelDim.Qreg b₁ b₂ := by
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hTmax0 ht
      have htTm : Tm ≤ t := le_trans (le_max_left _ _) ht
      have ht4 : |x| ≤ t / 4 := by
        have := le_trans (le_max_right _ _) ht
        linarith
      have himT : |(x + ((σ * t : ℝ) : ℂ) * Complex.I).im| = t := by
        rw [(hpt t).1, abs_mul, hσabs, one_mul, abs_of_nonneg (by linarith)]
      have hreT : |(x + ((σ * t : ℝ) : ℂ) * Complex.I).re| ≤ t / 4 := by
        rw [(hpt t).2]; exact ht4
      have hm := hmarg t _ (le_trans hTm_Tg htTm) himT hreT
      have hball := ballSubsetSafe htpos hm.1 hm.2
      have hmem : x + ((σ * t : ℝ) : ℂ) * Complex.I ∈
          Metric.ball (x + ((σ * t : ℝ) : ℂ) * Complex.I) (t / 8) := by
        rw [Metric.mem_ball, dist_self]; linarith
      exact hball hmem
    have hd : ∀ t : ℝ, max Tm (4 * |x| + 8) ≤ t →
        DifferentiableAt ℂ (devFn Φ ρ) (x + ((σ * t : ℝ) : ℂ) * Complex.I) := by
      intro t ht
      exact differentiableAt_devFn (hΦ.1.differentiableAt (hQopen.mem_nhds (hinQ t ht)))
    have hbd : ∀ t : ℝ, max Tm (4 * |x| + 8) ≤ t →
        ‖deriv (devFn Φ ρ) (x + ((σ * t : ℝ) : ℂ) * Complex.I)‖ ≤ psi K κ t := by
      intro t ht
      have htTm : Tm ≤ t := le_trans (le_max_left _ _) ht
      have ht4 : |x| ≤ t / 4 := by
        have := le_trans (le_max_right _ _) ht
        linarith
      exact hbound t _ htTm (hpt t).1 (by rw [(hpt t).2]; exact ht4)
    have hψc : ContinuousOn (fun t : ℝ => psi K κ t) (Set.Ici (max Tm (4 * |x| + 8))) := by
      have hne : ∀ t ∈ Set.Ici (max Tm (4 * |x| + 8)), t ^ 2 ≠ 0 := by
        intro t ht
        have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hTmax0 ht
        positivity
      have h1 : ContinuousOn (fun t : ℝ => 2 * K / t ^ 2) (Set.Ici (max Tm (4 * |x| + 8))) :=
        ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) hne
      have h2 : ContinuousOn (fun t : ℝ => 2 * K * Real.exp (-(κ * t / 8)))
          (Set.Ici (max Tm (4 * |x| + 8))) := by fun_prop
      have h3 : ContinuousOn (fun t : ℝ => 2 * K / t ^ 2 + 2 * K * Real.exp (-(κ * t / 8)))
          (Set.Ici (max Tm (4 * |x| + 8))) := by
        convert h1.add h2 using 1
      simpa [psi] using h3
    have hchain := endsRayIntegral (B := devFn Φ ρ)
      (γ := fun t : ℝ => x + ((σ * t : ℝ) : ℂ) * Complex.I)
      (γ' := fun _ : ℝ => (σ : ℂ) * Complex.I) (ψ := fun t : ℝ => psi K κ t)
      hTmax0 hγderiv continuousOn_const hγnorm hd hψc hbd T₂ T₁ hT₁ h12
    have hint := endsTailIntegral (K := K) (κ := κ) hK0 hκ (lt_of_lt_of_le hTmax0 hT₁) h12
    calc ‖devFn Φ ρ (x + ((σ * T₂ : ℝ) : ℂ) * Complex.I) -
          devFn Φ ρ (x + ((σ * T₁ : ℝ) : ℂ) * Complex.I)‖
        ≤ ∫ t in T₁..T₂, psi K κ t := hchain
      _ ≤ 2 * K / T₁ + 16 * K / κ * Real.exp (-(κ * T₁ / 8)) := hint
  -- ## The limit along each ray
  have hconv : ∀ x T : ℝ, (fun w : ℂ => devFn Φ ρ (x + (σ : ℂ) * (w - x))) (x + (T : ℂ) * Complex.I)
      = devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I) := by
    intro x T
    simp only []
    congr 1
    push_cast
    ring
  have hlim : ∀ x : ℝ, ∃ c : ℂ,
      Tendsto (fun T : ℝ => devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 c) ∧
      ∀ T : ℝ, max Tm (4 * |x| + 8) ≤ T →
        ‖devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I) - c‖ ≤
          2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)) := by
    intro x
    have hTmax1 : 1 ≤ max Tm (4 * |x| + 8) := le_trans hTm1 (le_max_left _ _)
    have hseg : ∀ T₂ T₁ : ℝ, max Tm (4 * |x| + 8) ≤ T₁ → T₁ ≤ T₂ →
        ‖(fun w : ℂ => devFn Φ ρ (x + (σ : ℂ) * (w - x))) (x + (T₂ : ℂ) * Complex.I) -
          (fun w : ℂ => devFn Φ ρ (x + (σ : ℂ) * (w - x))) (x + (T₁ : ℂ) * Complex.I)‖
          ≤ 2 * K / T₁ + 16 * K / κ * Real.exp (-(κ * T₁ / 8)) := by
      intro T₂ T₁ h1 h2
      rw [hconv x T₂, hconv x T₁]
      exact hray x T₂ T₁ h1 h2
    obtain ⟨c, hc1, hc2⟩ := endsVerticalLimit (B := fun w : ℂ => devFn Φ ρ (x + (σ : ℂ) * (w - x)))
      (x := x) (K := K) (κ := κ) (T₀ := max Tm (4 * |x| + 8)) hTmax1 hseg hPsimono hPsizero
    refine ⟨c, ?_, ?_⟩
    · simpa only [hconv x] using hc1
    · intro T hT
      simpa only [hconv x] using hc2 T hT
  -- ## The final assembly
  obtain ⟨c, hc0, hc0b⟩ := hlim 0
  refine ⟨c, ?_⟩
  intro x ε hε
  have htend : Tendsto (fun s : ℝ => (|x| + 2) * psi K κ s + Psi K κ s) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => (|x| + 2) * psi K κ s) atTop (𝓝 ((|x| + 2) * 0)) :=
      hpsizero.const_mul (|x| + 2)
    have h2 : Tendsto (fun s : ℝ => Psi K κ s) atTop (𝓝 0) := hPsizero
    simpa using h1.add h2
  have hPsiu : ∀ s : ℝ, Psi K κ s = 2 * K / s + 16 * K / κ * Real.exp (-(κ * s / 8)) := fun s => rfl
  obtain ⟨Tε, hTε⟩ : ∃ Tε : ℝ, ∀ s : ℝ, Tε ≤ s → (|x| + 2) * psi K κ s + Psi K κ s < ε := by
    have h := htend.eventually (isOpen_Iio.mem_nhds hε)
    rw [eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun s hs => hN s hs⟩
  refine ⟨max (max Tm (4 * |x| + 8)) (max Tε 1), ?_⟩
  intro z hzQ hz hzre
  set T : ℝ := σ * z.im with hTdef
  have hTY : max (max Tm (4 * |x| + 8)) (max Tε 1) < T := hz
  have hTmT : Tm ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_of_lt hTY))
  have h4xT : 4 * |x| + 8 ≤ T :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_of_lt hTY))
  have hTεT : Tε ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_of_lt hTY))
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_of_lt hTY))
  have hTpos : 0 < T := by linarith
  have himz : z.im = σ * T := by
    rw [hTdef]
    have h : σ * (σ * z.im) = (σ * σ) * z.im := by ring
    rw [h, hσ2, one_mul]
  have hzreT : |z.re| ≤ T / 4 := by
    have h1 : |z.re| ≤ |x| + 2 := by
      calc |z.re| = |x + (z.re - x)| := by ring_nf
        _ ≤ |x| + |z.re - x| := abs_add_le _ _
        _ ≤ |x| + 2 := by linarith [hzre]
    have h2 : |x| + 2 ≤ T / 4 := by linarith
    linarith
  have hxT : |x| ≤ T / 4 := by linarith
  have hpt1 : (x + ((σ * T : ℝ) : ℂ) * Complex.I).im = σ * T ∧
      (x + ((σ * T : ℝ) : ℂ) * Complex.I).re = x := by
    constructor
    · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
  have hpt0 : (((σ * T : ℝ) : ℂ) * Complex.I).im = σ * T ∧
      (((σ * T : ℝ) : ℂ) * Complex.I).re = 0 := by
    constructor
    · simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    · simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  -- the horizontal segment from the ray point `x + σ T i` to `z`
  have hseg1 : ‖devFn Φ ρ z - devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * psi K κ T := by
    have hdiff : ∀ u ∈ segment ℝ (x + ((σ * T : ℝ) : ℂ) * Complex.I) z,
        DifferentiableAt ℂ (devFn Φ ρ) u := by
      intro u hu
      rw [segment_eq_image] at hu
      obtain ⟨θ, hθ, rfl⟩ := hu
      obtain ⟨himu, hreu⟩ := hseg_point T _ _ hpt1.1 himz (by rw [hpt1.2]; exact hxT) hzreT θ hθ
      have himT : |((1 - θ) • (x + ((σ * T : ℝ) : ℂ) * Complex.I) + θ • z).im| = T := by
        rw [himu, abs_mul, hσabs, one_mul, abs_of_nonneg (by linarith)]
      have hm := hmarg T _ (le_trans hTm_Tg hTmT) himT hreu
      have hball := ballSubsetSafe hTpos hm.1 hm.2
      have hmem : ((1 - θ) • (x + ((σ * T : ℝ) : ℂ) * Complex.I) + θ • z) ∈
          Metric.ball ((1 - θ) • (x + ((σ * T : ℝ) : ℂ) * Complex.I) + θ • z) (T / 8) := by
        rw [Metric.mem_ball, dist_self]; linarith
      exact differentiableAt_devFn (hΦ.1.differentiableAt (hQopen.mem_nhds (hball hmem)))
    have hbound' : ∀ u ∈ segment ℝ (x + ((σ * T : ℝ) : ℂ) * Complex.I) z,
        ‖deriv (devFn Φ ρ) u‖ ≤ psi K κ T := by
      intro u hu
      rw [segment_eq_image] at hu
      obtain ⟨θ, hθ, rfl⟩ := hu
      obtain ⟨himu, hreu⟩ := hseg_point T _ _ hpt1.1 himz (by rw [hpt1.2]; exact hxT) hzreT θ hθ
      exact hbound T _ hTmT himu hreu
    have hmain := segment_bound (a := x + ((σ * T : ℝ) : ℂ) * Complex.I) (b := z) hdiff hbound'
    have hnorm : ‖z - (x + ((σ * T : ℝ) : ℂ) * Complex.I)‖ ≤ 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im (z - (x + ((σ * T : ℝ) : ℂ) * Complex.I))
      have hre : (z - (x + ((σ * T : ℝ) : ℂ) * Complex.I)).re = z.re - x := by
        rw [Complex.sub_re, hpt1.2]
      have him : (z - (x + ((σ * T : ℝ) : ℂ) * Complex.I)).im = 0 := by
        rw [Complex.sub_im, hpt1.1, himz]; ring
      rw [hre, him] at h
      simp only [abs_zero, add_zero] at h
      have h2 : |z.re - x| ≤ 2 := hzre
      linarith
    calc ‖devFn Φ ρ z - devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I)‖
        ≤ psi K κ T * ‖z - (x + ((σ * T : ℝ) : ℂ) * Complex.I)‖ := hmain
      _ ≤ psi K κ T * 2 := mul_le_mul_of_nonneg_left hnorm (hpsinonneg T hTpos)
      _ = 2 * psi K κ T := by ring
  -- the horizontal chord between the two rays
  have hseg2 : ‖devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I) -
      devFn Φ ρ (((σ * T : ℝ) : ℂ) * Complex.I)‖ ≤ psi K κ T * |x| := by
    have hdiff : ∀ u ∈ segment ℝ (((σ * T : ℝ) : ℂ) * Complex.I)
        (x + ((σ * T : ℝ) : ℂ) * Complex.I), DifferentiableAt ℂ (devFn Φ ρ) u := by
      intro u hu
      rw [segment_eq_image] at hu
      obtain ⟨θ, hθ, rfl⟩ := hu
      obtain ⟨himu, hreu⟩ := hseg_point T _ _ hpt0.1 hpt1.1
        (by rw [hpt0.2]; simp only [abs_zero]; linarith [hTpos])
        (by rw [hpt1.2]; exact hxT) θ hθ
      have himT : |((1 - θ) • (((σ * T : ℝ) : ℂ) * Complex.I) +
          θ • (x + ((σ * T : ℝ) : ℂ) * Complex.I)).im| = T := by
        rw [himu, abs_mul, hσabs, one_mul, abs_of_nonneg (by linarith)]
      have hm := hmarg T _ (le_trans hTm_Tg hTmT) himT hreu
      have hball := ballSubsetSafe hTpos hm.1 hm.2
      have hmem : ((1 - θ) • (((σ * T : ℝ) : ℂ) * Complex.I) +
          θ • (x + ((σ * T : ℝ) : ℂ) * Complex.I)) ∈
          Metric.ball ((1 - θ) • (((σ * T : ℝ) : ℂ) * Complex.I) +
            θ • (x + ((σ * T : ℝ) : ℂ) * Complex.I)) (T / 8) := by
        rw [Metric.mem_ball, dist_self]; linarith
      exact differentiableAt_devFn (hΦ.1.differentiableAt (hQopen.mem_nhds (hball hmem)))
    have hbound' : ∀ u ∈ segment ℝ (((σ * T : ℝ) : ℂ) * Complex.I)
        (x + ((σ * T : ℝ) : ℂ) * Complex.I), ‖deriv (devFn Φ ρ) u‖ ≤ psi K κ T := by
      intro u hu
      rw [segment_eq_image] at hu
      obtain ⟨θ, hθ, rfl⟩ := hu
      obtain ⟨himu, hreu⟩ := hseg_point T _ _ hpt0.1 hpt1.1
        (by rw [hpt0.2]; simp only [abs_zero]; linarith [hTpos])
        (by rw [hpt1.2]; exact hxT) θ hθ
      exact hbound T _ hTmT himu hreu
    have hmain := segment_bound (a := ((σ * T : ℝ) : ℂ) * Complex.I)
      (b := x + ((σ * T : ℝ) : ℂ) * Complex.I) hdiff hbound'
    have hnorm : ‖(x + ((σ * T : ℝ) : ℂ) * Complex.I) - ((σ * T : ℝ) : ℂ) * Complex.I‖ ≤ |x| := by
      have h := Complex.norm_le_abs_re_add_abs_im
        ((x + ((σ * T : ℝ) : ℂ) * Complex.I) - ((σ * T : ℝ) : ℂ) * Complex.I)
      have h1 : ((x + ((σ * T : ℝ) : ℂ) * Complex.I) - ((σ * T : ℝ) : ℂ) * Complex.I) = (x : ℂ) := by
        ring
      rw [h1] at h
      simpa using h
    calc ‖devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I) - devFn Φ ρ (((σ * T : ℝ) : ℂ) * Complex.I)‖
        ≤ psi K κ T *
          ‖(x + ((σ * T : ℝ) : ℂ) * Complex.I) - ((σ * T : ℝ) : ℂ) * Complex.I‖ := hmain
      _ ≤ psi K κ T * |x| := mul_le_mul_of_nonneg_left hnorm (hpsinonneg T hTpos)
  -- the ray bound at the origin
  have hray0 : ‖devFn Φ ρ (((σ * T : ℝ) : ℂ) * Complex.I) - c‖ ≤
      2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)) := by
    have h8 : (4 * |(0 : ℝ)| + 8 : ℝ) ≤ T := by
      have h9 : (0 : ℝ) ≤ |x| := abs_nonneg x
      simp only [abs_zero]
      linarith
    have h := hc0b T (max_le hTmT h8)
    simpa [zero_add] using h
  have hfinal : ‖devFn Φ ρ z - c‖ ≤ (|x| + 2) * psi K κ T + Psi K κ T := by
    have hA : devFn Φ ρ z - devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I) =
        devFn Φ ρ z - devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I) := rfl
    have htri : ‖devFn Φ ρ z - c‖ ≤
        ‖devFn Φ ρ z - devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I)‖ +
          (‖devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I) -
            devFn Φ ρ (((σ * T : ℝ) : ℂ) * Complex.I)‖ +
          ‖devFn Φ ρ (((σ * T : ℝ) : ℂ) * Complex.I) - c‖) := by
      have h1 : devFn Φ ρ z - c =
          (devFn Φ ρ z - devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I)) +
            ((devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I) -
              devFn Φ ρ (((σ * T : ℝ) : ℂ) * Complex.I)) +
              (devFn Φ ρ (((σ * T : ℝ) : ℂ) * Complex.I) - c)) := by ring
      rw [h1]
      exact norm_add_add_le' _ _ _
    calc ‖devFn Φ ρ z - c‖
        ≤ ‖devFn Φ ρ z - devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I)‖ +
          (‖devFn Φ ρ (x + ((σ * T : ℝ) : ℂ) * Complex.I) -
            devFn Φ ρ (((σ * T : ℝ) : ℂ) * Complex.I)‖ +
          ‖devFn Φ ρ (((σ * T : ℝ) : ℂ) * Complex.I) - c‖) := htri
      _ ≤ 2 * psi K κ T + (psi K κ T * |x| +
          (2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)))) :=
          add_le_add hseg1 (add_le_add hseg2 hray0)
      _ = (|x| + 2) * psi K κ T + Psi K κ T := by
          rw [hPsiu T]; ring
  exact lt_of_le_of_lt hfinal (hTε T hTεT)

end

end Work.FatouCH.Ends
