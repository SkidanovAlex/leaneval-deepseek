import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
import Submission.Work.Potential.periodic_vertical_integral_invariance
import Submission.Work.Potential.harmonic_halfplane_periodic_conjugate
import Submission.Work.Potential.periodic_holomorphic_fourier_coefficient
import Submission.Work.Potential.harmonic_annulus_fourier_structure

/-!
# Fourier structure of a harmonic function on a punctured disc

Let `u : ℂ → ℝ` be harmonic on the punctured disc `0 < ‖z‖ < ρ`.  Passing to the universal cover
`ζ ↦ exp ζ` (the half-plane `{ζ | ζ.re < log ρ}`, which is convex, hence simply connected), `u`
becomes a `2πi`-periodic harmonic function `U` on that half-plane.  Writing `U = Re G₀` and
correcting `G₀` by the drift of the conjugate along the period, we obtain a holomorphic
`2πi`-periodic `G` with `(G ζ).re = u (exp ζ) - γ · ζ.re`.  The Fourier coefficients of `u` along a
circle of radius `r` are then those of `Re G` on the vertical line `Re ζ = log r`; periodicity plus
Cauchy's theorem on a rectangle show that each of them is of the form `2π (A r^k + B r^{-k})`,
and the mean value is affine in `log r`.
-/

namespace Work.Potential

open Complex Set Metric Filter MeasureTheory
open scoped Real Topology Interval

lemma punctured_disc_integral_exp_neg_int_mul_I {k : ℤ} (hk : k ≠ 0) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) = 0 := by
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hc : (-(k : ℂ) * Complex.I) ≠ 0 := by simp [hkc]
  have key : (fun θ : ℝ => Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
      = fun θ : ℝ => Complex.exp ((-(k : ℂ) * Complex.I) * (θ : ℂ)) := by
    funext θ; congr 1; push_cast; ring
  rw [key, integral_exp_mul_complex hc]
  have hnum : Complex.exp ((-(k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ))
      - Complex.exp ((-(k : ℂ) * Complex.I) * ((0 : ℝ) : ℂ)) = 0 := by
    have h1 : Complex.exp ((-(k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have h2 : (-(k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)
          = ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
      rw [h2, Complex.exp_int_mul_two_pi_mul_I]
    have h3 : Complex.exp ((-(k : ℂ) * Complex.I) * ((0 : ℝ) : ℂ)) = 1 := by simp
    rw [h1, h3, sub_self]
  rw [hnum, zero_div]

/-- `Re` commutes with the interval integral. -/
lemma punctured_disc_intervalIntegral_re {a b : ℝ} {f : ℝ → ℂ} (hf : IntervalIntegrable f volume a b) :
    (∫ θ in a..b, (f θ).re) = (∫ θ in a..b, f θ).re := by
  simpa using Complex.reCLM.intervalIntegral_comp_comm hf


/-- Arithmetic for the mean value. -/
private lemma add_two_pi_mul_div_eq (a b : ℝ) :
    a + 2 * Real.pi * b = 2 * Real.pi * (a / (2 * Real.pi) + b) := by
  field_simp

/-- The interval integral of a constant. -/
lemma punctured_disc_intervalIntegral_const {a b c : ℝ} : (∫ _ : ℝ in a..b, c) = (b - a) * c := by
  rw [intervalIntegral.integral_const, smul_eq_mul]

theorem harmonic_punctured_disc_fourier_structure
    {u : ℂ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt u z) :
    (∃ α β : ℝ, ∀ r : ℝ, 0 < r → r < ρ →
        (∫ θ in (0:ℝ)..(2 * Real.pi), u (r * Complex.exp (θ * Complex.I)))
          = 2 * Real.pi * (α + β * Real.log r)) ∧
    (∀ k : ℤ, k ≠ 0 → ∃ A B : ℂ, ∀ r : ℝ, 0 < r → r < ρ →
        (∫ θ in (0:ℝ)..(2 * Real.pi),
            (u (r * Complex.exp (θ * Complex.I)) : ℂ) * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
          = 2 * Real.pi * (A * (r : ℂ) ^ k + B * (r : ℂ) ^ (-k))) := by
  set L : ℝ := Real.log ρ with hLdef
  have hLρ : Real.exp L = ρ := by rw [hLdef]; exact Real.exp_log hρ
  have hlogLt : ∀ r : ℝ, 0 < r → r < ρ → Real.log r < L := by
    intro r hr hrρ; rw [hLdef]; exact Real.log_lt_log hr hrρ
  have hUharm : ∀ ζ : ℂ, ζ.re < L →
      InnerProductSpace.HarmonicAt (fun ζ : ℂ => u (Complex.exp ζ)) ζ := by
    intro ζ hζ
    refine Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic ?_ ?_
    · fun_prop
    · refine hu _ ?_ ?_
      · rw [Complex.norm_exp]; exact Real.exp_pos _
      · rw [Complex.norm_exp]
        have h : Real.exp ζ.re < Real.exp L := Real.exp_lt_exp.mpr hζ
        rwa [hLρ] at h
  have hUper : ∀ ζ : ℂ, ζ.re < L →
      (fun ζ : ℂ => u (Complex.exp ζ)) (ζ + 2 * Real.pi * Complex.I)
        = (fun ζ : ℂ => u (Complex.exp ζ)) ζ := by
    intro ζ hζ
    show u (Complex.exp (ζ + 2 * Real.pi * Complex.I)) = u (Complex.exp ζ)
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  obtain ⟨γ, G, hGana, hGper, hGre⟩ := harmonic_halfplane_periodic_conjugate hUharm hUper
  have hval : ∀ (r θ : ℝ), 0 < r → r < ρ →
      u (r * Complex.exp ((θ : ℂ) * Complex.I))
        = (G ((Real.log r : ℂ) + (θ : ℂ) * Complex.I)).re + γ * Real.log r := by
    intro r θ hr hrρ
    have hζre : ((Real.log r : ℂ) + (θ : ℂ) * Complex.I).re = Real.log r := by simp
    have hexp : Complex.exp ((Real.log r : ℂ) + (θ : ℂ) * Complex.I)
        = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
    have hgr := hGre _ (by rw [hζre]; exact hlogLt r hr hrρ)
    rw [← hexp, hgr, hζre]; ring
  -- continuity helper
  have hGcont : ContinuousOn G {ζ : ℂ | ζ.re < L} := fun z hz =>
    (hGana z hz).continuousAt.continuousWithinAt
  have contOf : ∀ r : ℝ, 0 < r → r < ρ →
      ContinuousOn (fun θ : ℝ => G ((Real.log r : ℂ) + θ * Complex.I)) [[(0:ℝ), 2 * Real.pi]] := by
    intro r hr hrρ
    have hrL : Real.log r < L := hlogLt r hr hrρ
    have hmap : MapsTo (fun θ : ℝ => (Real.log r : ℂ) + θ * Complex.I)
        [[(0:ℝ), 2 * Real.pi]] {ζ : ℂ | ζ.re < L} := by
      intro θ hθ
      simp only [Set.mem_ofPred_eq]
      have h1 : ((Real.log r : ℂ) + θ * Complex.I).re = Real.log r := by simp
      rw [h1]; exact hrL
    have hparam : ContinuousOn (fun θ : ℝ => (Real.log r : ℂ) + θ * Complex.I)
        [[(0:ℝ), 2 * Real.pi]] := by fun_prop
    exact hGcont.comp hparam hmap
  constructor
  · set C : ℂ := ∫ θ in (0:ℝ)..(2 * Real.pi), G ((Real.log (ρ / 2) : ℂ) + θ * Complex.I) with hCdef
    refine ⟨C.re / (2 * Real.pi), γ, ?_⟩
    intro r hr hrρ
    have hrL : Real.log r < L := hlogLt r hr hrρ
    have hh : 0 < ρ / 2 := by linarith
    have hρ2L : Real.log (ρ / 2) < L := hlogLt _ hh (by linarith)
    have hcontG := contOf r hr hrρ
    have hcontGr : ContinuousOn (fun θ : ℝ => (G ((Real.log r : ℂ) + θ * Complex.I)).re)
        [[(0:ℝ), 2 * Real.pi]] := Continuous.comp_continuousOn continuous_re hcontG
    have hintG : IntervalIntegrable (fun θ : ℝ => G ((Real.log r : ℂ) + θ * Complex.I))
        volume (0:ℝ) (2 * Real.pi) := hcontG.intervalIntegrable
    have hintGr : IntervalIntegrable (fun θ : ℝ => (G ((Real.log r : ℂ) + θ * Complex.I)).re)
        volume (0:ℝ) (2 * Real.pi) := hcontGr.intervalIntegrable
    have hintc : IntervalIntegrable (fun _ : ℝ => γ * Real.log r) volume (0:ℝ) (2 * Real.pi) :=
      continuous_const.intervalIntegrable _ _
    have h1 : (∫ θ in (0:ℝ)..(2 * Real.pi), u (r * Complex.exp (θ * Complex.I)))
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
            ((G ((Real.log r : ℂ) + θ * Complex.I)).re + γ * Real.log r) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact hval r θ hr hrρ
    have hadd : (∫ θ in (0:ℝ)..(2 * Real.pi),
            ((G ((Real.log r : ℂ) + θ * Complex.I)).re + γ * Real.log r))
        = (∫ θ in (0:ℝ)..(2 * Real.pi), (G ((Real.log r : ℂ) + θ * Complex.I)).re)
          + ∫ _ : ℝ in (0:ℝ)..(2 * Real.pi), γ * Real.log r :=
      intervalIntegral.integral_add hintGr hintc
    have hmain : (∫ θ in (0:ℝ)..(2 * Real.pi), u (r * Complex.exp (θ * Complex.I)))
        = C.re + 2 * Real.pi * (γ * Real.log r) := by
      rw [h1, hadd, punctured_disc_intervalIntegral_re hintG,
        periodic_vertical_integral_invariance hGana hGper hr hrL hh hρ2L, ← hCdef,
        punctured_disc_intervalIntegral_const, sub_zero]
    rw [hmain, add_two_pi_mul_div_eq]
  · intro k hk
    obtain ⟨A, B, hAB⟩ := periodic_holomorphic_fourier_coefficient hGana hGper hk
    refine ⟨A, B, ?_⟩
    intro r hr hrρ
    have hrL : Real.log r < L := hlogLt r hr hrρ
    have hcontG := contOf r hr hrρ
    have hcontGr : ContinuousOn (fun θ : ℝ => (G ((Real.log r : ℂ) + θ * Complex.I)).re)
        [[(0:ℝ), 2 * Real.pi]] := Continuous.comp_continuousOn continuous_re hcontG
    have he : ContinuousOn (fun θ : ℝ => Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
        [[(0:ℝ), 2 * Real.pi]] := by fun_prop
    have hf : ContinuousOn (fun θ : ℝ => ((G ((Real.log r : ℂ) + θ * Complex.I)).re : ℂ)
              * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) [[(0:ℝ), 2 * Real.pi]] :=
      ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hcontGr) he
    have hgc : ContinuousOn (fun θ : ℝ => ((γ : ℂ) * (Real.log r : ℂ))
              * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) [[(0:ℝ), 2 * Real.pi]] :=
      ContinuousOn.mul continuousOn_const he
    have h1 : (∫ θ in (0:ℝ)..(2 * Real.pi),
          (u (r * Complex.exp (θ * Complex.I)) : ℂ)
            * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
            (((G ((Real.log r : ℂ) + θ * Complex.I)).re : ℂ)
              * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))
            + ((γ : ℂ) * (Real.log r : ℂ))
              * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      show (u (r * Complex.exp ((θ : ℂ) * Complex.I)) : ℂ)
            * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))
          = ((G ((Real.log r : ℂ) + (θ : ℂ) * Complex.I)).re : ℂ)
              * Complex.exp (-(((k : ℝ) * (θ : ℝ) : ℂ) * Complex.I))
            + ((γ : ℂ) * (Real.log r : ℂ))
              * Complex.exp (-(((k : ℝ) * (θ : ℝ) : ℂ) * Complex.I))
      rw [hval r θ hr hrρ]
      push_cast
      ring
    have hadd : (∫ θ in (0:ℝ)..(2 * Real.pi),
            (((G ((Real.log r : ℂ) + θ * Complex.I)).re : ℂ)
              * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))
            + ((γ : ℂ) * (Real.log r : ℂ))
              * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))))
        = (∫ θ in (0:ℝ)..(2 * Real.pi),
              ((G ((Real.log r : ℂ) + θ * Complex.I)).re : ℂ)
              * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
          + ∫ θ in (0:ℝ)..(2 * Real.pi),
              ((γ : ℂ) * (Real.log r : ℂ))
              * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)) :=
      intervalIntegral.integral_add hf.intervalIntegrable hgc.intervalIntegrable
    have hzero : (∫ θ in (0:ℝ)..(2 * Real.pi),
        ((γ : ℂ) * (Real.log r : ℂ))
          * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) = 0 := by
      rw [intervalIntegral.integral_const_mul, punctured_disc_integral_exp_neg_int_mul_I hk, mul_zero]
    rw [h1, hadd, hzero, add_zero, hAB r hr hrL]

end Work.Potential

