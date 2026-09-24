import Mathlib
import Submission.Commons.Analysis.Fourier.poisson_tsum_eq_tsum_fourier

namespace Commons.Analysis.Fourier

open MeasureTheory
open Filter
open scoped Topology

/-- **Poisson summation for a truncated log-phase sum.**  If `g : ℝ → ℂ`-valued weight is smooth,
compactly supported and vanishes on `(-∞, 1/2]` (so that the phase `x ↦ exp(i t log x)` is smooth on
its support), then

`∑' n : ℤ, g n · e^{i t log n} = ∑' k : ℤ, ∫ x, g x · e^{i (t log x - 2πkx)}`,

i.e. the Poisson transform of the log-phase sum.  Proof: the function `x ↦ g x · exp(i t log x)` is
smooth with compact support, so by
`Commons.Analysis.Calculus.exists_schwartzMap_eq_of_contDiff_hasCompactSupport` it is a Schwartz
function and `Commons.Analysis.Fourier.poisson_tsum_eq_tsum_fourier` applies; then rewrite the
Fourier transform with `Real.fourier_eq'`. -/
theorem poisson_log_phase {g : ℝ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hcs : HasCompactSupport g) (hpos : ∀ x : ℝ, x ≤ 1 / 2 → g x = 0) (t : ℝ) :
    (∑' n : ℤ, (g n : ℂ) * Complex.exp (Complex.I * (((t * Real.log n) : ℝ) : ℂ)))
      = ∑' k : ℤ, ∫ x : ℝ, (g x : ℂ)
          * Complex.exp (Complex.I * (((t * Real.log x - 2 * Real.pi * k * x) : ℝ) : ℂ)) := by
  have hf_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (g x : ℂ) * Complex.exp (Complex.I * (((t * Real.log x) : ℝ) : ℂ))) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge x (1 / 2) with hx | hx
    · -- below `1/2` the weight vanishes on a whole neighbourhood
      have hev : (fun x : ℝ => (g x : ℂ) * Complex.exp (Complex.I * (((t * Real.log x) : ℝ) : ℂ)))
          =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        simp only [hpos y hy.le, Complex.ofReal_zero, zero_mul]
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
    · -- at and above `1/2` the logarithm is smooth (the point is nonzero)
      have hxne : x ≠ 0 := by
        intro h; rw [h] at hx; norm_num at hx
      have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.log x :=
        Real.contDiffAt_log.mpr hxne
      have hcast : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => (g x : ℂ)) x :=
        (Complex.ofRealCLM.contDiff.comp hg).contDiffAt
      have hpsi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ => Complex.exp (Complex.I * (((t * Real.log x) : ℝ) : ℂ))) x := by
        have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => t * Real.log x) x :=
          (contDiffAt_const (c := t)).mul hlog
        have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : ℝ => (((t * Real.log x) : ℝ) : ℂ)) x :=
          (Complex.ofRealCLM.contDiff.contDiffAt).comp x h1
        have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : ℝ => Complex.I * (((t * Real.log x) : ℝ) : ℂ)) x :=
          (contDiffAt_const (c := Complex.I)).mul h2
        exact (Complex.contDiff_exp.contDiffAt).comp x h3
      exact hcast.mul hpsi
  have hf_cs : HasCompactSupport
      (fun x : ℝ => (g x : ℂ) * Complex.exp (Complex.I * (((t * Real.log x) : ℝ) : ℂ))) :=
    HasCompactSupport.mul_right (f := fun x : ℝ => (g x : ℂ))
      (f' := fun x : ℝ => Complex.exp (Complex.I * (((t * Real.log x) : ℝ) : ℂ)))
      (hcs.comp_left Complex.ofReal_zero)
  have key := Commons.Analysis.Fourier.poisson_tsum_eq_tsum_fourier hf_smooth hf_cs
  rw [key]
  apply tsum_congr; intro k
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hexp : Complex.exp ((((-2 : ℝ) * Real.pi * (x * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
        * Complex.exp (Complex.I * (((t * Real.log x) : ℝ) : ℂ))
      = Complex.exp (Complex.I * (((t * Real.log x - 2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc Complex.exp ((((-2 : ℝ) * Real.pi * (x * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
          * ((g x : ℂ) * Complex.exp (Complex.I * (((t * Real.log x) : ℝ) : ℂ)))
      = (g x : ℂ) * (Complex.exp ((((-2 : ℝ) * Real.pi * (x * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
          * Complex.exp (Complex.I * (((t * Real.log x) : ℝ) : ℂ))) := by ring
    _ = (g x : ℂ) * Complex.exp (Complex.I * (((t * Real.log x - 2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ)) := by
        rw [hexp]

end Commons.Analysis.Fourier
