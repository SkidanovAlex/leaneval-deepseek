import Mathlib
import Submission.Lib.Unif2.Work.Potential.harmonic_punctured_disc_fourier_structure
import Submission.Lib.Unif2.Work.Potential.eq_zero_of_forall_moments_eq_zero
import Submission.Lib.Unif2.Work.Potential.log_estimate_defs
import Submission.Lib.Unif2.Work.Potential.harmonic_halfplane_periodic_conjugate
import Submission.Lib.Unif2.Work.Potential.descend_periodic_halfplane
import Submission.Lib.Unif2.Work.Potential.analyticAt_zero_of_re_ge_log
import Submission.Lib.Unif2.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

/-!
# The logarithmic estimate at a puncture

`Work.Potential.punctured_log_estimate`: a positive harmonic function on the punctured disc
`0 < ‖z‖ < ρ` differs from `-c · log ‖z‖` by a bounded quantity near the origin, with `c ≥ 0`.

## Proof

Lift `u` to the half-plane `{ζ : ℂ | ζ.re < log ρ}` by `ζ ↦ u (exp ζ)`.  This lift is harmonic
(local harmonicity is preserved by the analytic map `exp`) and `2πi`-periodic.  The workspace
theorem `Work.Potential.harmonic_halfplane_periodic_conjugate` then produces `γ : ℝ` and a
`2πi`-periodic holomorphic `G` on the half-plane with `(G ζ).re = u (exp ζ) - γ * ζ.re`.  Being
periodic, `G` descends through the universal cover `exp` to a holomorphic `H` on the punctured
disc, and there

  `(H z).re = u z - γ * log ‖z‖`.

Since `u > 0`, the real part of `H` satisfies the one-sided logarithmic bound
`(H z).re ≥ γ * log (1 / ‖z‖)`, i.e. `(H z).re ≥ -(-γ) * log (1 / ‖z‖)`.  The removable
singularity theorem `Work.Potential.analyticAt_zero_of_re_ge_log` then extends `H` across the
origin, so `Re H` is bounded near `0`; the estimate follows with `c = -γ`.  Finally `c ≥ 0`,
because otherwise `u z + c * log ‖z‖ ≥ |c| * log (1 / ‖z‖)` would be unbounded above as `z → 0`
(here `u > 0` is used again).
-/

noncomputable section

open scoped Real
open Complex

namespace Work.Potential

theorem punctured_log_estimate {u : ℂ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt u z)
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → 0 < u z) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ C : ℝ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → |u z + c * Real.log ‖z‖| ≤ C := by
  set L : ℝ := Real.log ρ with hLdef
  have hLexp : Real.exp L = ρ := by rw [hLdef]; exact Real.exp_log hρ
  -- the lift of `u` to the half-plane is harmonic and `2πi`-periodic
  have hU : ∀ ζ : ℂ, ζ.re < L →
      InnerProductSpace.HarmonicAt (fun ζ : ℂ => u (Complex.exp ζ)) ζ := by
    intro ζ hζ
    refine Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
      (Complex.differentiable_exp.analyticAt ζ) ?_
    refine hu _ ?_ ?_
    · rw [Complex.norm_exp]; exact Real.exp_pos _
    · rw [Complex.norm_exp]
      calc Real.exp ζ.re < Real.exp L := Real.exp_lt_exp.mpr hζ
        _ = ρ := hLexp
  have hUper : ∀ ζ : ℂ, ζ.re < L →
      (fun ζ : ℂ => u (Complex.exp ζ)) (ζ + 2 * Real.pi * Complex.I)
        = (fun ζ : ℂ => u (Complex.exp ζ)) ζ := by
    intro ζ _
    show u (Complex.exp (ζ + 2 * Real.pi * Complex.I)) = u (Complex.exp ζ)
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  obtain ⟨γ, G, hGan, hGper, hGre⟩ :=
    harmonic_halfplane_periodic_conjugate (L := L) hU hUper
  -- descend to the punctured disc
  obtain ⟨H, hHan, hHex⟩ := descend_periodic_halfplane hLexp hGan hGper
  have hHre : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → (H z).re = u z - γ * Real.log ‖z‖ := by
    intro z hz0 hzρ
    have hz0' : z ≠ 0 := norm_pos_iff.mp hz0
    have hlog : (Complex.log z).re < L := by
      rw [Complex.log_re, hLdef]
      exact Real.log_lt_log hz0 hzρ
    calc (H z).re = (H (Complex.exp (Complex.log z))).re := by rw [Complex.exp_log hz0']
      _ = (G (Complex.log z)).re := by rw [hHex _ hlog]
      _ = u (Complex.exp (Complex.log z)) - γ * (Complex.log z).re := hGre _ hlog
      _ = u z - γ * Real.log ‖z‖ := by rw [Complex.exp_log hz0', Complex.log_re]
  -- the one-sided logarithmic bound for `Re H`
  have hlo : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → -(-γ) * Real.log (1 / ‖z‖) - 0 ≤ (H z).re := by
    intro z hz0 hzρ
    rw [hHre z hz0 hzρ]
    have h1 : Real.log (1 / ‖z‖) = -Real.log ‖z‖ := by rw [one_div, Real.log_inv]
    have h2 : 0 < u z := hpos z hz0 hzρ
    rw [h1]; ring_nf; linarith
  -- remove the singularity at the origin
  obtain ⟨g, hgan, hgeq⟩ := analyticAt_zero_of_re_ge_log hρ hHan hlo
  have hcont : ContinuousAt (fun z : ℂ => (g z).re) 0 :=
    (Complex.continuous_re.continuousAt).comp (hgan 0 (by simpa using hρ)).continuousAt
  obtain ⟨ε₁, hε₁, hε₁b⟩ := Metric.continuousAt_iff.mp hcont (1 / 2) (by norm_num)
  set C : ℝ := |(g 0).re| + 1 with hCdef
  have hbound : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < min ε₁ ρ →
      |u z + (-γ) * Real.log ‖z‖| ≤ C := by
    intro z hz0 hzε
    have hzρ : ‖z‖ < ρ := lt_of_lt_of_le hzε (min_le_right _ _)
    have hzε₁ : ‖z‖ < ε₁ := lt_of_lt_of_le hzε (min_le_left _ _)
    have hbz : |(g z).re - (g 0).re| < 1 / 2 := by
      have := hε₁b (x := z) (by simpa [dist_eq_norm] using hzε₁)
      simpa [Real.dist_eq] using this
    have hHeq : (H z).re = (g z).re := by rw [hgeq z hz0 hzρ]
    have hbnd : |(g z).re| ≤ C := by
      have h2 : |(g z).re| ≤ |(g 0).re| + |(g z).re - (g 0).re| := by
        have h3 := abs_add_le (g 0).re ((g z).re - (g 0).re)
        rw [add_sub_cancel] at h3
        exact h3
      rw [hCdef]
      linarith
    rw [show u z + -γ * Real.log ‖z‖ = (H z).re from by
      rw [hHre z hz0 hzρ]; ring, hHeq]
    exact hbnd
  -- `c = -γ` is nonnegative
  have hnn : 0 ≤ -γ := by
    by_contra hcon
    push_neg at hcon
    have hγ : 0 < γ := by linarith
    set M : ℝ := |(g 0).re| + 1 with hMdef
    have hMC : M = C := by rw [hMdef, hCdef]
    set t : ℝ := min (min ε₁ ρ / 2) (Real.exp (-((M + 2) / γ))) with htdef
    have htpos : 0 < t := lt_min (by positivity) (Real.exp_pos _)
    have htε : t < min ε₁ ρ := by
      have h1 : min ε₁ ρ / 2 < min ε₁ ρ := by
        have h2 : 0 < min ε₁ ρ := lt_min hε₁ hρ
        linarith
      exact lt_of_le_of_lt (min_le_left _ _) h1
    have htlog : M + 2 ≤ γ * Real.log (1 / t) := by
      have h2 : t ≤ Real.exp (-((M + 2) / γ)) := min_le_right _ _
      have h3 : Real.log t ≤ -((M + 2) / γ) := by
        calc Real.log t ≤ Real.log (Real.exp (-((M + 2) / γ))) := Real.log_le_log htpos h2
          _ = -((M + 2) / γ) := Real.log_exp _
      have h4 : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
      have h5 : (M + 2) / γ ≤ Real.log (1 / t) := by rw [h4]; linarith
      have h6 : γ * ((M + 2) / γ) ≤ γ * Real.log (1 / t) :=
        mul_le_mul_of_nonneg_left h5 hγ.le
      have h7 : γ * ((M + 2) / γ) = M + 2 := by field_simp
      linarith [h6]
    have hz0 : 0 < ‖((t : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]; exact htpos
    have hzε : ‖((t : ℝ) : ℂ)‖ < min ε₁ ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]; exact htε
    have hbd := hbound _ hz0 hzε
    have hlogval : Real.log ‖((t : ℝ) : ℂ)‖ = Real.log t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    rw [hlogval] at hbd
    have huval : 0 < u ((t : ℝ) : ℂ) := hpos _ hz0 (lt_of_lt_of_le hzε (min_le_right _ _))
    have hlow : M + 2 ≤ u ((t : ℝ) : ℂ) + (-γ) * Real.log t := by
      have h6 : (-γ) * Real.log t = γ * Real.log (1 / t) := by
        rw [one_div, Real.log_inv]; ring
      rw [h6]
      linarith [htlog, huval]
    have hbd' : |u ((t : ℝ) : ℂ) + (-γ) * Real.log t| ≤ M := by
      have h := hbd
      rwa [← hMC] at h
    have hMpos : 0 < M := by rw [hMdef]; positivity
    have hposval : 0 < u ((t : ℝ) : ℂ) + (-γ) * Real.log t := by linarith [hlow, hMpos]
    rw [abs_of_pos hposval] at hbd'
    linarith
  exact ⟨-γ, hnn, C, min ε₁ ρ, lt_min hε₁ hρ, min_le_right _ _, hbound⟩

end Work.Potential
