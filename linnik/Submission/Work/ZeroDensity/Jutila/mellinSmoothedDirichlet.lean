import Mathlib
import Submission.Work.LinnikAreas.Density4.mellin_kernel_exp
import Submission.Work.LinnikAreas.Density4.gamma_vertical_integrable_of_bound
import Submission.Work.LinnikAreas.Density4.SsmTerm_tsum_eq
import Submission.Work.ZeroDensity.Jutila.smoothedDirichletDefs

open MeasureTheory Complex
open scoped Classical BigOperators

noncomputable section

namespace Work.ZeroDensity.Jutila

/-!
# The Mellin representation of an exponentially smoothed Dirichlet sum

This file proves `mellinSmoothedDirichlet`, the analytic content of Jutila's (2.11).  The
`sorry`-free development below builds the identity from its three natural pieces, in the same
shape as the already-proved specialisation `Ssm_eq_line` (Heath-Brown's `c = 1` normalisation):

* `smTermIntegral` — termwise inverse Mellin transform of the exponential kernel
  (`mellin_kernel_exp` at the parameter `c` and `y = n/X`);
* `smTermTsumEq` — the pointwise reassembly `Σ_n (b n·n^{-s}·(n/X)^{-w}Γ(w)) = Γ(w)X^w·Σ_n b n·n^{-(s+w)}`;
* `smTermTsumIntegral` — the Tonelli/Fubini exchange of `Σ_n` and `∫_ℝ`, justified by the absolute
  convergence `Σ_n ‖b n‖ n^{-(Re s+c)} < ∞` and the exponential decay of `Γ` on `Re w = c`.
-/

/-- `t ↦ ‖Γ(c+it)‖` is integrable on `ℝ` for `c > 0` (Stirling-type exponential decay on the
vertical line `Re w = c`). -/
lemma integrable_norm_gamma_vertical (c : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨C, hCpos, hCbd⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay c hc
  refine (Work.LinnikAreas.Density4.gamma_vertical_integrable_of_bound c C hCpos ?_).norm
  intro t
  rw [show c + (t : ℂ) * Complex.I = (c : ℂ) + Complex.I * (t : ℂ) by ring]
  exact hCbd t

/-- `t ↦ SmTerm b X s c n t` is ae-strongly measurable (it is continuous for `n ≥ 1`, and
identically `0` for `n = 0` because `b 0 = 0`). -/
lemma aestronglyMeasurable_SmTerm (b : ℕ → ℂ) (X : ℝ) (s : ℂ) (c : ℝ) (hX : 0 < X)
    (hc : 0 < c) (h0 : b 0 = 0) (n : ℕ) :
    AEStronglyMeasurable (fun t : ℝ => SmTerm b X s c n t) volume := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [SmTerm, h0, zero_mul]
    exact (continuous_const : Continuous fun _ : ℝ => (0 : ℂ)).aestronglyMeasurable
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hb : (((n : ℝ) / X : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (div_pos hnpos hX)
    have hcpow : Continuous
        (fun t : ℝ => (((n : ℝ) / X : ℝ) : ℂ) ^ (-(c + (t : ℂ) * Complex.I))) := by
      have harg : Continuous (fun t : ℝ => -(c + (t : ℂ) * Complex.I)) := by fun_prop
      exact harg.const_cpow (Or.inl hb)
    have hΓc : Continuous (fun t : ℝ => Complex.Gamma (c + (t : ℂ) * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hinner : ContinuousAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) t := by fun_prop
      refine ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I)
        (g := Complex.Gamma) (x := t) ?_ hinner
      refine Complex.continuousAt_Gamma ((c : ℂ) + (t : ℂ) * Complex.I) (fun m hm => ?_)
      have hre : c = -(m : ℝ) := by
        have := congrArg Complex.re hm
        simpa using this
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hmain : Continuous fun t : ℝ => b n * (n : ℂ) ^ (-s) *
        ((((n : ℝ) / X : ℝ) : ℂ) ^ (-(c + (t : ℂ) * Complex.I))
          * Complex.Gamma (c + (t : ℂ) * Complex.I)) :=
      (continuous_const.mul continuous_const).mul (hcpow.mul hΓc)
    simpa only [SmTerm] using hmain.aestronglyMeasurable

/-- **Termwise inverse Mellin transform.**  For `c > 0` and `n ≥ 1` (so that `n/X > 0`),
`(1/2π) ∫_ℝ b n·n^{-s}·((n/X)^{-(c+it)}·Γ(c+it)) dt = b n·n^{-s}·e^{-n/X}`; for `n = 0` both
sides vanish because `b 0 = 0`. -/
lemma smTermIntegral {b : ℕ → ℂ} {X : ℝ} (hX : 0 < X) {s : ℂ} {c : ℝ} (hc : 0 < c)
    (h0 : b 0 = 0) (n : ℕ) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, SmTerm b X s c n t
      = b n * (n : ℂ) ^ (-s) * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [SmTerm, h0]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hy : 0 < (n : ℝ) / X := div_pos hnpos hX
    set A : ℂ := b n * (n : ℂ) ^ (-s) with hA
    have hfun : (fun t : ℝ => SmTerm b X s c n t)
        = fun t : ℝ => A * ((((n : ℝ) / X : ℝ) : ℂ) ^ (-(c + (t : ℂ) * Complex.I))
            * Complex.Gamma (c + (t : ℂ) * Complex.I)) := by
      funext t
      simp only [SmTerm, hA]
    have h1 : ∫ t : ℝ, SmTerm b X s c n t
        = A * ∫ t : ℝ, ((((n : ℝ) / X : ℝ) : ℂ) ^ (-(c + (t : ℂ) * Complex.I))
            * Complex.Gamma (c + (t : ℂ) * Complex.I)) := by
      rw [hfun, integral_const_mul]
    have h2 : (1 / (2 * Real.pi)) * ∫ t : ℝ,
          ((((n : ℝ) / X : ℝ) : ℂ) ^ (-(c + (t : ℂ) * Complex.I))
            * Complex.Gamma (c + (t : ℂ) * Complex.I))
        = ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by
      simpa only [neg_div] using
        Work.LinnikAreas.Density4.mellin_kernel_exp c hc ((n : ℝ) / X) hy
    calc (1 / (2 * Real.pi)) * ∫ t : ℝ, SmTerm b X s c n t
        = (1 / (2 * Real.pi)) * (A * ∫ t : ℝ,
            ((((n : ℝ) / X : ℝ) : ℂ) ^ (-(c + (t : ℂ) * Complex.I))
              * Complex.Gamma (c + (t : ℂ) * Complex.I))) := by rw [h1]
      _ = A * ((1 / (2 * Real.pi)) * ∫ t : ℝ,
            ((((n : ℝ) / X : ℝ) : ℂ) ^ (-(c + (t : ℂ) * Complex.I))
              * Complex.Gamma (c + (t : ℂ) * Complex.I))) := by ring
      _ = A * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by rw [h2]
      _ = b n * (n : ℂ) ^ (-s) * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by rw [hA]

/-- **Reassembly of the integrand sum.**  Pointwise in `t`, with `w = c + t·I`,
`Σ_n b n·n^{-s}·((n/X)^{-w}·Γ(w)) = Γ(w)·X^w·Σ_n b n·n^{-(s+w)}`. -/
lemma smTermTsumEq {b : ℕ → ℂ} {X : ℝ} (hX : 0 < X) {s : ℂ} {c : ℝ}
    (h0 : b 0 = 0) (t : ℝ) :
    (∑' n : ℕ, SmTerm b X s c n t)
      = Complex.Gamma (c + (t : ℂ) * Complex.I) * (X : ℂ) ^ (c + (t : ℂ) * Complex.I)
          * (∑' n : ℕ, b n * (n : ℂ) ^ (-(s + (c + (t : ℂ) * Complex.I)))) := by
  have hpt : ∀ n : ℕ, SmTerm b X s c n t
      = (Complex.Gamma (c + (t : ℂ) * Complex.I) * (X : ℂ) ^ (c + (t : ℂ) * Complex.I))
          * (b n * (n : ℂ) ^ (-(s + (c + (t : ℂ) * Complex.I)))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [SmTerm, h0]
    · have hdiv : ((((n : ℝ) / X : ℝ)) : ℂ) = (n : ℂ) / (X : ℂ) := by
        rw [Complex.ofReal_div, Complex.ofReal_natCast]
      have key := Work.LinnikAreas.Density4.cpow_div_mul_of_pos s (c + (t : ℂ) * Complex.I) hn hX
      calc SmTerm b X s c n t
          = b n * ((n : ℂ) ^ (-s) * ((n : ℂ) / (X : ℂ)) ^ (-(c + (t : ℂ) * Complex.I)))
              * Complex.Gamma (c + (t : ℂ) * Complex.I) := by
            rw [SmTerm, hdiv]; ring
        _ = b n * ((X : ℂ) ^ (c + (t : ℂ) * Complex.I)
              * (n : ℂ) ^ (-(s + (c + (t : ℂ) * Complex.I))))
              * Complex.Gamma (c + (t : ℂ) * Complex.I) := by rw [key]
        _ = (Complex.Gamma (c + (t : ℂ) * Complex.I) * (X : ℂ) ^ (c + (t : ℂ) * Complex.I))
              * (b n * (n : ℂ) ^ (-(s + (c + (t : ℂ) * Complex.I)))) := by ring
  rw [← tsum_mul_left]
  exact tsum_congr hpt

/-- **The absolute-convergence majorant.**  For `X > 0` and `b 0 = 0`,
`‖SmTerm b X s c n t‖ ≤ (X^c·(‖b n‖·n^{-(Re s+c)}))·‖Γ(c+it)‖`. -/
lemma norm_SmTerm_le_rpow (b : ℕ → ℂ) (X : ℝ) (s : ℂ) (c : ℝ) (hX : 0 < X)
    (h0 : b 0 = 0) (n : ℕ) (t : ℝ) :
    ‖SmTerm b X s c n t‖
      ≤ (X ^ c * (‖b n‖ * (n : ℝ) ^ (-(s.re + c)))) * ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [SmTerm, h0]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
    have hkey : (n : ℝ) ^ (-s.re) * ((n : ℝ) / X) ^ (-c)
        = X ^ c * (n : ℝ) ^ (-(s.re + c)) := by
      have h1 : ((n : ℝ) / X) ^ (-c) = (n : ℝ) ^ (-c) * X ^ c := by
        rw [Real.div_rpow hn0.le hX.le (-c), Real.rpow_neg hX.le c, div_eq_mul_inv, inv_inv]
      have h2 : (n : ℝ) ^ (-s.re) * (n : ℝ) ^ (-c) = (n : ℝ) ^ (-(s.re + c)) := by
        rw [← Real.rpow_add hn0, show -s.re + -c = -(s.re + c) by ring]
      calc (n : ℝ) ^ (-s.re) * ((n : ℝ) / X) ^ (-c)
          = (n : ℝ) ^ (-s.re) * ((n : ℝ) ^ (-c) * X ^ c) := by rw [h1]
        _ = X ^ c * ((n : ℝ) ^ (-s.re) * (n : ℝ) ^ (-c)) := by ring
        _ = X ^ c * (n : ℝ) ^ (-(s.re + c)) := by rw [h2]
    rw [SmTerm, norm_mul, norm_mul, norm_mul, hcast,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-s),
      Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hn0 hX) (-(c + (t : ℂ) * Complex.I))]
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero]
    refine le_of_eq ?_
    calc (‖b n‖ * (n : ℝ) ^ (-s.re))
            * (((n : ℝ) / X) ^ (-c) * ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖)
        = ‖b n‖ * ((n : ℝ) ^ (-s.re) * ((n : ℝ) / X) ^ (-c))
            * ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖ := by ring
      _ = ‖b n‖ * (X ^ c * (n : ℝ) ^ (-(s.re + c)))
            * ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖ := by rw [hkey]
      _ = (X ^ c * (‖b n‖ * (n : ℝ) ^ (-(s.re + c))))
            * ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖ := by ring

/-- **Tonelli/Fubini exchange** of `Σ_n` and `∫_ℝ` for the integrands `SmTerm`, justified by the
absolute convergence `Σ_n ‖b n‖ n^{-(Re s+c)} < ∞` together with the exponential decay of `Γ`
along `Re w = c`. -/
lemma smTermTsumIntegral {b : ℕ → ℂ} {X : ℝ} (hX : 0 < X) {s : ℂ} {c : ℝ} (hc : 0 < c)
    (h0 : b 0 = 0) (hsum : Summable (fun n : ℕ => ‖b n‖ * (n : ℝ) ^ (-(s.re + c)))) :
    (∑' n : ℕ, ∫ t : ℝ, SmTerm b X s c n t)
      = ∫ t : ℝ, ∑' n : ℕ, SmTerm b X s c n t := by
  have hΓ : Integrable (fun t : ℝ => ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖) :=
    integrable_norm_gamma_vertical c hc
  have hgsum : Summable (fun n : ℕ => X ^ c * (‖b n‖ * (n : ℝ) ^ (-(s.re + c)))) :=
    hsum.mul_left (X ^ c)
  have hFint : ∀ n : ℕ, Integrable (fun t : ℝ => SmTerm b X s c n t) := by
    intro n
    refine (hΓ.const_mul (X ^ c * (‖b n‖ * (n : ℝ) ^ (-(s.re + c))))).mono'
      (aestronglyMeasurable_SmTerm b X s c hX hc h0 n) ?_
    filter_upwards with t
    exact norm_SmTerm_le_rpow b X s c hX h0 n t
  have hsumint : Summable (fun n : ℕ => ∫ t : ℝ, ‖SmTerm b X s c n t‖) := by
    have hbd : Summable (fun n : ℕ => ∫ t : ℝ,
        (X ^ c * (‖b n‖ * (n : ℝ) ^ (-(s.re + c))))
          * ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖) := by
      have h2 : ∀ n : ℕ, (∫ t : ℝ,
            (X ^ c * (‖b n‖ * (n : ℝ) ^ (-(s.re + c))))
              * ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖)
          = (X ^ c * (‖b n‖ * (n : ℝ) ^ (-(s.re + c))))
              * ∫ t : ℝ, ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖ :=
        fun n => integral_const_mul _ _
      simpa only [h2] using
        hgsum.mul_right (∫ t : ℝ, ‖Complex.Gamma (c + (t : ℂ) * Complex.I)‖)
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _))
      (fun n => ?_) hbd
    refine integral_mono (hFint n).norm
      (hΓ.const_mul (X ^ c * (‖b n‖ * (n : ℝ) ^ (-(s.re + c))))) (fun t => ?_)
    exact norm_SmTerm_le_rpow b X s c hX h0 n t
  exact MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsumint

/-- **Mellin representation of an exponentially smoothed Dirichlet sum** — the analytic content of Jutila's (2.11) in his Lemma 6 (the zero detector of Jutila, *On Linnik's constant*, Math. Scand. 41 (1977), p. 50). For any coefficient sequence `b` with `b 0 = 0`, any `X > 0`, any `c > 0` and any `s : ℂ` for which `Σ_n ‖b n‖ n^{-(Re s + c)}` converges,

`Σ_n b n · n^{-s} · e^{-n/X}  =  (1/2π) ∫_ℝ Γ(c+it) · X^{c+it} · (Σ_n b n · n^{-(s+c+it)}) dt,`

i.e. the exponentially smoothed Dirichlet series is the Mellin transform of the (unsmoothed) Dirichlet series against the `Γ(w) X^w` kernel along the vertical line `Re w = c`.  This is the step that turns a smoothed sum into a contour integral, after which the contour may be shifted (Jutila's contour move to `Re w = -1+δ`).  The exponential-kernel identity `(1/2π)∫_ℝ y^{-(c+it)}Γ(c+it)dt = e^{-y}` (`Work.LinnikAreas.Density4.mellin_kernel_exp`) and the vertical-line integrability of `Γ` (`Work.LinnikAreas.Density4.gamma_vertical_integrable_of_bound`) are already in the workspace, and the *same* identity with `c = 1` is already proved as `Ssm_eq_line` in `Work.LinnikAreas.Density4.Ssm_fixed_bound` (Heath-Brown 1992 §11's normalisation) — this is that identity with an arbitrary `c > 0` and arbitrary coefficients, so it can be obtained by generalising `Ssm_eq_line`.  Being generic in `b`, it does not depend on the exact form of the detector's coefficients. -/
theorem mellinSmoothedDirichlet {b : ℕ → ℂ} {X : ℝ} (hX : 0 < X) {s : ℂ} {c : ℝ} (hc : 0 < c)
    (h0 : b 0 = 0) (hsum : Summable (fun n : ℕ => ‖b n‖ * (n : ℝ) ^ (-(s.re + c)))) :
    (∑' n : ℕ, b n * (n : ℂ) ^ (-s) * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ))
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, Complex.Gamma (c + (t : ℂ) * Complex.I)
          * (X : ℂ) ^ (c + (t : ℂ) * Complex.I)
          * (∑' n : ℕ, b n * (n : ℂ) ^ (-(s + (c + (t : ℂ) * Complex.I)))) := by
  rw [show (∑' n : ℕ, b n * (n : ℂ) ^ (-s) * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ))
      = ∑' n : ℕ, (1 / (2 * Real.pi)) * ∫ t : ℝ, SmTerm b X s c n t from
    tsum_congr fun n => (smTermIntegral hX hc h0 n).symm]
  rw [tsum_mul_left]
  rw [smTermTsumIntegral hX hc h0 hsum]
  congr 1
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun t => smTermTsumEq hX h0 t)

end Work.ZeroDensity.Jutila
