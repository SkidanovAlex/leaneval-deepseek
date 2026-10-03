/-
# FATOU-L1: the Cauchy–Heine solver bound

`Work.FatouL1.hcSolver h z = (I/2) * ∫ y, h (z - 1/2 + y*I) * tanh (π y) dy` is holomorphic on the
shifted strip `(a + 1/2, b + 1/2) × ℝ` and obeys the sharp mass bound
`‖hcSolver h z‖ ≤ (1/2) * ∫⁻ ‖h (z - 1/2 + · I)‖` whenever `h` is holomorphic on the strip
`(a,b) × ℝ` and has a uniform `L¹` mass bound `m` on every vertical line of that strip.

## The proof of holomorphy (the interesting half)

The integrand of `hcSolver` is `h (z - 1/2 + y*I)` against the *bounded* kernel `tanh (π y)`, and
the only control available on `h` is the *line mass* bound: it is false in general that
`y ↦ h (z - 1/2 + y*I)` is dominated by an integrable function uniformly in `z` (take
`h = Σ εₖ exp ((· - i yₖ)²)` with `yₖ → ∞`), so the naive "differentiate under the integral sign"
fails.  The contour-shift route is what works:

* on the very line `Re w = Re z - 1/2` on which `hcSolver` integrates one has
  `cot (π (w - z)) = cot (π (-1/2 + i(y - Im z))) = -I tanh (π (y - Im z))`
  (`Work.FatouL1.cotPiNegHalf`), so `hcSolver h z` equals `-1/2` times the *Cauchy-type* integral
  `∫ h (c + y*I) cot (π (c + y*I - z)) dy` taken on the line `c = Re z - 1/2`
  (`Work.FatouL1.cotContourSelf`);
* that Cauchy-type integral is independent of the line `c ∈ (Re z - 1, Re z)` on which it is taken
  (`Work.FatouL1.cotContourIndep`: push the contour across the rectangle `[c₁,c₂] × [-Y,Y]`,
  Cauchy's theorem; the horizontal contributions are `L¹` in `Y` with mass `≤ C (c₂-c₁) m`, so they
  vanish along a sequence `Yₖ → ∞` — here `Work.FatouL1.existsSeqTendstoZero` is used);
* the resulting integral is a *fixed-contour* Cauchy integral with the bounded holomorphic kernel
  `cot (π (c + y*I - z))` of `z`, dominated by `C ‖h (c + y*I)‖`, hence holomorphic in `z` on the
  band `c < Re z < c + 1` by differentiation under the integral sign
  (`Work.FatouL1.cotContourHolo`).

Fixing `z₀` in the shifted strip and taking `c = Re z₀ - 1/2`, the three facts combine to
`hcSolver h =ᶠ[𝓝 z₀] (fun z => -(1/2) * ∫ h (c + y*I) cot (π (c + y*I - z)) dy)`, a function that is
complex differentiable at `z₀`; since differentiability is local, `hcSolver h` is holomorphic.

The mass bound (second conjunct) is immediate from `‖(I/2) * tanh (π y)‖ ≤ 1/2` and
`‖∫ f‖ ≤ (∫⁻ ‖f‖ₑ).toReal`.
-/
import Mathlib
import Submission.Work.FatouL1.solverKernel
import Submission.Work.FatouL1.cotPiNegHalf
import Submission.Work.FatouL1.existsNormCotPiLe
import Submission.Work.FatouL1.existsSeqTendstoZero
import Submission.Work.FatouL1.cotContourIndep
import Submission.Work.FatouL1.cotContourSelf
import Submission.Work.FatouL1.cotContourHolo

open MeasureTheory
open scoped Topology ENNReal

namespace Work.FatouL1

noncomputable section

/-- **The sharp bound for the Cauchy–Heine/translation solver.** -/
theorem hcSolverBound {a b m : ℝ} (hab : a < b) {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b, ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m) :
    DifferentiableOn ℂ (Work.FatouL1.hcSolver h)
      {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} ∧
    (∀ z : ℂ, a + 1 / 2 < z.re → z.re < b + 1 / 2 →
      ‖Work.FatouL1.hcSolver h z‖ ≤
        (1 / 2) * (∫⁻ y : ℝ, ENNReal.ofReal ‖h (z - 1 / 2 + y * Complex.I)‖).toReal) := by
  constructor
  · -- holomorphy, by the fixed-contour representation
    intro z₀ hz₀
    obtain ⟨hz₀a, hz₀b⟩ := hz₀
    set c : ℝ := z₀.re - 1 / 2 with hc
    have hca : a < c := by rw [hc]; linarith
    have hcb : c < b := by rw [hc]; linarith
    set F : ℂ → ℂ := fun z => ∫ y : ℝ, h ((c : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + y * Complex.I - z)) with hF
    have hFON : DifferentiableOn ℂ F {z : ℂ | c < z.re ∧ z.re < c + 1} := by
      rw [hF]; exact cotContourHolo hab hint hmass hca hcb
    have hz₀mem : z₀ ∈ {z : ℂ | c < z.re ∧ z.re < c + 1} := by
      constructor <;> (rw [hc]; linarith)
    have hopen : IsOpen ({z : ℂ | c < z.re ∧ z.re < c + 1}) :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hFdiff : DifferentiableAt ℂ F z₀ := hFON.differentiableAt (hopen.mem_nhds hz₀mem)
    have hev : Work.FatouL1.hcSolver h =ᶠ[𝓝 z₀] fun z => -(1 / 2) * F z := by
      set δ : ℝ := min (1 / 8) (min ((z₀.re - 1 / 2 - a) / 2) ((b - (z₀.re - 1 / 2)) / 2)) with hδ
      have hδpos : 0 < δ := by
        rw [hδ]
        refine lt_min (by norm_num) (lt_min ?_ ?_) <;> linarith
      filter_upwards [Metric.ball_mem_nhds z₀ hδpos] with z hz
      have hdist : ‖z - z₀‖ < δ := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
      have hzre : |z.re - z₀.re| < δ := by
        have h1 : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
        have h2 : (z - z₀).re = z.re - z₀.re := by simp
        rw [h2] at h1; linarith
      have hzre' : z.re - z₀.re < δ := lt_of_le_of_lt (le_abs_self _) hzre
      have hzre'' : -(δ) < z.re - z₀.re := by
        have := neg_abs_le (z.re - z₀.re); linarith
      have hδ1 : δ ≤ (z₀.re - 1 / 2 - a) / 2 := by
        rw [hδ]; exact min_le_of_right_le (min_le_left _ _)
      have hδ2 : δ ≤ (b - (z₀.re - 1 / 2)) / 2 := by
        rw [hδ]; exact min_le_of_right_le (min_le_right _ _)
      have hδ3 : δ ≤ 1 / 8 := by rw [hδ]; exact min_le_left _ _
      have hzσ : z.re - 1 / 2 ∈ Set.Ioo a b := by
        constructor
        · have hpos : 0 < z₀.re - 1 / 2 - a := by linarith
          linarith
        · have hpos : 0 < b - (z₀.re - 1 / 2) := by linarith
          linarith
      have hB := cotContourSelf (h := h) (z := z) (hint (z.re - 1 / 2) hzσ)
      rcases lt_trichotomy c (z.re - 1 / 2) with hlt | heq | hgt
      · have hA : F z = (∫ y : ℝ, h (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I) *
            Complex.cot (Real.pi * (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I - z))) := by
          rw [hF]
          exact cotContourIndep hab hhol hmass ⟨hca, hcb⟩ hzσ hlt (by linarith) (by linarith)
        rw [hA.trans hB]; ring
      · have hmain : F z = -2 * Work.FatouL1.hcSolver h z := by
          rw [hF, heq]; exact hB
        rw [hmain]; ring
      · have hA : (∫ y : ℝ, h (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I) *
            Complex.cot (Real.pi * (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I - z))) = F z := by
          rw [hF]
          exact cotContourIndep hab hhol hmass hzσ ⟨hca, hcb⟩ hgt (by linarith) (by linarith)
        have hmain : F z = -2 * Work.FatouL1.hcSolver h z := hA.symm.trans hB
        rw [hmain]; ring
    have hHdiff : DifferentiableAt ℂ (fun z => -(1 / 2) * F z) z₀ := hFdiff.const_mul (-(1 / 2))
    exact (hHdiff.congr_of_eventuallyEq hev).differentiableWithinAt
  · -- the mass bound
    intro z hz1 hz2
    have hσmem : z.re - 1 / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    have harg : ∀ y : ℝ, z - 1 / 2 + (y : ℂ) * Complex.I =
        (((z.re - 1 / 2 : ℝ)) : ℂ) + ((y + z.im : ℝ) : ℂ) * Complex.I := by
      intro y
      rw [Complex.ofReal_add]
      apply Complex.ext <;>
        simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring
    have hfun : (fun y : ℝ => ENNReal.ofReal ‖h (z - 1 / 2 + y * Complex.I)‖) =
        fun y : ℝ => ENNReal.ofReal
          ‖h (((z.re - 1 / 2 : ℝ) : ℂ) + ((y + z.im : ℝ) : ℂ) * Complex.I)‖ := by
      funext y; rw [harg y]
    have hline : ∫⁻ y : ℝ, ENNReal.ofReal ‖h (z - 1 / 2 + y * Complex.I)‖ ≤ ENNReal.ofReal m := by
      rw [hfun]
      rw [MeasureTheory.lintegral_add_right_eq_self
        (fun y : ℝ => ENNReal.ofReal ‖h (((z.re - 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖) z.im]
      exact hmass (z.re - 1 / 2) hσmem
    have hfin : (∫⁻ y : ℝ, ENNReal.ofReal ‖h (z - 1 / 2 + y * Complex.I)‖) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hline
    rw [hcSolver]
    calc ‖(Complex.I / 2) * ∫ (y : ℝ), h (z - 1 / 2 + y * Complex.I) * ↑(Real.tanh (Real.pi * y))‖
        = (1 / 2) * ‖∫ (y : ℝ), h (z - 1 / 2 + y * Complex.I) * ↑(Real.tanh (Real.pi * y))‖ := by
          rw [norm_mul]
          norm_num [Complex.norm_I]
      _ ≤ (1 / 2) * (∫⁻ y : ℝ,
            ENNReal.ofReal ‖h (z - 1 / 2 + y * Complex.I) * ↑(Real.tanh (Real.pi * y))‖).toReal := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact MeasureTheory.norm_integral_le_lintegral_norm _
      _ ≤ (1 / 2) * (∫⁻ y : ℝ, ENNReal.ofReal ‖h (z - 1 / 2 + y * Complex.I)‖).toReal := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply ENNReal.toReal_mono hfin
          apply MeasureTheory.lintegral_mono
          intro y
          apply ENNReal.ofReal_le_ofReal
          have h2 : ‖((Real.tanh (Real.pi * y) : ℝ) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact Work.FatouL1.abs_tanh_le_one (Real.pi * y)
          calc ‖h (z - 1 / 2 + y * Complex.I) * ((Real.tanh (Real.pi * y) : ℝ) : ℂ)‖
              = ‖h (z - 1 / 2 + y * Complex.I)‖ * ‖((Real.tanh (Real.pi * y) : ℝ) : ℂ)‖ :=
                norm_mul _ _
            _ ≤ ‖h (z - 1 / 2 + y * Complex.I)‖ * 1 :=
                mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
            _ = ‖h (z - 1 / 2 + y * Complex.I)‖ := mul_one _

end

end Work.FatouL1
