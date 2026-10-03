import Mathlib
import Submission.Work.FatouL1.existsNormCotPiLe
import Submission.Work.FatouL1.normDivSinSqLe
import Submission.Work.FatouL1.hasDerivAtCotPiSub
import Submission.Work.FatouL1.hasDerivAtDivSinSq
import Submission.Work.FatouL1.existsNormCosDivSinCubeLe
import Submission.Work.FatouL1.existsLeSinSqOnIcc
import Submission.Work.FatouL1.normSqSinComplex

/-!
# FATOU-L1: the two contour integrals of `cot (π ·)` over a horizontal line have the
claimed complex derivatives

For data `h : ℂ → ℂ` which is `L¹` along the vertical line `Re = c`, and `z` in the open
strip `c < Re z < c + 1`, the cotangent contour integral

  `F z = ∫ y, h (c + y*I) * cot (π (c + y*I - z))`

is complex differentiable at `z` with derivative

  `F' z = ∫ y, h (c + y*I) * (π / sin (π (c + y*I - z))²)`

and the second contour integral satisfies the analogous statement

  `G z = ∫ y, h (c + y*I) * (π / sin (π (c + y*I - z))²)`,
  `G' z = ∫ y, h (c + y*I) * (2π² cos (π (c + y*I - z)) / sin (π (c + y*I - z))³)`.

Both are instances of differentiation under the integral sign
(`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`).  The point of the width-one
strip is that the poles of `z ↦ cot (π (w - z))` (situated at `w - z ∈ ℤ`) never meet the
contour `Re w = c`: for `Re z ∈ (c, c+1)` the argument `w - z` has real part in `(-1, 0)`, an
interval containing no integer.  Hence the kernels `cot (π (· - z))`,
`π / sin (π (· - z))²` and `2π² cos (π (· - z)) / sin (π (· - z))³` are each uniformly bounded
on every closed sub-band of `(-1,0) × ℝ` — see `Work.FatouL1.existsNormCotPiLe`,
`Work.FatouL1.normDivSinSqLe`, `Work.FatouL1.existsNormCosDivSinCubeLe` — so the corresponding
dominating functions are constant multiples of `‖h (c + ·*I)‖`, which is integrable.

No holomorphy of `h` is needed: only the `L¹` bound along the single line `Re = c`.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Work.FatouL1

noncomputable section

/-- On a closed sub-band `{s | p ≤ Re s ≤ q}` of the band `(-1,0) × ℝ`, the square modulus of
`sin (π s)` is bounded below by a positive constant. -/
private lemma exists_normSin_sq_lower {p q : ℝ} (hp : -1 < p) (hq : q < 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ s : ℂ, s.re ∈ Set.Icc p q → m ≤ ‖Complex.sin (Real.pi * s)‖ ^ 2 := by
  obtain ⟨m, hm0, _hm1, hm⟩ := existsLeSinSqOnIcc hp hq
  refine ⟨m, hm0, fun s hs => ?_⟩
  rw [normSqSinComplex]
  have hre : (Real.pi * s).re = Real.pi * s.re := by simp [Complex.mul_re]
  rw [hre]
  have := hm s.re hs
  nlinarith [sq_nonneg (Real.sinh ((Real.pi * s).im))]

/-- **First derivative.**  Under the `L¹` bound of `h` on the line `Re = c`, the contour
integral `w ↦ ∫ y, h (c + y*I) * cot (π (c + y*I - w))` is differentiable at every `z₀` of the
strip `c < Re < c + 1`, with the derivative obtained by differentiating the kernel. -/
private lemma cotLine_hasDerivAt {c : ℝ} {h : ℂ → ℂ} {z₀ : ℂ}
    (hline_int : MeasureTheory.Integrable (fun y : ℝ => h ((c : ℂ) + y * Complex.I)))
    (hz₀c : c < z₀.re) (hz₀1 : z₀.re < c + 1) :
    HasDerivAt (fun w : ℂ => ∫ y : ℝ, h ((c : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + y * Complex.I - w)))
      (∫ y : ℝ, h ((c : ℂ) + y * Complex.I) *
        ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + y * Complex.I - z₀))) ^ 2)) z₀ := by
  -- the closed sub-band `s` of the strip on which `cot (π (· - z))` is uniformly bounded
  set t₀ : ℝ := z₀.re - c with ht₀
  have ht₀0 : 0 < t₀ := by rw [ht₀]; linarith
  have ht₀1 : t₀ < 1 := by rw [ht₀]; linarith
  set δ : ℝ := min t₀ (1 - t₀) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; exact half_pos (lt_min ht₀0 (by linarith))
  have hδt : δ < t₀ := by rw [hδ]; have := min_le_left t₀ (1 - t₀); nlinarith
  have hδ1t : δ < 1 - t₀ := by rw [hδ]; have := min_le_right t₀ (1 - t₀); nlinarith
  set p : ℝ := δ - 1 with hp
  set q : ℝ := -δ with hq
  have hpp : -1 < p := by rw [hp]; linarith
  have hqq : q < 0 := by rw [hq]; linarith
  set s : Set ℂ := {z : ℂ | c + δ < z.re ∧ z.re < c + 1 - δ} with hs
  have hz₀s : z₀ ∈ s := by rw [hs]; exact ⟨by linarith, by linarith⟩
  have hsmem : s ∈ 𝓝 z₀ := by
    have hρpos : 0 < min (t₀ - δ) (1 - t₀ - δ) := lt_min (by linarith) (by linarith)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds z₀ hρpos) ?_
    intro z hz
    have hdist : ‖z - z₀‖ < min (t₀ - δ) (1 - t₀ - δ) := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
    have habs : |z.re - z₀.re| < min (t₀ - δ) (1 - t₀ - δ) := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      have h2 : (z - z₀).re = z.re - z₀.re := by simp
      rw [h2] at h1
      linarith
    rw [hs]
    constructor
    · have h1 : -(min (t₀ - δ) (1 - t₀ - δ)) < z.re - z₀.re := neg_lt_of_abs_lt habs
      have h2 : min (t₀ - δ) (1 - t₀ - δ) ≤ t₀ - δ := min_le_left _ _
      linarith
    · have h1 : z.re - z₀.re < min (t₀ - δ) (1 - t₀ - δ) := lt_of_abs_lt habs
      have h2 : min (t₀ - δ) (1 - t₀ - δ) ≤ 1 - t₀ - δ := min_le_right _ _
      linarith
  obtain ⟨C₁, hC₁⟩ := existsNormCotPiLe hpp hqq
  obtain ⟨C₂, hC₂0, hC₂⟩ := normDivSinSqLe hpp hqq
  obtain ⟨m₀, hm₀0, hm₀⟩ := exists_normSin_sq_lower hpp hqq
  have hre_eq : ∀ (z : ℂ) (y : ℝ), (((c:ℂ) + y * Complex.I) - z).re = c - z.re := by
    intro z y
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
  have hre_mem : ∀ z ∈ s, ∀ y : ℝ, (((c:ℂ) + y*Complex.I) - z).re ∈ Set.Icc p q := by
    intro z hz y
    rw [hs] at hz
    rw [Set.mem_Icc, hre_eq z y, hp, hq]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hsin_ne : ∀ z ∈ s, ∀ y : ℝ,
      Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)) ≠ 0 := by
    intro z hz y hzero
    have hb := hm₀ _ (hre_mem z hz y)
    rw [hzero] at hb
    simp at hb
    linarith
  have hcotb : ∀ z ∈ s, ∀ y : ℝ,
      ‖Complex.cot (Real.pi * (((c:ℂ) + y*Complex.I) - z))‖ ≤ C₁ :=
    fun z hz y => hC₁ _ (hre_mem z hz y)
  have hkerb : ∀ z ∈ s, ∀ y : ℝ,
      ‖(Real.pi:ℂ) / (Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)))^2‖ ≤ C₂ :=
    fun z hz y => hC₂ _ (hre_mem z hz y)
  have hline_meas : MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => h ((c:ℂ) + y*Complex.I)) volume :=
    hline_int.aestronglyMeasurable
  -- continuity of the two kernels in the contour parameter `y`
  have hker_cont : ∀ z ∈ s,
      Continuous (fun y : ℝ => Complex.cot (Real.pi * (((c:ℂ) + y*Complex.I) - z))) := by
    intro z hz
    have harg : Continuous (fun y : ℝ => Real.pi * (((c:ℂ) + y*Complex.I) - z)) := by fun_prop
    have hne : ∀ y : ℝ, Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)) ≠ 0 :=
      fun y => hsin_ne z hz y
    have hcont := (Complex.continuous_cos.comp harg).div (Complex.continuous_sin.comp harg) hne
    have hfun : (fun y : ℝ => Complex.cot (Real.pi * (((c:ℂ) + y*Complex.I) - z))) =
        (fun y : ℝ => Complex.cos (Real.pi * (((c:ℂ) + y*Complex.I) - z)) /
          Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z))) := by
      funext y; rw [Complex.cot_eq_cos_div_sin]
    rw [hfun]
    exact hcont
  have hkerd_cont : ∀ z ∈ s, Continuous (fun y : ℝ =>
      (Real.pi:ℂ) / (Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)))^2) := by
    intro z hz
    have harg : Continuous (fun y : ℝ => Real.pi * (((c:ℂ) + y*Complex.I) - z)) := by fun_prop
    have hne : ∀ y : ℝ, Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)) ≠ 0 :=
      fun y => hsin_ne z hz y
    have hsin := Complex.continuous_sin.comp harg
    exact continuous_const.div (hsin.pow 2) (fun y => pow_ne_zero 2 (hne y))
  let F : ℂ → ℝ → ℂ := fun z y =>
    h ((c:ℂ) + y*Complex.I) * Complex.cot (Real.pi * ((c:ℂ) + y*Complex.I - z))
  let F' : ℂ → ℝ → ℂ := fun z y =>
    h ((c:ℂ) + y*Complex.I) * ((Real.pi:ℂ) / (Complex.sin (Real.pi * ((c:ℂ) + y*Complex.I - z)))^2)
  let bound : ℝ → ℝ := fun y => C₂ * ‖h ((c:ℂ) + y*Complex.I)‖
  have hF_int : MeasureTheory.Integrable (F z₀) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun y : ℝ => max C₁ 0 * ‖h ((c:ℂ) + y*Complex.I)‖) ?_ ?_ ?_
    · exact hline_int.norm.const_mul (max C₁ 0)
    · exact hline_meas.mul ((hker_cont z₀ hz₀s).aestronglyMeasurable)
    · filter_upwards with y
      have hb := hcotb z₀ hz₀s y
      have hmax : C₁ ≤ max C₁ 0 := le_max_left _ _
      show ‖h ((c:ℂ) + y*Complex.I) * Complex.cot (Real.pi * ((c:ℂ) + y*Complex.I - z₀))‖ ≤
        max C₁ 0 * ‖h ((c:ℂ) + y*Complex.I)‖
      rw [norm_mul]
      calc ‖h ((c:ℂ) + y*Complex.I)‖ *
            ‖Complex.cot (Real.pi * (((c:ℂ) + y*Complex.I) - z₀))‖
          ≤ ‖h ((c:ℂ) + y*Complex.I)‖ * max C₁ 0 :=
            mul_le_mul_of_nonneg_left (le_trans hb hmax) (norm_nonneg _)
        _ = max C₁ 0 * ‖h ((c:ℂ) + y*Complex.I)‖ := by ring
  have hF_meas : ∀ᶠ x in 𝓝 z₀, MeasureTheory.AEStronglyMeasurable (F x) volume := by
    filter_upwards [hsmem] with x hx
    exact hline_meas.mul ((hker_cont x hx).aestronglyMeasurable)
  have hF'_meas : MeasureTheory.AEStronglyMeasurable (F' z₀) volume :=
    hline_meas.mul ((hkerd_cont z₀ hz₀s).aestronglyMeasurable)
  have hbound_int : MeasureTheory.Integrable bound := hline_int.norm.const_mul C₂
  have hbound_le : ∀ᵐ a ∂(volume : Measure ℝ), ∀ x ∈ s, ‖F' x a‖ ≤ bound a := by
    filter_upwards with a x hx
    have hb := hkerb x hx a
    show ‖h ((c:ℂ) + a*Complex.I) *
        ((Real.pi:ℂ) / (Complex.sin (Real.pi * ((c:ℂ) + a*Complex.I - x)))^2)‖ ≤
      C₂ * ‖h ((c:ℂ) + a*Complex.I)‖
    rw [norm_mul]
    calc ‖h ((c:ℂ) + a*Complex.I)‖ *
          ‖(Real.pi:ℂ) / (Complex.sin (Real.pi * (((c:ℂ) + a*Complex.I) - x)))^2‖
        ≤ ‖h ((c:ℂ) + a*Complex.I)‖ * C₂ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = C₂ * ‖h ((c:ℂ) + a*Complex.I)‖ := by ring
  have hdiff : ∀ᵐ a ∂(volume : Measure ℝ), ∀ x ∈ s, HasDerivAt (fun x => F x a) (F' x a) x := by
    filter_upwards with a x hx
    have hsin : Complex.sin (Real.pi * (((c:ℂ) + a*Complex.I) - x)) ≠ 0 := hsin_ne x hx a
    have hd := hasDerivAtCotPiSub (w := (c:ℂ) + a*Complex.I) (z := x) hsin
    show HasDerivAt
      (fun x => h ((c:ℂ) + a*Complex.I) * Complex.cot (Real.pi * ((c:ℂ) + a*Complex.I - x)))
      (h ((c:ℂ) + a*Complex.I) *
        ((Real.pi:ℂ) / (Complex.sin (Real.pi * ((c:ℂ) + a*Complex.I - x)))^2)) x
    exact hd.const_mul (h ((c:ℂ) + a*Complex.I))
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) hsmem hF_meas hF_int hF'_meas hbound_le hbound_int hdiff
  exact hderiv

/-- **Second derivative.**  Under the `L¹` bound of `h` on the line `Re = c`, the contour
integral `w ↦ ∫ y, h (c + y*I) * (π / sin (π (c + y*I - w))²)` is differentiable at every `z₀`
of the strip `c < Re < c + 1`, with the derivative obtained by differentiating the kernel. -/
private lemma divSinSqLine_hasDerivAt {c : ℝ} {h : ℂ → ℂ} {z₀ : ℂ}
    (hline_int : MeasureTheory.Integrable (fun y : ℝ => h ((c : ℂ) + y * Complex.I)))
    (hz₀c : c < z₀.re) (hz₀1 : z₀.re < c + 1) :
    HasDerivAt (fun w : ℂ => ∫ y : ℝ, h ((c : ℂ) + y * Complex.I) *
        ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + y * Complex.I - w))) ^ 2))
      (∫ y : ℝ, h ((c : ℂ) + y * Complex.I) *
        ((2 : ℂ) * (Real.pi : ℂ) ^ 2 *
          Complex.cos (Real.pi * ((c : ℂ) + y * Complex.I - z₀)) /
          (Complex.sin (Real.pi * ((c : ℂ) + y * Complex.I - z₀))) ^ 3)) z₀ := by
  set t₀ : ℝ := z₀.re - c with ht₀
  have ht₀0 : 0 < t₀ := by rw [ht₀]; linarith
  have ht₀1 : t₀ < 1 := by rw [ht₀]; linarith
  set δ : ℝ := min t₀ (1 - t₀) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; exact half_pos (lt_min ht₀0 (by linarith))
  have hδt : δ < t₀ := by rw [hδ]; have := min_le_left t₀ (1 - t₀); nlinarith
  have hδ1t : δ < 1 - t₀ := by rw [hδ]; have := min_le_right t₀ (1 - t₀); nlinarith
  set p : ℝ := δ - 1 with hp
  set q : ℝ := -δ with hq
  have hpp : -1 < p := by rw [hp]; linarith
  have hqq : q < 0 := by rw [hq]; linarith
  set s : Set ℂ := {z : ℂ | c + δ < z.re ∧ z.re < c + 1 - δ} with hs
  have hz₀s : z₀ ∈ s := by rw [hs]; exact ⟨by linarith, by linarith⟩
  have hsmem : s ∈ 𝓝 z₀ := by
    have hρpos : 0 < min (t₀ - δ) (1 - t₀ - δ) := lt_min (by linarith) (by linarith)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds z₀ hρpos) ?_
    intro z hz
    have hdist : ‖z - z₀‖ < min (t₀ - δ) (1 - t₀ - δ) := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
    have habs : |z.re - z₀.re| < min (t₀ - δ) (1 - t₀ - δ) := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      have h2 : (z - z₀).re = z.re - z₀.re := by simp
      rw [h2] at h1
      linarith
    rw [hs]
    constructor
    · have h1 : -(min (t₀ - δ) (1 - t₀ - δ)) < z.re - z₀.re := neg_lt_of_abs_lt habs
      have h2 : min (t₀ - δ) (1 - t₀ - δ) ≤ t₀ - δ := min_le_left _ _
      linarith
    · have h1 : z.re - z₀.re < min (t₀ - δ) (1 - t₀ - δ) := lt_of_abs_lt habs
      have h2 : min (t₀ - δ) (1 - t₀ - δ) ≤ 1 - t₀ - δ := min_le_right _ _
      linarith
  obtain ⟨C₂, hC₂0, hC₂⟩ := normDivSinSqLe hpp hqq
  obtain ⟨C₃, hC₃0, hC₃⟩ := existsNormCosDivSinCubeLe hpp hqq
  obtain ⟨m₀, hm₀0, hm₀⟩ := exists_normSin_sq_lower hpp hqq
  have hre_eq : ∀ (z : ℂ) (y : ℝ), (((c:ℂ) + y * Complex.I) - z).re = c - z.re := by
    intro z y
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
  have hre_mem : ∀ z ∈ s, ∀ y : ℝ, (((c:ℂ) + y*Complex.I) - z).re ∈ Set.Icc p q := by
    intro z hz y
    rw [hs] at hz
    rw [Set.mem_Icc, hre_eq z y, hp, hq]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hsin_ne : ∀ z ∈ s, ∀ y : ℝ,
      Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)) ≠ 0 := by
    intro z hz y hzero
    have hb := hm₀ _ (hre_mem z hz y)
    rw [hzero] at hb
    simp at hb
    linarith
  have hkerb : ∀ z ∈ s, ∀ y : ℝ,
      ‖(Real.pi:ℂ) / (Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)))^2‖ ≤ C₂ :=
    fun z hz y => hC₂ _ (hre_mem z hz y)
  have hker2b : ∀ z ∈ s, ∀ y : ℝ,
      ‖(2:ℂ) * (Real.pi:ℂ)^2 * Complex.cos (Real.pi * (((c:ℂ) + y*Complex.I) - z)) /
        (Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)))^3‖ ≤ C₃ :=
    fun z hz y => hC₃ _ (hre_mem z hz y)
  have hline_meas : MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => h ((c:ℂ) + y*Complex.I)) volume :=
    hline_int.aestronglyMeasurable
  have hkerd_cont : ∀ z ∈ s, Continuous (fun y : ℝ =>
      (Real.pi:ℂ) / (Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)))^2) := by
    intro z hz
    have harg : Continuous (fun y : ℝ => Real.pi * (((c:ℂ) + y*Complex.I) - z)) := by fun_prop
    have hne : ∀ y : ℝ, Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)) ≠ 0 :=
      fun y => hsin_ne z hz y
    have hsin := Complex.continuous_sin.comp harg
    exact continuous_const.div (hsin.pow 2) (fun y => pow_ne_zero 2 (hne y))
  have hker2_cont : ∀ z ∈ s, Continuous (fun y : ℝ =>
      (2:ℂ) * (Real.pi:ℂ)^2 * Complex.cos (Real.pi * (((c:ℂ) + y*Complex.I) - z)) /
        (Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)))^3) := by
    intro z hz
    have harg : Continuous (fun y : ℝ => Real.pi * (((c:ℂ) + y*Complex.I) - z)) := by fun_prop
    have hne : ∀ y : ℝ, Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z)) ≠ 0 :=
      fun y => hsin_ne z hz y
    have hnum : Continuous (fun y : ℝ => (2:ℂ) * (Real.pi:ℂ)^2 *
        Complex.cos (Real.pi * (((c:ℂ) + y*Complex.I) - z))) :=
      continuous_const.mul (Complex.continuous_cos.comp harg)
    exact hnum.div ((Complex.continuous_sin.comp harg).pow 3) (fun y => pow_ne_zero 3 (hne y))
  let F : ℂ → ℝ → ℂ := fun z y =>
    h ((c:ℂ) + y*Complex.I) * ((Real.pi:ℂ) / (Complex.sin (Real.pi * ((c:ℂ) + y*Complex.I - z)))^2)
  let F' : ℂ → ℝ → ℂ := fun z y =>
    h ((c:ℂ) + y*Complex.I) * ((2:ℂ) * (Real.pi:ℂ)^2 *
      Complex.cos (Real.pi * ((c:ℂ) + y*Complex.I - z)) /
      (Complex.sin (Real.pi * ((c:ℂ) + y*Complex.I - z)))^3)
  let bound : ℝ → ℝ := fun y => C₃ * ‖h ((c:ℂ) + y*Complex.I)‖
  have hF_int : MeasureTheory.Integrable (F z₀) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun y : ℝ => C₂ * ‖h ((c:ℂ) + y*Complex.I)‖) ?_ ?_ ?_
    · exact hline_int.norm.const_mul C₂
    · exact hline_meas.mul ((hkerd_cont z₀ hz₀s).aestronglyMeasurable)
    · filter_upwards with y
      have hb := hkerb z₀ hz₀s y
      show ‖h ((c:ℂ) + y*Complex.I) *
        ((Real.pi:ℂ) / (Complex.sin (Real.pi * ((c:ℂ) + y*Complex.I - z₀)))^2)‖ ≤
        C₂ * ‖h ((c:ℂ) + y*Complex.I)‖
      rw [norm_mul]
      calc ‖h ((c:ℂ) + y*Complex.I)‖ *
            ‖(Real.pi:ℂ) / (Complex.sin (Real.pi * (((c:ℂ) + y*Complex.I) - z₀)))^2‖
          ≤ ‖h ((c:ℂ) + y*Complex.I)‖ * C₂ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = C₂ * ‖h ((c:ℂ) + y*Complex.I)‖ := by ring
  have hF_meas : ∀ᶠ x in 𝓝 z₀, MeasureTheory.AEStronglyMeasurable (F x) volume := by
    filter_upwards [hsmem] with x hx
    exact hline_meas.mul ((hkerd_cont x hx).aestronglyMeasurable)
  have hF'_meas : MeasureTheory.AEStronglyMeasurable (F' z₀) volume :=
    hline_meas.mul ((hker2_cont z₀ hz₀s).aestronglyMeasurable)
  have hbound_int : MeasureTheory.Integrable bound := hline_int.norm.const_mul C₃
  have hbound_le : ∀ᵐ a ∂(volume : Measure ℝ), ∀ x ∈ s, ‖F' x a‖ ≤ bound a := by
    filter_upwards with a x hx
    have hb := hker2b x hx a
    show ‖h ((c:ℂ) + a*Complex.I) * ((2:ℂ)*(Real.pi:ℂ)^2 *
        Complex.cos (Real.pi * ((c:ℂ) + a*Complex.I - x)) /
        (Complex.sin (Real.pi * ((c:ℂ) + a*Complex.I - x)))^3)‖ ≤
      C₃ * ‖h ((c:ℂ) + a*Complex.I)‖
    rw [norm_mul]
    calc ‖h ((c:ℂ) + a*Complex.I)‖ *
          ‖(2:ℂ)*(Real.pi:ℂ)^2 * Complex.cos (Real.pi * (((c:ℂ) + a*Complex.I) - x)) /
            (Complex.sin (Real.pi * (((c:ℂ) + a*Complex.I) - x)))^3‖
        ≤ ‖h ((c:ℂ) + a*Complex.I)‖ * C₃ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = C₃ * ‖h ((c:ℂ) + a*Complex.I)‖ := by ring
  have hdiff : ∀ᵐ a ∂(volume : Measure ℝ), ∀ x ∈ s, HasDerivAt (fun x => F x a) (F' x a) x := by
    filter_upwards with a x hx
    have hsin : Complex.sin (Real.pi * (((c:ℂ) + a*Complex.I) - x)) ≠ 0 := hsin_ne x hx a
    have hd := hasDerivAtDivSinSq (w := (c:ℂ) + a*Complex.I) (z := x) hsin
    show HasDerivAt
      (fun x => h ((c:ℂ) + a*Complex.I) *
        ((Real.pi:ℂ) / (Complex.sin (Real.pi * ((c:ℂ) + a*Complex.I - x)))^2))
      (h ((c:ℂ) + a*Complex.I) * ((2:ℂ)*(Real.pi:ℂ)^2 *
        Complex.cos (Real.pi * ((c:ℂ) + a*Complex.I - x)) /
        (Complex.sin (Real.pi * ((c:ℂ) + a*Complex.I - x)))^3)) x
    exact hd.const_mul (h ((c:ℂ) + a*Complex.I))
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) hsmem hF_meas hF_int hF'_meas hbound_le hbound_int hdiff
  exact hderiv

theorem cotContourHasDeriv {a b m : ℝ} (hab : a < b) {h : ℂ → ℂ}
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {c : ℝ} (hca : a < c) (hcb : c < b) :
    (∀ z : ℂ, c < z.re → z.re < c + 1 →
      HasDerivAt (fun w : ℂ => ∫ y : ℝ, h ((c : ℂ) + y * Complex.I) *
          Complex.cot (Real.pi * ((c : ℂ) + y * Complex.I - w)))
        (∫ y : ℝ, h ((c : ℂ) + y * Complex.I) *
          ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + y * Complex.I - z))) ^ 2)) z) ∧
    (∀ z : ℂ, c < z.re → z.re < c + 1 →
      HasDerivAt (fun w : ℂ => ∫ y : ℝ, h ((c : ℂ) + y * Complex.I) *
          ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + y * Complex.I - w))) ^ 2))
        (∫ y : ℝ, h ((c : ℂ) + y * Complex.I) *
          ((2 : ℂ) * (Real.pi : ℂ) ^ 2 *
            Complex.cos (Real.pi * ((c : ℂ) + y * Complex.I - z)) /
            (Complex.sin (Real.pi * ((c : ℂ) + y * Complex.I - z))) ^ 3)) z) := by
  have _ := hab
  have _ := hmass
  have hcmem : c ∈ Set.Ioo a b := ⟨hca, hcb⟩
  have hline_int := hint c hcmem
  exact ⟨fun z hz hz1 => cotLine_hasDerivAt hline_int hz hz1,
         fun z hz hz1 => divSinSqLine_hasDerivAt hline_int hz hz1⟩

end

end Work.FatouL1
