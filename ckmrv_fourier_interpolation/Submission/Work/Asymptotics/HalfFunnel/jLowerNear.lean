/-
# The near-cusp lower bound `‖j τ - j(i t)‖ ≳ e^{2π/t} ‖τ - i/t‖`

For `0 < t ≤ 1` and `τ ∈ ℍ` with `Im τ ≥ 2` in a fixed neighbourhood of the point `i/t` of the
"half funnel", the modular `j`-invariant separates `τ` from the cusp point `i t` (which has the
same `j`-value as `i/t`, since `S • (i/t) = i t` and `j` is `S`-invariant) at least like
`e^{2π/t}` times the Euclidean distance:

`c e^{2π/t} ‖τ - i/t‖ ≤ ‖j τ - j(i t)‖`.

This is the statement `Work.Asymptotics.HalfFunnel.jLowerNear`.

The mathematics is a specialisation of `Work.Asymptotics.CuspDecay.KMinusMiddle.JLowerGeSevenFourths`,
which states that for `s ≥ 7/4`, `τ ∈ 𝒟` with `|Im τ - s| ≤ 1/4`,

`c e^{2πs} dist(τ, {i s - 1, i s, i s + 1}) ≤ ‖j τ - j (i/s)‖`.

Taking `s = 1/t` (so `i/s = i t` is exactly the cusp point of the target and `i s = i/t` is the
centre of the neighbourhood) and `ρ = 1/4`:

* `τ ∈ 𝒟`: `|Re τ| < 1/4` and `Im τ ≥ 2` give the two strip inequalities and both `|τ ∓ 1/2| > 1/2`;
* `7/4 ≤ 1/t`: `Im τ ≥ 2` and `|Im τ - 1/t| ≤ ‖τ - i/t‖ < 1/4` give `1/t > 2 - 1/4 = 7/4`;
* the `min` over the three lattice translates is the distance to the middle point `i/t`, because
  `|Re τ| < 1/4` makes the two other translates `i/t ± 1` strictly farther;
* `‖q (i/t)‖ = e^{-2π/t}`, which is where the exponential factor comes from.

Since the centre `i/t` has imaginary part `1/t ≥ 7/4 > 1`, the "height" of the whole configuration
is at least `3/2`, which is why the `7/4`-version of the cusp estimate (rather than the `2`-version
`Work.Asymptotics.CuspDecay.KMinusMiddle.JLower`) is the right input here.
-/
import Mathlib
import Submission.Work.Kernels.Theorem31
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.jInvariantFun_cusp_second
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atZero
import Submission.Work.Asymptotics.CuspDecay.KMinusMiddle.JLowerGeSevenFourths

namespace Work.Asymptotics.HalfFunnel

open UpperHalfPlane

theorem jLowerNear : ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧
    ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 → ∀ τ : UpperHalfPlane, 2 ≤ τ.im →
      ‖(τ : ℂ) - (t : ℂ)⁻¹ * Complex.I‖ < ρ →
      c * Real.exp (2 * Real.pi / t) * ‖(τ : ℂ) - (t : ℂ)⁻¹ * Complex.I‖ ≤
        ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
  obtain ⟨c, hc, hJ⟩ := Work.Asymptotics.CuspDecay.KMinusMiddle.JLowerGeSevenFourths
  refine ⟨1 / 4, c, by norm_num, hc, ?_⟩
  intro t ht ht1 τ hτim hdist
  -- `s = 1/t` is the height of the centre `i/t` of the neighbourhood
  set s : ℝ := 1 / t with hsdef
  have hspos : 0 < s := by rw [hsdef]; positivity
  have hscoe : (s : ℂ) = (t : ℂ)⁻¹ := by rw [hsdef, one_div, Complex.ofReal_inv]
  have hst : 1 / s = t := by rw [hsdef, one_div_one_div]
  -- the vector from the centre to `τ`
  set u : ℂ := (τ : ℂ) - (s : ℂ) * Complex.I with hudef
  have hu_re : u.re = τ.re := by
    rw [hudef]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, UpperHalfPlane.coe_re]
  have hu_im : u.im = τ.im - s := by
    rw [hudef]
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, UpperHalfPlane.coe_im]
  have hA : ‖(τ : ℂ) - (t : ℂ)⁻¹ * Complex.I‖ = ‖u‖ := by
    rw [hudef, ← hscoe]
  have hdist_u : ‖u‖ < 1 / 4 := by rw [← hA]; exact hdist
  have hre_u : |τ.re| ≤ ‖u‖ := by
    have h := Complex.abs_re_le_norm u
    rwa [hu_re] at h
  have him_u : |τ.im - s| ≤ ‖u‖ := by
    have h := Complex.abs_im_le_norm u
    rwa [hu_im] at h
  have hre_lt : |τ.re| < 1 / 4 := lt_of_le_of_lt hre_u hdist_u
  -- the centre is high enough for the `7/4`-estimate
  have hs74 : 7 / 4 ≤ s := by
    have h1 : τ.im - s ≤ ‖u‖ := (abs_le.mp him_u).2
    linarith
  -- `τ` lies in the fundamental domain `𝒟` of `Γ(2)`
  have hτD : τ ∈ Work.Asymptotics.DomainD := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith [(abs_lt.mp hre_lt).1]
    · linarith [(abs_lt.mp hre_lt).2]
    · have h := Complex.abs_im_le_norm ((τ : ℂ) - (1 / 2 : ℂ))
      have him : (((τ : ℂ) - (1 / 2 : ℂ))).im = τ.im := by simp
      rw [him, abs_of_pos τ.im_pos] at h
      linarith
    · have h := Complex.abs_im_le_norm ((τ : ℂ) + (1 / 2 : ℂ))
      have him : (((τ : ℂ) + (1 / 2 : ℂ))).im = τ.im := by simp
      rw [him, abs_of_pos τ.im_pos] at h
      linarith
  have him : |τ.im - s| ≤ 1 / 4 := le_of_lt (lt_of_le_of_lt him_u hdist_u)
  -- the three distances appearing in `hJ` are `‖u‖`, `‖u - 1‖`, `‖u + 1‖`
  have hcoes : ∀ h : 0 < s, ((Work.Kernels.imagAxis s h : UpperHalfPlane) : ℂ)
      = (s : ℂ) * Complex.I := by
    intro h
    simp [Work.Kernels.imagAxis]
  have h1eq : ∀ h : 0 < s,
      ‖(τ : ℂ) - ((Work.Kernels.imagAxis s h : UpperHalfPlane) : ℂ)‖ = ‖u‖ := by
    intro h
    rw [hcoes h, hudef]
  have h2eq : ∀ h : 0 < s,
      ‖(τ : ℂ) - (((1 : ℝ) +ᵥ (Work.Kernels.imagAxis s h) : UpperHalfPlane) : ℂ)‖
        = ‖u - 1‖ := by
    intro h
    have hv : (((1 : ℝ) +ᵥ (Work.Kernels.imagAxis s h) : UpperHalfPlane) : ℂ)
        = (1 : ℂ) + (s : ℂ) * Complex.I := by
      rw [UpperHalfPlane.coe_vadd, hcoes h, Complex.ofReal_one]
    rw [hv, hudef]
    congr 1
    ring
  have h3eq : ∀ h : 0 < s,
      ‖(τ : ℂ) - (((-1 : ℝ) +ᵥ (Work.Kernels.imagAxis s h) : UpperHalfPlane) : ℂ)‖
        = ‖u + 1‖ := by
    intro h
    have hv : (((-1 : ℝ) +ᵥ (Work.Kernels.imagAxis s h) : UpperHalfPlane) : ℂ)
        = (-1 : ℂ) + (s : ℂ) * Complex.I := by
      rw [UpperHalfPlane.coe_vadd, hcoes h]
      norm_num
    rw [hv, hudef]
    congr 1
    ring
  -- `|Re τ| < 1/4` makes the two lattice translates `i/t ± 1` farther than `i/t`
  have hsq : ∀ v : ℂ, ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    intro v
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hu1 : ‖u‖ ≤ ‖u - 1‖ := by
    have h1 : ‖u - 1‖ ^ 2 = (u.re - 1) ^ 2 + u.im ^ 2 := by
      rw [hsq, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      ring
    have h3 : ‖u‖ ^ 2 ≤ ‖u - 1‖ ^ 2 := by
      rw [hsq u, h1, hu_re]
      have hle : τ.re ≤ 1 / 2 := by linarith [(abs_lt.mp hre_lt).2]
      nlinarith [hle]
    nlinarith [h3, norm_nonneg u, norm_nonneg (u - 1)]
  have hu2 : ‖u‖ ≤ ‖u + 1‖ := by
    have h1 : ‖u + 1‖ ^ 2 = (u.re + 1) ^ 2 + u.im ^ 2 := by
      rw [hsq, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
      ring
    have h3 : ‖u‖ ^ 2 ≤ ‖u + 1‖ ^ 2 := by
      rw [hsq u, h1, hu_re]
      have hle : -(1 / 2 : ℝ) ≤ τ.re := by linarith [(abs_lt.mp hre_lt).1]
      nlinarith [hle]
    nlinarith [h3, norm_nonneg u, norm_nonneg (u + 1)]
  have hmin_eq : min (min ‖u‖ ‖u - 1‖) ‖u + 1‖ = ‖u‖ := by
    rw [min_eq_left (le_trans (min_le_left _ _) hu2), min_eq_left hu1]
  -- the cusp point `i/s = i t` of the estimate is the point of the target
  have hpt : ∀ h : 0 < 1 / s, Work.Kernels.imagAxis (1 / s) h = Work.Kernels.imagAxis t ht := by
    intro h
    apply UpperHalfPlane.ext
    have h1 : ((Work.Kernels.imagAxis (1 / s) h : UpperHalfPlane) : ℂ)
        = (↑(1 / s) : ℂ) * Complex.I := by simp [Work.Kernels.imagAxis]
    have h2 : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := by
      simp [Work.Kernels.imagAxis]
    rw [h1, h2, hst]
  have hexp : Real.exp (2 * Real.pi * s) = Real.exp (2 * Real.pi / t) := by
    rw [hsdef]
    congr 1
    ring
  -- the estimate of `JLowerGeSevenFourths` at `s = 1/t`
  have hres := hJ s hs74 τ hτD him
  rw [h1eq, h2eq, h3eq] at hres
  rw [hmin_eq] at hres
  rw [hpt] at hres
  rw [hexp] at hres
  rw [hA]
  exact hres

end Work.Asymptotics.HalfFunnel
