/-
# Definitions for the local continuation of the CKMRV contour transform at `1 + i s₀`

This module collects the *definitions* used by `Work.Asymptotics.kernelTransform_local_continuation`
and by the lemmas delegated for it.  It is deliberately free of anything that imports the target
module, so that the auxiliary lemmas can be stated in this vocabulary without creating an import
cycle.

## The contour

Fix `t₀ = s₀ > 0` and let `τ₀ = 1 + i t₀`.  The CKMRV transform

  `kernelTransform K τ r = 4 sin²(πr²/2) ∫_0^∞ K(τ,it) e^{-πr²t} dt`

is the curve integral of the *analytic* `1`-form `K(τ,z) e^{iπr²z} dz / i` over the positive
imaginary axis: with `z = it` we have `dz/i = dt` and `e^{iπr²z} = e^{-πr²t}`.

Near `τ₀` the imaginary axis carries the genuine pole `z = T⁻¹τ = τ - 1` (residue `1/(2π)`,
`φ(T) = 1`) as soon as `Re τ` crosses `1`, and it carries the *removable* coincidence
`z = ST⁻¹τ = -1/(τ-1)` (`φ(TS) = 0`) at `i/t₀`.  The contour of the continuation therefore has
to avoid the ball `B - 1` of radius `ε` around `i t₀` (the genuine pole) and the ball
`(ST⁻¹)B` around `i/t₀` (where the literal `Kfun`, whose convention is `0⁻¹ = 0`, jumps):
it is the imaginary axis with

* the interval `I₁ = (t₀-A₁, t₀+A₁)` replaced by the three sides of the rectangle
  `R₁ = [0,ξ₁] × [t₀-A₁, t₀+A₁]` lying in `Re > 0` ("`detourRight`"), and
* the interval `I₂ = (1/t₀-A₂, 1/t₀+A₂)` replaced by the three sides of
  `R₂ = [-ξ₂,0] × [1/t₀-A₂, 1/t₀+A₂]` ("`detourLeft`").

When `1/t₀ ∈ I₁` (i.e. `t₀ > 1/√2`) the second detour is not needed and one takes
`A₂ = ξ₂ = 0`, which degenerates all of `detourLeft` to `0`; the definitions below are therefore
uniform in the parameters.

## The `dz/i` normalisation

Because the `1`-form is `K e^{iπr²z} dz/i`, the horizontal edges (where `dz = ±du`) contribute
`(-i)·∫K e^{iπr²z} du` and the vertical edges (`dz = i dv`) contribute `∫ K e^{iπr²z} dv`.
This is why `detourRight`/`detourLeft` below carry the factors `1/i = -i` (bottom edges) and
`-1/i = i` (top edges) while the vertical edges are plain.  With this normalisation
Cauchy–Goursat on `Rᵢ` reads exactly `∫_{Iᵢ} K(iy)e^{-πr²y}dy = detourᵢ`.
-/
import Mathlib
import Submission.Work.Kernels.All

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.Asymptotics

open UpperHalfPlane MeasureTheory

/-! ## The centre of the ball -/

/-- The point `1 + i s₀` of `ℍ`, the centre of the ball on which the transform is continued. -/
def onePlusI (s₀ : ℝ) (hs₀ : 0 < s₀) : UpperHalfPlane :=
  ⟨(1 : ℂ) + (s₀ : ℂ) * Complex.I, by simpa using hs₀⟩

@[simp] lemma onePlusI_re (s₀ : ℝ) (hs₀ : 0 < s₀) : (onePlusI s₀ hs₀).re = 1 := by
  simp [onePlusI]

@[simp] lemma onePlusI_im (s₀ : ℝ) (hs₀ : 0 < s₀) : (onePlusI s₀ hs₀).im = s₀ := by
  simp [onePlusI]

lemma onePlusI_coe (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ((onePlusI s₀ hs₀ : UpperHalfPlane) : ℂ) = (1 : ℂ) + (s₀ : ℂ) * Complex.I := rfl

/-! ## The geometric input: the web avoids the ball off the line `Re τ = 1`

Near `1 + i s₀` the `SL(2,ℤ)`-orbit of the imaginary axis meets a small ball only in the line
`Re τ = 1`.  This is the local form of the Farey-tessellation picture and is the only genuinely
geometric input of the construction; it is proved by direct computation from
`γ • (it) = (a i t + b)/(c i t + d)`. -/

private lemma two_mul_sqrt_mul_le' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have h : (2 * Real.sqrt (a * b)) ^ 2 ≤ (a + b) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg ha hb)]
    nlinarith [sq_nonneg (a - b)]
  have h1 : |2 * Real.sqrt (a * b)| ≤ |a + b| := sq_le_sq.mp h
  rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)] at h1

/-- The real and imaginary parts of `γ • (it)` in terms of the entries of `γ`. -/
lemma web_re_im (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t) :
    ((γ • Work.Kernels.imagAxis t ht : ℍ) : ℂ).im
        = t / (((γ 1 0 : ℤ) : ℝ) ^ 2 * t ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2) ∧
      (((γ • Work.Kernels.imagAxis t ht : ℍ) : ℂ) - 1).re
        = ((((γ 0 0 : ℤ) : ℝ) - ((γ 1 0 : ℤ) : ℝ)) * ((γ 1 0 : ℤ) : ℝ) * t ^ 2
          + (((γ 0 1 : ℤ) : ℝ) - ((γ 1 1 : ℤ) : ℝ)) * ((γ 1 1 : ℤ) : ℝ))
          / (((γ 1 0 : ℤ) : ℝ) ^ 2 * t ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2) := by
  set w : ℍ := γ • Work.Kernels.imagAxis t ht with hw
  set N : ℂ := ((γ 0 0 : ℤ) : ℂ) * ((t:ℂ)*Complex.I) + ((γ 0 1 : ℤ) : ℂ) with hN
  set Dv : ℂ := ((γ 1 0 : ℤ) : ℂ) * ((t:ℂ)*Complex.I) + ((γ 1 1 : ℤ) : ℂ) with hDv
  have hwC : (w : ℂ) = N / Dv := by
    rw [hw, hN, hDv]
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [Work.Kernels.imagAxis]
  have hDv_ne : Dv ≠ 0 := by
    rw [hDv]
    have hcd : (![((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] : Fin 2 → ℝ) ≠ 0 := by
      intro hh
      have h10 : γ 1 0 = 0 := by
        have h' : ((γ 1 0 : ℤ) : ℝ) = 0 := by simpa using congrFun hh 0
        exact_mod_cast h'
      have h11 : γ 1 1 = 0 := by
        have h' : ((γ 1 1 : ℤ) : ℝ) = 0 := by simpa using congrFun hh 1
        exact_mod_cast h'
      have hdet := γ.2
      rw [Matrix.det_fin_two, h10, h11] at hdet
      norm_num at hdet
    have := UpperHalfPlane.linear_ne_zero (Work.Kernels.imagAxis t ht) hcd
    simpa [Work.Kernels.imagAxis, mul_comm, mul_left_comm, mul_assoc] using this
  have hmul : ((w:ℂ) - 1) * Dv = N - Dv := by
    rw [hwC, sub_mul, div_mul_cancel₀ _ hDv_ne, one_mul]
  have hDr : Dv.re = ((γ 1 1 : ℤ) : ℝ) := by rw [hDv]; simp
  have hDi : Dv.im = ((γ 1 0 : ℤ) : ℝ) * t := by rw [hDv]; simp
  have hNr : (N - Dv).re = ((γ 0 1 : ℤ) : ℝ) - ((γ 1 1 : ℤ) : ℝ) := by
    rw [hN, hDv]; simp
  have hNi : (N - Dv).im = (((γ 0 0 : ℤ) : ℝ) - ((γ 1 0 : ℤ) : ℝ)) * t := by
    rw [hN, hDv]; simp; ring
  have h1 : ((w:ℂ)-1).re * Dv.re - ((w:ℂ)-1).im * Dv.im = (N - Dv).re := by
    have := congrArg Complex.re hmul
    simpa [Complex.mul_re] using this
  have h2 : ((w:ℂ)-1).re * Dv.im + ((w:ℂ)-1).im * Dv.re = (N - Dv).im := by
    have := congrArg Complex.im hmul
    simpa [Complex.mul_im] using this
  rw [hDr, hDi, hNr] at h1
  rw [hDr, hDi, hNi] at h2
  have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  have hdet' : (((γ 0 0 : ℤ) : ℝ) - ((γ 1 0 : ℤ) : ℝ)) * ((γ 1 1 : ℤ) : ℝ)
      - (((γ 0 1 : ℤ) : ℝ) - ((γ 1 1 : ℤ) : ℝ)) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    linarith [hdet]
  have hd2 : 0 < (((γ 1 0 : ℤ) : ℝ)^2 * t^2 + ((γ 1 1 : ℤ) : ℝ)^2) := by
    rcases eq_or_ne (γ 1 1) 0 with hd0 | hd0
    · have hd0R : ((γ 1 1 : ℤ) : ℝ) = 0 := by exact_mod_cast hd0
      have hc0 : γ 1 0 ≠ 0 := by
        intro hc0
        have h := γ.2
        rw [Matrix.det_fin_two, hd0, hc0, mul_zero, mul_zero, sub_zero] at h
        norm_num at h
      rw [hd0R]
      have h1 : (0:ℝ) < ((γ 1 0 : ℤ) : ℝ)^2 := by
        have : ((γ 1 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc0
        positivity
      have : (0:ℝ) < ((γ 1 0 : ℤ) : ℝ)^2 * t^2 := mul_pos h1 (pow_pos ht 2)
      simpa using this
    · have hpos : (0:ℝ) < ((γ 1 1 : ℤ) : ℝ)^2 := by
        have : ((γ 1 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hd0
        positivity
      nlinarith [hpos, mul_nonneg (sq_nonneg ((γ 1 0 : ℤ) : ℝ)) (sq_nonneg t)]
  constructor
  · have hkey : ((w:ℂ)-1).im * (((γ 1 0 : ℤ) : ℝ)^2 * t^2 + ((γ 1 1 : ℤ) : ℝ)^2) = t := by
      linear_combination (((γ 1 1 : ℤ) : ℝ)) * h2 - (((γ 1 0 : ℤ) : ℝ) * t) * h1 + t * hdet'
    rw [eq_div_iff (ne_of_gt hd2)]
    rw [Complex.sub_im, Complex.one_im, sub_zero] at hkey
    exact hkey
  · have hkey : ((w:ℂ)-1).re * (((γ 1 0 : ℤ) : ℝ)^2 * t^2 + ((γ 1 1 : ℤ) : ℝ)^2)
        = (((γ 0 0 : ℤ) : ℝ) - ((γ 1 0 : ℤ) : ℝ)) * ((γ 1 0 : ℤ) : ℝ) * t^2
          + (((γ 0 1 : ℤ) : ℝ) - ((γ 1 1 : ℤ) : ℝ)) * ((γ 1 1 : ℤ) : ℝ) := by
      linear_combination (((γ 1 1 : ℤ) : ℝ)) * h1 + (((γ 1 0 : ℤ) : ℝ) * t) * h2
    rw [eq_div_iff (ne_of_gt hd2)]
    rw [Complex.sub_re, Complex.one_re] at hkey
    exact hkey

/-- **Near `1 + i s₀` the web meets the ball only in the line `Re τ = 1`.** -/
theorem webAvoidBall (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (γ • Work.Kernels.imagAxis t ht) (onePlusI s₀ hs₀) < ε →
        ((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ).re = 1 := by
  have hsqrt_gt : s₀ < Real.sqrt (1 + s₀ ^ 2) := by
    rw [Real.lt_sqrt hs₀.le]; nlinarith
  set X₀ : ℝ := 2 * (Real.sqrt (1 + s₀ ^ 2) - s₀) with hX₀
  have hX₀pos : 0 < X₀ := by rw [hX₀]; linarith
  set Y₀ : ℝ := s₀ ^ 2 / 2 with hY₀
  have hY₀pos : 0 < Y₀ := by rw [hY₀]; positivity
  set Z₀ : ℝ := s₀ ^ 4 / 8 with hZ₀
  have hZ₀pos : 0 < Z₀ := by rw [hZ₀]; positivity
  set F₀ : ℝ := min X₀ (min Y₀ Z₀) with hF₀
  have hF₀pos : 0 < F₀ := by rw [hF₀]; exact lt_min hX₀pos (lt_min hY₀pos hZ₀pos)
  have hF₀X : F₀ ≤ X₀ := by rw [hF₀]; exact min_le_left _ _
  have hF₀Y : F₀ ≤ Y₀ := by rw [hF₀, hY₀]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hF₀Z : F₀ ≤ Z₀ := by rw [hF₀, hZ₀]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨Real.arcosh (1 + F₀ / (2 * s₀)), Real.arcosh_pos (by
    have : 0 < F₀ / (2 * s₀) := div_pos hF₀pos (by positivity)
    linarith), ?_⟩
  intro γ t ht hlt
  set w : ℍ := γ • Work.Kernels.imagAxis t ht with hw
  have hy_raw : (w:ℂ).im = t / (((γ 1 0 : ℤ) : ℝ) ^ 2 * t ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2) := by
    rw [hw]; exact (web_re_im γ t ht).1
  have he_raw : (w:ℂ).re - 1
      = ((((γ 0 0 : ℤ) : ℝ) - ((γ 1 0 : ℤ) : ℝ)) * ((γ 1 0 : ℤ) : ℝ) * t ^ 2
        + (((γ 0 1 : ℤ) : ℝ) - ((γ 1 1 : ℤ) : ℝ)) * ((γ 1 1 : ℤ) : ℝ))
        / (((γ 1 0 : ℤ) : ℝ) ^ 2 * t ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2) := by
    rw [hw]; exact (web_re_im γ t ht).2
  set A : ℝ := ((γ 0 0 : ℤ) : ℝ) with hA
  set B : ℝ := ((γ 0 1 : ℤ) : ℝ) with hB
  set C : ℝ := ((γ 1 0 : ℤ) : ℝ) with hC
  set Dd : ℝ := ((γ 1 1 : ℤ) : ℝ) with hDd
  have hy : (w:ℂ).im = t / (C ^ 2 * t ^ 2 + Dd ^ 2) := by rw [hy_raw]
  have he : (w:ℂ).re - 1 = ((A - C) * C * t ^ 2 + (B - Dd) * Dd) / (C ^ 2 * t ^ 2 + Dd ^ 2) := by
    rw [he_raw]
  have hP : 0 < C ^ 2 * t ^ 2 + Dd ^ 2 := by
    rw [hC, hDd]
    rcases eq_or_ne (γ 1 1) 0 with hd0 | hd0
    · have hd0R : ((γ 1 1 : ℤ) : ℝ) = 0 := by exact_mod_cast hd0
      have hc0 : γ 1 0 ≠ 0 := by
        intro hc0
        have h := γ.2
        rw [Matrix.det_fin_two, hd0, hc0, mul_zero, mul_zero, sub_zero] at h
        norm_num at h
      rw [hd0R]
      have h1 : (0:ℝ) < ((γ 1 0 : ℤ) : ℝ)^2 := by
        have : ((γ 1 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc0
        positivity
      have : (0:ℝ) < ((γ 1 0 : ℤ) : ℝ)^2 * t^2 := mul_pos h1 (pow_pos ht 2)
      simpa using this
    · have hpos : (0:ℝ) < ((γ 1 1 : ℤ) : ℝ)^2 := by
        have : ((γ 1 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hd0
        positivity
      nlinarith [hpos, mul_nonneg (sq_nonneg ((γ 1 0 : ℤ) : ℝ)) (sq_nonneg t)]
  have hdet : A * Dd - B * C = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [hA, hB, hC, hDd]
    exact_mod_cast h
  have hdetC : (A - C) * Dd - (B - Dd) * C = 1 := by linarith [hdet]
  set e : ℝ := (w:ℂ).re - 1 with he_def
  set y : ℝ := (w:ℂ).im with hy_def
  have he_re : e = w.re - 1 := by rw [he_def, UpperHalfPlane.coe_re]
  have hy_im : y = w.im := by rw [hy_def, UpperHalfPlane.coe_im]
  have hypos : 0 < y := by rw [hy_im]; exact w.im_pos
  have hcosh : Real.cosh (dist w (onePlusI s₀ hs₀))
      = 1 + (e ^ 2 + (y - s₀) ^ 2) / (2 * s₀ * y) := by
    rw [UpperHalfPlane.cosh_dist', onePlusI_re, onePlusI_im, ← he_re, ← hy_im]
    field_simp
    ring
  by_contra hne
  have hne' : e ≠ 0 := by
    intro h
    refine hne ?_
    rw [he_def] at h
    linarith
  have hFge : F₀ ≤ (e ^ 2 + (y - s₀) ^ 2) / y := by
    rcases eq_or_ne C 0 with hC0 | hC0
    · -- C = 0
      have hAD : A * Dd = 1 := by
        have h := hdetC
        rw [hC0] at h
        ring_nf at h ⊢
        linarith [h]
      have hDd2 : Dd ^ 2 = 1 := by
        have h := hAD
        rw [hA, hDd] at h
        have hZ : γ 0 0 * γ 1 1 = 1 := by exact_mod_cast h
        rcases Int.eq_one_or_neg_one_of_mul_eq_one' hZ with ⟨_, h11⟩ | ⟨_, h11⟩
        · rw [hDd, h11]; norm_num
        · rw [hDd, h11]; norm_num
      have hy0 : y = t := by rw [hy, hC0, hDd2]; ring_nf
      have he0 : e = (B - Dd) * Dd := by rw [he, hC0, hDd2]; ring_nf
      have he0Z : e = ((((γ 0 1) - (γ 1 1)) * (γ 1 1) : ℤ) : ℝ) := by
        rw [he0, hB, hDd]; push_cast; ring
      have hge1 : 1 ≤ e ^ 2 := by
        rw [he0Z]
        have hneZ : ((γ 0 1 - γ 1 1) * (γ 1 1) : ℤ) ≠ 0 := by
          intro h
          exact hne' (by rw [he0Z, h]; norm_num)
        have h1 : (1:ℤ) ≤ |((γ 0 1 - γ 1 1) * (γ 1 1) : ℤ)| := Int.one_le_abs hneZ
        have h2 : (1:ℝ) ≤ |((((γ 0 1 - γ 1 1) * (γ 1 1) : ℤ)) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast h1
        have h3 : |(1:ℝ)| ≤ |((((γ 0 1 - γ 1 1) * (γ 1 1) : ℤ)) : ℝ)| := by simpa using h2
        simpa using (sq_le_sq.mpr h3 :
          (1:ℝ) ^ 2 ≤ ((((γ 0 1 - γ 1 1) * (γ 1 1) : ℤ)) : ℝ) ^ 2)
      rw [hy0]
      have hb1 : (1 + (t - s₀) ^ 2) / t ≤ (e ^ 2 + (t - s₀) ^ 2) / t :=
        div_le_div_of_nonneg_right (by linarith [hge1]) (by positivity)
      have hb2 : X₀ ≤ (1 + (t - s₀) ^ 2) / t := by
        rw [hX₀]
        have heq : (1 + (t - s₀) ^ 2) / t = t + (1 + s₀ ^ 2) / t - 2 * s₀ := by
          field_simp; ring
        rw [heq]
        have hagm := two_mul_sqrt_mul_le' t ((1 + s₀ ^ 2) / t) ht.le (by positivity)
        rw [show t * ((1 + s₀ ^ 2) / t) = (1 + s₀ ^ 2) by field_simp] at hagm
        linarith [hagm]
      exact le_trans hF₀X (le_trans hb2 hb1)
    · rcases eq_or_ne Dd 0 with hD0 | hD0
      · -- Dd = 0
        have hBC : B * C = -1 := by
          have h := hdetC
          rw [hD0] at h
          ring_nf at h ⊢
          linarith [h]
        have hC2 : C ^ 2 = 1 := by
          have h := hBC
          rw [hB, hC] at h
          have hZ : γ 0 1 * γ 1 0 = -1 := by exact_mod_cast h
          rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' hZ with ⟨_, h10⟩ | ⟨_, h10⟩
          · rw [hC, h10]; norm_num
          · rw [hC, h10]; norm_num
        have hy0 : y = 1 / t := by
          rw [hy, hD0, hC2]; field_simp; ring
        have he0 : e = (A - C) * C := by
          rw [he, hD0, hC2]; field_simp; ring
        have he0Z : e = ((((γ 0 0) - (γ 1 0)) * (γ 1 0) : ℤ) : ℝ) := by
          rw [he0, hA, hC]; push_cast; ring
        have hge1 : 1 ≤ e ^ 2 := by
          rw [he0Z]
          have hneZ : ((γ 0 0 - γ 1 0) * (γ 1 0) : ℤ) ≠ 0 := by
            intro h
            exact hne' (by rw [he0Z, h]; norm_num)
          have h1 : (1:ℤ) ≤ |((γ 0 0 - γ 1 0) * (γ 1 0) : ℤ)| := Int.one_le_abs hneZ
          have h2 : (1:ℝ) ≤ |((((γ 0 0 - γ 1 0) * (γ 1 0) : ℤ)) : ℝ)| := by
            rw [← Int.cast_abs]; exact_mod_cast h1
          have h3 : |(1:ℝ)| ≤ |((((γ 0 0 - γ 1 0) * (γ 1 0) : ℤ)) : ℝ)| := by simpa using h2
          simpa using (sq_le_sq.mpr h3 :
            (1:ℝ) ^ 2 ≤ ((((γ 0 0 - γ 1 0) * (γ 1 0) : ℤ)) : ℝ) ^ 2)
        rw [hy0]
        have hb1 : (1 + (1/t - s₀) ^ 2) / (1/t) ≤ (e ^ 2 + (1/t - s₀) ^ 2) / (1/t) :=
          div_le_div_of_nonneg_right (by linarith [hge1]) (by positivity)
        have hb2 : X₀ ≤ (1 + (1/t - s₀) ^ 2) / (1/t) := by
          rw [hX₀]
          have heq : (1 + (1/t - s₀) ^ 2) / (1/t) = (1 + s₀^2)*t + 1/t - 2*s₀ := by
            field_simp; ring
          rw [heq]
          have hagm := two_mul_sqrt_mul_le' ((1+s₀^2)*t) (1/t) (by positivity) (by positivity)
          have h' : ((1+s₀^2)*t) * (1/t) = 1+s₀^2 := by field_simp
          rw [h'] at hagm
          linarith [hagm]
        exact le_trans hF₀X (le_trans hb2 hb1)
      · -- C ≠ 0 and Dd ≠ 0
        have hCne : |C| ≠ 0 := abs_ne_zero.mpr hC0
        have hDne : |Dd| ≠ 0 := abs_ne_zero.mpr hD0
        have hCabs : 0 < |C| := abs_pos.mpr hC0
        have hDabs : 0 < |Dd| := abs_pos.mpr hD0
        set m : ℝ := |C| * |Dd| with hm
        set u : ℝ := |C| * t / |Dd| with hu
        have hupos : 0 < u := div_pos (mul_pos hCabs ht) hDabs
        have hmpos : 0 < m := mul_pos hCabs hDabs
        have hC0Z : γ 1 0 ≠ 0 := by
          intro h; exact hC0 (by rw [hC, h]; norm_num)
        have hD0Z : γ 1 1 ≠ 0 := by
          intro h; exact hD0 (by rw [hDd, h]; norm_num)
        have hm1 : 1 ≤ m := by
          rw [hm]
          refine one_le_mul_of_one_le_of_one_le ?_ ?_
          · rw [hC, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs hC0Z
          · rw [hDd, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs hD0Z
        have hu2 : u ^ 2 = C ^ 2 * t ^ 2 / Dd ^ 2 := by
          rw [hu, div_pow, mul_pow, sq_abs, sq_abs]
        have ht2 : t ^ 2 = Dd ^ 2 * u ^ 2 / C ^ 2 := by
          rw [hu, div_pow, mul_pow, sq_abs C, sq_abs Dd]
          field_simp
        have ht1 : t = |Dd| * u / |C| := by
          rw [hu]; field_simp
        have hP' : C ^ 2 * t ^ 2 + Dd ^ 2 = Dd ^ 2 * (1 + u ^ 2) := by
          rw [hu2]; field_simp; ring
        have hy_u : y = u / (m * (1 + u ^ 2)) := by
          rw [hy, hP', ht1, hm, show Dd ^ 2 = |Dd| ^ 2 by rw [sq_abs]]
          field_simp
        have he_u : e = (((A - C) * Dd) * u ^ 2 + ((B - Dd) * C)) / ((C * Dd) * (1 + u ^ 2)) := by
          rw [he, hP', ht2]; field_simp
        set Ap : ℝ := (A - C) * Dd with hAp
        set Bp : ℝ := (B - Dd) * C with hBp
        have hAt : Ap = Bp + 1 := by linarith [hdetC]
        have hBpZ : Bp = (((γ 0 1 - γ 1 1) * (γ 1 0) : ℤ) : ℝ) := by
          rw [hBp, hB, hDd, hC]; push_cast; ring
        have hMv2 : ((C * Dd) * (1 + u ^ 2)) ^ 2 = m ^ 2 * (1 + u ^ 2) ^ 2 := by
          rw [hm]
          rw [show (|C| * |Dd|) ^ 2 = (C * Dd) ^ 2 by rw [mul_pow, mul_pow, sq_abs, sq_abs]]
          ring
        have hclaimA : Bp ≠ 0 → Bp ≠ -1 → 1 / m ^ 2 ≤ e ^ 2 := by
          intro hB0 hBm1
          have hbZ : ((γ 0 1 - γ 1 1) * (γ 1 0) : ℤ) ≠ 0 := by
            intro h; exact hB0 (by rw [hBpZ, h]; norm_num)
          have hbmZ : ((γ 0 1 - γ 1 1) * (γ 1 0) : ℤ) ≠ -1 := by
            intro h; exact hBm1 (by rw [hBpZ, h]; norm_num)
          have hcase : (1:ℝ) ≤ Bp ∨ Bp ≤ -2 := by
            rw [hBpZ]
            rcases (show (1:ℤ) ≤ ((γ 0 1 - γ 1 1) * (γ 1 0)) ∨
                ((γ 0 1 - γ 1 1) * (γ 1 0)) ≤ -2 by omega) with h | h
            · left; exact_mod_cast h
            · right; exact_mod_cast h
          have hnum : 1 + u ^ 2 ≤ |Ap * u ^ 2 + Bp| := by
            rcases hcase with h | h
            · rw [abs_of_nonneg (by nlinarith [h, hAt, sq_nonneg u])]
              nlinarith [h, hAt, sq_nonneg u]
            · rw [abs_of_nonpos (by nlinarith [h, hAt])]
              nlinarith [h, hAt, sq_nonneg u]
          rw [he_u, div_pow, hMv2]
          rw [div_le_iff₀ (by positivity : (0:ℝ) < m ^ 2)]
          have hnum2 : (1 + u ^ 2) ^ 2 ≤ (Ap * u ^ 2 + Bp) ^ 2 := by
            rw [sq_le_sq, abs_of_nonneg (by positivity)]
            exact hnum
          have hkey : (Ap * u ^ 2 + Bp) ^ 2 / (m ^ 2 * (1 + u ^ 2) ^ 2) * m ^ 2
              = (Ap * u ^ 2 + Bp) ^ 2 / (1 + u ^ 2) ^ 2 := by
            field_simp
          rw [hkey]
          rw [le_div_iff₀ (by positivity : (0:ℝ) < (1 + u ^ 2) ^ 2)]
          nlinarith [hnum2]
        have hclaimB : Bp = 0 ∨ Bp = -1 → m ^ 2 * y ^ 4 ≤ e ^ 2 := by
          intro hb
          have hq : u ^ 2 ≤ |Ap * u ^ 2 + Bp| * (1 + u ^ 2) := by
            rcases hb with hb | hb
            · have hAp1 : Ap = 1 := by linarith [hAt, hb]
              rw [hAp1, hb, one_mul, add_zero, abs_of_nonneg (sq_nonneg u)]
              nlinarith [sq_nonneg (u ^ 2), sq_nonneg u]
            · have hAp0 : Ap = 0 := by linarith [hAt, hb]
              rw [hAp0, hb, zero_mul, zero_add, abs_neg, abs_one, one_mul]
              nlinarith [sq_nonneg u]
          have he2 : e ^ 2 = (Ap * u ^ 2 + Bp) ^ 2 / (m ^ 2 * (1 + u ^ 2) ^ 2) := by
            rw [he_u, div_pow, hMv2]
          have hy4 : m ^ 2 * y ^ 4 = u ^ 4 / (m ^ 2 * (1 + u ^ 2) ^ 4) := by
            rw [hy_u, div_pow, mul_pow]
            field_simp
            ring
          rw [hy4, he2]
          rw [div_le_iff₀ (by positivity : (0:ℝ) < m ^ 2 * (1 + u ^ 2) ^ 4)]
          have hq2 : u ^ 4 ≤ (Ap * u ^ 2 + Bp) ^ 2 * (1 + u ^ 2) ^ 2 := by
            have h1 : (u ^ 2) ^ 2 ≤ (|Ap * u ^ 2 + Bp| * (1 + u ^ 2)) ^ 2 := by
              rw [sq_le_sq, abs_of_nonneg (sq_nonneg u),
                abs_of_nonneg (mul_nonneg (abs_nonneg _) (by positivity))]
              exact hq
            have h2 : (|Ap * u ^ 2 + Bp| * (1 + u ^ 2)) ^ 2
                = (Ap * u ^ 2 + Bp) ^ 2 * (1 + u ^ 2) ^ 2 := by
              rw [mul_pow, sq_abs]
            rw [h2, show (u ^ 2) ^ 2 = u ^ 4 by ring] at h1
            exact h1
          have hkey : (Ap * u ^ 2 + Bp) ^ 2 / (m ^ 2 * (1 + u ^ 2) ^ 2)
                * (m ^ 2 * (1 + u ^ 2) ^ 4)
              = (Ap * u ^ 2 + Bp) ^ 2 * (1 + u ^ 2) ^ 2 := by
            field_simp
          rw [hkey]
          exact hq2
        have hylem : y ≤ 1 / (2 * m) := by
          rw [hy_u]
          rw [div_le_iff₀ (by positivity : (0:ℝ) < m * (1 + u ^ 2))]
          rw [show (1/(2*m)) * (m*(1+u^2)) = (1+u^2)/2 by field_simp]
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
          nlinarith [sq_nonneg (u - 1)]
        have hyhalf : y ≤ 1/2 := by
          have h2 : 1 / (2 * m) ≤ 1/2 := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * m)]
            rw [show (1/2) * (2 * m) = m by ring]
            linarith [hm1]
          linarith [hylem, h2]
        by_cases hyc : y ≤ s₀ / 2
        · have h1 : Y₀ ≤ (e ^ 2 + (y - s₀) ^ 2) / y := by
            rw [hY₀, le_div_iff₀ hypos]
            nlinarith [hyc, hyhalf, hs₀, hypos, sq_nonneg (y - s₀), sq_nonneg e]
          exact le_trans hF₀Y h1
        · have hyge : s₀ / 2 ≤ y := le_of_lt (lt_of_not_ge hyc)
          by_cases hBp' : Bp = 0 ∨ Bp = -1
          · have hb := hclaimB hBp'
            have h1 : Z₀ ≤ (e ^ 2 + (y - s₀) ^ 2) / y := by
              rw [hZ₀, le_div_iff₀ hypos]
              have hy4 : (s₀ / 2) ^ 4 ≤ y ^ 4 :=
                pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ s₀ / 2) hyge 4
              have hm2 : (1:ℝ) ≤ m ^ 2 := by nlinarith [hm1]
              nlinarith [hb, hy4, hm2, hyhalf, hypos, sq_nonneg (s₀ ^ 2)]
            exact le_trans hF₀Z h1
          · have hBp0 : Bp ≠ 0 := fun h => hBp' (Or.inl h)
            have hBp1 : Bp ≠ -1 := fun h => hBp' (Or.inr h)
            have hb := hclaimA hBp0 hBp1
            have hminv : s₀ ≤ 1 / m := by
              have h2 : s₀ / 2 ≤ 1 / (2 * m) := le_trans hyge hylem
              have h3 : 1 / (2 * m) = (1 / m) / 2 := by field_simp
              rw [h3] at h2; linarith [h2]
            have hem2 : s₀ ^ 2 ≤ e ^ 2 := by
              have h3 : (1 / m) ^ 2 ≤ e ^ 2 := by simpa [one_div, inv_pow] using hb
              have h4 : s₀ ^ 2 ≤ (1 / m) ^ 2 := by
                apply sq_le_sq.mpr
                rw [abs_of_nonneg hs₀.le, abs_of_nonneg (by positivity)]
                exact hminv
              linarith [h3, h4]
            have h1 : Y₀ ≤ (e ^ 2 + (y - s₀) ^ 2) / y := by
              rw [hY₀, le_div_iff₀ hypos]
              nlinarith [hem2, hyhalf, hypos]
            exact le_trans hF₀Y h1
  have hle : Real.arcosh (1 + F₀ / (2 * s₀)) ≤ dist w (onePlusI s₀ hs₀) := by
    have hcc : Real.cosh (Real.arcosh (1 + F₀ / (2 * s₀))) = 1 + F₀ / (2 * s₀) :=
      Real.cosh_arcosh (by
        have h : (0:ℝ) ≤ F₀ / (2 * s₀) := div_nonneg hF₀pos.le (by positivity)
        linarith)
    have h1 : Real.cosh (Real.arcosh (1 + F₀ / (2 * s₀)))
        ≤ Real.cosh (dist w (onePlusI s₀ hs₀)) := by
      rw [hcc, hcosh]
      have h2 : F₀ / (2 * s₀) ≤ (e ^ 2 + (y - s₀) ^ 2) / (2 * s₀ * y) := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * s₀)]
        have heq : (e ^ 2 + (y - s₀) ^ 2) / (2 * s₀ * y) * (2 * s₀) = (e ^ 2 + (y - s₀) ^ 2) / y := by
          field_simp
        rw [heq]
        exact hFge
      linarith
    have h3 := Real.cosh_le_cosh.mp h1
    rw [abs_of_nonneg (Real.arcosh_nonneg (by
        have h : (0:ℝ) ≤ F₀ / (2 * s₀) := div_nonneg hF₀pos.le (by positivity)
        linarith)), abs_of_nonneg dist_nonneg] at h3
    exact h3
  exact absurd hle (not_le.mpr hlt)

end Work.Asymptotics

namespace Work.Asymptotics

open UpperHalfPlane MeasureTheory

/-! ## The `1`-form of the contour integral

We work with the *normalised* `1`-form `K(τ,z) e^{iπr²z} dz / i`: on the imaginary axis
`z = it` this is `K(τ,it) e^{-πr²t} dt`, so that its integral over `iℝ` is exactly the
integrand of `Work.Kernels.kernelTransform`.  Dividing by `i` is why the horizontal edges below
carry an extra `1/i`. -/

/-- The point `u + i v` of `ℍ`, junk when `v ≤ 0` (only the values on `v > 0` are ever used). -/
def ofReImT (u v : ℝ) : UpperHalfPlane :=
  if h : 0 < v then ⟨(u : ℂ) + (v : ℂ) * Complex.I, by simpa using h⟩ else ⟨Complex.I, by simp⟩

lemma ofReImT_eq (u v : ℝ) (h : 0 < v) :
    ofReImT u v = (⟨(u : ℂ) + (v : ℂ) * Complex.I, by simpa using h⟩ : UpperHalfPlane) :=
  dif_pos h

lemma ofReImT_coe (u v : ℝ) (h : 0 < v) : ((ofReImT u v : UpperHalfPlane) : ℂ)
    = (u : ℂ) + (v : ℂ) * Complex.I := by
  rw [ofReImT_eq u v h]

lemma ofReImT_re (u v : ℝ) (h : 0 < v) : (ofReImT u v).re = u := by
  simp [ofReImT_eq u v h]

lemma ofReImT_im (u v : ℝ) (h : 0 < v) : (ofReImT u v).im = v := by
  simp [ofReImT_eq u v h]

/-- The Gaussian weight at height `v`, i.e. `e^{-π r² v}`. -/
def gaussWeight (r v : ℝ) : ℂ := Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (v : ℂ)))

/-- The phase factor `e^{iπr²u}` of a horizontal displacement. -/
def phaseWeight (r u : ℝ) : ℂ := Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * (u : ℂ))

/-- The prefactor `4 sin²(πr²/2)`. -/
def sinSqC (r : ℝ) : ℂ := 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2

lemma norm_gaussWeight (r v : ℝ) : ‖gaussWeight r v‖ = Real.exp (-(Real.pi * r ^ 2 * v)) := by
  have h : (-(Real.pi * (r : ℂ) ^ 2 * (v : ℂ))) = ((-(Real.pi * r ^ 2 * v) : ℝ) : ℂ) := by
    push_cast; ring
  rw [gaussWeight, h, Complex.norm_exp, Complex.ofReal_re]

lemma norm_phaseWeight (r u : ℝ) : ‖phaseWeight r u‖ = 1 := by
  rw [phaseWeight,
    show (Real.pi : ℂ) * Complex.I * (r : ℂ) ^ 2 * (u : ℂ)
      = ((Real.pi * r ^ 2 * u : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-! ## The edges of the detours

The horizontal edge integrand is the `1`-form `K e^{iπr²z}/i` divided by `du`, the vertical edge
integrand is `K e^{iπr²z}` divided by `dv`. -/

/-- Horizontal edge integrand of `K(τ,z)e^{iπr²z}dz/i` at `z = u + iv` (so that the edge integral
is `∫ · du`). -/
def edgeH (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ) (τ : UpperHalfPlane)
    (u v : ℝ) : ℂ :=
  Work.Kernels.Kfun ℓ d τ (ofReImT u v) * (phaseWeight r u * gaussWeight r v) / Complex.I

/-- Vertical edge integrand of `K(τ,z)e^{iπr²z}dz/i` at `z = u + iv` (so that the edge integral
is `∫ · dv`). -/
def edgeV (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ) (τ : UpperHalfPlane)
    (u v : ℝ) : ℂ :=
  Work.Kernels.Kfun ℓ d τ (ofReImT u v) * (phaseWeight r u * gaussWeight r v)

lemma edgeH_eq (ℓ d r τ u v) :
    edgeH ℓ d r τ u v = edgeV ℓ d r τ u v / Complex.I := by
  rw [edgeH, edgeV]

/-! ## The pieces of the contour integral -/

/-- The part of the contour on the imaginary axis, with the two removed intervals
`I₁ = (t₀-A₁, t₀+A₁)` and `I₂ = (1/t₀-A₂, 1/t₀+A₂)` deleted.  With `A₂ = ξ₂ = 0` (the case
`t₀ > 1/√2`, where `1/t₀ ∈ I₁`) the second interval is empty. -/
def straightPart (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r t₀ A₁ A₂ : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  ∫ t in (Set.Ioi (0 : ℝ)) \
      (Set.Ioo (t₀ - A₁) (t₀ + A₁) ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)),
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * gaussWeight r t

/-- The right detour: the three sides of `[0,ξ₁] × [t₀-A₁, t₀+A₁]` traversed upwards, normalised
by `dz/i`. -/
def detourRight (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r t₀ A₁ ξ₁ : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  (∫ u in Set.Ioo (0 : ℝ) ξ₁, edgeH ℓ d r τ u (t₀ - A₁))
  + (∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁), edgeV ℓ d r τ ξ₁ v)
  - (∫ u in Set.Ioo (0 : ℝ) ξ₁, edgeH ℓ d r τ u (t₀ + A₁))

/-- The left detour: the three sides of `[-ξ₂,0] × [1/t₀-A₂, 1/t₀+A₂]` traversed upwards,
normalised by `dz/i` (note `dz = -du` on the horizontal edges). -/
def detourLeft (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r t₀ A₂ ξ₂ : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  (∫ u in Set.Ioo (0 : ℝ) ξ₂, edgeH ℓ d r τ (-u) (t₀⁻¹ - A₂))
  + (∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂), edgeV ℓ d r τ (-ξ₂) v)
  - (∫ u in Set.Ioo (0 : ℝ) ξ₂, edgeH ℓ d r τ (-u) (t₀⁻¹ + A₂))

/-- **The transform continued along the indented contour.**  The imaginary axis with the two
intervals `I₁`, `I₂` replaced by the detours `detourRight`, `detourLeft`.  For `Re τ < 1` (the
pole `τ - 1` of `z ↦ K(τ,z)` has negative real part) the two rectangles `R₁`, `R₂` are pole-free
and Cauchy–Goursat identifies this with `kernelTransform`; for `τ` in a small ball around
`1 + i t₀` the contour is pole-free (as a curve in `z`) and the integral is holomorphic in `τ`. -/
def contourH (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r t₀ A₁ ξ₁ A₂ ξ₂ : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  sinSqC r * (straightPart ℓ d r t₀ A₁ A₂ τ + detourRight ℓ d r t₀ A₁ ξ₁ τ
    + detourLeft ℓ d r t₀ A₂ ξ₂ τ)

lemma contourH_def (ℓ d r t₀ A₁ ξ₁ A₂ ξ₂ τ) : contourH ℓ d r t₀ A₁ ξ₁ A₂ ξ₂ τ
    = sinSqC r * (straightPart ℓ d r t₀ A₁ A₂ τ + detourRight ℓ d r t₀ A₁ ξ₁ τ
      + detourLeft ℓ d r t₀ A₂ ξ₂ τ) := rfl

end Work.Asymptotics
