import Mathlib

/-! Guidance from the project lead (the requester):

# Guidance (project lead) — saddleModelPsi (pure calculus in ℂ; the lead's construction, just formalise it)
This is the local model of the n = 2 movie at a SADDLE (f = c + Re z² in a Morse chart; flow lines of the model field X₀ = (u,−v)/(2|z|²) are
{Im z² = const}). EXPLICIT construction:
  σ(s, w) := s + μ(|w|)·(−η − s),  with μ : ℝ → [0,1] smooth, μ = 0 on [0, 2 − 4δ], μ = 1 on [2 − 2δ, ∞);
  φ(ζ) := σ(Re ζ, Im ζ) + i·Im ζ;      Ψ(z) := z · sqrt( φ(z²) / z² )   (principal sqrt),  Ψ(z) := z near 0.
Facts to prove:
- The ratio φ(ζ)/ζ = (σ + iw)/(s + iw) is 1 in the core (μ = 0) and, on the window |s| ≤ η, |w| ≤ 2 (outside a small ball, where μ can be > 0 only
  if |w| ≥ 2 − 4δ ≥ 1), it lies in the right half-plane (|w| ≥ 1 dominates |s|, |σ| ≤ η < 1/10). So the principal sqrt is smooth there and Ψ is
  smooth. Ψ = id wherever μ(|Im z²|) = 0, in particular near 0. To make Ψ smooth on all of ℂ, multiply μ by a cutoff that vanishes outside the
  window; only the window matters.
- Ψ(z)² = φ(z²), so Im Ψ(z)² = Im z² = w.
- LEVEL INJECTIVITY: on one level (same s), Ψ z = Ψ z' ⇒ Ψ² equal ⇒ w = w' ⇒ z² = z'² (same s and w) ⇒ z' = ±z; and Ψ(−z) = −Ψ(z) ≠ Ψ(z)
  since Ψ(z) ≠ 0 for z ≠ 0 (φ(ζ) = 0 forces w = 0 and σ(s, 0) = s = 0, i.e. z = 0).
- COLLAR: for |w| ≥ 2 − 2δ, σ = −η, so Ψ(z)² = −η + iw, and Ψ(z) = z·sqrt(ratio) with the ratio in the right half-plane, so Re(Ψ z · z̄) > 0.
- IMMERSION along the level: the level tangent at z is i·z̄ (the gradient of Re z² is 2z̄); d(Ψ²) = dφ(z²)·2z dz; along the level ds = 0 and
  dw ≠ 0 (z ≠ 0), so d(Ψ²) has imaginary part dw ≠ 0, hence 2Ψ dΨ ≠ 0, hence dΨ ≠ 0.
-/

namespace Work.Drive.N2

open scoped ContDiff Topology
open Filter

/-! ## The smooth plateau `μ` and the plateau `M` in the variable `w = Im ζ`

The model function of the saddle `f = c + Re z²` has flow lines `{Im z² = const}`; the movie is built by
moving the level coordinate `s = Re z²` to `σ (s, w) = s + M w · (-η - s)`, where `M` is a smooth
plateau which is `0` for `|w| ≤ 2 - 4δ` (so the map is the identity near `0` and on the core of the
window) and `1` for `2 - 2δ ≤ |w| ≤ 2` (so the map is the flow-foot in the collar). -/

/-- The smooth plateau `μ` of the saddle model: `0` on `(-∞, 2 - 4δ]`, `1` on `[2 - 2δ, 2]`. -/
noncomputable def saddleMu (δ t : ℝ) : ℝ :=
  Real.smoothTransition ((t - (2 - 4 * δ)) / (2 * δ)) * (1 - Real.smoothTransition (t - 2))

/-- `M w = μ |w|`: the absolute value is harmless because `μ` vanishes on a neighbourhood of `0`
(and the model is only ever used with `δ < 1/2`). -/
noncomputable def saddleM (δ w : ℝ) : ℝ := saddleMu δ |w|

lemma contDiff_saddleMu (δ : ℝ) : ContDiff ℝ ∞ (saddleMu δ) := by
  change ContDiff ℝ ∞ (fun t : ℝ =>
    Real.smoothTransition ((t - (2 - 4 * δ)) / (2 * δ)) * (1 - Real.smoothTransition (t - 2)))
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition ((t - (2 - 4 * δ)) / (2 * δ))) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (t - 2)) :=
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  exact h1.mul ((contDiff_const (c := (1:ℝ))).sub h2)

lemma saddleMu_eq_zero_of_le {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ 2 - 4 * δ) :
    saddleMu δ t = 0 := by
  have h : (t - (2 - 4 * δ)) / (2 * δ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [saddleMu, Real.smoothTransition.zero_of_nonpos h]
  ring

lemma saddleMu_eq_one {δ t : ℝ} (hδ : 0 < δ) (ht₁ : 2 - 2 * δ ≤ t) (ht₂ : t ≤ 2) :
    saddleMu δ t = 1 := by
  have h₁ : 1 ≤ (t - (2 - 4 * δ)) / (2 * δ) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * δ)]
    linarith
  have h₂ : t - 2 ≤ 0 := by linarith
  rw [saddleMu, Real.smoothTransition.one_of_one_le h₁, Real.smoothTransition.zero_of_nonpos h₂]
  norm_num

lemma saddleM_eq_zero_of_abs_le {δ w : ℝ} (hδ : 0 < δ) (hw : |w| ≤ 2 - 4 * δ) :
    saddleM δ w = 0 :=
  saddleMu_eq_zero_of_le hδ hw

lemma saddleM_zero {δ : ℝ} (hδ : 0 < δ) (h2 : 0 ≤ 2 - 4 * δ) : saddleM δ 0 = 0 :=
  saddleM_eq_zero_of_abs_le hδ (by simpa using h2)

lemma saddleM_eq_one_of_abs {δ w : ℝ} (hδ : 0 < δ) (hw₁ : 2 - 2 * δ ≤ |w|)
    (hw₂ : |w| ≤ 2) : saddleM δ w = 1 :=
  saddleMu_eq_one hδ hw₁ hw₂

lemma contDiff_saddleM {δ : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ) :
    ContDiff ℝ ∞ (saddleM δ) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  rcases eq_or_ne w 0 with rfl | hw
  · refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0:ℝ))) ?_
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) h2] with y hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    exact saddleM_eq_zero_of_abs_le hδ (le_of_lt hy)
  · have habs : ContDiffAt ℝ ∞ (fun y : ℝ => |y|) w := contDiffAt_id.abs hw
    exact (contDiff_saddleMu δ).contDiffAt.comp w habs

/-! ## The model map `φ` on the plane `ζ = z²` and the ratio `φ (z²) / z²` -/

/-- The level coordinate of the model: `σ (s, w) = s + M w · (-η - s)`. -/
noncomputable def saddleSigma (η δ : ℝ) (p : ℝ × ℝ) : ℝ := p.1 + saddleM δ p.2 * (-η - p.1)

lemma saddleSigma_apply (η δ s w : ℝ) : saddleSigma η δ (s, w) = s + saddleM δ w * (-η - s) := rfl

lemma contDiff_saddleSigma (η δ : ℝ) (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ) :
    ContDiff ℝ ∞ (saddleSigma η δ) := by
  have hM : ContDiff ℝ ∞ (fun p : ℝ × ℝ => saddleM δ p.2) :=
    (contDiff_saddleM hδ h2).comp contDiff_snd
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => -η - p.1) := contDiff_const.sub contDiff_fst
  exact contDiff_fst.add (hM.mul h1)

/-- In the collar `2 - 2δ ≤ |w| ≤ 2` the plateau equals one, so the level coordinate is `-η`. -/
lemma saddleSigma_eq_neg_eta {η δ s w : ℝ} (hδ : 0 < δ) (h₁ : 2 - 2 * δ ≤ |w|)
    (h₂ : |w| ≤ 2) : saddleSigma η δ (s, w) = -η := by
  rw [saddleSigma_apply, saddleM_eq_one_of_abs hδ h₁ h₂]
  ring

/-- The model map of the saddle movie: it keeps the level invariant `Im ζ` and moves the real part
`Re ζ` to `σ (Re ζ, Im ζ)`. -/
noncomputable def saddlePhi (η δ : ℝ) (ζ : ℂ) : ℂ :=
  ((saddleSigma η δ (ζ.re, ζ.im) : ℝ) : ℂ) + ((ζ.im : ℝ) : ℂ) * Complex.I

lemma contDiff_saddlePhi (η δ : ℝ) (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ) :
    ContDiff ℝ ∞ (saddlePhi η δ) := by
  have hpair : ContDiff ℝ ∞ (fun ζ : ℂ => (ζ.re, ζ.im)) :=
    (Complex.reCLM.prod Complex.imCLM).contDiff
  have h1 : ContDiff ℝ ∞ (fun ζ : ℂ => saddleSigma η δ (ζ.re, ζ.im)) :=
    (contDiff_saddleSigma η δ hδ h2).comp hpair
  have h2' : ContDiff ℝ ∞ (fun ζ : ℂ => ((saddleSigma η δ (ζ.re, ζ.im) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h1
  have h3 : ContDiff ℝ ∞ (fun ζ : ℂ => ((ζ.im : ℝ) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).mul contDiff_const
  exact h2'.add h3

lemma saddlePhi_im (η δ : ℝ) (ζ : ℂ) : (saddlePhi η δ ζ).im = ζ.im := by
  simp [saddlePhi, Complex.add_im]

lemma saddlePhi_re (η δ : ℝ) (ζ : ℂ) :
    (saddlePhi η δ ζ).re = saddleSigma η δ (ζ.re, ζ.im) := by
  simp [saddlePhi, Complex.add_re]

/-- A complex number written through its two coordinates, with a real shift: the algebraic
identity behind `saddlePhi_eq_sub`. -/
lemma ofReal_sub_add_im_mul_I (b : ℝ) (ζ : ℂ) :
    ((ζ.re - b : ℝ) : ℂ) + ((ζ.im : ℝ) : ℂ) * Complex.I = ζ - ((b : ℝ) : ℂ) := by
  rw [Complex.ofReal_sub]
  have h : ((ζ.re : ℝ) : ℂ) + ((ζ.im : ℝ) : ℂ) * Complex.I = ζ := Complex.re_add_im ζ
  linear_combination h

/-- `φ ζ = ζ - (M (Im ζ) · (η + Re ζ) : ℝ)`: the "displacement" of the model is a real number. -/
lemma saddlePhi_eq_sub (η δ : ℝ) (ζ : ℂ) :
    saddlePhi η δ ζ = ζ - ((saddleM δ ζ.im * (η + ζ.re) : ℝ) : ℂ) := by
  rw [saddlePhi]
  have hs : saddleSigma η δ (ζ.re, ζ.im) = ζ.re - saddleM δ ζ.im * (η + ζ.re) := by
    simp only [saddleSigma]; ring
  rw [hs]
  exact ofReal_sub_add_im_mul_I _ _

lemma saddlePhi_eq_self_of_abs_le {η δ : ℝ} (hδ : 0 < δ) {ζ : ℂ}
    (hζ : |ζ.im| ≤ 2 - 4 * δ) : saddlePhi η δ ζ = ζ := by
  have hM := saddleM_eq_zero_of_abs_le hδ hζ
  have hs : saddleSigma η δ (ζ.re, ζ.im) = ζ.re := by simp [saddleSigma, hM]
  rw [saddlePhi, hs, Complex.re_add_im]

lemma saddlePhi_zero {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 ≤ 2 - 4 * δ) :
    saddlePhi η δ 0 = 0 := by
  rw [saddlePhi, Complex.zero_re, Complex.zero_im]
  simp [saddleSigma, saddleM_zero hδ h2]

/-- `φ` vanishes only at `0` (the model has no other zero of the square root). -/
lemma saddlePhi_eq_zero_iff {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 ≤ 2 - 4 * δ) (ζ : ℂ) :
    saddlePhi η δ ζ = 0 ↔ ζ = 0 := by
  constructor
  · intro h
    have him : ζ.im = 0 := by rw [← saddlePhi_im η δ ζ, h, Complex.zero_im]
    have hsub := saddlePhi_eq_sub (η := η) (δ := δ) ζ
    rw [h] at hsub
    have hζ : ζ = ((saddleM δ ζ.im * (η + ζ.re) : ℝ) : ℂ) := (sub_eq_zero.mp hsub.symm)
    rw [hζ, him, saddleM_zero hδ h2, zero_mul, Complex.ofReal_zero]
  · rintro rfl
    exact saddlePhi_zero hδ h2

/-- The ratio `φ (z²)/z²`, extended by `1` at `0` (where `φ (z²) = z²`). -/
noncomputable def saddleRatio (η δ : ℝ) (z : ℂ) : ℂ :=
  if z = 0 then 1 else saddlePhi η δ (z ^ 2) / z ^ 2

lemma saddleRatio_mul_sq {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 ≤ 2 - 4 * δ) (z : ℂ) :
    saddleRatio η δ z * z ^ 2 = saddlePhi η δ (z ^ 2) := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [saddleRatio, if_pos rfl]
    simp [saddlePhi_zero hδ h2]
  · rw [saddleRatio, if_neg hz]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hz)

lemma saddleRatio_neg (η δ : ℝ) (z : ℂ) : saddleRatio η δ (-z) = saddleRatio η δ z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [saddleRatio]
  · have h1 : (-z) ^ 2 = z ^ 2 := neg_sq z
    have h2 : (-z) ≠ 0 := neg_ne_zero.mpr hz
    rw [saddleRatio, if_neg h2, saddleRatio, if_neg hz, h1]

lemma im_div_ofReal (a : ℝ) (ζ : ℂ) :
    (((a : ℂ) / ζ).im) = -a * ζ.im / Complex.normSq ζ := by
  rw [Complex.div_im, Complex.ofReal_im, Complex.ofReal_re]
  ring

/-- The imaginary part of the ratio is explicit: it vanishes only in the degenerate cases in which
the ratio itself equals `1`. -/
lemma saddleRatio_im (η δ : ℝ) (z : ℂ) (hz : z ≠ 0) :
    (saddleRatio η δ z).im
      = (saddleM δ (z ^ 2).im * (η + (z ^ 2).re)) * (z ^ 2).im / Complex.normSq (z ^ 2) := by
  rw [saddleRatio, if_neg hz, saddlePhi_eq_sub, sub_div, div_self (pow_ne_zero 2 hz),
    Complex.sub_im, Complex.one_im, im_div_ofReal]
  ring

lemma saddleRatio_eq_one_of_coeff_zero {η δ : ℝ} {z : ℂ} (hz : z ≠ 0)
    (ha : saddleM δ (z ^ 2).im * (η + (z ^ 2).re) = 0) : saddleRatio η δ z = 1 := by
  rw [saddleRatio, if_neg hz, saddlePhi_eq_sub, ha, Complex.ofReal_zero, sub_zero,
    div_self (pow_ne_zero 2 hz)]

/-- The ratio never lies on the branch cut `(-∞, 0]` of the principal square root: it is `1`
whenever it is real. -/
lemma saddleRatio_mem_slitPlane {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 ≤ 2 - 4 * δ) (z : ℂ) :
    saddleRatio η δ z ∈ Complex.slitPlane := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [saddleRatio, if_pos rfl, Complex.mem_slitPlane_iff]
    left; norm_num
  · rcases eq_or_ne (saddleM δ (z ^ 2).im * (η + (z ^ 2).re)) 0 with ha | ha
    · rw [Complex.mem_slitPlane_iff]
      left
      rw [saddleRatio_eq_one_of_coeff_zero hz ha]
      norm_num
    · rw [Complex.mem_slitPlane_iff]
      right
      rw [saddleRatio_im η δ z hz]
      have hN : Complex.normSq (z ^ 2) ≠ 0 := by
        rw [Complex.normSq_eq_norm_sq]
        exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (pow_ne_zero 2 hz))
      have hw : (z ^ 2).im ≠ 0 := by
        intro hw0
        exact ha (by rw [hw0, saddleM_zero hδ h2, zero_mul])
      exact div_ne_zero (mul_ne_zero ha hw) hN

/-- The multiplicative form of the ratio, whose smoothness is manifest (the only inverse is the
inverse of the real number `‖z²‖`). -/
noncomputable def saddleRatioAux (η δ : ℝ) (z : ℂ) : ℂ :=
  saddlePhi η δ (z ^ 2) * (z ^ 2)⁻¹

lemma saddleRatioAux_eq {η δ : ℝ} {z : ℂ} (hz : z ≠ 0) :
    saddleRatioAux η δ z = saddleRatio η δ z := by
  rw [saddleRatioAux, saddleRatio, if_neg hz, div_eq_mul_inv]

lemma contDiffAt_saddleRatio {η δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (z : ℂ) :
    ContDiffAt ℝ ∞ (saddleRatio η δ) z := by
  have h2 : (0:ℝ) < 2 - 4 * δ := by linarith
  rcases eq_or_ne z 0 with rfl | hz
  · refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (1:ℂ))) ?_
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by linarith : (0:ℝ) < (2 - 4 * δ) / 4)]
      with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [saddleRatio, if_pos rfl]
    · rw [saddleRatio, if_neg hy0]
      have h3 : |(y ^ 2).im| ≤ 2 - 4 * δ := by
        have h4 : ‖y ^ 2‖ = ‖y‖ ^ 2 := norm_pow y 2
        have h5 : ‖y ^ 2‖ < 2 - 4 * δ := by
          rw [h4]
          have h6 : (0:ℝ) < (2 - 4 * δ) / 4 := by linarith
          have h7 : ‖y‖ * ‖y‖ < (2 - 4 * δ) / 4 * ((2 - 4 * δ) / 4) :=
            by nlinarith [norm_nonneg y, hy, h6]
          have h8 : (2 - 4 * δ) / 4 * ((2 - 4 * δ) / 4) < 2 - 4 * δ := by nlinarith
          nlinarith [h7, h8, pow_two ‖y‖]
        exact le_trans (Complex.abs_im_le_norm _) h5.le
      rw [saddlePhi_eq_self_of_abs_le hδ h3, div_self (pow_ne_zero 2 hy0)]
  · have haux : ContDiffAt ℝ ∞ (saddleRatioAux η δ) z := by
      unfold saddleRatioAux
      exact ((contDiff_saddlePhi η δ hδ h2).contDiffAt.comp z (contDiffAt_id.pow 2)).mul
        ((contDiffAt_id.pow 2).inv (pow_ne_zero 2 hz))
    have heq : (saddleRatio η δ) =ᶠ[𝓝 z] (saddleRatioAux η δ) := by
      filter_upwards [(isOpen_ne (x := (0:ℂ))).mem_nhds hz] with y hy
      exact (saddleRatioAux_eq hy).symm
    exact haux.congr_of_eventuallyEq heq

lemma contDiff_saddleRatio (η δ : ℝ) (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) :
    ContDiff ℝ ∞ (saddleRatio η δ) := by
  rw [contDiff_iff_contDiffAt]
  exact contDiffAt_saddleRatio hδ hδ₂

/-! ## The model map `Ψ (z) = z · √(φ (z²)/z²)` and its basic properties -/

/-- The saddle model map: `Ψ z = z · √(φ (z²)/z²)`, with the principal square root. -/
noncomputable def saddlePsi (η δ : ℝ) (z : ℂ) : ℂ := z * Complex.sqrt (saddleRatio η δ z)

lemma complex_sqrt_sq (x : ℂ) : Complex.sqrt x ^ 2 = x := by
  simp only [Complex.sqrt]
  exact Complex.cpow_nat_inv_pow x (by norm_num)

/-- The principal square root is real smooth on the slit plane. -/
lemma contDiffAt_sqrt_of_mem_slitPlane {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.sqrt w := by
  have h1 : ContDiffAt ℂ ∞ (fun z : ℂ => Complex.exp (Complex.log z / 2)) w :=
    Complex.contDiff_exp.contDiffAt.comp w ((Complex.contDiffAt_log hw).div_const 2)
  have h2 : ContDiffAt ℝ ∞ (fun z : ℂ => Complex.exp (Complex.log z / 2)) w :=
    h1.restrict_scalars ℝ
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Complex.isOpen_slitPlane.mem_nhds hw] with z hz
  exact sqrt_eq_exp (fun h0 => Complex.zero_notMem_slitPlane (h0 ▸ hz))

lemma contDiff_saddlePsi (η δ : ℝ) (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) :
    ContDiff ℝ ∞ (saddlePsi η δ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have h2 : (0:ℝ) < 2 - 4 * δ := by linarith
  have hsqrt : ContDiffAt ℝ ∞ (fun y : ℂ => Complex.sqrt (saddleRatio η δ y)) z :=
    (contDiffAt_sqrt_of_mem_slitPlane (saddleRatio_mem_slitPlane hδ (le_of_lt h2) z)).comp z
      (contDiffAt_saddleRatio hδ hδ₂ z)
  exact contDiffAt_id.mul hsqrt

lemma saddlePsi_neg (η δ : ℝ) (z : ℂ) : saddlePsi η δ (-z) = -saddlePsi η δ z := by
  rw [saddlePsi, saddlePsi, saddleRatio_neg, neg_mul]

lemma saddlePsi_sq {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 ≤ 2 - 4 * δ) (z : ℂ) :
    saddlePsi η δ z ^ 2 = saddlePhi η δ (z ^ 2) := by
  rw [saddlePsi, mul_pow, complex_sqrt_sq, mul_comm (z ^ 2), saddleRatio_mul_sq hδ h2]

lemma saddlePsi_sq_im {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 ≤ 2 - 4 * δ) (z : ℂ) :
    (saddlePsi η δ z ^ 2).im = (z ^ 2).im := by
  rw [saddlePsi_sq hδ h2, saddlePhi_im]

lemma saddlePsi_eq_zero_iff {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 ≤ 2 - 4 * δ) (z : ℂ) :
    saddlePsi η δ z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hsq : saddlePsi η δ z ^ 2 = 0 := by rw [h]; ring
    rw [saddlePsi_sq hδ h2] at hsq
    exact sq_eq_zero_iff.mp ((saddlePhi_eq_zero_iff hδ h2 (z ^ 2)).mp hsq)
  · rintro rfl
    simp [saddlePsi]

/-- `Ψ` is injective on every level set `{Re z² = const}`. -/
lemma saddlePsi_injOn_level {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 ≤ 2 - 4 * δ) {z z' : ℂ}
    (hre : (z ^ 2).re = (z' ^ 2).re) (h : saddlePsi η δ z = saddlePsi η δ z') : z = z' := by
  have him : (z ^ 2).im = (z' ^ 2).im := by
    rw [← saddlePsi_sq_im hδ h2 z, ← saddlePsi_sq_im hδ h2 z', h]
  have hsq : z ^ 2 = z' ^ 2 := Complex.ext hre him
  have hfac : (z - z') * (z + z') = 0 := by
    have hh : (z - z') * (z + z') = z ^ 2 - z' ^ 2 := by ring
    rw [hh, hsq, sub_self]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact sub_eq_zero.mp h1
  · have hz' : z' = -z := eq_neg_of_add_eq_zero_right h1
    rw [hz', saddlePsi_neg] at h
    have hzero : saddlePsi η δ z = 0 := by
      have hsum : saddlePsi η δ z + saddlePsi η δ z = 0 := by
        nth_rewrite 2 [h]
        exact add_neg_cancel _
      exact add_self_eq_zero.mp hsum
    have hzz : z = 0 := (saddlePsi_eq_zero_iff hδ h2 z).mp hzero
    rw [hz', hzz, neg_zero]

/-- `Ψ` is the identity on the ball of radius `(2 - 4δ)/4`, where the plateau vanishes. -/
lemma saddlePsi_eq_self_of_norm_lt {η δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) {z : ℂ}
    (hz : ‖z‖ < (2 - 4 * δ) / 4) : saddlePsi η δ z = z := by
  have h2 : (0:ℝ) < 2 - 4 * δ := by linarith
  have h3 : |(z ^ 2).im| ≤ 2 - 4 * δ := by
    have h4 : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
    have h5 : ‖z ^ 2‖ < 2 - 4 * δ := by
      rw [h4]
      have h6 : (0:ℝ) < (2 - 4 * δ) / 4 := by linarith
      have h7 : ‖z‖ * ‖z‖ < (2 - 4 * δ) / 4 * ((2 - 4 * δ) / 4) :=
        by nlinarith [norm_nonneg z, hz, h6]
      have h8 : (2 - 4 * δ) / 4 * ((2 - 4 * δ) / 4) < 2 - 4 * δ := by nlinarith
      nlinarith [h7, h8, pow_two ‖z‖]
    exact le_trans (Complex.abs_im_le_norm _) h5.le
  have hphi : saddlePhi η δ (z ^ 2) = z ^ 2 := saddlePhi_eq_self_of_abs_le hδ h3
  rw [saddlePsi]
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · have hr : saddleRatio η δ z = 1 := by
      have h6 : saddleRatio η δ z * z ^ 2 = z ^ 2 := by
        rw [saddleRatio_mul_sq hδ (le_of_lt h2), hphi]
      exact mul_right_cancel₀ (pow_ne_zero 2 hz0) (by rw [h6, one_mul])
    rw [hr, Complex.sqrt_one, mul_one]

/-- In the collar `2 - 2δ ≤ |Im z²| ≤ 2` the model is the flow-foot of the level `-η`, and it keeps
the positive side of the level direction. -/
lemma saddlePsi_collar {η δ : ℝ} (hη : 0 < η) (hη' : η < 1/10) (hδ : 0 < δ) (hδ' : δ < 1/10)
    {z : ℂ} (hs : |(z ^ 2).re| ≤ η) (hw₁ : 2 - 2 * δ ≤ |(z ^ 2).im|)
    (hw₂ : |(z ^ 2).im| ≤ 2) :
    saddlePsi η δ z ^ 2 = (-η : ℂ) + ((z ^ 2).im : ℂ) * Complex.I ∧
      0 < (saddlePsi η δ z * (starRingEnd ℂ) z).re := by
  have h2 : (0:ℝ) < 2 - 4 * δ := by linarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hw₁
    simp at hw₁
    linarith
  have hsigma : saddleSigma η δ ((z ^ 2).re, (z ^ 2).im) = -η :=
    saddleSigma_eq_neg_eta hδ hw₁ hw₂
  have hre : 0 < (saddleRatio η δ z).re := by
    rw [saddleRatio, if_neg hz0, Complex.div_re, saddlePhi_re, saddlePhi_im, hsigma, ← add_div]
    apply div_pos
    · have hs' := abs_le.mp hs
      have h1 : -η * η ≤ -η * (z ^ 2).re := by nlinarith [hs'.2, hη]
      have hδ18 : (1.8:ℝ) ≤ 2 - 2 * δ := by linarith
      have hw18 : (1.8:ℝ) ≤ |(z ^ 2).im| := le_trans hδ18 hw₁
      have h3 : (1.8:ℝ) * 1.8 ≤ (z ^ 2).im * (z ^ 2).im := by
        have h4 : (1.8:ℝ) * 1.8 ≤ |(z ^ 2).im| * |(z ^ 2).im| :=
          by nlinarith [hw18, abs_nonneg ((z ^ 2).im)]
        rwa [abs_mul_abs_self] at h4
      have h5 : η * η < (1.8:ℝ) * 1.8 := by nlinarith
      linarith
    · exact Complex.normSq_pos.mpr (pow_ne_zero 2 hz0)
  have hsqrt : 0 < (Complex.sqrt (saddleRatio η δ z)).re := by
    rw [Complex.sqrt, Complex.cpow_inv_two_re, Real.sqrt_pos]
    linarith [hre, norm_nonneg (saddleRatio η δ z)]
  constructor
  · rw [saddlePsi_sq hδ (le_of_lt h2), saddlePhi, hsigma]
    simp
  · rw [saddlePsi]
    have hconv : z * Complex.sqrt (saddleRatio η δ z) * (starRingEnd ℂ) z
        = Complex.sqrt (saddleRatio η δ z) * ((Complex.normSq z : ℝ) : ℂ) := by
      rw [show z * Complex.sqrt (saddleRatio η δ z) * (starRingEnd ℂ) z
          = Complex.sqrt (saddleRatio η δ z) * (z * (starRingEnd ℂ) z) by ring]
      rw [Complex.mul_conj]
    rw [hconv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hnorm : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    nlinarith [hsqrt, hnorm]

/-! ## The immersion of `Ψ` along the level curves `{Re z² = const}` -/

lemma fderiv_sq_apply (w v : ℂ) : (fderiv ℝ (fun z : ℂ => z ^ 2) w) v = 2 * w * v := by
  have h := hasFDerivAt_pow (𝕜 := ℝ) 2 (x := w)
  rw [h.fderiv]
  simp

lemma fderiv_im_sq_apply (z v : ℂ) :
    (fderiv ℝ (fun y : ℂ => (y ^ 2).im) z) v = (2 * z * v).im := by
  have hsq : HasFDerivAt (fun y : ℂ => y ^ 2) ((2 * z) • ContinuousLinearMap.id ℝ ℂ) z := by
    simpa [two_nsmul, pow_one] using hasFDerivAt_pow (𝕜 := ℝ) 2 (x := z)
  have him : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM (z ^ 2) := Complex.imCLM.hasFDerivAt
  have h : HasFDerivAt (fun y : ℂ => (y ^ 2).im)
      (Complex.imCLM ∘SL ((2 * z) • ContinuousLinearMap.id ℝ ℂ)) z := him.comp z hsq
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply]

/-- `Im (2 z · (i z̄)) = 2 ‖z‖²`: the imaginary part of the derivative of `Im z²` in the level
direction `i z̄`. -/
lemma im_of_sq_dir (z : ℂ) :
    (2 * z * (Complex.I * (starRingEnd ℂ) z)).im = 2 * Complex.normSq z := by
  rw [show 2 * z * (Complex.I * (starRingEnd ℂ) z)
      = 2 * (Complex.I * (z * (starRingEnd ℂ) z)) by ring]
  rw [Complex.mul_conj]
  simp

/-- `Ψ` is immersive along the level curves at every nonzero point of the window. -/
theorem fderiv_saddlePsi_ne_zero {η δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (z : ℂ)
    (hz : z ≠ 0) :
    fderiv ℝ (saddlePsi η δ) z (Complex.I * (starRingEnd ℂ) z) ≠ 0 := by
  have h2 : (0:ℝ) < 2 - 4 * δ := by linarith
  have hP : ContDiff ℝ ∞ (saddlePsi η δ) := contDiff_saddlePsi η δ hδ hδ₂
  have hΦ : ContDiff ℝ ∞ (saddlePhi η δ) := contDiff_saddlePhi η δ hδ h2
  have hsq : ∀ y : ℂ, saddlePsi η δ y ^ 2 = saddlePhi η δ (y ^ 2) :=
    fun y => saddlePsi_sq hδ (le_of_lt h2) y
  have him : ∀ ζ : ℂ, (saddlePhi η δ ζ).im = ζ.im := fun ζ => saddlePhi_im η δ ζ
  intro h0
  set v : ℂ := Complex.I * (starRingEnd ℂ) z with hv
  have hdP : DifferentiableAt ℝ (saddlePsi η δ) z := (hP.differentiable (by simp)).differentiableAt
  have hdF : DifferentiableAt ℝ (fun y : ℂ => saddlePhi η δ (y ^ 2)) z :=
    (hΦ.differentiable (by simp)).differentiableAt.comp z ((differentiableAt_id).pow 2)
  have hstep1 : (fderiv ℝ (fun y : ℂ => (saddlePsi η δ y) ^ 2) z) v = 0 := by
    have hd2 : DifferentiableAt ℝ (fun w : ℂ => w ^ 2) (saddlePsi η δ z) :=
      (differentiableAt_id).pow 2
    rw [show (fderiv ℝ (fun y : ℂ => (saddlePsi η δ y) ^ 2) z) v
        = (fderiv ℝ ((fun w : ℂ => w ^ 2) ∘ (saddlePsi η δ)) z) v from rfl,
      fderiv_comp z hd2 hdP, ContinuousLinearMap.comp_apply, fderiv_sq_apply]
    rw [h0]
    ring
  have hstep2 : (fderiv ℝ (fun y : ℂ => saddlePhi η δ (y ^ 2)) z) v = 0 := by
    have hfun : (fun y : ℂ => (saddlePsi η δ y) ^ 2) = fun y : ℂ => saddlePhi η δ (y ^ 2) :=
      funext hsq
    rwa [hfun] at hstep1
  have hstep3 : (fderiv ℝ (fun y : ℂ => (saddlePhi η δ (y ^ 2)).im) z) v = 0 := by
    have hcomp := (Complex.imCLM.hasFDerivAt).comp z hdF.hasFDerivAt
    have h3 : fderiv ℝ (fun y : ℂ => (saddlePhi η δ (y ^ 2)).im) z
        = Complex.imCLM ∘SL fderiv ℝ (fun y : ℂ => saddlePhi η δ (y ^ 2)) z := hcomp.fderiv
    rw [h3, ContinuousLinearMap.comp_apply, hstep2, map_zero]
  have hstep4 : (fderiv ℝ (fun y : ℂ => (y ^ 2).im) z) v = 0 := by
    have hfun : (fun y : ℂ => (saddlePhi η δ (y ^ 2)).im) = fun y : ℂ => (y ^ 2).im :=
      funext fun y => him (y ^ 2)
    rwa [hfun] at hstep3
  have hcalc : (2 * z * v).im = 0 := by
    rw [← fderiv_im_sq_apply z v, hstep4]
  rw [hv, im_of_sq_dir] at hcalc
  have hpos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  linarith

end Work.Drive.N2

namespace Work.Drive.N2

/-- The saddle model map for the level-separating movie: on the saddle window `R = {|Re z²| ≤ η, |Im z²| ≤ 2}` a smooth
`Ψ : ℂ → ℂ` which is the identity near `0`, injective on every level `Re z² = const`, equal to the flow-foot on level `-η`
in the collar `|Im z²| ≥ 2 - 2δ`, and immersive along levels. -/
theorem saddleModelPsi (η δ : ℝ) (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10) :
    ∃ Ψ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      (∃ r₀ : ℝ, 0 < r₀ ∧ ∀ z : ℂ, ‖z‖ < r₀ → Ψ z = z) ∧
      (∀ z z' : ℂ, |(z ^ 2).re| ≤ η → |(z ^ 2).im| ≤ 2 → |(z' ^ 2).re| ≤ η → |(z' ^ 2).im| ≤ 2 →
        (z ^ 2).re = (z' ^ 2).re → Ψ z = Ψ z' → z = z') ∧
      (∀ z : ℂ, |(z ^ 2).re| ≤ η → 2 - 2 * δ ≤ |(z ^ 2).im| → |(z ^ 2).im| ≤ 2 →
        Ψ z ^ 2 = (-η : ℂ) + ((z ^ 2).im : ℂ) * Complex.I ∧ 0 < (Ψ z * (starRingEnd ℂ) z).re) ∧
      (∀ z : ℂ, z ≠ 0 → |(z ^ 2).re| ≤ η → |(z ^ 2).im| ≤ 2 →
        fderiv ℝ Ψ z (Complex.I * (starRingEnd ℂ) z) ≠ 0) := by
  have h2 : (0:ℝ) < 2 - 4 * δ := by linarith
  have hδ₂ : δ < 1 / 2 := by linarith
  refine ⟨saddlePsi η δ, contDiff_saddlePsi η δ hδ hδ₂, ?_, ?_, ?_, ?_⟩
  · exact ⟨(2 - 4 * δ) / 4, by linarith,
      fun z hz => saddlePsi_eq_self_of_norm_lt hδ hδ₂ hz⟩
  · intro z z' _ _ _ _ hre h
    exact saddlePsi_injOn_level hδ (le_of_lt h2) hre h
  · intro z hs hw₁ hw₂
    exact saddlePsi_collar hη hη' hδ hδ' hs hw₁ hw₂
  · intro z hz _ _
    exact fderiv_saddlePsi_ne_zero hδ hδ₂ z hz

end Work.Drive.N2
