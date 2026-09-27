import Mathlib
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.mobius_lowerProfile

namespace Work.Drive.N2Lead

/-- For complex numbers `w, v`: `(conj w * v).im = w.re * v.im - w.im * v.re`. -/
private lemma im_conj_mul_im (w v : ℂ) : (star w * v).im = w.re * v.im - w.im * v.re := by
  simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

/-- The imaginary part of the bridge rate `conj (z φ - 1) · z'(φ)` of the polar curve
`z φ = r φ · exp (i φ)`, with `z'` replaced by the value `(d + i r) · exp (i φ)`:
`Im (conj (z φ - 1) z'(φ)) = r² - r cos φ - d sin φ` (here `d = deriv r φ`). -/
private lemma polar_rate_im (r d φ : ℝ) :
    (star (((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) - 1)) *
      (((d : ℂ) + (r : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I))).im
    = r ^ 2 - r * Real.cos φ - d * Real.sin φ := by
  have hE : Complex.exp ((φ : ℂ) * Complex.I) = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [im_conj_mul_im, hE]
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq φ]

/-- Derivative of the polar curve `ψ ↦ r ψ · exp (i ψ)` of a differentiable radial profile. -/
private lemma deriv_polar_exp {r : ℝ → ℝ} (hdiff : Differentiable ℝ r) (φ : ℝ) :
    deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) φ
      = (((deriv r φ : ℝ) : ℂ) + (r φ : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I) := by
  have h1 : HasDerivAt (fun ψ : ℝ => (r ψ : ℂ)) (((deriv r φ : ℝ)) : ℂ) φ :=
    HasDerivAt.ofReal_comp (f := r) (hdiff.differentiableAt.hasDerivAt)
  have hcos : HasDerivAt (fun ψ : ℝ => (Real.cos ψ : ℂ)) (((-Real.sin φ : ℝ)) : ℂ) φ :=
    (Real.hasDerivAt_cos φ).ofReal_comp
  have hsin : HasDerivAt (fun ψ : ℝ => (Real.sin ψ : ℂ)) (((Real.cos φ : ℝ)) : ℂ) φ :=
    (Real.hasDerivAt_sin φ).ofReal_comp
  have h2 : HasDerivAt (fun ψ : ℝ => (Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I)
      (((-Real.sin φ : ℝ) : ℂ) + ((Real.cos φ : ℝ) : ℂ) * Complex.I) φ :=
    hcos.add (hsin.mul_const Complex.I)
  have hfun : (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
      = (fun ψ : ℝ => (r ψ : ℂ)) * (fun ψ : ℝ => (Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I) := by
    funext ψ
    rw [Pi.mul_apply, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h4 := h1.mul h2
  rw [hfun, h4.deriv]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Complex.ofReal_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

open scoped Manifold ContDiff Topology in
/-- **The *bridge* rate row of the upper certificate** (`NOTES_LEAD_saddlePacket.md` §4.3: "Bridge: `r² − (r cos φ + r′ sin φ) ≥ r(r − 1) > 0`").  For the polar curve `z φ = r φ · exp (i φ)` of a radial profile `r` that is smooth, positive, **even**, and on the *bridge zone* `[0, φE]` (`φE = Work.Drive.N2Lead.mobiusPhiE η m = arg √(-η + i m)`, the argument of the endpoint `E₁` of the pinned arc) satisfies `√(η² + m²) ≤ r φ ^ 2`, and `deriv r ≤ 0`, the angular rate about the centre `1` is **positive** on the bridge zone:

    `0 < Im (conj (z φ - 1) · z'(φ))`,   `|φ| ≤ φE`.

This is the `hrate` obligation of `Work.Drive.N2Lead.isCertifiedAt_of_starRegions` about the centre `1` for the points of the upper level drawn by `A ∘ foot` (whose pictures lie on the polar curve of `Work.Drive.N2Lead.mobius_lowerProfile`, whose bridge-zone rows are exactly `hlo`, `hmono`, `hrev`).  Route: with `z φ = r φ e^{iφ}`, `z' = (r' + i r) e^{iφ}`, so
`Im (conj (z φ - 1) z'(φ)) = Im (r(r' + i r) - (r' + i r) e^{iφ}) = r² - r cos φ - r' sin φ = r (r - cos φ) - r' sin φ`,
and `r(r - cos φ) ≥ r (r - 1) > 0` because `r φ ^ 2 ≥ √(η² + m²) > 1 ≥ cos φ` (`m > 1`), while `- r' sin φ ≥ 0` on the bridge zone: for `φ ∈ [0, φE]` this is `deriv r ≤ 0` with `sin φ ≥ 0`; for `φ ∈ [-φE, 0]` it follows from the evenness of `r` (`deriv r` is odd) with `sin φ ≤ 0`.  Nothing about the arcs (`φ ∈ [φE, π - φE]`) is claimed: there `r` realises the hyperbola branch and the model piece of the picture takes over.

The only fact used besides the hypotheses is `0 ≤ φE ≤ π/2` (for the sign of `sin`): that is `Work.Drive.N2Lead.mobiusPhiE_mem_Icc` (or `leadProfile_phiE` in `Drive/N2Lead/mobius_lowerProfile.lean`), which is unconditional for `η, m > 0` — the prover may need to import its module. -/
theorem polarBridgeRate {η m : ℝ} (hη : 0 < η) (hm : 1 < m)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrev : ∀ φ : ℝ, r (-φ) = r φ)
    (hlo : ∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE η m),
      Real.sqrt (η ^ 2 + m ^ 2) ≤ r φ ^ 2)
    (hmono : ∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE η m), deriv r φ ≤ 0)
    {φ : ℝ} (hφ : |φ| ≤ Work.Drive.N2Lead.mobiusPhiE η m) :
    0 < (star ((r φ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) - (1 : ℂ))
          * deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) φ).im := by
  have hm0 : 0 < m := by linarith
  obtain ⟨-, -, hφElt⟩ := leadProfile_phiE hη hm0
  set φE := Work.Drive.N2Lead.mobiusPhiE η m with hφEdef
  have hφE_le : φE ≤ Real.pi / 2 := le_of_lt hφElt
  have hle : φ ≤ φE := (abs_le.mp hφ).2
  have hge : -φE ≤ φ := (abs_le.mp hφ).1
  -- `√(η² + m²) > 1`, hence `r φ > 1` on the bridge zone.
  have hsqrt_gt1 : 1 < Real.sqrt (η ^ 2 + m ^ 2) := by
    rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith [sq_nonneg η, hm]
  have hlo_abs : Real.sqrt (η ^ 2 + m ^ 2) ≤ r φ ^ 2 := by
    have hψmem : |φ| ∈ Set.Icc (0:ℝ) φE := ⟨abs_nonneg φ, hφ⟩
    have h := hlo |φ| hψmem
    have hrφabs : r |φ| = r φ := by
      rcases le_total 0 φ with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, hrev]
    rwa [hrφabs] at h
  have hrφ_gt1 : 1 < r φ := by
    have h1 : 1 < r φ ^ 2 := lt_of_lt_of_le hsqrt_gt1 hlo_abs
    nlinarith [hrpos φ, h1]
  -- `- (deriv r φ) · sin φ ≥ 0` on the bridge zone.
  have hB : deriv r φ * Real.sin φ ≤ 0 := by
    rcases le_total 0 φ with hφ0 | hφ0
    · have hs : 0 ≤ Real.sin φ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [hle, hφE_le, Real.pi_pos])
      have hd : deriv r φ ≤ 0 := hmono φ ⟨hφ0, hle⟩
      exact mul_nonpos_of_nonpos_of_nonneg hd hs
    · have hneg0 : 0 ≤ -φ := by linarith
      have hnegle : -φ ≤ φE := by linarith
      have hd : 0 ≤ deriv r φ := by
        have hdψ : deriv r (-φ) ≤ 0 := hmono (-φ) ⟨hneg0, hnegle⟩
        have hodd : deriv r φ = - deriv r (-φ) := by
          have h1 : (fun x : ℝ => r (-x)) = r := funext fun x => hrev x
          have h2 := deriv_comp_neg (f := r) φ
          rw [h1] at h2
          exact h2
        rw [hodd]; linarith
      have hsφ : Real.sin φ ≤ 0 := by
        have hsψ : 0 ≤ Real.sin (-φ) :=
          Real.sin_nonneg_of_nonneg_of_le_pi hneg0 (by linarith [hnegle, hφE_le, Real.pi_pos])
        have h := Real.sin_neg φ
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos hd hsφ
  -- `r (r - cos φ) > 0`.
  have hA : 0 < r φ ^ 2 - r φ * Real.cos φ := by
    have hsub : 0 < r φ - Real.cos φ := by linarith [Real.cos_le_one φ]
    nlinarith [mul_pos (hrpos φ) hsub]
  rw [deriv_polar_exp (hr.differentiable (by simp)) φ]
  rw [polar_rate_im (r φ) (deriv r φ) φ]
  linarith [hA, hB]

end Work.Drive.N2Lead
