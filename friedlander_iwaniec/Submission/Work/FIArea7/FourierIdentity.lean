import Mathlib
import Submission.Work.FIArea7.SepK

/-!
# The separating identity for the smooth trapezoid `sepK`

For the smooth trapezoid `K = sepK λ ε` (a real, even, compactly supported `C^∞` function) the
real part of its Fourier transform separates the multiplicative frequencies `k`:

`∫_ℝ (Re 𝓕K)(t) · k^{it} dt = K(log k / 2π)`   for every `k ≥ 1`.

This is the Fourier inversion formula for `K`, together with the two structure facts that
`𝓕K` is real valued (because `K` is real and even).  We prove:

* `contDiff_sepPsi`, `contDiff_sepK` : `sepPsi` and `sepK λ ε` are `C^∞`;
* `hasCompactSupport_sepK_complex` : `y ↦ (sepK λ ε y : ℂ)` has compact support;
* `integrable_fourier_sepK` : the Fourier transform of that function is integrable
  (it is the Fourier transform of a Schwartz function);
* `fourier_sepK_re` : `𝓕K` is real valued, i.e. `((𝓕K t).re : ℂ) = 𝓕K t`;
* `cpow_nat_eq_exp` : `(k : ℂ)^(t * I) = exp (↑(t log k) * I)`.

The main theorem `FourierIdentity` then follows by Fourier inversion.
-/

namespace Work.FIArea7

open MeasureTheory Filter
open scoped FourierTransform ComplexConjugate Topology

noncomputable section

/-! ## Smoothness and support of `sepK` -/

/-- `sepPsi` is `C^∞`. -/
lemma contDiff_sepPsi : ContDiff ℝ (↑(⊤ : ℕ∞)) sepPsi := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨sepPsi_diff, ?_⟩
  rw [deriv_sepPsi]
  unfold sepRho
  fun_prop

/-- `sepK λ ε` is `C^∞`. -/
lemma contDiff_sepK (lam eps : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (sepK lam eps) := by
  unfold sepK
  exact ((contDiff_sepPsi.comp (by fun_prop)).sub (contDiff_sepPsi.comp (by fun_prop)))

/-- The complexification of `sepK λ ε` has compact support (it vanishes off
`[-(λ+ε), λ+ε]`). -/
lemma hasCompactSupport_sepK_complex {lam eps : ℝ} (hlam : 0 ≤ lam) (hε : 0 < eps) :
    HasCompactSupport (fun y : ℝ => (sepK lam eps y : ℂ)) := by
  refine HasCompactSupport.intro (K := Set.Icc (-(lam + eps)) (lam + eps)) isCompact_Icc ?_
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · rw [sepK_eq_zero_of_le hlam hε (le_of_lt h)]; rfl
  · rw [sepK_eq_zero_of_ge hlam hε (le_of_lt h)]; rfl

/-- The Fourier transform of `sepK λ ε` is integrable: `sepK λ ε` is a `C^∞` compactly
supported function, hence a Schwartz function whose Fourier transform is integrable. -/
lemma integrable_fourier_sepK {lam eps : ℝ} (hlam : 0 ≤ lam) (hε : 0 < eps) :
    Integrable (𝓕 (fun y : ℝ => (sepK lam eps y : ℂ))) := by
  have hcd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => (sepK lam eps y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_sepK lam eps)
  have hcs := hasCompactSupport_sepK_complex hlam hε
  let F : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hcd
  have hFcoe : (F : ℝ → ℂ) = fun y : ℝ => (sepK lam eps y : ℂ) := rfl
  have h := (𝓕 F).integrable (μ := volume)
  rwa [SchwartzMap.fourier_coe, hFcoe] at h

/-! ## Reality of the Fourier transform of `sepK` -/

/-- Conjugation exchanges the two Fourier characters. -/
lemma conj_exp_neg_mul (a : ℝ) :
    (starRingEnd ℂ) (Complex.exp (↑(-2 * Real.pi * a) * Complex.I))
      = Complex.exp (↑(2 * Real.pi * a) * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- `𝓕 (sepK λ ε)` is real valued, because `sepK λ ε` is real and even. -/
lemma fourier_sepK_re (lam eps : ℝ) (t : ℝ) :
    ((𝓕 (fun y : ℝ => (sepK lam eps y : ℂ)) t).re : ℂ)
      = 𝓕 (fun y : ℝ => (sepK lam eps y : ℂ)) t := by
  rw [← Complex.conj_eq_iff_re]
  rw [Real.fourier_eq']
  simp only [Real.inner_apply]
  rw [(integral_conj (f := fun v : ℝ =>
        Complex.exp (↑(-2 * Real.pi * (v*t)) * Complex.I) • (sepK lam eps v : ℂ))).symm]
  -- the substitution `v ↦ -v` inverts the sign of the exponent
  have key : (∫ v : ℝ, Complex.exp (↑(2 * Real.pi * (v*t)) * Complex.I) • (sepK lam eps v : ℂ))
      = ∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * (v*t)) * Complex.I) • (sepK lam eps v : ℂ) := by
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      measurableEmbedding_neg
      (fun u : ℝ => Complex.exp (↑(-2 * Real.pi * (u*t)) * Complex.I) • (sepK lam eps u : ℂ))
    rw [← hmp]
    apply integral_congr_ae
    filter_upwards with u
    simp only [smul_eq_mul]
    rw [sepK_even lam eps u]
    congr 1
    push_cast
    ring_nf
  have h1 : (∫ v : ℝ, (starRingEnd ℂ)
        (Complex.exp (↑(-2 * Real.pi * (v*t)) * Complex.I) • (sepK lam eps v : ℂ)))
      = ∫ v : ℝ, Complex.exp (↑(2 * Real.pi * (v*t)) * Complex.I) • (sepK lam eps v : ℂ) := by
    apply integral_congr_ae
    filter_upwards with v
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
    simp_rw [conj_exp_neg_mul]
  rw [h1]
  exact key

/-! ## The complex power `k^{it}` -/

/-- For `k ≥ 1` the complex power `(k : ℂ)^(t * I)` is the unit complex number
`exp (↑(t log k) * I)`. -/
lemma cpow_nat_eq_exp (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    (k : ℂ) ^ (t * Complex.I) = Complex.exp (↑(t * Real.log k) * Complex.I) := by
  have hk0 : (k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
  rw [Complex.cpow_def_of_ne_zero hk0]
  have hlog : Complex.log (k : ℂ) = ↑(Real.log k) := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) from by push_cast; ring]
    rw [← Complex.ofReal_log (show (0 : ℝ) ≤ (k : ℝ) by positivity)]
  rw [hlog]
  congr 1
  push_cast
  ring

/-! ## The separating identity -/

/-- **The separating identity.** With `K = sepK λ ε` the smooth trapezoid, the real part of the
Fourier transform of `K` separates the points `log k / 2π`: for every `k ≥ 1`,
`∫_ℝ (Re 𝓕K)(t) · k^{it} dt = K(log k / 2π)`, where `𝓕K(t) = ∫_y K(y) exp(-2πiyt) dy`. -/
theorem FourierIdentity (lam eps : ℝ) (hε : 0 < eps) (hle : eps ≤ lam) (k : ℕ) (hk : 1 ≤ k) :
    (∫ t : ℝ, (((FourierTransform.fourier (fun y : ℝ => (sepK lam eps y : ℂ)) t).re : ℂ)
        * (k : ℂ) ^ (t * Complex.I)))
      = (sepK lam eps (Real.log k / (2 * Real.pi)) : ℂ) := by
  have hlam : 0 ≤ lam := le_of_lt (lt_of_lt_of_le hε hle)
  have hKint : Integrable (fun y : ℝ => (sepK lam eps y : ℂ)) :=
    (integrable_sepK lam eps hlam hε).ofReal
  have hFint : Integrable (𝓕 (fun y : ℝ => (sepK lam eps y : ℂ))) :=
    integrable_fourier_sepK hlam hε
  have hKcont : Continuous (fun y : ℝ => (sepK lam eps y : ℂ)) :=
    Complex.continuous_ofReal.comp (sepK_continuous lam eps hε.ne')
  set x : ℝ := Real.log k / (2 * Real.pi) with hx
  -- the two characters `k^{it}` and `exp (2πi t x)` agree
  have hcpow : ∀ t : ℝ, (k : ℂ) ^ (t * Complex.I)
      = Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) := by
    intro t
    rw [cpow_nat_eq_exp k hk t]
    congr 1
    have harg : 2 * Real.pi * (t * (Real.log k / (2 * Real.pi))) = t * Real.log k := by
      field_simp
    rw [Real.inner_apply, hx, harg]
  calc (∫ t : ℝ, (((FourierTransform.fourier (fun y : ℝ => (sepK lam eps y : ℂ)) t).re : ℂ)
          * (k : ℂ) ^ (t * Complex.I)))
      = ∫ t : ℝ, (𝓕 (fun y : ℝ => (sepK lam eps y : ℂ)) t) * (k : ℂ) ^ (t * Complex.I) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [fourier_sepK_re]
    _ = ∫ t : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I)
          • (𝓕 (fun y : ℝ => (sepK lam eps y : ℂ)) t) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hcpow t, smul_eq_mul, mul_comm]
    _ = 𝓕⁻ (𝓕 (fun y : ℝ => (sepK lam eps y : ℂ))) x := by rw [Real.fourierInv_eq']
    _ = (fun y : ℝ => (sepK lam eps y : ℂ)) x :=
        hKint.fourierInv_fourier_eq hFint hKcont.continuousAt
    _ = (sepK lam eps (Real.log k / (2 * Real.pi)) : ℂ) := by rw [← hx]

end

end Work.FIArea7
