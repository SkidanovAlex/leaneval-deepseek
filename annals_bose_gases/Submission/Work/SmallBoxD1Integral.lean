import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.SmallBoxD1KinDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-283 — the D1 integration, STEP 1: combining the two words

FS `lm:appbogolubov` adds the kinetic word `Σ_i Q_iχ_i[√−Δ_i − c]₊²χ_iQ_i` (the corpus's
`kinPWord`) to the pairing word `A₂` (the corpus's `q4PairWord`) and then applies Bogoliubov
at each momentum `p`.  Session 281 proved the PER-`p` identity; Session 282 proved the
integrability of BOTH halves.  This module performs the combination:

  `kinPWord s c Φ + q4PairWord Φ = (2π)⁻³ ∫_q [F(q)(P_{u_q}+P_{v_q}) + 𝓑(q)s⁻³(R_{u_q}+R_{v_q})]`

with `F(q) = [‖q‖−c]₊²`, `𝓑(q) = Re 𝓕W₁((2π)⁻¹q)`, and `P_g`, `R_g` the mode
number/pairing forms of `SmallBoxD1PerP`.

## Contents

* `pairW`, `pairR` — the D1 pairing weight and pair-content in the corpus notation;
* `integrable_pairingQ` — the `q`-parametrised pairing integrand is `Integrable`
  (transport of `SmallBoxD1PerP.integrable_pairingWeight` along the scaling `u ↦ (2π)⁻¹•u`);
* **`q4PairWord_eq_re_pairSum`** — the REAL form of `q4PairWord_eq_pairSum`;
* **`kinPWord_add_q4PairWord_eq_integral`** — STEP 1.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The D1 pairing weight** `𝓑(q) = Re 𝓕(W)((2π)⁻¹q)` — FS's `\widehat{WS₁}(q)` (real part;
for the even kernels of the application `𝓕W` is already real). -/
noncomputable def pairW (W : ℝ³ → ℝ) (q : ℝ³) : ℝ :=
  (FourierTransform.fourier (fun x => (W x : ℂ)) (((2 * π : ℝ)⁻¹) • q)).re

/-- **The D1 pair content** `R(q) = R_{u_q} + R_{v_q}`, the `B`-term of `bogoliubov_perP_chi`
at the momentum `q` (`u_q + iv_q = qMode ℓ q`). -/
noncomputable def pairR (ℓ : ℝ) {n : ℕ} (Φ : X (n + 1) → ℝ) (q : ℝ³) : ℝ :=
  (∫ x in abox (n + 1) ℓ,
      tauAnn ℓ (qModeRe ℓ q) Φ x * tauDag ℓ (qModeRe ℓ q) Φ x)
    + (∫ x in abox (n + 1) ℓ,
      tauAnn ℓ (qModeIm ℓ q) Φ x * tauDag ℓ (qModeIm ℓ q) Φ x)

/-- `(z * (b : ℂ)).re = z.re * b` for a real `b`. -/
lemma re_mul_ofReal (z : ℂ) (b : ℝ) : (z * (b : ℂ)).re = z.re * b := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- the complexified scalar `((ℓ)^3)⁻¹` is the coercion of the real `(ℓ^3)⁻¹`. -/
lemma ofReal_inv_pow_three (ℓ : ℝ) : (((ℓ : ℂ) ^ 3)⁻¹) = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_inv]

/-- **Integrability of the `q`-parametrised D1 pairing integrand.** -/
theorem integrable_pairingQ {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * chiR0) {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Integrable (fun q : ℝ³ =>
      FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ))
          (((2 * π : ℝ)⁻¹) • q)
        * ((((ℓ ^ 3)⁻¹ * pairR ℓ Φ q : ℝ)) : ℂ)) := by
  set F : ℝ³ → ℂ := fun u =>
    FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ)) u *
      (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * bDag ℓ (qMode ℓ (-((2 * π : ℝ) • u)))
        (bDag ℓ (qMode ℓ ((2 * π : ℝ) • u)) (fun y => (Φ y : ℂ))) x) with hFdef
  have hF : Integrable F :=
    integrable_pairingWeight hℓ hR hRℓ hv_supp h hΦ
  have h2π : ((2 * π : ℝ)) ≠ 0 := by positivity
  have hcomp : Integrable (fun q : ℝ³ => F (((2 * π : ℝ)⁻¹) • q)) :=
    hF.comp_smul (R := (2 * π : ℝ)⁻¹) (inv_ne_zero h2π)
  refine hcomp.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [hFdef]
  have hsq : (2 * π : ℝ) • (((2 * π : ℝ)⁻¹) • q) = q := by
    rw [smul_smul, mul_inv_cancel₀ h2π, one_smul]
  rw [hsq, bDag_pair_reduction hℓ (p := q) hΦ.continuous]
  simp only [pairR, ofReal_inv_pow_three, Complex.ofReal_mul]

/-- **REAL FORM of the pair-word identity.**  `q4PairWord` is the `q`-integral of the
FS weight `𝓑(q) = Re 𝓕W₁((2π)⁻¹q)` against `(s³)⁻¹(R_{u_q}+R_{v_q})`. -/
theorem q4PairWord_eq_re_pairSum {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * chiR0) {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      = ((2 * π : ℝ) ^ 3)⁻¹ * ∫ q,
          pairW (wScaled ℓ (g0 v h)) q * ((ℓ ^ 3)⁻¹ * pairR ℓ Φ q) := by
  set B : ℝ³ → ℂ := fun q =>
    FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ))
        (((2 * π : ℝ)⁻¹) • q)
      * ((((ℓ ^ 3)⁻¹ * pairR ℓ Φ q : ℝ)) : ℂ) with hBdef
  have hint : Integrable B :=
    integrable_pairingQ (ℓ := ℓ) (R := R) hℓ hR hRℓ hv_supp h hΦ
  have hp : ((q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) : ℝ) : ℂ)
      = (((2 * π : ℝ) ^ 3)⁻¹ : ℂ) * ∫ q, B q := by
    have h0 := q4PairWord_eq_pairSum (ℓ := ℓ) (R := R) hℓ hR hRℓ hv_supp h hΦ
    rw [hBdef]
    rw [show (fun q : ℝ³ => FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ))
            (((2 * π : ℝ)⁻¹) • q) * (((ℓ ^ 3)⁻¹ * pairR ℓ Φ q : ℝ) : ℂ))
        = fun q : ℝ³ => FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ))
            (((2 * π : ℝ)⁻¹) • q) * (((ℓ ^ 3)⁻¹ : ℂ) * ((pairR ℓ Φ q : ℝ) : ℂ)) from by
      funext q
      rw [ofReal_inv_pow_three, Complex.ofReal_mul]]
    exact h0
  have hreint : (∫ q, B q).re = ∫ q, (B q).re := by
    have h := Complex.reCLM.integral_comp_comm (φ := B) hint
    simpa only [Complex.reCLM_apply] using h.symm
  have hCre : ((((2 * π : ℝ) ^ 3)⁻¹ : ℂ)).re = ((2 * π : ℝ) ^ 3)⁻¹ := by
    rw [ofReal_inv_pow_three, Complex.ofReal_re]
  have hCim : ((((2 * π : ℝ) ^ 3)⁻¹ : ℂ)).im = 0 := by
    rw [ofReal_inv_pow_three, Complex.ofReal_im]
  have hkey := congrArg Complex.re hp
  rw [Complex.ofReal_re, Complex.mul_re, hCre, hCim, hreint] at hkey
  simp only [zero_mul, sub_zero] at hkey
  refine hkey.trans ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [hBdef]
  rw [pairW, re_mul_ofReal]

/-- **The D1 kinetic integrand** `F(q)(P_{u_q}+P_{v_q})`. -/
noncomputable def d1KinPart (s c : ℝ) {n : ℕ} (Φ : X (n + 1) → ℝ) (q : ℝ³) : ℝ :=
  fsKinCoeff c ‖q‖ * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)

/-- **STEP 1 — the D1 combination.**  The corpus's two D1 words are the two halves of ONE
`q`-integral: the kinetic content `F(q)(P_{u_q}+P_{v_q})` plus the pairing content
`𝓑(q)(s³)⁻¹(R_{u_q}+R_{v_q})`. -/
theorem kinPWord_add_q4PairWord_eq_integral {p : ℕ} {s c R : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    (hR : 0 < R) (hRs : R ≤ s * chiR0) {v : ℝ³ → ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    kinPWord s c Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
      = ((2 * π : ℝ) ^ 3)⁻¹ * ∫ q,
          (d1KinPart s c Φ q
            + pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q)) := by
  have hint_k : Integrable (d1KinPart s c Φ) :=
    integrable_kinetic_half hs hc (p + 1) Φ hΦ
  have hsc : (2 * Real.pi)⁻¹ ^ 3 = ((2 * π : ℝ) ^ 3)⁻¹ := by rw [inv_pow]
  have hk : kinPWord s c Φ
      = ((2 * π : ℝ) ^ 3)⁻¹ * ∫ q, d1KinPart s c Φ q := by
    rw [kinPWord, hsc]
    rfl
  have hq := q4PairWord_eq_re_pairSum (ℓ := s) (R := R) hs hR hRs hv_supp h hΦ
  have hint_q : Integrable (fun q : ℝ³ =>
      pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q)) := by
    have h0 := integrable_pairingQ (ℓ := s) (R := R) hs hR hRs hv_supp h hΦ
    have h1 := Complex.reCLM.integrable_comp h0
    refine h1.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Complex.reCLM_apply]
    rw [pairW, re_mul_ofReal]
  rw [hk, hq, ← mul_add, ← MeasureTheory.integral_add hint_k hint_q]

/-! ## 7 The window normalisation `∫_{Λ(s)} χ_s² = s³` -/

/-- `χ_s` vanishes outside the side-`s` cube. -/
lemma chiScale_eq_zero_of_notMem_acube {s : ℝ} (hs : 0 < s) {z : ℝ³}
    (hz : z ∉ acube s) : chiScale s z = 0 := by
  by_contra hne
  exact hz (mem_acube_of_norm_le hs.le (chiScale_support_le hs hne))

/-- **`∫_{Λ(s)} χ_s² = s³`** — the window normalisation used by every D1 trace
constant (`∫χ² = 1` and `χ_s(z) = χ(z/s)`). -/
lemma integral_chiScale_sq_acube {s : ℝ} (hs : 0 < s) :
    (∫ z in acube s, (chiScale s z) ^ 2) = s ^ 3 := by
  have hsupp : ∀ z : ℝ³, z ∉ acube s → (chiScale s z) ^ 2 = 0 :=
    fun z hz => by rw [chiScale_eq_zero_of_notMem_acube hs hz]; ring
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun z : ℝ³ => (chiScale s z) ^ 2)
    (s := acube s) hsupp]
  have hscale : (∫ z : ℝ³, (chiScale s z) ^ 2)
      = (s ^ 3 : ℝ) * ∫ w : ℝ³, (chi w) ^ 2 := by
    have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
      (fun w : ℝ³ => (chi w) ^ 2) (s⁻¹) (hR := inv_nonneg.mpr hs.le)
    rw [finrank_euclideanSpace, Fintype.card_fin] at h
    have h' : (∫ z : ℝ³, (chiScale s z) ^ 2)
        = (((s⁻¹) ^ 3 : ℝ))⁻¹ * ∫ w : ℝ³, (chi w) ^ 2 := by
      simpa [chiScale] using h
    rwa [inv_pow, inv_inv] at h'
  rw [hscale, chi_L2, mul_one]

/-! ## 8 STEP 2 — the pointwise D1 content bound -/

/-- **The pointwise D1 content bound at a single momentum.**  For `𝒜 > 0`, `|ℬ| ≤ 𝒜`,
`𝒜` the `A`-coefficient of FS's `h(p)/2` and `ℬ` the pairing coefficient, the
per-momentum D1 content `F·P + (ℬ/s³)·R` dominates
`−K(𝒜,ℬ)·(p+2) − (𝒜/s³ − F)·P` (with `P = P_{u_p}+P_{v_p}`, `R = R_{u_p}+R_{v_p}`
and `(p+2)` the particle number). -/
theorem d1_content_at {n : ℕ} {s c : ℝ} (hs : 0 < s) {Φ : X (n + 1) → ℝ}
    (hΦ : Continuous Φ)
    (hΦnorm : (∫ x in abox (n + 1) s, (Φ x) ^ 2) = 1)
    {𝒜 ℬ : ℝ} (hA : 0 < 𝒜) (hB : |ℬ| ≤ 𝒜) (p : ℝ³) :
    - ((𝒜 - Real.sqrt (𝒜 ^ 2 - ℬ ^ 2)) / 2) * ((n : ℝ) + 1)
      - (𝒜 * (s ^ 3)⁻¹ - fsKinCoeff c ‖p‖)
          * (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ)
    ≤ fsKinCoeff c ‖p‖ * (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ)
      + (ℬ * (s ^ 3)⁻¹) * pairR s Φ p := by
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hA0 : 0 < 𝒜 * (s ^ 3)⁻¹ := mul_pos hA (inv_pos.mpr hs3)
  have hB0 : |ℬ * (s ^ 3)⁻¹| ≤ 𝒜 * (s ^ 3)⁻¹ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hs3)]
    exact mul_le_mul_of_nonneg_right hB (le_of_lt (inv_pos.mpr hs3))
  have h := d1_content_bogoliubov (s := s) (n := n) (A₀ := 𝒜 * (s ^ 3)⁻¹)
    (B₀ := ℬ * (s ^ 3)⁻¹) (F := fsKinCoeff c ‖p‖) hs (p := p) hΦ hA0 hB0
  rw [integral_chiScale_sq_acube hs, hΦnorm] at h
  have hK : ((𝒜 * (s ^ 3)⁻¹ - Real.sqrt ((𝒜 * (s ^ 3)⁻¹) ^ 2 - (ℬ * (s ^ 3)⁻¹) ^ 2))
        / 2) * s ^ 3 = (𝒜 - Real.sqrt (𝒜 ^ 2 - ℬ ^ 2)) / 2 := by
    rw [show 𝒜 * (s ^ 3)⁻¹ = (s ^ 3)⁻¹ * 𝒜 from mul_comm _ _,
      show ℬ * (s ^ 3)⁻¹ = (s ^ 3)⁻¹ * ℬ from mul_comm _ _,
      bogoliubov_coeff_smul (A := 𝒜) (B := ℬ) (c := (s ^ 3)⁻¹) (inv_pos.mpr hs3)]
    field_simp
  have hpR : pairR s Φ p
      = (∫ x in abox (n + 1) s, tauAnn s (qModeRe s p) Φ x * tauDag s (qModeRe s p) Φ x)
        + (∫ x in abox (n + 1) s, tauAnn s (qModeIm s p) Φ x * tauDag s (qModeIm s p) Φ x) :=
    rfl
  rw [hpR]
  nlinarith [h, hK]

end BoseGases
end Submission
