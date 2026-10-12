import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BlockBound4.diag_content_point
import Submission.Work.BlockBound4.integrable_diagKF
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Work.BlockBound4

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The `(M+1)`-normalised kinetic word as a `q`-integral -/

/-- The `(M+1)`-normalised kinetic word is the `q`-integral of its mode content:
`kinPWord s c Φ / (M+1) = (2π)⁻³ ∫_q (fsKinCoeff c ‖q‖/(M+1))·(P_{u_q} + P_{v_q})`.
(`M` is the particle number and is arbitrary here; the identity is the definition of
`kinPWord` with the constant `(2π)⁻¹³ = ((2π)³)⁻¹` pulled inside the integral.) -/
lemma diagKinPartDiv_eq_integral {n : ℕ} {s c M : ℝ} {Φ : X (n + 1) → ℝ} :
    kinPWord s c Φ / (M + 1)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
          (fsKinCoeff c ‖q‖ / (M + 1)) *
            (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ) := by
  have hs3 : (2 * Real.pi)⁻¹ ^ 3 = ((2 * Real.pi) ^ 3)⁻¹ := by rw [inv_pow]
  have hcongr : (∫ q : ℝ³, (fsKinCoeff c ‖q‖ / (M + 1)) *
        (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ))
      = ∫ q : ℝ³, (1 / (M + 1)) * (fsKinCoeff c ‖q‖ *
          (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    ring
  rw [hcongr, MeasureTheory.integral_const_mul]
  unfold kinPWord
  rw [hs3]
  ring

/-- Integrability of the `(M+1)`-normalised kinetic integrand. -/
lemma integrable_diagKinPartDiv {n : ℕ} {s c M : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Integrable (fun q : ℝ³ => (fsKinCoeff c ‖q‖ / (M + 1)) *
      (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) := by
  have h := integrable_kinetic_half hs hc n Φ hΦ
  refine (h.const_mul (1 / (M + 1))).congr (Filter.Eventually.of_forall fun q => ?_)
  simp only []
  ring

/-- Integrability of the D1 pairing integrand at the weight `W = wScaled s (g0 v h)`. -/
lemma integrable_diagPairPart {p : ℕ} {s R : ℝ} (hs : 0 < s) (hR : 0 < R)
    (hRs : R ≤ s * chiR0) {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Integrable (fun q : ℝ³ =>
      pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q)) := by
  have h0 := integrable_pairingQ (ℓ := s) (R := R) hs hR hRs hv_supp h hΦ
  have h1 := Complex.reCLM.integrable_comp h0
  refine h1.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Complex.reCLM_apply]
  rw [re_mul_ofReal]
  unfold pairW
  ring

/-- NOTE for the prover: do NOT import `Submission.Work.SmallBoxD1Faithful` (that module does
NOT compile). Prove this directly. The ingredients: (i) `kinPWord s c Φ / (M+1)
= (2π)⁻³ ∫ q, (fsKinCoeff c ‖q‖/(M+1)) * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)`
with `M = (p:ℝ)+2` (unfold `kinPWord`, `(2π)⁻¹^3 = ((2π)^3)⁻¹`, `integral_const_mul`,
integrability from `integrable_kinetic_half`); (ii) `q4PairWord = (2π)⁻³ ∫ q, pairW W q * (s⁻³ * pairR s Φ q)`
(`SmallBoxD1Integral.q4PairWord_eq_re_pairSum`); (iii) the pointwise bound
`SmallBoxD1PerP.d1_content_bogoliubov` at `A₀ = diagAF s c0 (a v) M q * (s^3)⁻¹`,
`B₀ = d1Bcoef W q * (s^3)⁻¹`, `F = fsKinCoeff c0 ‖q‖ / (M+1)` together with
`|d1Bcoef W q| ≤ diagAF ...` (`DiagWF.abs_d1Bcoef_le_diagAF`), the exact deficit
`diagAF · s⁻³ − fsKinCoeff c0 ‖q‖/(M+1) = 2*d1Ks*(a v)*s⁻³` (by `field_simp; ring` from the
definition of `diagAF`), `integral_chiScale_sq_acube`, and `bogoliubov_coeff_smul` to turn
`K(A₀,B₀) * s^3` into `diagKF s c0 (a v) M W q`; (iv) integrate the pointwise bound against
`(2π)⁻³` (monotonicity + integrabilities: `integrable_modeP_sum`, `wScaled_g0_integrable`,
`abs_pairW_wScaled_g0_le`, `integrable_pairingQ`, `integrable_kinetic_half`). -/
theorem diag_content_integral {p : ℕ} {s c0 : ℝ} (hs : 0 < s) (hc0 : 0 < c0)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hRs : R ≤ s * chiR0)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hav : 0 < a v)
    (hWfin : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹))
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hΦnorm : (∫ x in abox (p + 2) s, (Φ x) ^ 2) = 1) :
    kinPWord s c0 Φ / (((p : ℝ) + 2) + 1) + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
      ≥ - (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : EuclideanSpace ℝ (Fin 3),
              Work.BlockBound4.diagKF s c0 (a v) ((p : ℝ) + 2)
                (wScaled s (g0 v h)) q * ((p : ℝ) + 2)))
        - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (((2 * Real.pi) ^ 3)⁻¹
              * (∫ q : EuclideanSpace ℝ (Fin 3),
                  (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ))) := by
  set M : ℝ := (p : ℝ) + 2 with hMdef
  have hM0 : (0 : ℝ) < M := by rw [hMdef]; positivity
  have hM2 : 2 ≤ M := by rw [hMdef]; exact le_add_of_nonneg_left (Nat.cast_nonneg p)
  -- integrability and the standing bounds for the weight `W = wScaled s (g0 v h)`
  have hWint : Integrable (wScaled s (g0 v h)) := wScaled_g0_integrable hR hv_supp h hs hRs
  have hW0 : 0 ≤ᵐ[volume] wScaled s (g0 v h) :=
    wScaled_g0_nonneg_ae (ℓ := s) hR hv_nonneg hvrad hv_supp h
  have hWb : ∀ q : ℝ³, |d1Bcoef (wScaled s (g0 v h)) q| ≤ 16 * Real.pi * (a v) := fun q =>
    abs_pairW_wScaled_g0_le hR hv_nonneg hvrad hv_supp h hs hRs q
  have hWb' : ∀ q : ℝ³, |pairW (wScaled s (g0 v h)) q| ≤ 16 * Real.pi * (a v) := fun q => by
    simpa only [d1Bcoef] using hWb q
  have hWmeas : Measurable (d1Bcoef (wScaled s (g0 v h))) := by
    unfold d1Bcoef
    exact (Complex.continuous_re.comp
      ((continuous_cfourier hWint).comp (continuous_const_smul _))).measurable
  have hInt : Integrable (fun q : ℝ³ => (d1Bcoef (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2) :=
    integrable_pairW_sq_div hWint hW0 hWfin
  -- integrability of the three integrands
  have hint_k : Integrable (fun q : ℝ³ => (fsKinCoeff c0 ‖q‖ / (M + 1)) *
      (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) :=
    integrable_diagKinPartDiv (M := M) hs hc0.le hΦ
  have hint_q : Integrable (fun q : ℝ³ =>
      pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q)) :=
    integrable_diagPairPart (p := p) (R := R) hs hR hRs hv_supp h hΦ
  have hKm : Integrable (fun q : ℝ³ => diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M) :=
    integrable_diagKF hs hc0 hav hM2 hWmeas hWb hInt
  have hPint : Integrable (fun q : ℝ³ =>
      modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ) :=
    integrable_modeP_sum hs (n := p + 1) hΦ
  -- the pointwise content bound
  have hpt : ∀ q : ℝ³, -(diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M)
      - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
      ≤ (fsKinCoeff c0 ‖q‖ / (M + 1)) * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
        + pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q) := by
    intro q
    calc -(diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M)
        - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
            * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
        = -diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M
          - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
            * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ) := by ring
      _ ≤ (fsKinCoeff c0 ‖q‖ / (M + 1)) * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
          + (d1Bcoef (wScaled s (g0 v h)) q * (s ^ 3)⁻¹) * pairR s Φ q :=
          diag_content_point (c0 := c0) hs hav hMdef hWb' hΦ.continuous hΦnorm q
      _ = (fsKinCoeff c0 ‖q‖ / (M + 1)) * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
          + pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q) := by
          simp only [d1Bcoef]; ring
  have hLower : Integrable (fun q : ℝ³ => -(diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M)
      - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) :=
    (hKm.neg).sub (hPint.const_mul (2 * d1Ks * (a v) * (s ^ 3)⁻¹))
  have hMono : (∫ q : ℝ³, (-(diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M)
        - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)))
      ≤ ∫ q : ℝ³, ((fsKinCoeff c0 ‖q‖ / (M + 1))
            * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
          + pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q)) :=
    integral_mono_ae hLower (hint_k.add hint_q) (Filter.Eventually.of_forall fun q => hpt q)
  have hExpand : (∫ q : ℝ³, (-(diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M)
        - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)))
      = -(∫ q : ℝ³, diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M)
        - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (∫ q : ℝ³, (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) := by
    rw [MeasureTheory.integral_sub
        (f := fun q : ℝ³ => -(diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M))
        (g := fun q : ℝ³ => 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ))
        (hKm.neg) (hPint.const_mul (2 * d1Ks * (a v) * (s ^ 3)⁻¹)),
      MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
  -- the two word identities
  have hstepk : kinPWord s c0 Φ / (M + 1)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³, (fsKinCoeff c0 ‖q‖ / (M + 1)) *
          (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ) :=
    diagKinPartDiv_eq_integral (n := p + 1) (s := s) (c := c0) (M := M)
  have hstepq : q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
          pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q) :=
    q4PairWord_eq_re_pairSum (ℓ := s) (R := R) hs hR hRs hv_supp h hΦ
  have hLHS : kinPWord s c0 Φ / (((p : ℝ) + 2) + 1) + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
          ((fsKinCoeff c0 ‖q‖ / (M + 1))
              * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
            + pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q)) := by
    rw [hstepk, hstepq, ← mul_add, ← MeasureTheory.integral_add hint_k hint_q]
  rw [hLHS]
  have hmain : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
          ((fsKinCoeff c0 ‖q‖ / (M + 1))
              * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
            + pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q))
      ≥ ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³, (-(diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M)
        - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) :=
    mul_le_mul_of_nonneg_left hMono (by positivity)
  rw [hExpand] at hmain
  have hgoal : -(((2 * Real.pi) ^ 3)⁻¹
          * (∫ q : ℝ³, diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M))
      - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
        * (((2 * Real.pi) ^ 3)⁻¹
            * (∫ q : ℝ³, (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)))
      = ((2 * Real.pi) ^ 3)⁻¹
        * (-(∫ q : ℝ³, diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M)
          - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
            * (∫ q : ℝ³, (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ))) := by
    ring
  rw [hgoal]
  exact hmain

end Work.BlockBound4
