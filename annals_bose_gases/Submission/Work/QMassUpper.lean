import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.NewtonCoulomb
import Submission.Work.FibreLocal
import Submission.Work.QDecompSimpler
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# eq:Q2n0 mass treatment, S1-UPPER — fibre localisation, upper side

Mirror of `QMassLower.qmass_fibre_local_lower` / `FibreLocal.
w1Fibre_pointwise_lower` with the UPPER sandwich: the χ-renormalised fibre
`fibre(x) := w1Fibre(wPairC(g0)) x` satisfies

    fibre(x) ≤ (8πa v)·χΛ(x)² + (R/ℓ)²·(8πa v)·(2C·chiSup² + 2·chiSup·Cχ)

under the standing hypotheses plus the `conv3χχ` second-order regime
`(C, r₁)` with `R/ℓ ≤ r₁`, `C(R/ℓ)² ≤ 1/2` (`NewtonCoulomb.wScaled_sandwich_at`
gives `wScaled ≤ g₀(1+2C(R/ℓ)²)` a.e.; `convolution_approx` gives the upper
side of `∫χΛ(y)g₀(x−y) ≤ χΛ(x)∫g₀ + Cχ(R/ℓ)²∫|g₀|`), and
`u := C(R/ℓ)² ≤ 1/2`, `0 ≤ χΛ ≤ chiSup`.  Summed:

    qOneMass ≤ (8πa v)·q2MassChi + (R/ℓ)²·(8πa v)·(2C·chiSup² + 2chiSup·Cχ)·cnPlus.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
set_option maxHeartbeats 400000

/-- Pointwise upper fibre bound: `fibre(x) ≤ (8πa v)·χΛ(x)² + Err` with
`Err := (R/ℓ)²·(8πa v)·(2C·chiSup² + 2·chiSup·Cχ)` (upper sandwich +
convolution upper). -/
lemma w1Fibre_pointwise_upper {v : ℝ³ → ℝ} {R ℓ Cχ C r₁ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT2 : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) (hCχ : 0 ≤ Cχ)
    (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2)
    (x : ℝ³) :
    w1Fibre ℓ (wPairC ℓ (g0 v h)) x
      ≤ (8 * π * a v) * (chiScale ℓ x) ^ 2
        + (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ) := by
  classical
  let g0f : ℝ³ → ℝ := g0 v h
  let u : ℝ := C * (R / ℓ) ^ 2
  have hAv : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact mul_nonneg hC (sq_nonneg (R / ℓ))
  have hu_le : u ≤ 1 / 2 := by
    dsimp [u]
    exact hcond
  have hg0supp : ∀ z : ℝ³, R ≤ ‖z‖ → g0f z = 0 := by
    intro z hz
    dsimp [g0f]
    exact g0_zero_of_norm_ge (v := v) hv_supp hz h
  have hg0i : MeasureTheory.Integrable g0f := by
    dsimp [g0f]
    exact g0_integrable hR hv_supp h
  have hg0nn : ∀ᵐ z : ℝ³, 0 ≤ g0f z := by
    dsimp [g0f]
    exact g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hg0even : ∀ z : ℝ³, g0f (-z) = g0f z := by
    intro z
    dsimp [g0f]
    exact g0_even hvrad h z
  have hg0int : (∫ z : ℝ³, g0f z) = 8 * π * a v := by
    dsimp [g0f]
    exact g0_integral hR hv_supp h
  have hg0abs : (∫ z : ℝ³, |g0f z|) = 8 * π * a v := by
    calc
      (∫ z : ℝ³, |g0f z|) = ∫ z : ℝ³, g0f z := by
        apply integral_congr_ae
        filter_upwards [hg0nn] with z hz
        exact abs_of_nonneg hz
      _ = 8 * π * a v := hg0int
  have hwi : MeasureTheory.Integrable (wScaled ℓ g0f) :=
    wScaled_integrable_ae hℓ hR.le hRℓ hg0i hg0supp
  have hconv := convolution_approx (ℓ := ℓ) (R := R) (Cχ := Cχ) hℓ hT hg0i hg0even hg0supp hR.le x
  -- chain (1): fibre = χΛ(x)·A, A := ∫_y χΛ(y)·wScaled(x−y)
  have hfibE : w1Fibre ℓ (wPairC ℓ (g0 v h)) x
      = chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y)) := by
    calc
      w1Fibre ℓ (wPairC ℓ (g0 v h)) x
          = ∫ y in acube ℓ, wPair ℓ (g0 v h) x y := by
              simp [w1Fibre, wPairC]
      _ = ∫ y : ℝ³, wPair ℓ (g0 v h) x y := mean_kernel_full hℓ hwi x
      _ = chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y)) := by
              simpa [g0f] using (kernel_fibre hℓ hwi x)
  -- chain (2): upper sandwich a.e.
  have hsw : ∀ᵐ y ∂(volume : Measure ℝ³),
      chiScale ℓ y * wScaled ℓ g0f (x - y)
        ≤ chiScale ℓ y * g0f (x - y) * (1 + 2 * u) := by
    have htr : ∀ᵐ y ∂(volume : Measure ℝ³), 0 ≤ g0f (x - y) :=
      ae_comp_sub_left (p := fun z : ℝ³ => 0 ≤ g0f z) hg0nn x
    filter_upwards [htr] with y hy
    have hsw' : wScaled ℓ g0f (x - y) ≤ g0f (x - y) * (1 + 2 * C * (R / ℓ) ^ 2) := by
      have hb := wScaled_sandwich_at (g := g0f) (ℓ := ℓ) (R := R) (r₁ := r₁) (C := C)
        hℓ hC hr₁ hT2 hg0supp hR.le hreg hcond hy
      exact hb.2
    have hχ : 0 ≤ chiScale ℓ y := chi_nonneg ((ℓ⁻¹) • y)
    calc
      chiScale ℓ y * wScaled ℓ g0f (x - y)
          ≤ chiScale ℓ y * (g0f (x - y) * (1 + 2 * C * (R / ℓ) ^ 2)) :=
              mul_le_mul_of_nonneg_left hsw' hχ
      _ = chiScale ℓ y * g0f (x - y) * (1 + 2 * C * (R / ℓ) ^ 2) := by ring
      _ = chiScale ℓ y * g0f (x - y) * (1 + 2 * u) := by
              dsimp [u]
              ring
  -- chain (3): A ≤ (1+2u)·B
  have hmono : (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y))
      ≤ (1 + 2 * u) * (∫ y : ℝ³, chiScale ℓ y * g0f (x - y)) := by
    have hLHS : MeasureTheory.Integrable (fun y : ℝ³ =>
        chiScale ℓ y * wScaled ℓ g0f (x - y)) := kernel_fibre_integrable hℓ hwi x
    have hRHS : MeasureTheory.Integrable (fun y : ℝ³ =>
        chiScale ℓ y * g0f (x - y)) := by
      have hg0c : MeasureTheory.Integrable (fun y : ℝ³ => g0f (x - y)) :=
        km_integrable_comp_sub_left hg0i x
      have hbnd : ∀ᵐ y ∂(volume : Measure ℝ³),
          ‖chiScale ℓ y * g0f (x - y)‖ ≤ chiSup * |g0f (x - y)| := by
        refine ae_of_all _ (fun y => ?_)
        calc
          ‖chiScale ℓ y * g0f (x - y)‖ = |chiScale ℓ y * g0f (x - y)| := by
                  rw [Real.norm_eq_abs]
          _ = |chiScale ℓ y| * |g0f (x - y)| := by rw [abs_mul]
          _ ≤ chiSup * |g0f (x - y)| := by
            exact mul_le_mul_of_nonneg_right (abs_chiScale_le_chiSup ℓ y) (abs_nonneg _)
      have hcm : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ y) volume :=
        (chiScale_continuous ℓ).aestronglyMeasurable
      have hg0m : AEStronglyMeasurable (fun y : ℝ³ => g0f (x - y)) volume :=
        km_aestronglyMeasurable_comp_sub_left hg0i.aestronglyMeasurable x
      exact MeasureTheory.Integrable.mono' (hg0c.abs.const_mul chiSup) (hcm.mul hg0m) hbnd
    have hbRHS : MeasureTheory.Integrable (fun y : ℝ³ =>
        (1 + 2 * u) * (chiScale ℓ y * g0f (x - y))) := hRHS.const_mul (1 + 2 * u)
    have hle' : ∀ᵐ y ∂(volume : Measure ℝ³),
        chiScale ℓ y * wScaled ℓ g0f (x - y)
          ≤ (1 + 2 * u) * (chiScale ℓ y * g0f (x - y)) := by
      filter_upwards [hsw] with y hy
      simpa [mul_assoc, mul_left_comm, mul_comm] using hy
    have hmi := integral_mono_ae hLHS hbRHS hle'
    rwa [integral_const_mul] at hmi
  -- chain (4): reflection
  have href : (∫ y : ℝ³, chiScale ℓ y * g0f (x - y))
      = ∫ y : ℝ³, g0f y * chiScale ℓ (x - y) := by
    have hg := integral_comp_sub_left
      (g := fun w : ℝ³ => g0f w * chiScale ℓ (x - w)) x
    calc
      (∫ y : ℝ³, chiScale ℓ y * g0f (x - y))
          = ∫ y : ℝ³, g0f (x - y) * chiScale ℓ y := by
              apply integral_congr_ae
              refine ae_of_all _ (fun y => ?_)
              ring
      _ = ∫ y : ℝ³, g0f y * chiScale ℓ (x - y) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hg
  -- chain (5): convolution UPPER side
  have hJ : (∫ y : ℝ³, g0f y * chiScale ℓ (x - y))
      ≤ chiScale ℓ x * (∫ y : ℝ³, g0f y) + Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|) := by
    have hJint : MeasureTheory.Integrable (fun y : ℝ³ =>
        g0f y * chiScale ℓ (x - y)) := by
      have hbnd : ∀ᵐ y ∂(volume : Measure ℝ³),
          ‖g0f y * chiScale ℓ (x - y)‖ ≤ |g0f y| * chiSup := by
        refine ae_of_all _ (fun y => ?_)
        calc
          ‖g0f y * chiScale ℓ (x - y)‖ = |g0f y * chiScale ℓ (x - y)| := by
                  rw [Real.norm_eq_abs]
          _ = |g0f y| * |chiScale ℓ (x - y)| := by rw [abs_mul]
          _ ≤ |g0f y| * chiSup := by
            exact mul_le_mul_of_nonneg_left (abs_chiScale_le_chiSup ℓ (x - y)) (abs_nonneg _)
      have hg0m : AEStronglyMeasurable g0f volume := hg0i.aestronglyMeasurable
      have hcm : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ (x - y)) volume :=
        (chiScale_continuous ℓ).comp (continuous_const.sub continuous_id) |>.aestronglyMeasurable
      exact MeasureTheory.Integrable.mono' (hg0i.abs.mul_const chiSup) (hg0m.mul hcm) hbnd
    have hcst : MeasureTheory.Integrable (fun y : ℝ³ => g0f y * chiScale ℓ x) :=
      hg0i.mul_const (chiScale ℓ x)
    have hdiff : (∫ y : ℝ³, g0f y * (chiScale ℓ (x - y) - chiScale ℓ x))
        = (∫ y : ℝ³, g0f y * chiScale ℓ (x - y))
          - chiScale ℓ x * (∫ y : ℝ³, g0f y) := by
      calc
        (∫ y : ℝ³, g0f y * (chiScale ℓ (x - y) - chiScale ℓ x))
            = ∫ y : ℝ³, g0f y * chiScale ℓ (x - y) - g0f y * chiScale ℓ x := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                ring
        _ = (∫ y : ℝ³, g0f y * chiScale ℓ (x - y))
            - (∫ y : ℝ³, g0f y * chiScale ℓ x) := by
                rw [← integral_sub hJint hcst]
        _ = (∫ y : ℝ³, g0f y * chiScale ℓ (x - y))
            - chiScale ℓ x * (∫ y : ℝ³, g0f y) := by
                rw [integral_mul_const]
                ring
    have habs : |∫ y : ℝ³, g0f y * (chiScale ℓ (x - y) - chiScale ℓ x)|
        ≤ Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|) := by
      simpa using hconv
    have hleU : (∫ y : ℝ³, g0f y * (chiScale ℓ (x - y) - chiScale ℓ x))
        ≤ Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|) := (abs_le.mp habs).2
    linarith
  -- assemble
  have hχ : 0 ≤ chiScale ℓ x := chi_nonneg ((ℓ⁻¹) • x)
  have hχle : chiScale ℓ x ≤ chiSup := by
    have h := abs_chiScale_le_chiSup ℓ x
    rwa [abs_of_nonneg hχ] at h
  have hu12 : 0 ≤ 1 + 2 * u := by nlinarith [hu0]
  have hBle : (∫ y : ℝ³, chiScale ℓ y * g0f (x - y))
      ≤ chiScale ℓ x * (∫ y : ℝ³, g0f y)
          + Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|) := by
    rw [href]
    exact hJ
  have hchain : chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y))
      ≤ chiScale ℓ x * ((1 + 2 * u) * (chiScale ℓ x * (∫ y : ℝ³, g0f y)
          + Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|))) := by
    have h1 : chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y))
        ≤ chiScale ℓ x * ((1 + 2 * u) * (∫ y : ℝ³, chiScale ℓ y * g0f (x - y))) :=
      mul_le_mul_of_nonneg_left hmono hχ
    have h2 : chiScale ℓ x * ((1 + 2 * u) * (∫ y : ℝ³, chiScale ℓ y * g0f (x - y)))
        ≤ chiScale ℓ x * ((1 + 2 * u) * (chiScale ℓ x * (∫ y : ℝ³, g0f y)
            + Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|))) := by
      have hm := mul_le_mul_of_nonneg_left hBle hu12
      exact mul_le_mul_of_nonneg_left hm hχ
    exact le_trans h1 h2
  have hfin : chiScale ℓ x * ((1 + 2 * u) * (chiScale ℓ x * (∫ y : ℝ³, g0f y)
      + Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|)))
      ≤ (8 * π * a v) * (chiScale ℓ x) ^ 2
        + (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ) := by
    rw [hg0int, hg0abs]
    have hc1 : 0 ≤ (8 * π * a v) := by
      exact mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * π) hAv
    have hx2 : (chiScale ℓ x) ^ 2 ≤ chiSup ^ 2 := by
      nlinarith [hχle, hχ]
    have hlead : (8 * π * a v) * (chiScale ℓ x) ^ 2 * (1 + 2 * u)
        ≤ (8 * π * a v) * (chiScale ℓ x) ^ 2
          + (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2) := by
      have hlead' : (8 * π * a v) * (chiScale ℓ x) ^ 2 * (2 * u)
          ≤ (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2) := by
        have hc3 : 2 * u = 2 * C * (R / ℓ) ^ 2 := by dsimp [u]; ring
        have hA : 0 ≤ 2 * C * (R / ℓ) ^ 2 := by positivity
        have hm := mul_le_mul_of_nonneg_right hx2 hA  -- χΛ²·A ≤ chiSup²·A
        have hm' := mul_le_mul_of_nonneg_left hm hc1
        calc
          (8 * π * a v) * (chiScale ℓ x) ^ 2 * (2 * u)
              = (8 * π * a v) * (chiScale ℓ x) ^ 2 * (2 * C * (R / ℓ) ^ 2) := by rw [hc3]
          _ = (8 * π * a v) * ((chiScale ℓ x) ^ 2 * (2 * C * (R / ℓ) ^ 2)) := by ring
          _ ≤ (8 * π * a v) * (chiSup ^ 2 * (2 * C * (R / ℓ) ^ 2)) := hm'
          _ = (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2) := by ring
      nlinarith
    have herr : chiScale ℓ x * (1 + 2 * u) * (Cχ * (R / ℓ) ^ 2 * (8 * π * a v))
        ≤ (R / ℓ) ^ 2 * (8 * π * a v) * (2 * chiSup * Cχ) := by
      have hc1e : 0 ≤ Cχ * (R / ℓ) ^ 2 * (8 * π * a v) := by
        exact mul_nonneg (mul_nonneg hCχ (sq_nonneg (R / ℓ)))
          (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * π) hAv)
      have h12 : 1 + 2 * u ≤ 2 := by nlinarith [hu_le]
      have hm : chiScale ℓ x * (1 + 2 * u) ≤ chiSup * 2 := by
        have hcx : chiScale ℓ x * (1 + 2 * u) ≤ chiSup * (1 + 2 * u) :=
          mul_le_mul_of_nonneg_right hχle (by nlinarith [hu0])
        exact le_trans hcx (mul_le_mul_of_nonneg_left h12 (le_of_lt chiSup_pos))
      calc
        chiScale ℓ x * (1 + 2 * u) * (Cχ * (R / ℓ) ^ 2 * (8 * π * a v))
            ≤ (chiSup * 2) * (Cχ * (R / ℓ) ^ 2 * (8 * π * a v)) :=
                mul_le_mul_of_nonneg_right hm hc1e
        _ = (R / ℓ) ^ 2 * (8 * π * a v) * (2 * chiSup * Cχ) := by ring
    nlinarith
  calc
    w1Fibre ℓ (wPairC ℓ (g0 v h)) x
        = chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y)) := hfibE
    _ ≤ chiScale ℓ x * ((1 + 2 * u) * (chiScale ℓ x * (∫ y : ℝ³, g0f y)
          + Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|))) := hchain
    _ ≤ (8 * π * a v) * (chiScale ℓ x) ^ 2
        + (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ) := hfin


/-- **S1-upper summed**: the one-body Q-mass is at most the χΛ²-mass plus the
dilute error: `qOneMass ≤ (8πa v)·Σ_i∫(Q_iΦ)²χΛ(xᵢ)² + Err·cnPlus` with
`Err := (R/ℓ)²·(8πa v)·(2C·chiSup² + 2·chiSup·Cχ)` (per-particle bound ×
`(Q_iΦ)² ≥ 0`, integrate, sum — mirror of `QMassLower.qmass_fibre_local_lower`). -/
lemma qmass_fibre_local_upper {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {C r₁ Cχ : ℝ}
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT2 : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2)
    (hCχ : 0 ≤ Cχ)
    (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      ≤ (8 * π * a v) * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
        + (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ) * cnPlus ℓ Φ := by
  classical
  let B : ℝ := 8 * π * a v
  let E : ℝ := (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ)
  have hAv : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hEnn : 0 ≤ E := by
    dsimp [E]
    have h1 : 0 ≤ (R / ℓ) ^ 2 * (8 * π * a v) := by
      exact mul_nonneg (sq_nonneg (R / ℓ)) (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * π) hAv)
    have h2 : 0 ≤ 2 * C * chiSup ^ 2 + 2 * chiSup * Cχ := by
      have hcs : 0 ≤ chiSup := le_of_lt chiSup_pos
      nlinarith
    exact mul_nonneg h1 h2
  -- per particle
  have hper : ∀ i : Fin N,
      (∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        ≤ B * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
          + E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
    intro i
    have hpw : ∀ x : X N,
        w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)
          ≤ (8 * π * a v) * (chiScale ℓ (x i)) ^ 2
            + (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ) := by
      intro x
      exact w1Fibre_pointwise_upper hR hv_nonneg hvrad hv_supp h hℓ hRℓ hC hr₁ hT2 hreg hcond hCχ hT (x i)
    let f : X N → ℝ := fun x => (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
    let g : X N → ℝ := fun x => (aQ ℓ i Φ x) ^ 2 * (B * (chiScale ℓ (x i)) ^ 2 + E)
    have hQc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
    have hgI : IntegrableOn g (abox N ℓ) volume := by
      dsimp [g]
      have h1 : Continuous (fun x : X N => B * (chiScale ℓ (x i)) ^ 2 + E) := by
        exact (continuous_const.mul
          ((chiScale_continuous ℓ).comp (continuous_apply i) |>.pow 2)).add continuous_const
      exact integrableOn_abox_of_continuous hℓ ((hQc.pow 2).mul h1)
    have hfI : IntegrableOn f (abox N ℓ) volume := by
      dsimp [f]
      have hFm : AEStronglyMeasurable (fun z : ℝ³ => w1Fibre ℓ (wPairC ℓ (g0 v h)) z)
          (volume.restrict (acube ℓ)) := by
        have hfac := fibre_acube_aem (ℓ := ℓ) (h := g0 v h) (g0_integrable hR hv_supp h)
        simpa [w1Fibre, wPairC] using hfac
      have hbnd : ∀ z : ℝ³, z ∈ acube ℓ →
          |w1Fibre ℓ (wPairC ℓ (g0 v h)) z| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
        intro z hz
        exact w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
      exact integrableOn_slot_fibre hℓ i hFm hbnd (hQc.pow 2)
    have hmono : (∫ x in abox N ℓ, f x) ≤ ∫ x in abox N ℓ, g x := by
      refine integral_mono hfI hgI ?_
      intro x
      dsimp [f, g, B, E]
      have hc : 0 ≤ (aQ ℓ i Φ x) ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_left (hpw x) hc
    have hsplit : (∫ x in abox N ℓ, g x)
        = B * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
          + E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
      dsimp [g]
      calc
        (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (B * (chiScale ℓ (x i)) ^ 2 + E))
            = ∫ x in abox N ℓ,
                B * ((aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2) + E * (aQ ℓ i Φ x) ^ 2 := by
                apply integral_congr_ae
                refine ae_of_all _ (fun x => ?_)
                ring
        _ = (∫ x in abox N ℓ, B * ((aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2))
            + (∫ x in abox N ℓ, E * (aQ ℓ i Φ x) ^ 2) := by
                exact integral_add (integrableOn_abox_of_continuous hℓ
                  (continuous_const.mul ((hQc.pow 2).mul
                    ((chiScale_continuous ℓ).comp (continuous_apply i) |>.pow 2))))
                  (integrableOn_abox_of_continuous hℓ (continuous_const.mul (hQc.pow 2)))
        _ = B * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
            + E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
                rw [integral_const_mul]
                rw [integral_const_mul]
    calc
      (∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
          = ∫ x in abox N ℓ, f x := by rfl
      _ ≤ ∫ x in abox N ℓ, g x := hmono
      _ = B * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
          + E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := hsplit
      _ = B * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
          + E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by rfl
  -- sum over i
  calc
    (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        ≤ ∑ i : Fin N,
            (B * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
              + E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) :=
            Finset.sum_le_sum (fun i hi => hper i)
    _ = B * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
        + E * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
            rw [Finset.sum_add_distrib]
            rw [← Finset.mul_sum]
            rw [← Finset.mul_sum]
    _ = (8 * π * a v) * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
        + (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ) * cnPlus ℓ Φ := by
            dsimp [B, E, cnPlus]


/-- **eq:Q2n0 at `ρ₀ = 0` (typeset goal; the mass-combination bound).**
Per the Session-51 design, the scalar `ρ₀` enters tied to the state
(`ρ₀ := cS1/(ℓ³J)`), and its `ρ₀ = 0` case must give

    q2PairWord − μ·qOneMass ≥ −μ·(8πa v)·q2MassChi − μ·Err·cnPlus,
    Err := (R/ℓ)²·(8πa v)·(2C·chiSup² + 2·chiSup·Cχ)

with the ERROR PLACEMENT:
  * `−μ·qOneMass ≥ −μ·(8πa v)·q2MassChi − μ·Err·cnPlus` comes from the
    S1-UPPER fibre bound `qmass_fibre_local_upper`
    (`qOneMass ≤ (8πa v)·q2MassChi + Err·cnPlus`, multiply by `−μ ≤ 0`);
  * `q2PairWord ≥ 0` comes from `w₂ ≥ 0` a.e. over the box: POINTWISE
    `w₂ = wPairC(g2) = wPairC(v)·(1−ω²)` (`w2rel_chosen`) with
    `wPairC(v) ≥ 0` (`wPairC_nonneg hv_nonneg`, v ≥ 0 pointwise) and
    `1−ω² ≥ 0` a.e. (`w₀ ∈ [0,1]` a.e., pulled back to the box);
  * combine by `nlinarith` (μ ≥ 0).  (Unproven `def` — the two ingredients
    above are the next lemmas.) -/
def q2n0_rho0_statement {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {μ : ℝ} (hμ : 0 ≤ μ)
    {C r₁ Cχ : ℝ} {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT2 : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2)
    (hCχ : 0 ≤ Cχ)
    (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2)
    (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) : Prop :=
  q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) - μ * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
    ≥ - μ * (8 * π * a v) * q2MassChi (ℓ := ℓ) (Φ := Φ)
      - μ * (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ) * cnPlus ℓ Φ


/-- Chosen `w₀` bounds a.e.: `0 ≤ w₀ ≤ 1` (Layer-3 T3 in chosen form). -/
lemma chosen_w0_bounds_ae {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (∀ᵐ x : ℝ³, 0 ≤ Classical.choose h x) ∧ (∀ᵐ x : ℝ³, Classical.choose h x ≤ 1) := by
  have hspec := w0_spec h
  exact scattering_bounds_ae (v := v) (R := R) hR hv_nonneg hvrad hv_supp hspec.1 hspec.2

/-- The `w₂ := wPairC(g2)` kernel is non-negative a.e. over the analysis box:
pointwise `w₂(x,y) = wPairC(v)(x,y)·(1−w₀(x−y)²)` (`w2rel_chosen`), with
`wPairC(v) ≥ 0` pointwise and `0 ≤ w₀ ≤ 1` a.e. -/
lemma w2_pair_nonneg_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      0 ≤ wPairC ℓ (g2 v h) (x i) (x j) := by
  classical
  have hw0nn : ∀ᵐ z : ℝ³, 0 ≤ Classical.choose h z := (chosen_w0_bounds_ae hR hv_nonneg hvrad hv_supp h).1
  have hw0le : ∀ᵐ z : ℝ³, Classical.choose h z ≤ 1 := (chosen_w0_bounds_ae hR hv_nonneg hvrad hv_supp h).2
  have hboth : ∀ᵐ z : ℝ³, (0 ≤ Classical.choose h z) ∧ (Classical.choose h z ≤ 1) := by
    filter_upwards [hw0nn, hw0le] with z hz0 hz1
    exact ⟨hz0, hz1⟩
  have htr : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      (0 ≤ Classical.choose h (x i - x j)) ∧ (Classical.choose h (x i - x j) ≤ 1) := by
    simpa using (ae_pair_pullback (N := N) hℓ hij hboth)
  filter_upwards [htr] with x hx
  rcases hx with ⟨hz0, hz1⟩
  have hw2eq : wPairC ℓ (g2 v h) (x i) (x j)
      = wPairC ℓ v (x i) (x j) * (1 - (Classical.choose h (x i - x j)) ^ 2) := by
    simpa [omC] using (w2rel_chosen h ℓ (x i) (x j))
  rw [hw2eq]
  have hwv : 0 ≤ wPairC ℓ v (x i) (x j) := wPairC_nonneg hv_nonneg ℓ (x i) (x j)
  have hsq : (Classical.choose h (x i - x j)) ^ 2 ≤ 1 := by
    nlinarith [hz0, hz1]
  have hfac : 0 ≤ 1 - (Classical.choose h (x i - x j)) ^ 2 := by nlinarith
  exact mul_nonneg hwv hfac


/-- Pointwise `P_jQ_i = Q_iP_j` on projections (i ≠ j, different coordinates
commute through the `aQ = 1 − aP` identity). -/
lemma aP_aQ_comm_eq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (x : X N) :
    aQ ℓ j (aP ℓ i Φ) x = aP ℓ i (aQ ℓ j Φ) x := by
  have hPic : Continuous (aP ℓ i Φ) := aP_continuous hℓ i hΦc
  have hPjc : Continuous (aP ℓ j Φ) := aP_continuous hℓ j hΦc
  calc
    aQ ℓ j (aP ℓ i Φ) x = aP ℓ i Φ x - aP ℓ j (aP ℓ i Φ) x := by
            rfl
    _ = aP ℓ i Φ x - aP ℓ i (aP ℓ j Φ) x := by
            rw [← aP_comm hℓ i j hΦc x]
    _ = aP ℓ i (aQ ℓ j Φ) x := by
            have hsub := aP_sub hℓ i (Φ := Φ) (Ψ := aP ℓ j Φ) hΦc hPjc x
            have hA : aQ ℓ j Φ = Φ - aP ℓ j Φ := by funext y; rfl
            rw [hA]
            exact hsub.symm

/-- Each summand of `q2PairWord` is non-negative (the integrand is
`(P_iQ_jΦ)²·w₂(xᵢ,xⱼ) ≥ 0` a.e. since `w₂ ≥ 0` a.e. over the box). -/
lemma q2Pair_summand_nonneg {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) (p : Fin N × Fin N)
    (hp : p ∈ pairSet N) :
    0 ≤ ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2) := by
  classical
  have hpij : p.1 ≠ p.2 := by
    simpa [pairSet] using (Finset.mem_filter.mp hp).2
  have hw2 : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      0 ≤ wPairC ℓ (g2 v h) (x p.1) (x p.2) :=
    w2_pair_nonneg_ae (N := N) hℓ hv_nonneg hvrad hR hv_supp h hRℓ p.1 p.2 hpij
  have hnon : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      0 ≤ (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2) := by
    filter_upwards [hw2] with x hx
    have hcomm : aQ ℓ p.2 (aP ℓ p.1 Φ) x = aP ℓ p.1 (aQ ℓ p.2 Φ) x :=
      aP_aQ_comm_eq hℓ (i := p.1) (j := p.2) hpij hΦc x
    rw [hcomm]
    nlinarith [sq_nonneg (aP ℓ p.1 (aQ ℓ p.2 Φ) x), hx]
  exact integral_nonneg_of_ae hnon

/-- **`q2PairWord ≥ 0`** (`w₂ ≥ 0` a.e. over the box; the ρ₀ = 0 ingredient). -/
lemma q2PairWord_nonneg {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    0 ≤ q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) := by
  classical
  rw [q2PairWord]
  apply Finset.sum_nonneg
  intro p hp
  exact q2Pair_summand_nonneg hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc p hp


/-- **The `ρ₀ = 0` mass-combination bound** (closing `q2n0_rho0_statement`):
`q2PairWord − μ·qOneMass ≥ −μ·(8πa v)·q2MassChi − μ·Err·cnPlus`, from
`q2PairWord_nonneg` + the S1-upper fibre bound `qmass_fibre_local_upper`
multiplied by `−μ ≤ 0`. -/
theorem q2n0_rho0 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {μ : ℝ} (hμ : 0 ≤ μ)
    {C r₁ Cχ : ℝ} {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT2 : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2)
    (hCχ : 0 ≤ Cχ)
    (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) - μ * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
    ≥ - μ * (8 * π * a v) * q2MassChi (ℓ := ℓ) (Φ := Φ)
      - μ * (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ) * cnPlus ℓ Φ := by
  classical
  let Err : ℝ := (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ)
  have hP : 0 ≤ q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) :=
    q2PairWord_nonneg hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hU0 := qmass_fibre_local_upper (N := N) hℓ (C := C) (r₁ := r₁) (Cχ := Cχ)
    hv_nonneg hvrad hR hv_supp h hRℓ hC hr₁ hT2 hreg hcond hCχ hT hΦc
  have hU : qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
      ≤ (8 * π * a v) * q2MassChi (ℓ := ℓ) (Φ := Φ) + Err * cnPlus ℓ Φ := by
    dsimp [Err]
    simpa [qOneMass, q2MassChi] using hU0
  have hUμ : μ * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
      ≤ μ * ((8 * π * a v) * q2MassChi (ℓ := ℓ) (Φ := Φ) + Err * cnPlus ℓ Φ) :=
    mul_le_mul_of_nonneg_left hU hμ
  have hfin : q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) - μ * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
      ≥ - μ * (8 * π * a v) * q2MassChi (ℓ := ℓ) (Φ := Φ)
        - μ * Err * cnPlus ℓ Φ := by
    nlinarith
  simpa [Err, mul_assoc, mul_left_comm, mul_comm] using hfin

/-- The typeset goal is closed: `q2n0_rho0_statement` holds under its
hypotheses (the ρ₀ = 0 branch of the eq:Q2n0 mass combination). -/
theorem q2n0_rho0_statement_closed {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {μ : ℝ} (hμ : 0 ≤ μ)
    {C r₁ Cχ : ℝ} {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT2 : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2)
    (hCχ : 0 ≤ Cχ)
    (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2)
    (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q2n0_rho0_statement hℓ hμ hv_nonneg hvrad hR hv_supp h hRℓ hC hr₁ hT2 hreg hcond hCχ hT i hΦc := by
  simpa [q2n0_rho0_statement] using
    (q2n0_rho0 (N := N) hℓ hμ (C := C) (r₁ := r₁) (Cχ := Cχ) hv_nonneg hvrad hR hv_supp h
      hRℓ hC hr₁ hT2 hreg hcond hCχ hT hΦc)


/-- **eq:Q2n0 at `ρ₀ = 0`, full word form**: the corpus `q2word` (= T₁ + T₂ +
T₃ + T₄ with T₂+T₃ = q2PairWord − μ·qOneMass) satisfies

`q2word ≥ q1PairWord + q4PairWord − μ·(8πa v)·q2MassChi − μ·Err·cnPlus`,

i.e. keeping the two pair terms (T₁, T₄) unbounded exactly as FS eq:Q2n0
does, with the mass-coefficient `(ρ₀−μ)·8πa = −μ·8πa` at `ρ₀ = 0`. -/
lemma q2word_lower_rho0 {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {C r₁ Cχ : ℝ} {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT2 : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2)
    (hCχ : 0 ≤ Cχ)
    (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
      ≥ q1PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) + q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
        - μ * (8 * π * a v) * q2MassChi (ℓ := ℓ) (Φ := Φ)
        - μ * (R / ℓ) ^ 2 * (8 * π * a v) * (2 * C * chiSup ^ 2 + 2 * chiSup * Cχ) * cnPlus ℓ Φ := by
  classical
  have hsplit : q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
      = q1PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
        + q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
        - μ * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
        + q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) := by
    dsimp [q1PairWord, q2PairWord, q4PairWord, qOneMass]
    unfold q2word
    ring
  have hR := q2n0_rho0 (N := N) hℓ hμ (C := C) (r₁ := r₁) (Cχ := Cχ) hv_nonneg hvrad hR hv_supp h
    hRℓ hC hr₁ hT2 hreg hcond hCχ hT hΦc
  -- hR : q2PairWord − μ·qOneMass ≥ −μ(8πa v)q2MassChi − μ·Err·cnPlus
  rw [hsplit]
  nlinarith

end BoseGases

end Submission
