import Mathlib.Analysis.Fourier.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BlockBound4.Defs
import Submission.Work.SmallBoxBridge.Cauchy.integrable_cModeForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BlockBound4.DiagWF` — infrastructure for R1

The shared definitions and the elementary (sorry-free) facts that the pieces of R1
(`Work.BlockBound4.diagW_lm_appbogolubov_explicitC`, FS's `lm:appbogolubov` at the
FAITHFUL one-particle-sum word `pDiagForm s (fsKinCoeff c₀)`) are stated in terms of.

Throughout, `M` is the PARTICLE NUMBER of the state (`Φ : X (n+1)` with
`M = (n : ℝ) + 1`).  FS's faithful (one-particle-sum) form of `lm:appbogolubov`
(`final_v2.tex` l.3762–3865) applies Bogoliubov at the `b`-operators with the
coefficient `𝒜(p) = |B|/(N̂+1)[|p|−c]₊² + 2K_s a` where `N̂ = M` is the particle
number, so the coefficient denominator is `N̂ + 1 = M + 1`; this is exactly the
factor by which the faithful word `Σ_i Q_iχ_i[√−Δ_i−c]₊²χ_iQ_i` differs from the
corpus's square-of-a-sum `kinPWord` (`K̂inPSuperadd.kinPWord_le_diagWord`:
`kinPWord ≤ (M+1)·pDiagForm`), and `pDiagForm ≥ kinPWord/(M+1)`.

The route (the corpus's faithful `1/(N̂+1)`-form, SESSION-285):

* `pDiagForm ≥ kinPWord/(M+1)` — the Cauchy–Schwarz step of the kinetic bridge
  (`Work.KinPSuperadd.kinPWord_le_diagWord`);
* `kinPWord/(M+1) + q4PairWord ≥ −(2π)⁻³∫ K^F·M − A₁` — `diag_content_integral`
  (the Bogoliubov mass term carries the particle number `M`, and the deficit
  `𝒜·s⁻³ − F/(M+1) = 2K_s·a·s⁻³` is EXACT);
* the sharp main term `∫ K^F·M ≤ …` is `diag_main_term_le_sharp`, built from FS's
  faithful exterior coefficient (`diagKF_le_ext`) and the interior constant bound;
* the four scalar comparisons of the resulting error terms
  (`d1_main_arith_F`, `d1_log_arith_F`, `d1_quart_arith_F`, `d1_int_arith`);
* the `A₁` mass `a1_mass_bound`.

Here: the faithful Bogoliubov coefficients `diagAF`, `diagKF`, their pointwise bounds,
the faithful QUARTIC integrand `d1QuartF = ((M+1)³/(4s⁹))·ℬ⁴/F³` with integrability
and exterior bound, and the interior integrability of `diagKF·M`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Work.BlockBound4

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1 The faithful Bogoliubov coefficients -/

/-- **FS's faithful `𝒜(q)`**: the coefficient of `b_q†b_q` in FS's `h(q)` with the
`|B|/(N̂+1)` normalisation (`|B| = s³`, `N̂ = M` the particle number),
`s³·[‖q‖−c₀]₊²/(M+1) + 2K_s·a v`, `K_s = d1Ks = 16π`. -/
noncomputable def diagAF (s c0 av M : ℝ) (q : ℝ³) : ℝ :=
  s ^ 3 * fsKinCoeff c0 ‖q‖ / (M + 1) + 2 * d1Ks * av

/-- **FS's faithful sharp Bogoliubov coefficient** `K(𝒜,ℬ) = (𝒜−√(𝒜²−ℬ²))/2` at the
faithful `𝒜 = diagAF`, `ℬ = d1Bcoef W`. -/
noncomputable def diagKF (s c0 av M : ℝ) (W : ℝ³ → ℝ) (q : ℝ³) : ℝ :=
  (diagAF s c0 av M q
    - Real.sqrt ((diagAF s c0 av M q) ^ 2 - (d1Bcoef W q) ^ 2)) / 2

lemma two_d1Ks_pos {av : ℝ} (hav : 0 < av) : 0 < 2 * d1Ks * av := by
  have h := d1Ks_pos
  positivity

lemma two_d1Ks_nonneg {av : ℝ} (hav : 0 ≤ av) : 0 ≤ 2 * d1Ks * av := by
  have h := d1Ks_pos
  positivity

lemma diagAF_ge_two {s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hav : 0 ≤ av) (q : ℝ³) :
    2 * d1Ks * av ≤ diagAF s c0 av M q := by
  have h1 : 0 ≤ s ^ 3 * fsKinCoeff c0 ‖q‖ / (M + 1) :=
    div_nonneg (mul_nonneg (by positivity) (fsKinCoeff_nonneg c0 ‖q‖)) (by linarith)
  unfold diagAF
  linarith

lemma diagAF_ge_F {s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hav : 0 ≤ av) (q : ℝ³) :
    s ^ 3 * fsKinCoeff c0 ‖q‖ / (M + 1) ≤ diagAF s c0 av M q := by
  have h : 0 ≤ 2 * d1Ks * av := two_d1Ks_nonneg hav
  unfold diagAF
  linarith

lemma diagAF_pos {s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hav : 0 < av) (q : ℝ³) :
    0 < diagAF s c0 av M q := by
  have h := diagAF_ge_two (c0 := c0) hs hM (le_of_lt hav) q
  have h2 := two_d1Ks_pos hav
  linarith

/-- the pairing coefficient never exceeds the faithful `A`-coefficient. -/
lemma abs_d1Bcoef_le_diagAF {s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hav : 0 < av)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) (q : ℝ³) :
    |d1Bcoef W q| ≤ diagAF s c0 av M q := by
  have h1 : |d1Bcoef W q| ≤ 16 * Real.pi * av := hWb q
  have h2 : 16 * Real.pi * av ≤ 2 * d1Ks * av := by
    unfold d1Ks
    nlinarith [Real.pi_pos, hav]
  exact le_trans h1 (le_trans h2 (diagAF_ge_two (c0 := c0) hs hM (le_of_lt hav) q))

lemma diagKF_nonneg {s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hav : 0 < av)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) (q : ℝ³) :
    0 ≤ diagKF s c0 av M W q := by
  have hA := diagAF_pos (c0 := c0) hs hM hav q
  have hB := abs_d1Bcoef_le_diagAF (c0 := c0) hs hM hav hWb q
  have hB2 : (d1Bcoef W q) ^ 2 ≤ (diagAF s c0 av M q) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  have hs' : Real.sqrt ((diagAF s c0 av M q) ^ 2 - (d1Bcoef W q) ^ 2)
      ≤ diagAF s c0 av M q := by
    rw [Real.sqrt_le_left hA.le]
    linarith [sq_nonneg (d1Bcoef W q)]
  unfold diagKF
  linarith

lemma diagKF_le_sharp {s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hav : 0 < av)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) (q : ℝ³) :
    diagKF s c0 av M W q
      ≤ (d1Bcoef W q) ^ 2 / (4 * diagAF s c0 av M q)
        + (d1Bcoef W q) ^ 4 / (4 * (diagAF s c0 av M q) ^ 3) := by
  have hA := diagAF_pos (c0 := c0) hs hM hav q
  have hB := abs_d1Bcoef_le_diagAF (c0 := c0) hs hM hav hWb q
  have hB2 : (d1Bcoef W q) ^ 2 ≤ (diagAF s c0 av M q) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  exact Commons.Analysis.Real.bogoliubov_coeff_sharp hA hB2

/-- **the exterior pointwise bound**: for `2c₀ ≤ ‖q‖` the faithful sharp coefficient is
dominated by `ℬ²(N̂+1)/(4s³F) + ℬ⁴(N̂+1)³/(4s⁹F³)` (`N̂+1 = M+1`, no `(M−1)` loss). -/
lemma diagKF_le_ext {s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hav : 0 < av) (hc0 : 0 < c0)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av)
    {q : ℝ³} (hq : 2 * c0 ≤ ‖q‖) :
    diagKF s c0 av M W q
      ≤ ((M + 1) / (4 * s ^ 3)) * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
        + ((M + 1) ^ 3 / (4 * s ^ 9)) * ((d1Bcoef W q) ^ 4 / (fsKinCoeff c0 ‖q‖) ^ 3) := by
  have hFs : 0 < fsKinCoeff c0 ‖q‖ := by
    rw [fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)]
    have h : 0 < ‖q‖ - c0 := by linarith
    positivity
  have hAg : s ^ 3 * fsKinCoeff c0 ‖q‖ / (M + 1) ≤ diagAF s c0 av M q :=
    diagAF_ge_F (c0 := c0) hs hM (le_of_lt hav) q
  have hpos : (0 : ℝ) < s ^ 3 * fsKinCoeff c0 ‖q‖ / (M + 1) :=
    div_pos (mul_pos (by positivity) hFs) (by linarith)
  have hmain : (d1Bcoef W q) ^ 2 / (4 * diagAF s c0 av M q)
      ≤ ((M + 1) / (4 * s ^ 3)) * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖) := by
    have heq : ((M + 1) / (4 * s ^ 3)) * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
        = ((d1Bcoef W q) ^ 2 / 4) / (s ^ 3 * fsKinCoeff c0 ‖q‖ / (M + 1)) := by
      field_simp; try ring
    have h1 : (d1Bcoef W q) ^ 2 / (4 * diagAF s c0 av M q)
        = ((d1Bcoef W q) ^ 2 / 4) / diagAF s c0 av M q := by
      field_simp
    rw [heq, h1]
    exact div_le_div_of_nonneg_left (by positivity) hpos hAg
  have hquart : (d1Bcoef W q) ^ 4 / (4 * (diagAF s c0 av M q) ^ 3)
      ≤ ((M + 1) ^ 3 / (4 * s ^ 9)) * ((d1Bcoef W q) ^ 4 / (fsKinCoeff c0 ‖q‖) ^ 3) := by
    have heq : ((M + 1) ^ 3 / (4 * s ^ 9)) * ((d1Bcoef W q) ^ 4 / (fsKinCoeff c0 ‖q‖) ^ 3)
        = ((d1Bcoef W q) ^ 4 / 4) / (s ^ 3 * fsKinCoeff c0 ‖q‖ / (M + 1)) ^ 3 := by
      field_simp; try ring
    have h1 : (d1Bcoef W q) ^ 4 / (4 * (diagAF s c0 av M q) ^ 3)
        = ((d1Bcoef W q) ^ 4 / 4) / (diagAF s c0 av M q) ^ 3 := by
      field_simp
    rw [heq, h1]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (le_of_lt hpos) hAg 3)
  linarith [diagKF_le_sharp (c0 := c0) hs hM hav hWb q, hmain, hquart]

/-- **the interior constant bound**: `K^F ≤ 2π·a + (π/2)·a`. -/
lemma diagKF_le_int_const {s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hav : 0 < av)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) (q : ℝ³) :
    diagKF s c0 av M W q ≤ 2 * Real.pi * av + Real.pi / 2 * av := by
  have hK : 0 < 2 * d1Ks * av := two_d1Ks_pos hav
  have hsh := diagKF_le_sharp (c0 := c0) hs hM hav hWb q
  have hAg : 2 * d1Ks * av ≤ diagAF s c0 av M q :=
    diagAF_ge_two (c0 := c0) hs hM (le_of_lt hav) q
  have hmain : (d1Bcoef W q) ^ 2 / (4 * diagAF s c0 av M q)
      ≤ (d1Bcoef W q) ^ 2 / (4 * (2 * d1Ks * av)) := by
    have h1 : (d1Bcoef W q) ^ 2 / (4 * diagAF s c0 av M q)
        = ((d1Bcoef W q) ^ 2 / 4) / diagAF s c0 av M q := by field_simp
    have h2 : (d1Bcoef W q) ^ 2 / (4 * (2 * d1Ks * av))
        = ((d1Bcoef W q) ^ 2 / 4) / (2 * d1Ks * av) := by field_simp
    rw [h1, h2]
    exact div_le_div_of_nonneg_left (by positivity) hK hAg
  have hquart : (d1Bcoef W q) ^ 4 / (4 * (diagAF s c0 av M q) ^ 3)
      ≤ (d1Bcoef W q) ^ 4 / (4 * (2 * d1Ks * av) ^ 3) := by
    have h1 : (d1Bcoef W q) ^ 4 / (4 * (diagAF s c0 av M q) ^ 3)
        = ((d1Bcoef W q) ^ 4 / 4) / (diagAF s c0 av M q) ^ 3 := by field_simp
    have h2 : (d1Bcoef W q) ^ 4 / (4 * (2 * d1Ks * av) ^ 3)
        = ((d1Bcoef W q) ^ 4 / 4) / (2 * d1Ks * av) ^ 3 := by field_simp
    rw [h1, h2]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (le_of_lt hK) hAg 3)
  have hB : (d1Bcoef W q) ^ 2 ≤ (16 * Real.pi * av) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hWb q) 2
  have hB4 : (d1Bcoef W q) ^ 4 ≤ (16 * Real.pi * av) ^ 4 := by
    have h := pow_le_pow_left₀ (sq_nonneg (d1Bcoef W q)) hB 2
    simpa only [← pow_mul] using h
  have h1 : (d1Bcoef W q) ^ 2 / (4 * (2 * d1Ks * av)) ≤ 2 * Real.pi * av := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (16 * Real.pi * av) ^ 2 ≤ (2 * Real.pi * av) * (4 * (2 * d1Ks * av)) := by
      unfold d1Ks
      nlinarith [Real.pi_pos, le_of_lt hav]
    linarith [hB, h2]
  have h3 : (d1Bcoef W q) ^ 4 / (4 * (2 * d1Ks * av) ^ 3) ≤ Real.pi / 2 * av := by
    rw [div_le_iff₀ (by positivity)]
    have h4 : (16 * Real.pi * av) ^ 4
        ≤ (Real.pi / 2 * av) * (4 * (2 * d1Ks * av) ^ 3) := by
      unfold d1Ks
      nlinarith [Real.pi_pos, le_of_lt hav]
    linarith [hB4, h4]
  linarith [hsh, hmain, hquart, h1, h3]

/-! ## 2 The faithful exterior quartic integrand -/

/-- **The faithful exterior quartic integrand** `((N̂+1)³/(4s⁹))·ℬ(q)⁴/[‖q‖−c₀]₊⁶` — the
second summand of `diagKF_le_ext` (`N̂ + 1 = M + 1`). -/
noncomputable def d1QuartF (s c0 av M : ℝ) (W : ℝ³ → ℝ) (q : ℝ³) : ℝ :=
  ((M + 1) ^ 3 / (4 * s ^ 9)) * ((d1Bcoef W q) ^ 4 * ((fsKinCoeff c0 ‖q‖) ^ 3)⁻¹)

lemma d1QuartF_nonneg {s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (W : ℝ³ → ℝ) (q : ℝ³) :
    0 ≤ d1QuartF s c0 av M W q := by
  unfold d1QuartF
  exact mul_nonneg (by positivity)
    (mul_nonneg (by positivity)
      (inv_nonneg.mpr (pow_nonneg (fsKinCoeff_nonneg c0 ‖q‖) 3)))

/-- **the exterior bound of the faithful quartic integrand**: on `{2c₀ ≤ ‖q‖}`,

  `((M+1)³/(4s⁹))·ℬ⁴/F³ = ((M+1)³/(4s⁹))·ℬ⁴/[(‖q‖−c₀)⁶]`,

so `pBdd_exterior_pow4_inv_sub_sq6_le` gives the `‖q‖`-tail bound. -/
theorem d1_ext_quartF_le {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 0 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) :
    (∫ q in d1Ext c0, d1QuartF s c0 av M W q)
      ≤ ((M + 1) ^ 3 / (4 * s ^ 9)) * (64 * (16 * Real.pi * av) ^ 4
            * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹)) := by
  have hpt : ∀ q : ℝ³, q ∈ d1Ext c0 →
      d1QuartF s c0 av M W q
        = ((M + 1) ^ 3 / (4 * s ^ 9)) * ((d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹) := by
    intro q hq
    have hq' : 2 * c0 ≤ ‖q‖ := hq
    have hFs : fsKinCoeff c0 ‖q‖ = (‖q‖ - c0) ^ 2 :=
      fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)
    unfold d1QuartF
    rw [hFs, show ((‖q‖ - c0) ^ 2) ^ 3 = (‖q‖ - c0) ^ 6 from by ring]
  have hcongr : (∫ q in d1Ext c0, d1QuartF s c0 av M W q)
      = ((M + 1) ^ 3 / (4 * s ^ 9))
        * (∫ q in d1Ext c0, (d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_d1Ext c0) (fun q hq => ?_)
    rw [hpt q hq]
  rw [hcongr]
  have hb : (∫ q in d1Ext c0, (d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹)
      ≤ 64 * (16 * Real.pi * av) ^ 4 * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹) := by
    have h := pBdd_exterior_pow4_inv_sub_sq6_le (c := c0) (a := av) (C₀ := 16 * Real.pi)
      hc0 hav (by positivity) (F := d1Bcoef W) hWb
    simpa only [d1Ext] using h
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- **integrability of the faithful quartic integrand on the exterior.** -/
theorem integrableOn_d1QuartF {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 0 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) :
    IntegrableOn (d1QuartF s c0 av M W) (d1Ext c0) volume := by
  have h6 : Integrable (fun q : ℝ³ => ((‖q‖ : ℝ)⁻¹) ^ 6)
      ((volume : Measure ℝ³).restrict (d1Ext c0)) :=
    (integrableOn_inv_six_tail (by linarith : (0 : ℝ) < c0)).mono_set (d1Ext_subset hc0)
  have hmeasF : Measurable (fun q : ℝ³ => fsKinCoeff c0 ‖q‖) := by
    unfold fsKinCoeff
    fun_prop
  refine Integrable.mono' (μ := (volume : Measure ℝ³).restrict (d1Ext c0))
    (g := fun q : ℝ³ =>
      ((M + 1) ^ 3 / (4 * s ^ 9)) * (64 * (16 * Real.pi * av) ^ 4) * ((‖q‖ : ℝ)⁻¹) ^ 6)
    (h6.const_mul (((M + 1) ^ 3 / (4 * s ^ 9)) * (64 * (16 * Real.pi * av) ^ 4))) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have hB : Measurable (fun q : ℝ³ => d1Bcoef W q) := hWmeas
    unfold d1QuartF
    exact measurable_const.mul ((hB.pow_const 4).div (hmeasF.pow_const 3))
  · filter_upwards [ae_restrict_mem (measurableSet_d1Ext c0)] with q hq
    have hq' : 2 * c0 ≤ ‖q‖ := hq
    have hFs : fsKinCoeff c0 ‖q‖ = (‖q‖ - c0) ^ 2 :=
      fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)
    have hFs3 : (fsKinCoeff c0 ‖q‖) ^ 3 = (‖q‖ - c0) ^ 6 := by
      rw [hFs]; ring
    have hB4 : (d1Bcoef W q) ^ 4 ≤ (16 * Real.pi * av) ^ 4 := by
      have h2 : (d1Bcoef W q) ^ 2 ≤ (16 * Real.pi * av) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hWb q) 2
      calc (d1Bcoef W q) ^ 4 = ((d1Bcoef W q) ^ 2) ^ 2 := by ring
        _ ≤ ((16 * Real.pi * av) ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
        _ = (16 * Real.pi * av) ^ 4 := by ring
    have hhalf : ‖q‖ / 2 ≤ ‖q‖ - c0 := by linarith
    have h6le : ((‖q‖ - c0) ^ 6)⁻¹ ≤ 64 * ((‖q‖ : ℝ)⁻¹) ^ 6 := by
      have hc1 : 0 < ‖q‖ - c0 := by linarith
      have h1 : (0 : ℝ) < (‖q‖ - c0) ^ 6 := by positivity
      have h3 : ((‖q‖ / 2) ^ 6 : ℝ) ≤ (‖q‖ - c0) ^ 6 :=
        pow_le_pow_left₀ (by positivity) hhalf 6
      have key : (64 : ℝ) * ((‖q‖ : ℝ)⁻¹) ^ 6 = ((‖q‖ ^ 6) / 64)⁻¹ := by
        rw [inv_pow, inv_div]; ring
      have hq2 : (0 : ℝ) < ‖q‖ := by linarith
      rw [key, inv_le_inv₀ (a := (‖q‖ - c0) ^ 6) h1 (by positivity)]
      nlinarith [h3]
    have hkey : d1QuartF s c0 av M W q
        = ((M + 1) ^ 3 / (4 * s ^ 9)) * ((d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹) := by
      unfold d1QuartF
      rw [hFs3]
    rw [Real.norm_of_nonneg (d1QuartF_nonneg (s := s) (M := M) hs hM W q), hkey]
    have hle1 : (d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹
        ≤ (16 * Real.pi * av) ^ 4 * (64 * ((‖q‖ : ℝ)⁻¹) ^ 6) :=
      mul_le_mul hB4 h6le (by positivity) (by positivity)
    have hcst : (0 : ℝ) ≤ (M + 1) ^ 3 / (4 * s ^ 9) := by positivity
    calc ((M + 1) ^ 3 / (4 * s ^ 9)) * ((d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹)
        ≤ ((M + 1) ^ 3 / (4 * s ^ 9))
            * ((16 * Real.pi * av) ^ 4 * (64 * ((‖q‖ : ℝ)⁻¹) ^ 6)) :=
          mul_le_mul_of_nonneg_left hle1 hcst
      _ = ((M + 1) ^ 3 / (4 * s ^ 9)) * (64 * (16 * Real.pi * av) ^ 4) * ((‖q‖ : ℝ)⁻¹) ^ 6 := by
          ring

/-! ## 3 Integrability of the faithful coefficient on the interior -/

/-- **Integrability of `K^F·N̂` on the interior ball** (`‖q‖ < 2c₀`) with `N̂ = M` the
particle number, where it is bounded by the constant `M·(2π·a + (π/2)·a)`. -/
theorem integrableOn_diagKF_int {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 0 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) :
    IntegrableOn (fun q => diagKF s c0 av M W q * M) (d1Int c0) volume := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (d1Int c0)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    refine lt_of_le_of_lt (measure_mono ?_)
      (isCompact_closedBall (0 : ℝ³) (2 * c0)).measure_lt_top
    intro q hq
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [d1Int, Metric.mem_ball, dist_eq_norm, sub_zero] at hq
    exact hq.le
  refine Integrable.mono' (g := fun _ : ℝ³ => M * (2 * Real.pi * av + Real.pi / 2 * av))
    (integrable_const _) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have hAcont : Continuous (fun q : ℝ³ => diagAF s c0 av M q) := by
      unfold diagAF fsKinCoeff
      fun_prop
    have hB : Measurable (fun q : ℝ³ => d1Bcoef W q) := hWmeas
    unfold diagKF
    exact ((hAcont.measurable.sub
      (((hAcont.measurable.pow_const 2).sub (hB.pow_const 2)).sqrt)).div_const 2).mul_const M
  · filter_upwards with q
    rw [Real.norm_of_nonneg (mul_nonneg
      (diagKF_nonneg (c0 := c0) hs hM hav hWb q) hM)]
    calc diagKF s c0 av M W q * M
        ≤ (2 * Real.pi * av + Real.pi / 2 * av) * M :=
          mul_le_mul_of_nonneg_right (diagKF_le_int_const (c0 := c0) hs hM hav hWb q) hM
      _ = M * (2 * Real.pi * av + Real.pi / 2 * av) := by ring

end Work.BlockBound4
