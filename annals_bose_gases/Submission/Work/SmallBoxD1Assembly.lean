import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Commons.Analysis.Integral.integral_norm_neg_six_tail
import Submission.Commons.Analysis.Real.bogoliubov_coeff_sharp
import Submission.Work.SmallBoxBogPBracket
import Submission.Work.SmallBoxBogWS1Bound
import Submission.Work.SmallBoxD1A1Bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-284 — the D1 assembly (`lm:appbogolubov`, STEPS 3–5)

The D1 chain: for the small box `Λ(s)` and a state `Φ : X (N+1)` with `‖Φ‖ = 1`,

  `kinPWord s c₀ Φ + q4PairWord = (2π)^{-3} ∫_q [F(q)P(q) + ℬ(q)s^{-3}R(q)]`

(`SmallBoxD1Integral.kinPWord_add_q4PairWord_eq_integral`, STEP 1), and the per-`q`
Bogoliubov content bound (`SmallBoxD1Integral.d1_content_at`, STEP 2) turns each summand
into `-K(𝒜,ℬ)·M - (𝒜s^{-3} - F)·P` for any `0 < 𝒜`, `|ℬ| ≤ 𝒜`, with
`K(𝒜,ℬ) = (𝒜 - √(𝒜²-ℬ²))/2` the sharp Bogoliubov coefficient.

This module performs STEP 3: the choice `𝒜(q) := s³F(q)(M-1)/M + 2K_s·a`,
`ℬ(q) := Ŵ₁(q)` (`K_s := 16π`, `M := N+1`), the integration over `q`, and the
reduction of the resulting two terms to

  `-(2π)^{-3}∫_q M·K(𝒜,ℬ) - 2K_s a s^{-3}(2π)^{-3}∫_q (P_{u_q}+P_{v_q})`.

The first term is the D1 main term (`(2π)^{-3}∫ℬ²/F` etc., STEPS 4), the second is the
`A₁`-mass closed in `SmallBoxD1A1Bound` (`a1_mass_bound`).
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

/-! ## 1 The FS coefficients -/

/-- `K_s := 16π` — FS's universal constant of `eq:A1estimate` (the `C₀` of `∫W₁ ≤ C₀·a v`). -/
noncomputable def d1Ks : ℝ := 16 * Real.pi

lemma d1Ks_pos : 0 < d1Ks := by unfold d1Ks; positivity

/-- FS's kinetic-plus-`A₁` coefficient `𝒜(q) = s³[‖q‖−c]₊²(M−1)/M + 2K_s·a`. -/
noncomputable def d1Acoef (s c0 av M : ℝ) (q : ℝ³) : ℝ :=
  s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M + 2 * d1Ks * av

/-- FS's `ℬ(q) = Ŵ₁(q)`. -/
noncomputable def d1Bcoef (W : ℝ³ → ℝ) (q : ℝ³) : ℝ := pairW W q

/-- FS's sharp Bogoliubov coefficient `K(𝒜,ℬ) = (𝒜 − √(𝒜²−ℬ²))/2`. -/
noncomputable def d1Kcoef (s c0 av M : ℝ) (W : ℝ³ → ℝ) (q : ℝ³) : ℝ :=
  (d1Acoef s c0 av M q
    - Real.sqrt ((d1Acoef s c0 av M q) ^ 2 - (d1Bcoef W q) ^ 2)) / 2

/-- the deficit coefficient `𝒜(q)s^{-3} − F(q)`. -/
noncomputable def d1Deficit (s c0 av M : ℝ) (W : ℝ³ → ℝ) (q : ℝ³) : ℝ :=
  d1Acoef s c0 av M q * (s ^ 3)⁻¹ - fsKinCoeff c0 ‖q‖

/-- the pairing integrand of STEP 1. -/
noncomputable def d1PairPart (s : ℝ) (W : ℝ³ → ℝ) {n : ℕ} (Φ : X (n + 1) → ℝ)
    (q : ℝ³) : ℝ :=
  pairW W q * ((s ^ 3)⁻¹ * pairR s Φ q)

/-! ## 2 The elementary properties of the coefficients -/

lemma d1Acoef_pos {s c0 av M : ℝ} (hs : 0 < s) (hM : 2 ≤ M) (hav : 0 < av) (q : ℝ³) :
    0 < d1Acoef s c0 av M q := by
  have h1 : 0 ≤ s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) (fsKinCoeff_nonneg c0 ‖q‖))
      (by linarith)) (by linarith)
  have h2 : 0 < 2 * d1Ks * av := by have := d1Ks_pos; positivity
  unfold d1Acoef
  linarith

lemma d1Acoef_ge_two {s c0 av M : ℝ} (hs : 0 < s) (hM : 2 ≤ M) (hav : 0 < av) (q : ℝ³) :
    2 * d1Ks * av ≤ d1Acoef s c0 av M q := by
  have h1 : 0 ≤ s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) (fsKinCoeff_nonneg c0 ‖q‖))
      (by linarith)) (by linarith)
  unfold d1Acoef
  linarith

/-- `|pairW W q| ≤ ∫|W|` — the Fourier transform is dominated by the `L¹` mass. -/
lemma abs_pairW_le_integral_abs {W : ℝ³ → ℝ} (q : ℝ³) :
    |pairW W q| ≤ ∫ x : ℝ³, |W x| := by
  rw [pairW_eq_cfourier_re]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm (e := Real.fourierChar)
    (μ := volume) (L := innerₗ ℝ³) (f := fun x : ℝ³ => (W x : ℂ)) ((2 * π : ℝ)⁻¹ • q)
  have hcf : cfourier W = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ³)
      (fun x : ℝ³ => (W x : ℂ)) := rfl
  rw [hcf]
  have hnorm : (∫ v : ℝ³, ‖((W v : ℂ))‖) = ∫ x : ℝ³, |W x| := by
    simp only [Complex.norm_real, Real.norm_eq_abs]
  linarith [h, hnorm]

/-- the standing bound `|ℬ(q)| ≤ 16π·(a v)` for `W₁ = wScaled s (g0 v h)`. -/
lemma abs_pairW_wScaled_g0_le {v : ℝ³ → ℝ} {R s : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (q : ℝ³) :
    |pairW (wScaled s (g0 v h)) q| ≤ 16 * Real.pi * a v := by
  refine le_trans (abs_pairW_le_integral_abs q) ?_
  exact wScaled_g0_abs_integral_le hR hv_nonneg hvrad hv_supp h hs hRs

/-! ## 3 STEP 3a — the pointwise content bound at the FS coefficients -/

theorem d1_content_point {p : ℕ} {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av)
    (hM : M = (p : ℝ) + 2)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |pairW W q| ≤ 16 * Real.pi * av)
    {Φ : X (p + 2) → ℝ} (hΦ : Continuous Φ)
    (hΦnorm : (∫ x in abox (p + 2) s, (Φ x) ^ 2) = 1) (q : ℝ³) :
    - d1Kcoef s c0 av M W q * M
      - d1Deficit s c0 av M W q * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
    ≤ fsKinCoeff c0 ‖q‖ * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
      + (d1Bcoef W q * (s ^ 3)⁻¹) * pairR s Φ q := by
  have hM2 : 2 ≤ M := by rw [hM]; linarith
  have hA : 0 < d1Acoef s c0 av M q := d1Acoef_pos hs hM2 hav q
  have hB : |d1Bcoef W q| ≤ d1Acoef s c0 av M q := by
    have h1 : |d1Bcoef W q| ≤ 16 * Real.pi * av := hWb q
    have h2 : 16 * Real.pi * av ≤ 2 * d1Ks * av := by
      have hp : (0 : ℝ) < Real.pi := Real.pi_pos
      unfold d1Ks
      nlinarith [le_of_lt hav]
    exact le_trans h1 (le_trans h2 (d1Acoef_ge_two hs hM2 hav q))
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have h := d1_content_bogoliubov (n := p + 1) (s := s)
    (A₀ := d1Acoef s c0 av M q * (s ^ 3)⁻¹) (B₀ := d1Bcoef W q * (s ^ 3)⁻¹)
    (F := fsKinCoeff c0 ‖q‖) hs (p := q) hΦ
    (mul_pos hA (inv_pos.mpr hs3))
    (by rw [abs_mul, abs_of_pos (inv_pos.mpr hs3)]
        exact mul_le_mul_of_nonneg_right hB (le_of_lt (inv_pos.mpr hs3)))
  rw [integral_chiScale_sq_acube hs, hΦnorm] at h
  have hcast : (↑(p + 1) : ℝ) + 1 = M := by rw [hM]; push_cast; ring
  have hK : ((d1Acoef s c0 av M q * (s ^ 3)⁻¹
        - Real.sqrt ((d1Acoef s c0 av M q * (s ^ 3)⁻¹) ^ 2
            - (d1Bcoef W q * (s ^ 3)⁻¹) ^ 2)) / 2) * s ^ 3
      = (d1Acoef s c0 av M q - Real.sqrt (d1Acoef s c0 av M q ^ 2 - d1Bcoef W q ^ 2)) / 2 := by
    rw [show d1Acoef s c0 av M q * (s ^ 3)⁻¹ = (s ^ 3)⁻¹ * d1Acoef s c0 av M q
        from mul_comm _ _,
      show d1Bcoef W q * (s ^ 3)⁻¹ = (s ^ 3)⁻¹ * d1Bcoef W q from mul_comm _ _,
      bogoliubov_coeff_smul (A := d1Acoef s c0 av M q) (B := d1Bcoef W q)
        (c := (s ^ 3)⁻¹) (inv_pos.mpr hs3)]
    field_simp
  have hKtr : -((d1Acoef s c0 av M q * (s ^ 3)⁻¹
        - Real.sqrt ((d1Acoef s c0 av M q * (s ^ 3)⁻¹) ^ 2
            - (d1Bcoef W q * (s ^ 3)⁻¹) ^ 2)) / 2) * (s ^ 3 * (↑(p + 1) + 1) * 1)
      = -((d1Acoef s c0 av M q - Real.sqrt (d1Acoef s c0 av M q ^ 2 - d1Bcoef W q ^ 2)) / 2)
          * M := by
    rw [hcast, mul_one]
    rw [show -((d1Acoef s c0 av M q * (s ^ 3)⁻¹
          - Real.sqrt ((d1Acoef s c0 av M q * (s ^ 3)⁻¹) ^ 2
              - (d1Bcoef W q * (s ^ 3)⁻¹) ^ 2)) / 2) * (s ^ 3 * M)
        = -(((d1Acoef s c0 av M q * (s ^ 3)⁻¹
          - Real.sqrt ((d1Acoef s c0 av M q * (s ^ 3)⁻¹) ^ 2
              - (d1Bcoef W q * (s ^ 3)⁻¹) ^ 2)) / 2) * s ^ 3) * M from by ring]
    rw [hK]
  rw [hKtr] at h
  unfold d1Kcoef d1Deficit pairR
  linarith [h]


/-! ## 4 Integrability of the main-term integrands -/

lemma fsKinCoeff_eq_of_le {c r : ℝ} (h : c ≤ r) : fsKinCoeff c r = (r - c) ^ 2 := by
  unfold fsKinCoeff
  rw [max_eq_left]
  linarith

/-- the exterior region `{q | 2c ≤ ‖q‖}` (the OPEN ball `{‖q‖ < 2c}` is then the exact
complement). -/
def d1Ext (c : ℝ) : Set ℝ³ := {q : ℝ³ | 2 * c ≤ ‖q‖}

lemma measurableSet_d1Ext (c : ℝ) : MeasurableSet (d1Ext c) :=
  measurableSet_le measurable_const measurable_norm

/-- the interior open ball (in metric form, so that `momentum_ball_integral_one` applies). -/
def d1Int (c : ℝ) : Set ℝ³ := Metric.ball (0 : ℝ³) (2 * c)

lemma measurableSet_d1Int (c : ℝ) : MeasurableSet (d1Int c) :=
  Metric.isOpen_ball.measurableSet

lemma d1Int_union_d1Ext (c : ℝ) : d1Int c ∪ d1Ext c = Set.univ := by
  refine Set.eq_univ_of_forall fun q => ?_
  rw [Set.mem_union, d1Int, Metric.mem_ball, dist_eq_norm, sub_zero]
  exact lt_or_ge ‖q‖ (2 * c)

/-- the crude exterior weight bound `1/[‖q‖−c]₊² ≤ 4/‖q‖²` for `2c ≤ ‖q‖`. -/
lemma d1_inv_fsKinCoeff_le {c0 : ℝ} (hc0 : 0 < c0) {q : ℝ³} (hq : 2 * c0 ≤ ‖q‖) :
    (fsKinCoeff c0 ‖q‖)⁻¹ ≤ 4 / ‖q‖ ^ 2 := by
  have h1 : c0 ≤ ‖q‖ := by linarith
  have h2 : 0 < ‖q‖ - c0 := by linarith
  have h3 : 0 < ‖q‖ := by linarith
  rw [fsKinCoeff_eq_of_le h1, inv_eq_one_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : ‖q‖ / 2 ≤ ‖q‖ - c0 := by linarith
  nlinarith [norm_nonneg q]

/-- the sharp main-term integrand `ℬ²/(4𝒜)`. -/
noncomputable def d1MainInt (s c0 av M : ℝ) (W : ℝ³ → ℝ) (q : ℝ³) : ℝ :=
  (d1Bcoef W q) ^ 2 / (4 * d1Acoef s c0 av M q)

/-- the quartic integrand `ℬ⁴/(4𝒜³)`. -/
noncomputable def d1QuartInt (s c0 av M : ℝ) (W : ℝ³ → ℝ) (q : ℝ³) : ℝ :=
  (d1Bcoef W q) ^ 4 / (4 * (d1Acoef s c0 av M q) ^ 3)

lemma d1MainInt_nonneg {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    (W : ℝ³ → ℝ) (q : ℝ³) : 0 ≤ d1MainInt s c0 av M W q := by
  unfold d1MainInt
  refine div_nonneg (sq_nonneg _) ?_
  have := d1Acoef_pos (c0 := c0) hs hM hav q
  linarith

lemma d1QuartInt_nonneg {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    (W : ℝ³ → ℝ) (q : ℝ³) : 0 ≤ d1QuartInt s c0 av M W q := by
  unfold d1QuartInt
  refine div_nonneg (by positivity) ?_
  have := d1Acoef_pos (c0 := c0) hs hM hav q
  nlinarith [sq_nonneg (d1Acoef s c0 av M q)]

/-- **the interior bound**: on `{‖q‖ ≤ 2c}` the main-term integrand is bounded by `2π·(a v)`. -/
lemma d1MainInt_le_of_interior {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) (q : ℝ³) :
    d1MainInt s c0 av M W q ≤ 2 * Real.pi * av := by
  have hA : (0 : ℝ) < d1Acoef s c0 av M q := d1Acoef_pos hs hM hav q
  have hAg : 2 * d1Ks * av ≤ d1Acoef s c0 av M q := d1Acoef_ge_two hs hM hav q
  have h1 : |d1Bcoef W q| ≤ 16 * Real.pi * av := hWb q
  have h2 : (d1Bcoef W q) ^ 2 ≤ (16 * Real.pi * av) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hav0 : 0 ≤ av := le_of_lt hav
  unfold d1MainInt
  rw [div_le_iff₀ (by linarith)]
  have h3 : (16 * Real.pi * av) ^ 2 ≤ (2 * Real.pi * av) * (4 * (2 * d1Ks * av)) := by
    unfold d1Ks
    nlinarith [Real.pi_pos, hav0]
  have h4 : (2 * Real.pi * av) * (4 * (2 * d1Ks * av))
      ≤ (2 * Real.pi * av) * (4 * d1Acoef s c0 av M q) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith [h2, h3, h4]

/-- **the exterior bound**: on `{2c ≤ ‖q‖}` the main-term integrand is dominated by
`(M/(s³(M−1)))·(ℬ²/‖q‖²)`. -/
lemma d1MainInt_le_of_exterior {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    (hc0 : 0 < c0) {W : ℝ³ → ℝ} {q : ℝ³} (hq : 2 * c0 ≤ ‖q‖) :
    d1MainInt s c0 av M W q ≤ (M / (s ^ 3 * (M - 1))) * ((d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) := by
  have hFs : 0 < fsKinCoeff c0 ‖q‖ := by
    rw [fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)]
    have h : c0 < ‖q‖ := by linarith
    positivity
  have hA : 0 < d1Acoef s c0 av M q := d1Acoef_pos hs hM hav q
  have hs3 : 0 < s ^ 3 := by positivity
  have hM1 : 0 < M - 1 := by linarith
  have hnorm : 0 < ‖q‖ ^ 2 := by
    have h : 0 < ‖q‖ := by linarith
    positivity
  have hAg : s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M ≤ d1Acoef s c0 av M q := by
    unfold d1Acoef
    have h : 0 ≤ 2 * d1Ks * av := by have := d1Ks_pos; positivity
    linarith
  have h1 : 1 / (4 * d1Acoef s c0 av M q)
      ≤ M / (4 * s ^ 3 * (M - 1)) * (fsKinCoeff c0 ‖q‖)⁻¹ := by
    have ha : 1 / (4 * d1Acoef s c0 av M q)
        ≤ 1 / (4 * (s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hb : 1 / (4 * (s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M))
        = M / (4 * s ^ 3 * (M - 1)) * (fsKinCoeff c0 ‖q‖)⁻¹ := by
      field_simp
    linarith [ha, hb]
  have h2 : M / (4 * s ^ 3 * (M - 1)) * (fsKinCoeff c0 ‖q‖)⁻¹
      ≤ M / (4 * s ^ 3 * (M - 1)) * (4 / ‖q‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (d1_inv_fsKinCoeff_le hc0 hq) (by positivity)
  have h3 : M / (4 * s ^ 3 * (M - 1)) * (4 / ‖q‖ ^ 2)
      = M / (s ^ 3 * (M - 1)) * (1 / ‖q‖ ^ 2) := by
    field_simp
  have hkey : 1 / (4 * d1Acoef s c0 av M q) ≤ M / (s ^ 3 * (M - 1)) * (1 / ‖q‖ ^ 2) := by
    linarith [h1, h2, h3]
  have hfin : d1MainInt s c0 av M W q
      = (d1Bcoef W q) ^ 2 * (1 / (4 * d1Acoef s c0 av M q)) := by
    unfold d1MainInt
    rw [div_eq_mul_inv, inv_eq_one_div]
  rw [hfin]
  calc (d1Bcoef W q) ^ 2 * (1 / (4 * d1Acoef s c0 av M q))
      ≤ (d1Bcoef W q) ^ 2 * (M / (s ^ 3 * (M - 1)) * (1 / ‖q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    _ = M / (s ^ 3 * (M - 1)) * ((d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) := by ring

/-- **the exterior bound in the SHARP form** (weight `ℬ²/F`, with the `1/4` of `ℬ²/(4𝒜)`):
`ℬ²/(4𝒜) ≤ (M/(4s³(M−1)))·ℬ²/F` on `{2c ≤ ‖q‖}`. -/
lemma d1MainInt_le_of_exterior_F {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    (hc0 : 0 < c0) {W : ℝ³ → ℝ} {q : ℝ³} (hq : 2 * c0 ≤ ‖q‖) :
    d1MainInt s c0 av M W q
      ≤ (M / (4 * s ^ 3 * (M - 1))) * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖) := by
  have hFs : 0 < fsKinCoeff c0 ‖q‖ := by
    rw [fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)]
    have h : 0 < ‖q‖ - c0 := by linarith
    positivity
  have hA : 0 < d1Acoef s c0 av M q := d1Acoef_pos (c0 := c0) hs hM hav q
  have hs3 : 0 < s ^ 3 := by positivity
  have hM1 : 0 < M - 1 := by linarith
  have hM0 : 0 < M := by linarith
  have hnorm : 0 < ‖q‖ := by linarith
  have hAg : s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M ≤ d1Acoef s c0 av M q := by
    unfold d1Acoef
    have h : 0 ≤ 2 * d1Ks * av := by have := d1Ks_pos; positivity
    linarith
  have hkey : 1 / (4 * d1Acoef s c0 av M q)
      ≤ M / (4 * s ^ 3 * (M - 1)) * (fsKinCoeff c0 ‖q‖)⁻¹ := by
    have ha : 1 / (4 * d1Acoef s c0 av M q)
        ≤ 1 / (4 * (s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hb : 1 / (4 * (s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M))
        = M / (4 * s ^ 3 * (M - 1)) * (fsKinCoeff c0 ‖q‖)⁻¹ := by
      field_simp
    linarith [ha, hb]
  have hfin : d1MainInt s c0 av M W q
      = (d1Bcoef W q) ^ 2 * (1 / (4 * d1Acoef s c0 av M q)) := by
    unfold d1MainInt
    rw [div_eq_mul_inv, inv_eq_one_div]
  rw [hfin]
  calc (d1Bcoef W q) ^ 2 * (1 / (4 * d1Acoef s c0 av M q))
      ≤ (d1Bcoef W q) ^ 2
          * (M / (4 * s ^ 3 * (M - 1)) * (fsKinCoeff c0 ‖q‖)⁻¹) :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    _ = (M / (4 * s ^ 3 * (M - 1))) * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖) := by
        rw [div_eq_mul_inv]
        ring

/-- **integrability of the sharp main-term integrand.** -/
theorem integrable_d1MainInt {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 2 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av)
    (hInt : Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2)) :
    Integrable (d1MainInt s c0 av M W) := by
  have hmeas : Measurable (d1MainInt s c0 av M W) := by
    have hB : Measurable (fun q : ℝ³ => d1Bcoef W q) := hWmeas
    unfold d1MainInt d1Acoef
    refine Measurable.div (hB.pow_const 2) ?_
    unfold d1Ks fsKinCoeff
    fun_prop
  have hI : IntegrableOn (d1MainInt s c0 av M W) (d1Int c0) volume := by
    haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (d1Int c0)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      refine lt_of_le_of_lt (measure_mono ?_)
        (isCompact_closedBall (0 : ℝ³) (2 * c0)).measure_lt_top
      intro q hq
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      rw [d1Int, Metric.mem_ball, dist_eq_norm, sub_zero] at hq
      exact hq.le
    refine Integrable.mono' (μ := (volume : Measure ℝ³).restrict (d1Int c0))
      (g := fun _ => 2 * Real.pi * av) (integrable_const _) hmeas.aestronglyMeasurable ?_
    filter_upwards with q
    rw [Real.norm_of_nonneg (d1MainInt_nonneg hs hav hM (c0 := c0) W q)]
    exact d1MainInt_le_of_interior hs hav hM hWb q
  have hII : IntegrableOn (d1MainInt s c0 av M W) (d1Ext c0) volume := by
    have hg : Integrable (fun q : ℝ³ =>
        (M / (s ^ 3 * (M - 1))) * ((d1Bcoef W q) ^ 2 / ‖q‖ ^ 2)) volume :=
      hInt.const_mul (M / (s ^ 3 * (M - 1)))
    refine Integrable.mono' (μ := (volume : Measure ℝ³).restrict (d1Ext c0))
      (g := fun q : ℝ³ => (M / (s ^ 3 * (M - 1))) * ((d1Bcoef W q) ^ 2 / ‖q‖ ^ 2))
      hg.integrableOn hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_d1Ext c0)] with q hq
    rw [Real.norm_of_nonneg (d1MainInt_nonneg hs hav hM (c0 := c0) W q)]
    exact d1MainInt_le_of_exterior hs hav hM hc0 hq
  have hunion : IntegrableOn (d1MainInt s c0 av M W) (d1Int c0 ∪ d1Ext c0) volume :=
    (integrableOn_union).2 ⟨hI, hII⟩
  rw [d1Int_union_d1Ext c0] at hunion
  exact (integrableOn_univ).1 hunion


/-- the exterior quartic constant (no `c₀`-dependence: the exterior weight is `‖q‖⁻⁶`). -/
noncomputable def d1Qcoef (s av M : ℝ) : ℝ :=
  16 * M ^ 3 * (16 * Real.pi * av) ^ 4 / (s ^ 9 * (M - 1) ^ 3)

/-- **the interior bound** for the quartic integrand: `ℬ⁴/(4𝒜³) ≤ (π/2)·(a v)`. -/
lemma d1QuartInt_le_of_interior {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) (q : ℝ³) :
    d1QuartInt s c0 av M W q ≤ Real.pi / 2 * av := by
  have hA : (0 : ℝ) < d1Acoef s c0 av M q := d1Acoef_pos (c0 := c0) hs hM hav q
  have hAg : 2 * d1Ks * av ≤ d1Acoef s c0 av M q := d1Acoef_ge_two hs hM hav q
  have hKs0 : 0 ≤ d1Ks := le_of_lt d1Ks_pos
  have h2 : (d1Bcoef W q) ^ 4 ≤ (16 * Real.pi * av) ^ 4 := by
    calc (d1Bcoef W q) ^ 4 = ((d1Bcoef W q) ^ 2) ^ 2 := by ring
      _ ≤ ((16 * Real.pi * av) ^ 2) ^ 2 := by
            refine pow_le_pow_left₀ (sq_nonneg _) ?_ 2
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hWb q) 2
      _ = (16 * Real.pi * av) ^ 4 := by ring
  have hav0 : 0 ≤ av := le_of_lt hav
  unfold d1QuartInt
  rw [div_le_iff₀ (by positivity)]
  have h3 : (16 * Real.pi * av) ^ 4 ≤ (Real.pi / 2 * av) * (4 * (2 * d1Ks * av) ^ 3) := by
    unfold d1Ks
    nlinarith [Real.pi_pos, hav0]
  have h4 : (Real.pi / 2 * av) * (4 * (2 * d1Ks * av) ^ 3)
      ≤ (Real.pi / 2 * av) * (4 * (d1Acoef s c0 av M q) ^ 3) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hKs0 : 0 ≤ d1Ks := le_of_lt d1Ks_pos
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * d1Ks * av) hAg 3) (by norm_num)
  linarith [h2, h3, h4]

/-- **the exterior bound** for the quartic integrand (crude form, weight `‖q‖⁻⁶`). -/
lemma d1QuartInt_le_of_exterior {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    (hc0 : 0 < c0) {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av)
    {q : ℝ³} (hq : 2 * c0 ≤ ‖q‖) :
    d1QuartInt s c0 av M W q ≤ d1Qcoef s av M * ((‖q‖ : ℝ)⁻¹) ^ 6 := by
  have hFs : 0 < fsKinCoeff c0 ‖q‖ := by
    rw [fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)]
    have h : c0 < ‖q‖ := by linarith
    positivity
  have hA : 0 < d1Acoef s c0 av M q := d1Acoef_pos (c0 := c0) hs hM hav q
  have hAg : s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M ≤ d1Acoef s c0 av M q := by
    unfold d1Acoef
    have h : 0 ≤ 2 * d1Ks * av := by have := d1Ks_pos; positivity
    linarith
  have hs3 : 0 < s ^ 3 := by positivity
  have hM1 : 0 < M - 1 := by linarith
  have hM0 : 0 < M := by linarith
  have hq1 : 0 < ‖q‖ := by linarith
  have hB4 : (d1Bcoef W q) ^ 4 ≤ (16 * Real.pi * av) ^ 4 := by
    calc (d1Bcoef W q) ^ 4 = ((d1Bcoef W q) ^ 2) ^ 2 := by ring
      _ ≤ ((16 * Real.pi * av) ^ 2) ^ 2 := by
            refine pow_le_pow_left₀ (sq_nonneg _) ?_ 2
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hWb q) 2
      _ = (16 * Real.pi * av) ^ 4 := by ring
  have hFge : ‖q‖ ^ 2 / 4 ≤ fsKinCoeff c0 ‖q‖ := by
    rw [fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)]
    nlinarith [norm_nonneg q, hq]
  have hbase : s ^ 3 * (‖q‖ ^ 2 / 4) * (M - 1) / M ≤ s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M := by
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hM0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFge (le_of_lt hs3)) (by linarith)
  have hAex : 0 < s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M :=
    div_pos (mul_pos (mul_pos hs3 hFs) hM1) hM0
  have hA3 : (s ^ 3 * (‖q‖ ^ 2 / 4) * (M - 1) / M) ^ 3 ≤ (d1Acoef s c0 av M q) ^ 3 :=
    le_trans (pow_le_pow_left₀ (by positivity) hbase 3)
      (pow_le_pow_left₀ (le_of_lt hAex) hAg 3)
  have hkey : 1 / (4 * (d1Acoef s c0 av M q) ^ 3)
      ≤ 16 * M ^ 3 / (s ^ 9 * (M - 1) ^ 3 * ‖q‖ ^ 6) := by
    have h1 : 1 / (4 * (d1Acoef s c0 av M q) ^ 3)
        ≤ 1 / (4 * (s ^ 3 * (‖q‖ ^ 2 / 4) * (M - 1) / M) ^ 3) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hA3])
    have h2 : 1 / (4 * (s ^ 3 * (‖q‖ ^ 2 / 4) * (M - 1) / M) ^ 3)
        = 16 * M ^ 3 / (s ^ 9 * (M - 1) ^ 3 * ‖q‖ ^ 6) := by
      field_simp; ring
    linarith [h1, h2]
  have hfin : d1QuartInt s c0 av M W q
      = (d1Bcoef W q) ^ 4 * (1 / (4 * (d1Acoef s c0 av M q) ^ 3)) := by
    unfold d1QuartInt
    rw [div_eq_mul_inv, inv_eq_one_div]
  rw [hfin]
  calc (d1Bcoef W q) ^ 4 * (1 / (4 * (d1Acoef s c0 av M q) ^ 3))
      ≤ (16 * Real.pi * av) ^ 4 * (16 * M ^ 3 / (s ^ 9 * (M - 1) ^ 3 * ‖q‖ ^ 6)) :=
        mul_le_mul hB4 hkey (by positivity) (by positivity)
    _ = d1Qcoef s av M * ((‖q‖ : ℝ)⁻¹) ^ 6 := by
        unfold d1Qcoef
        have hq0 : (‖q‖ : ℝ) ≠ 0 := ne_of_gt hq1
        have hM0' : M ≠ 0 := ne_of_gt hM0
        have hM1' : (M - 1) ≠ 0 := ne_of_gt hM1
        have hs0 : s ≠ 0 := ne_of_gt hs
        have hπ : (16 * Real.pi * av) ≠ 0 := by
          have h1 : (0:ℝ) < 16 * Real.pi * av := by have := Real.pi_pos; positivity
          exact ne_of_gt h1
        field_simp

/-- `‖q‖⁻⁶` is integrable on the exterior `{R < ‖q‖}` (`ℝ³`). -/
lemma integrableOn_inv_six_tail {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun q : ℝ³ => ((‖q‖ : ℝ)⁻¹) ^ 6) {q : ℝ³ | R < ‖q‖} volume := by
  by_contra h
  have h0 : (∫ q in {q : ℝ³ | R < ‖q‖}, ((‖q‖ : ℝ)⁻¹) ^ 6) = 0 := integral_undef h
  rw [Commons.Analysis.Integral.integral_norm_neg_six_tail hR] at h0
  have : (0 : ℝ) < 4 * Real.pi / (3 * R ^ 3) := by positivity
  linarith

/-- the exterior `{2c₀ ≤ ‖q‖}` is contained in `{c₀ < ‖q‖}`. -/
lemma d1Ext_subset {c0 : ℝ} (hc0 : 0 < c0) : d1Ext c0 ⊆ {q : ℝ³ | c0 < ‖q‖} := by
  intro q hq
  exact lt_of_lt_of_le (by linarith : c0 < 2 * c0) hq

/-- **integrability of the quartic integrand.** -/
theorem integrable_d1QuartInt {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 2 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) :
    Integrable (d1QuartInt s c0 av M W) := by
  have hmeas : Measurable (d1QuartInt s c0 av M W) := by
    have hB : Measurable (fun q : ℝ³ => d1Bcoef W q) := hWmeas
    unfold d1QuartInt d1Acoef
    refine Measurable.div (hB.pow_const 4) ?_
    unfold d1Ks fsKinCoeff
    fun_prop
  have hI : IntegrableOn (d1QuartInt s c0 av M W) (d1Int c0) volume := by
    haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (d1Int c0)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      refine lt_of_le_of_lt (measure_mono ?_)
        (isCompact_closedBall (0 : ℝ³) (2 * c0)).measure_lt_top
      intro q hq
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      rw [d1Int, Metric.mem_ball, dist_eq_norm, sub_zero] at hq
      exact hq.le
    refine Integrable.mono' (μ := (volume : Measure ℝ³).restrict (d1Int c0))
      (g := fun _ => Real.pi / 2 * av) (integrable_const _) hmeas.aestronglyMeasurable ?_
    filter_upwards with q
    rw [Real.norm_of_nonneg (d1QuartInt_nonneg hs hav hM (c0 := c0) W q)]
    exact d1QuartInt_le_of_interior hs hav hM hWb q
  have hII : IntegrableOn (d1QuartInt s c0 av M W) (d1Ext c0) volume := by
    have htail : IntegrableOn (fun q : ℝ³ => ((‖q‖ : ℝ)⁻¹) ^ 6) (d1Ext c0) volume :=
      (integrableOn_inv_six_tail (by linarith : (0 : ℝ) < c0)).mono_set (d1Ext_subset hc0)
    refine Integrable.mono' (μ := (volume : Measure ℝ³).restrict (d1Ext c0))
      (g := fun q : ℝ³ => d1Qcoef s av M * ((‖q‖ : ℝ)⁻¹) ^ 6)
      ((htail.const_mul (d1Qcoef s av M))) hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_d1Ext c0)] with q hq
    rw [Real.norm_of_nonneg (d1QuartInt_nonneg hs hav hM (c0 := c0) W q)]
    exact d1QuartInt_le_of_exterior hs hav hM hc0 hWb hq
  have hunion : IntegrableOn (d1QuartInt s c0 av M W) (d1Int c0 ∪ d1Ext c0) volume :=
    (integrableOn_union).2 ⟨hI, hII⟩
  rw [d1Int_union_d1Ext c0] at hunion
  exact (integrableOn_univ).1 hunion


/-- the standing bound `|ℬ(q)| ≤ 𝒜(q)`. -/
lemma d1Bcoef_abs_le_d1Acoef {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) (q : ℝ³) :
    |d1Bcoef W q| ≤ d1Acoef s c0 av M q := by
  have hAg : 2 * d1Ks * av ≤ d1Acoef s c0 av M q := d1Acoef_ge_two hs hM hav q
  have h2 : 16 * Real.pi * av ≤ 2 * d1Ks * av := by
    have hp : (0 : ℝ) < Real.pi := Real.pi_pos
    unfold d1Ks
    nlinarith [le_of_lt hav]
  exact le_trans (hWb q) (le_trans h2 hAg)

/-- the squared form of the standing bound. -/
lemma d1Bcoef_sq_le_d1Acoef_sq {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) (q : ℝ³) :
    (d1Bcoef W q) ^ 2 ≤ (d1Acoef s c0 av M q) ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (d1Bcoef_abs_le_d1Acoef hs hav hM hWb q) 2

/-- **the Bogoliubov coefficient is nonnegative.** -/
lemma d1Kcoef_nonneg {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) (q : ℝ³) :
    0 ≤ d1Kcoef s c0 av M W q := by
  have hA : 0 < d1Acoef s c0 av M q := d1Acoef_pos (c0 := c0) hs hM hav q
  have hB : (d1Bcoef W q) ^ 2 ≤ (d1Acoef s c0 av M q) ^ 2 :=
    d1Bcoef_sq_le_d1Acoef_sq (c0 := c0) hs hav hM hWb q
  have hsqrt : Real.sqrt ((d1Acoef s c0 av M q) ^ 2 - (d1Bcoef W q) ^ 2)
      ≤ d1Acoef s c0 av M q := by
    calc Real.sqrt ((d1Acoef s c0 av M q) ^ 2 - (d1Bcoef W q) ^ 2)
        ≤ Real.sqrt ((d1Acoef s c0 av M q) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith [sq_nonneg (d1Bcoef W q)])
      _ = |d1Acoef s c0 av M q| := Real.sqrt_sq_eq_abs _
      _ = d1Acoef s c0 av M q := abs_of_pos hA
  unfold d1Kcoef
  refine div_nonneg ?_ (by norm_num)
  linarith

/-- **the sharp Bogoliubov coefficient bound at the D1 coefficients.** -/
lemma d1Kcoef_le {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av) (hM : 2 ≤ M)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) (q : ℝ³) :
    d1Kcoef s c0 av M W q ≤ d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q := by
  have hA : 0 < d1Acoef s c0 av M q := d1Acoef_pos (c0 := c0) hs hM hav q
  have hB : (d1Bcoef W q) ^ 2 ≤ (d1Acoef s c0 av M q) ^ 2 :=
    d1Bcoef_sq_le_d1Acoef_sq (c0 := c0) hs hav hM hWb q
  have hsharp := Commons.Analysis.Real.bogoliubov_coeff_sharp
    (A := d1Acoef s c0 av M q) (B := d1Bcoef W q) hA hB
  unfold d1Kcoef d1MainInt d1QuartInt
  linarith [hsharp]

/-- **integrability of the Bogoliubov coefficient.** -/
theorem integrable_d1Kcoef {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 2 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av)
    (hInt : Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2)) :
    Integrable (fun q : ℝ³ => d1Kcoef s c0 av M W q * M) := by
  have hsum : Integrable (fun q : ℝ³ =>
      (d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q) * M) :=
    ((integrable_d1MainInt hs hc0 hav hM hWmeas hWb hInt).add
      (integrable_d1QuartInt hs hc0 hav hM hWmeas hWb)).mul_const M
  have hmeasK : Measurable (fun q : ℝ³ => d1Kcoef s c0 av M W q * M) := by
    have hB : Measurable (fun q : ℝ³ => d1Bcoef W q) := hWmeas
    have hAcoef : Measurable (fun q : ℝ³ => d1Acoef s c0 av M q) := by
      unfold d1Acoef d1Ks fsKinCoeff
      fun_prop
    unfold d1Kcoef
    exact ((hAcoef.sub ((hAcoef.pow_const 2).sub (hB.pow_const 2)).sqrt).div_const 2).mul_const M
  refine Integrable.mono' (μ := volume)
    (g := fun q : ℝ³ => (d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q) * M)
    hsum hmeasK.aestronglyMeasurable ?_
  filter_upwards with q
  have hM0 : (0 : ℝ) ≤ M := by linarith
  rw [Real.norm_of_nonneg (mul_nonneg (d1Kcoef_nonneg hs hav hM hWb q) hM0)]
  exact mul_le_mul_of_nonneg_right (d1Kcoef_le hs hav hM hWb q) hM0


/-! ## 5 The X-space Newtonian finiteness ⟹ the Fourier-side integrability -/

/-- the x-space Newtonian finiteness transfers to the iterated `∫⁻` of `W x W y/‖x−y‖`. -/
lemma lintegral_lintegral_ne_top_of_integrable {W : ℝ³ → ℝ} (hW0 : 0 ≤ᵐ[volume] W)
    (hfin : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤ := by
  have hfst : ∀ᵐ p ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)), 0 ≤ W p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))).ae hW0
  have hsnd : ∀ᵐ p ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)), 0 ≤ W p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))).ae hW0
  have hF0 : 0 ≤ᵐ[volume.prod volume]
      (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) := by
    filter_upwards [hfst, hsnd] with p h1 h2
    exact mul_nonneg (mul_nonneg h1 h2) (inv_nonneg.mpr (norm_nonneg _))
  have hFmeas : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) (volume.prod volume) :=
    hfin.aestronglyMeasurable
  have h1 : (∫⁻ p : ℝ³ × ℝ³,
      ENNReal.ofReal (W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) ≠ ⊤ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hFmeas hF0).mpr hfin
  have h2 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y * (‖x - y‖ : ℝ)⁻¹))
      = ∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) :=
    MeasureTheory.lintegral_lintegral
      (f := fun x y => ENNReal.ofReal (W x * W y * (‖x - y‖ : ℝ)⁻¹))
      (ENNReal.measurable_ofReal.comp_aemeasurable hFmeas.aemeasurable)
  have h3 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y * (‖x - y‖ : ℝ)⁻¹))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) := by
    refine lintegral_congr_ae (Eventually.of_forall fun x => ?_)
    exact lintegral_congr_ae (Eventually.of_forall fun y => by simp only [div_eq_mul_inv])
  rw [← h3, h2]
  exact h1

/-- **the Fourier-side integrability of the D1 pairing weight.**  From the x-space Newtonian
finiteness (and the Coulomb inequality, which gives `fourier ≤ position` in `∫⁻`, applied to the
positive part `max W 0`, whose Fourier transform agrees with `W`'s), `q ↦ ℬ(q)²/‖q‖²` is
integrable. -/
theorem integrable_pairW_sq_div {W : ℝ³ → ℝ} (hW : Integrable W) (hW0 : 0 ≤ᵐ[volume] W)
    (hfin : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) :
    Integrable (fun q : ℝ³ => (pairW W q) ^ 2 / ‖q‖ ^ 2) := by
  set Wp : ℝ³ → ℝ := fun x => max (W x) 0 with hWpdef
  have hWp0 : 0 ≤ Wp := fun x => le_max_right _ _
  have hae : Wp =ᵐ[volume] W := max_zero_ae_eq hW0
  have hcfsame : cfourier Wp = cfourier W := cfourier_max_eq hW0
  have hWpint : Integrable Wp := hW.congr hae.symm
  have hae1 : ∀ᵐ p ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)), Wp p.1 = W p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))).ae_eq hae
  have hae2 : ∀ᵐ p ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)), Wp p.2 = W p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))).ae_eq hae
  have haep : (fun p : ℝ³ × ℝ³ => Wp p.1 * Wp p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)
      =ᵐ[volume.prod volume]
      (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) := by
    filter_upwards [hae1, hae2] with p hp1 hp2
    rw [hp1, hp2]
  have hfinp : Integrable (fun p : ℝ³ × ℝ³ => Wp p.1 * Wp p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) :=
    hfin.congr haep.symm
  have hYp : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Wp x * Wp y / ‖x - y‖)) ≠ ⊤ :=
    lintegral_lintegral_ne_top_of_integrable (Eventually.of_forall hWp0) hfinp
  set Xp : ℝ≥0∞ := ∫⁻ q, ENNReal.ofReal (‖cfourier Wp (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 / ‖q‖ ^ 2)
    with hXpdef
  have hCoul : ENNReal.ofReal (((2 * π) ^ 3)⁻¹) * Xp
      ≤ ENNReal.ofReal (1 / (4 * Real.pi)) *
          (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Wp x * Wp y / ‖x - y‖)) :=
    Commons.Analysis.Fourier.lintegral_fourier_inv_smul_sq_div_le hWpint hWp0
  have hXpne : Xp ≠ ⊤ := by
    have h1' : ENNReal.ofReal (((2 * π) ^ 3)⁻¹) * Xp ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYp) hCoul
    have h2' : ENNReal.ofReal (((2 * π) ^ 3)⁻¹) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      positivity
    exact ne_of_lt (ENNReal.lt_top_of_mul_ne_top_right h1' h2')
  have hXeq : (∫⁻ q, ENNReal.ofReal
        (‖cfourier W (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 / ‖q‖ ^ 2)) = Xp := by
    rw [hXpdef]
    refine lintegral_congr_ae (Eventually.of_forall fun q => ?_)
    have hcfq : cfourier W (((2 * π : ℝ)⁻¹) • q) = cfourier Wp (((2 * π : ℝ)⁻¹) • q) := by
      rw [hcfsame]
    simp only [hcfq]
  have hpoint : (∫⁻ q, ENNReal.ofReal ((pairW W q) ^ 2 / ‖q‖ ^ 2)) ≤ Xp := by
    rw [← hXeq]
    refine lintegral_mono (fun q => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact div_le_div_of_nonneg_right (pairW_sq_le_normSq_cfourier W q) (sq_nonneg _)
  have hfin' : (∫⁻ q, ENNReal.ofReal ((pairW W q) ^ 2 / ‖q‖ ^ 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top hXpne hpoint
  have hmeas' : AEStronglyMeasurable (fun q : ℝ³ => (pairW W q) ^ 2 / ‖q‖ ^ 2) volume := by
    have hc : Continuous (fun q : ℝ³ => pairW W q) :=
      Complex.continuous_re.comp ((continuous_cfourier hW).comp (continuous_const_smul _))
    exact ((hc.pow 2).measurable.div ((continuous_norm.pow 2).measurable)).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[volume] (fun q : ℝ³ => (pairW W q) ^ 2 / ‖q‖ ^ 2) :=
    Eventually.of_forall fun q => div_nonneg (sq_nonneg _) (sq_nonneg _)
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas' hnonneg).mp hfin'


/-- the `toReal`-bridge for the Newton double integral, with the FINITENESS hypothesis (instead of
the boundedness of `W`). -/
lemma toReal_lintegral_lintegral_eq_integral_of_fin {W : ℝ³ → ℝ} (hW0 : ∀ x, 0 ≤ W x)
    (hWmeas : AEMeasurable W volume)
    (hfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)).toReal
      = ∫ x, ∫ y, W x * W y * (‖x - y‖)⁻¹ := by
  set F : ℝ³ × ℝ³ → ℝ := fun p => W p.1 * W p.2 * (‖p.1 - p.2‖)⁻¹ with hFdef
  have hF0 : 0 ≤ᵐ[volume.prod volume] F := by
    filter_upwards with p
    exact mul_nonneg (mul_nonneg (hW0 p.1) (hW0 p.2)) (inv_nonneg.mpr (norm_nonneg _))
  have hFmeas : AEMeasurable F (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : ℝ³ × ℝ³ => W p.1) (volume.prod volume) :=
      hWmeas.comp_fst
    have h2 : AEMeasurable (fun p : ℝ³ × ℝ³ => W p.2) (volume.prod volume) :=
      hWmeas.comp_snd
    have h3 : AEMeasurable (fun p : ℝ³ × ℝ³ => (‖p.1 - p.2‖ : ℝ)⁻¹) (volume.prod volume) :=
      ((measurable_fst.sub measurable_snd).norm.inv).aemeasurable
    exact (h1.mul h2).mul h3
  have hFmeasE : AEMeasurable (fun p : ℝ³ × ℝ³ => ENNReal.ofReal (F p)) (volume.prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hFmeas
  have h2 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x, y)))
      = ∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (F p) :=
    MeasureTheory.lintegral_lintegral (f := fun x y => ENNReal.ofReal (F (x, y))) hFmeasE
  have hgoal : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x, y)))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hFdef, div_eq_mul_inv]
  have hFfin : (∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (F p)) ≠ ⊤ := by
    rw [← h2, hgoal]
    exact hfin
  have hFint : Integrable F :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hFmeas.aestronglyMeasurable hF0).mp hFfin
  have h1 : ENNReal.ofReal (∫ p : ℝ³ × ℝ³, F p)
      = ∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (F p) :=
    ofReal_integral_eq_lintegral_ofReal hFint hF0
  have h3 : (∫ p : ℝ³ × ℝ³, F p) = ∫ x, ∫ y, F (x, y) :=
    MeasureTheory.integral_prod (f := F) hFint
  have hIntF : (0 : ℝ) ≤ ∫ p : ℝ³ × ℝ³, F p := by
    refine integral_nonneg (fun p => ?_)
    simp only [hFdef]
    exact mul_nonneg (mul_nonneg (hW0 p.1) (hW0 p.2)) (inv_nonneg.mpr (norm_nonneg _))
  have htoReal : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x, y))).toReal = ∫ x, ∫ y, F (x, y) := by
    rw [h2, ← h1, ENNReal.toReal_ofReal hIntF, h3]
  rw [← hgoal, htoReal]

/-- **M1 with the finiteness hypothesis** (the `hWbdd` of
`SmallBoxD1Newtonian.integral_pairW_sq_div_sq_le_newtonian` is NOT available for
`W₁ = wScaled s (g0 v h)`): for measurable, a.e.-nonnegative integrable `W` and a finite
`∬W W/‖x−y‖`,
`(2π)⁻³∫_q ℬ(q)²/‖q‖² ≤ (1/(4π))∬W(x)W(y)/‖x−y‖`. -/
theorem integral_pairW_sq_div_sq_le_newtonian_of_fin {W : ℝ³ → ℝ} (hW : Integrable W)
    (hW0 : 0 ≤ᵐ[volume] W) (hWmeas : AEMeasurable W volume)
    (hfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, (pairW W q) ^ 2 / ‖q‖ ^ 2
      ≤ (1 / (4 * π)) * ∫ x, ∫ y, W x * W y * (‖x - y‖)⁻¹ := by
  set Wp : ℝ³ → ℝ := fun x => max (W x) 0 with hWp
  have hWp0 : ∀ x, 0 ≤ Wp x := fun x => le_max_right _ _
  have hWpint : Integrable Wp := by
    rw [hWp]
    exact hW.congr (max_zero_ae_eq hW0).symm
  have hWpmeas : AEMeasurable Wp volume := by
    rw [hWp]
    exact hWmeas.congr (max_zero_ae_eq hW0).symm
  have hcfsame : cfourier Wp = cfourier W := cfourier_max_eq hW0
  have hpairfun : (fun q : ℝ³ => pairW W q) = fun q : ℝ³ => pairW Wp q := by
    funext q
    rw [pairW_eq_cfourier_re, pairW_eq_cfourier_re, hcfsame]
  -- (a) Bochner ⇄ lintegral for the momentum side
  have hmommeas : AEStronglyMeasurable (fun q : ℝ³ => (pairW W q) ^ 2 / ‖q‖ ^ 2) := by
    have hc : Continuous (fun q : ℝ³ => pairW W q) := by
      rw [hpairfun]
      exact Complex.continuous_re.comp
        ((continuous_cfourier hWpint).comp (continuous_const_smul ((2 * π : ℝ)⁻¹)))
    exact ((hc.pow 2).measurable.div (continuous_norm.pow 2).measurable).aestronglyMeasurable
  have hmom0 : ∀ q : ℝ³, 0 ≤ (pairW W q) ^ 2 / ‖q‖ ^ 2 := fun q =>
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmom : (∫ q, (pairW W q) ^ 2 / ‖q‖ ^ 2)
      = (∫⁻ q, ENNReal.ofReal ((pairW W q) ^ 2 / ‖q‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hmom0) hmommeas
  -- (b) the pointwise comparison to the Fourier modulus
  have hLI : (∫⁻ q, ENNReal.ofReal ((pairW W q) ^ 2 / ‖q‖ ^ 2))
      ≤ ∫⁻ q, ENNReal.ofReal (‖cfourier Wp (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 / ‖q‖ ^ 2) := by
    refine lintegral_mono (fun q => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show pairW W q = pairW Wp q from congrFun hpairfun q]
    exact div_le_div_of_nonneg_right (pairW_sq_le_normSq_cfourier Wp q) (sq_nonneg _)
  -- (c) the Coulomb inequality
  have hfleet := Commons.Analysis.Fourier.lintegral_fourier_inv_smul_sq_div_le hWpint hWp0
  -- (d) the position-side conversion (with the finiteness hypothesis)
  have hfinp : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Wp x * Wp y / ‖x - y‖)) ≠ ⊤ := by
    rw [hWp]
    rw [← lintegral_max_eq hW0]
    exact hfin
  have hJto : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)).toReal
      = ∫ x, ∫ y, W x * W y * (‖x - y‖)⁻¹ := by
    rw [lintegral_max_eq hW0,
      toReal_lintegral_lintegral_eq_integral_of_fin (fun x => le_max_right (W x) 0) hWpmeas hfinp,
      ← integral_integral_max_eq hW0]
  have hcnonneg : (0 : ℝ) ≤ ((2 * π) ^ 3)⁻¹ := by positivity
  have hc2nonneg : (0 : ℝ) ≤ 1 / (4 * π) := by positivity
  have hfleet' : ENNReal.ofReal (((2 * π) ^ 3)⁻¹)
        * (∫⁻ q, ENNReal.ofReal (‖cfourier Wp (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 / ‖q‖ ^ 2))
      ≤ ENNReal.ofReal (1 / (4 * π))
        * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) := by
    rw [← lintegral_max_eq hW0] at hfleet
    exact hfleet
  have hcomb : ENNReal.ofReal (((2 * π) ^ 3)⁻¹)
        * (∫⁻ q, ENNReal.ofReal ((pairW W q) ^ 2 / ‖q‖ ^ 2))
      ≤ ENNReal.ofReal (1 / (4 * π))
        * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) :=
    le_trans (mul_le_mul_of_nonneg_left hLI zero_le) hfleet'
  have hcombne : ENNReal.ofReal (1 / (4 * π))
        * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  calc ((2 * π) ^ 3)⁻¹ * ∫ q, (pairW W q) ^ 2 / ‖q‖ ^ 2
      = (ENNReal.ofReal (((2 * π) ^ 3)⁻¹)
          * (∫⁻ q, ENNReal.ofReal ((pairW W q) ^ 2 / ‖q‖ ^ 2))).toReal := by
          rw [hmom, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcnonneg]
    _ ≤ (ENNReal.ofReal (1 / (4 * π))
          * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖))).toReal :=
          ENNReal.toReal_mono hcombne hcomb
    _ = (1 / (4 * π))
          * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc2nonneg]
    _ = (1 / (4 * π)) * ∫ x, ∫ y, W x * W y * (‖x - y‖)⁻¹ := by rw [hJto]


/-- the sharp exterior weight `ℬ²/F` is integrable on `d1Ext c₀` (dominated by `4ℬ²/‖q‖²`). -/
lemma integrableOn_sharp_weight {c0 : ℝ} (hc0 : 0 < c0) {W : ℝ³ → ℝ}
    (hWmeas : Measurable (d1Bcoef W))
    (hInt : Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2)) :
    IntegrableOn (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖) (d1Ext c0) volume := by
  have hmeas : Measurable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖) := by
    unfold fsKinCoeff
    exact (hWmeas.pow_const 2).div (by fun_prop)
  refine Integrable.mono' (μ := (volume : Measure ℝ³).restrict (d1Ext c0))
    (g := fun q : ℝ³ => 4 * ((d1Bcoef W q) ^ 2 / ‖q‖ ^ 2)) (hInt.const_mul 4).integrableOn
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_d1Ext c0)] with q hq
  have hq' : 2 * c0 ≤ ‖q‖ := hq
  have hFs : 0 < fsKinCoeff c0 ‖q‖ := by
    rw [fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)]
    have h : 0 < ‖q‖ - c0 := by linarith
    positivity
  have hinv : (fsKinCoeff c0 ‖q‖)⁻¹ ≤ 4 / ‖q‖ ^ 2 := d1_inv_fsKinCoeff_le hc0 hq'
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hFs))]
  have h1 : (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖
      = (d1Bcoef W q) ^ 2 * (fsKinCoeff c0 ‖q‖)⁻¹ := by rw [div_eq_mul_inv]
  have h2 : (d1Bcoef W q) ^ 2 * (fsKinCoeff c0 ‖q‖)⁻¹
      ≤ (d1Bcoef W q) ^ 2 * (4 / ‖q‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
  have h3 : (d1Bcoef W q) ^ 2 * (4 / ‖q‖ ^ 2)
      = 4 * ((d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) := by ring
  linarith [h1, h2, h3]

/-- **THE D1 MAIN-TERM BOOKKEEPING**: from the SHARP exterior bracket inequality (`hpB`), the
exterior quartic bound (`hqE`) and the interior bound (`hCi`),
`(2π)⁻³∫_q M·K(𝒜,ℬ) ≤ M·[(M/(4s³(M−1)))·((1+6c₀·a v)·∫ℬ²/‖q‖² + Clog) + QE + Ci]`
(the `(2π)⁻³` on the left costs nothing since `(2π)³ ≥ 1`). -/
theorem d1_main_term_raw {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 2 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av)
    (hInt : Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2))
    {Clog QE Ci : ℝ}
    (hpB : (∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
      ≤ (1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
    (hqE : (∫ q in d1Ext c0, d1QuartInt s c0 av M W q) ≤ QE)
    (hCi : (∫ q in d1Int c0,
        d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q) ≤ Ci) :
    ∫ q, d1Kcoef s c0 av M W q * M
      ≤ M * ((M / (4 * s ^ 3 * (M - 1)))
              * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
            + QE + Ci) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hM1 : (0 : ℝ) < M - 1 := by linarith
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hKm : Integrable (fun q : ℝ³ => d1Kcoef s c0 av M W q * M) :=
    integrable_d1Kcoef hs hc0 hav hM hWmeas hWb hInt
  have hSint : Integrable (fun q : ℝ³ =>
      d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q) :=
    (integrable_d1MainInt hs hc0 hav hM hWmeas hWb hInt).add
      (integrable_d1QuartInt hs hc0 hav hM hWmeas hWb)
  have hmono : (∫ q : ℝ³, d1Kcoef s c0 av M W q * M)
      ≤ ∫ q : ℝ³, (d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q) * M :=
    integral_mono_ae hKm (hSint.mul_const M) (Eventually.of_forall fun q =>
      mul_le_mul_of_nonneg_right (d1Kcoef_le hs hav hM hWb q) (le_of_lt hM0))
  have hsplit := integral_add_compl
    (s := d1Int c0)
    (μ := (volume : Measure ℝ³)) (f := fun q : ℝ³ =>
      d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q)
    (measurableSet_d1Int c0) hSint
  have hcompl : (d1Int c0)ᶜ = d1Ext c0 := by
    ext q
    rw [Set.mem_compl_iff, d1Int, Metric.mem_ball, dist_eq_norm, sub_zero]
    exact not_lt
  rw [hcompl] at hsplit
  have hMainIntOn : IntegrableOn (d1MainInt s c0 av M W) (d1Ext c0) volume :=
    (integrable_d1MainInt hs hc0 hav hM hWmeas hWb hInt).integrableOn
  have hQuartOn : IntegrableOn (d1QuartInt s c0 av M W) (d1Ext c0) volume :=
    (integrable_d1QuartInt hs hc0 hav hM hWmeas hWb).integrableOn
  have hsharpInt : IntegrableOn (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
      (d1Ext c0) volume := integrableOn_sharp_weight hc0 hWmeas hInt
  have hExtMain : (∫ q in d1Ext c0, d1MainInt s c0 av M W q)
      ≤ (M / (4 * s ^ 3 * (M - 1)))
          * (∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖) := by
    rw [← MeasureTheory.integral_const_mul]
    have hg : IntegrableOn (fun q : ℝ³ =>
        (M / (4 * s ^ 3 * (M - 1))) * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖))
        (d1Ext c0) volume := hsharpInt.const_mul _
    refine integral_mono_of_nonneg (Eventually.of_forall fun q =>
      d1MainInt_nonneg hs hav hM (c0 := c0) W q) hg ?_
    filter_upwards [ae_restrict_mem (measurableSet_d1Ext c0)] with q hq
    exact d1MainInt_le_of_exterior_F (W := W) hs hav hM hc0 hq
  have hExtSum : (∫ q in d1Ext c0,
        (d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q))
      = (∫ q in d1Ext c0, d1MainInt s c0 av M W q)
        + ∫ q in d1Ext c0, d1QuartInt s c0 av M W q :=
    MeasureTheory.integral_add hMainIntOn hQuartOn
  have hExtQ : (∫ q in d1Ext c0, d1QuartInt s c0 av M W q) ≤ QE := hqE
  have hmain : (∫ q : ℝ³, d1Kcoef s c0 av M W q * M)
      ≤ M * ((M / (4 * s ^ 3 * (M - 1)))
              * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
            + QE + Ci) := by
    have h2 : (∫ q : ℝ³, (d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q) * M)
        = M * (∫ q : ℝ³, (d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q)) := by
      rw [MeasureTheory.integral_mul_const]
      ring
    rw [h2, ← hsplit, hExtSum] at hmono
    have h3 : (M / (4 * s ^ 3 * (M - 1))
          * (∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖))
        ≤ (M / (4 * s ^ 3 * (M - 1)))
          * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog) :=
      mul_le_mul_of_nonneg_left hpB (by positivity)
    have h4 : (0 : ℝ) ≤ M := le_of_lt hM0
    have h5 : M * (∫ q in d1Int c0,
          (d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q)) ≤ M * Ci :=
      mul_le_mul_of_nonneg_left hCi h4
    have h6 : M * ((M / (4 * s ^ 3 * (M - 1)))
            * (∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖))
        ≤ M * ((M / (4 * s ^ 3 * (M - 1)))
            * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)) :=
      mul_le_mul_of_nonneg_left h3 h4
    have h7 : M * (∫ q in d1Ext c0, d1QuartInt s c0 av M W q) ≤ M * QE :=
      mul_le_mul_of_nonneg_left hExtQ h4
    have h8 : M * (∫ q in d1Ext c0, d1MainInt s c0 av M W q)
        ≤ M * ((M / (4 * s ^ 3 * (M - 1)))
            * (∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)) :=
      mul_le_mul_of_nonneg_left hExtMain h4
    linarith [hmono, h5, h6, h7, h8]
  exact hmain

theorem d1_main_term_le {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 2 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av)
    (hInt : Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2))
    {Clog QE Ci : ℝ}
    (hpB : (∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
      ≤ (1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
    (hqE : (∫ q in d1Ext c0, d1QuartInt s c0 av M W q) ≤ QE)
    (hCi : (∫ q in d1Int c0,
        d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q) ≤ Ci) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, d1Kcoef s c0 av M W q * M
      ≤ M * ((M / (4 * s ^ 3 * (M - 1)))
              * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
            + QE + Ci) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have h := d1_main_term_raw hs hc0 hav hM hWmeas hWb hInt hpB hqE hCi
  have h2π : ((2 * π : ℝ) ^ 3)⁻¹ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (2 * π) ^ 3 := by
      have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have h7 : (6 : ℝ) < 2 * Real.pi := by linarith
      have h8 : (6 : ℝ) ^ 3 < (2 * Real.pi) ^ 3 :=
        pow_lt_pow_left₀ h7 (by norm_num : (0 : ℝ) ≤ 6) (by norm_num : (3 : ℕ) ≠ 0)
      norm_num at h8
      linarith
    exact inv_le_one_of_one_le₀ h1
  have hK0 : (0 : ℝ) ≤ ∫ q : ℝ³, d1Kcoef s c0 av M W q * M :=
    integral_nonneg fun q => mul_nonneg (d1Kcoef_nonneg hs hav hM hWb q) (le_of_lt hM0)
  have hle : ((2 * π) ^ 3)⁻¹ * ∫ q : ℝ³, d1Kcoef s c0 av M W q * M
      ≤ ∫ q : ℝ³, d1Kcoef s c0 av M W q * M := by
    nlinarith [h2π, hK0]
  linarith [h, hle]

theorem d1_main_term_le_sharp {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 2 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av)
    (hInt : Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2))
    {Clog QE Ci : ℝ}
    (hpB : (∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
      ≤ (1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
    (hqE : (∫ q in d1Ext c0, d1QuartInt s c0 av M W q) ≤ QE)
    (hCi : (∫ q in d1Int c0,
        d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q) ≤ Ci) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, d1Kcoef s c0 av M W q * M
      ≤ M * ((2 * π) ^ 3)⁻¹ * ((M / (4 * s ^ 3 * (M - 1)))
              * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
            + QE + Ci) := by
  have h := d1_main_term_raw hs hc0 hav hM hWmeas hWb hInt hpB hqE hCi
  have h2π : (0 : ℝ) ≤ ((2 * π : ℝ) ^ 3)⁻¹ := by positivity
  calc ((2 * π) ^ 3)⁻¹ * ∫ q, d1Kcoef s c0 av M W q * M
      ≤ ((2 * π) ^ 3)⁻¹ * (M * ((M / (4 * s ^ 3 * (M - 1)))
              * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
            + QE + Ci)) := mul_le_mul_of_nonneg_left h h2π
    _ = M * ((2 * π) ^ 3)⁻¹ * ((M / (4 * s ^ 3 * (M - 1)))
              * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
            + QE + Ci) := by ring


/-! ## 6 STAGE 2 — the integrated D1 content bound -/

/-- the `q`-dependence of the two mode masses is integrable. -/
lemma integrable_modeP_sum {s : ℝ} (hs : 0 < s) {n : ℕ} {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) :
    Integrable (fun q : ℝ³ => modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ) := by
  obtain ⟨K, hK0, hK⟩ := exists_modeP_decay hs n Φ
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  have hR : Integrable (fun q : ℝ³ => modeP s (qModeRe s q) Φ) := by
    refine Integrable.mono' (g := fun q : ℝ³ => K * (1 + ‖q‖) ^ (-(6 : ℝ))) ?_ ?_ ?_
    · exact integrable_one_add_norm_six_r3.const_mul K
    · exact (continuous_modeP_qModeRe hs n Φ hΦ.continuous).aestronglyMeasurable
    · filter_upwards with q
      rw [Real.norm_of_nonneg (modeP_nonneg hs _ Φ)]
      calc modeP s (qModeRe s q) Φ ≤ modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ :=
            le_add_of_nonneg_right (modeP_nonneg hs _ Φ)
        _ ≤ K / (1 + ‖q‖) ^ 6 := hK q
        _ = K * (1 + ‖q‖) ^ (-(6 : ℝ)) := by
            rw [div_eq_mul_inv, rpow_neg_six_eq (1 + ‖q‖) (by positivity)]
  have hI : Integrable (fun q : ℝ³ => modeP s (qModeIm s q) Φ) := by
    refine Integrable.mono' (g := fun q : ℝ³ => K * (1 + ‖q‖) ^ (-(6 : ℝ))) ?_ ?_ ?_
    · exact integrable_one_add_norm_six_r3.const_mul K
    · exact (continuous_modeP_qModeIm hs n Φ hΦ.continuous).aestronglyMeasurable
    · filter_upwards with q
      rw [Real.norm_of_nonneg (modeP_nonneg hs _ Φ)]
      calc modeP s (qModeIm s q) Φ ≤ modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ :=
            le_add_of_nonneg_left (modeP_nonneg hs _ Φ)
        _ ≤ K / (1 + ‖q‖) ^ 6 := hK q
        _ = K * (1 + ‖q‖) ^ (-(6 : ℝ)) := by
            rw [div_eq_mul_inv, rpow_neg_six_eq (1 + ‖q‖) (by positivity)]
  exact hR.add hI

/-- **STAGE 2 — the integrated D1 content bound**: the `q`-integral of the FS content bound is
bounded below by the two explicit terms (the Bogoliubov main term and the `A₁` mass). -/
theorem d1_content_integral {p : ℕ} {s c0 : ℝ} (hs : 0 < s) (hc0 : 0 < c0)
    {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hRs : R ≤ s * chiR0)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hav : 0 < a v)
    (hWfin : Integrable (fun q : ℝ³ × ℝ³ =>
      wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹))
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hΦnorm : (∫ x in abox (p + 2) s, (Φ x) ^ 2) = 1) :
    kinPWord s c0 Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
      ≥ - (((2 * π) ^ 3)⁻¹ * (∫ q : ℝ³,
              d1Kcoef s c0 (a v) ((p : ℝ) + 2) (wScaled s (g0 v h)) q * ((p : ℝ) + 2)))
        - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (((2 * π) ^ 3)⁻¹
              * (∫ q : ℝ³, (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ))) := by
  set W : ℝ³ → ℝ := wScaled s (g0 v h) with hWdef
  set M : ℝ := (p : ℝ) + 2 with hMdef
  have hM0 : (0 : ℝ) < M := by rw [hMdef]; positivity
  have hM2 : 2 ≤ M := by
    rw [hMdef]
    exact le_add_of_nonneg_left (Nat.cast_nonneg p)
  have hWint : Integrable W := wScaled_g0_integrable hR hv_supp h hs hRs
  have hW0 : 0 ≤ᵐ[volume] W := wScaled_g0_nonneg_ae (ℓ := s) hR hv_nonneg hvrad hv_supp h
  have hWfin' : Integrable (fun q : ℝ³ × ℝ³ => W q.1 * W q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹) := hWfin
  have hWmeas : Measurable (d1Bcoef W) := by
    unfold d1Bcoef
    exact (Complex.continuous_re.comp
      ((continuous_cfourier hWint).comp (continuous_const_smul _))).measurable
  have hInt : Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) :=
    integrable_pairW_sq_div hWint hW0 hWfin'
  have hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * a v :=
    fun q => abs_pairW_wScaled_g0_le hR hv_nonneg hvrad hv_supp h hs hRs q
  have hint_k : Integrable (d1KinPart s c0 Φ) := integrable_kinetic_half hs hc0.le (p + 1) Φ hΦ
  have hint_q : Integrable (fun q : ℝ³ => d1PairPart s W Φ q) := by
    have h0 := integrable_pairingQ (ℓ := s) (R := R) hs hR hRs hv_supp h hΦ
    have h1 := Complex.reCLM.integrable_comp h0
    refine h1.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Complex.reCLM_apply]
    unfold d1PairPart
    rw [show W = wScaled s (g0 v h) from hWdef, pairW, re_mul_ofReal]
  have hKm : Integrable (fun q : ℝ³ => d1Kcoef s c0 (a v) M W q * M) :=
    integrable_d1Kcoef hs hc0 hav hM2 hWmeas hWb hInt
  have hPint : Integrable (fun q : ℝ³ =>
      modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ) :=
    integrable_modeP_sum hs (n := p + 1) hΦ
  have hc : (0 : ℝ) ≤ 2 * d1Ks * (a v) * (s ^ 3)⁻¹ := by
    have h := d1Ks_pos
    positivity
  -- the pointwise bound
  have hpt : ∀ q : ℝ³, -(d1Kcoef s c0 (a v) M W q * M)
      - 2 * d1Ks * (a v) * (s ^ 3)⁻¹ * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
      ≤ d1KinPart s c0 Φ q + d1PairPart s W Φ q := by
    intro q
    have hP : 0 ≤ modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ :=
      add_nonneg (modeP_nonneg hs _ Φ) (modeP_nonneg hs _ Φ)
    have h1 := d1_content_point (p := p) (s := s) (c0 := c0) (av := a v) (M := M)
      hs hav hMdef hWb hΦ.continuous hΦnorm q
    have h2 : -(2 * d1Ks * (a v) * (s ^ 3)⁻¹) ≤ -(d1Deficit s c0 (a v) M W q) := by
      unfold d1Deficit d1Acoef
      rw [show (s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M + 2 * d1Ks * (a v)) * (s ^ 3)⁻¹
            - fsKinCoeff c0 ‖q‖
          = -(fsKinCoeff c0 ‖q‖ / M) + 2 * d1Ks * (a v) * (s ^ 3)⁻¹ from by
        field_simp
        ring]
      have hFs : 0 ≤ fsKinCoeff c0 ‖q‖ / M :=
        div_nonneg (fsKinCoeff_nonneg c0 ‖q‖) (le_of_lt hM0)
      linarith
    have h3 : -(2 * d1Ks * (a v) * (s ^ 3)⁻¹)
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)
        ≤ -(d1Deficit s c0 (a v) M W q)
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ) :=
      mul_le_mul_of_nonneg_right h2 hP
    have h4 : d1Bcoef W q * (s ^ 3)⁻¹ * pairR s Φ q
        = pairW W q * ((s ^ 3)⁻¹ * pairR s Φ q) := by
      unfold d1Bcoef
      ring
    have h5 : -d1Kcoef s c0 (a v) M W q * M = -(d1Kcoef s c0 (a v) M W q * M) := by ring
    unfold d1KinPart d1PairPart
    linarith [h1, h3, h4, h5]
  have hLower : Integrable (fun q : ℝ³ => -(d1Kcoef s c0 (a v) M W q * M)
      - 2 * d1Ks * (a v) * (s ^ 3)⁻¹ * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) :=
    (hKm.neg).sub (hPint.const_mul (2 * d1Ks * (a v) * (s ^ 3)⁻¹))
  have hMono : (∫ q : ℝ³, (-(d1Kcoef s c0 (a v) M W q * M)
        - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)))
      ≤ ∫ q : ℝ³, (d1KinPart s c0 Φ q + d1PairPart s W Φ q) :=
    integral_mono_ae hLower (hint_k.add hint_q) (Eventually.of_forall fun q => hpt q)
  have hExpand : (∫ q : ℝ³, (-(d1Kcoef s c0 (a v) M W q * M)
        - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)))
      = -(∫ q : ℝ³, d1Kcoef s c0 (a v) M W q * M)
        - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (∫ q : ℝ³, (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) := by
    rw [MeasureTheory.integral_sub
        (f := fun q : ℝ³ => -(d1Kcoef s c0 (a v) M W q * M))
        (g := fun q : ℝ³ => 2 * d1Ks * (a v) * (s ^ 3)⁻¹
          * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ))
        (hKm.neg) (hPint.const_mul (2 * d1Ks * (a v) * (s ^ 3)⁻¹)),
      MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
  have hstep := kinPWord_add_q4PairWord_eq_integral (p := p) hs hc0.le hR hRs hv_supp h hΦ
  have hunfold : ((2 * π) ^ 3)⁻¹ * ∫ q : ℝ³, (d1KinPart s c0 Φ q + d1PairPart s W Φ q)
      = ((2 * π) ^ 3)⁻¹ * ∫ q : ℝ³, (d1KinPart s c0 Φ q
          + pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q)) := by
    unfold d1PairPart
    rw [hWdef]
  calc kinPWord s c0 Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
      = ((2 * π) ^ 3)⁻¹ * ∫ q : ℝ³, (d1KinPart s c0 Φ q
          + pairW (wScaled s (g0 v h)) q * ((s ^ 3)⁻¹ * pairR s Φ q)) := hstep
    _ = ((2 * π) ^ 3)⁻¹ * ∫ q : ℝ³, (d1KinPart s c0 Φ q + d1PairPart s W Φ q) := hunfold.symm
    _ ≥ ((2 * π) ^ 3)⁻¹ * ∫ q : ℝ³, (-(d1Kcoef s c0 (a v) M W q * M)
          - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
            * (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) :=
        mul_le_mul_of_nonneg_left hMono (by positivity)
    _ = -(((2 * π) ^ 3)⁻¹ * (∫ q : ℝ³, d1Kcoef s c0 (a v) M W q * M))
          - 2 * d1Ks * (a v) * (s ^ 3)⁻¹
            * (((2 * π) ^ 3)⁻¹
                * (∫ q : ℝ³, (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ))) := by
        rw [hExpand]
        ring


/-! ## 7 The instantiation of the two analytic inputs (`pBracket`, `pBdd`) and the interior -/

/-- **the interior bound** (main + quartic on the open ball). -/
lemma d1_interior_le {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av) (hM : 2 ≤ M)
    {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) :
    (∫ q in d1Int c0, d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q)
      ≤ (2 * Real.pi * av + Real.pi / 2 * av)
          * ((4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3) := by
  have hpt : ∀ q : ℝ³, d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q
      ≤ 2 * Real.pi * av + Real.pi / 2 * av := fun q =>
    add_le_add (d1MainInt_le_of_interior hs hav hM hWb q)
      (d1QuartInt_le_of_interior hs hav hM hWb q)
  haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (d1Int c0)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    refine lt_of_le_of_lt (measure_mono ?_)
      (isCompact_closedBall (0 : ℝ³) (2 * c0)).measure_lt_top
    intro q hq
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [d1Int, Metric.mem_ball, dist_eq_norm, sub_zero] at hq
    exact hq.le
  have hvol : (volume : Measure ℝ³).real (d1Int c0) = (4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3 := by
    have h1 : (∫ q in d1Int c0, (1 : ℝ)) = (volume : Measure ℝ³).real (d1Int c0) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    rw [← h1]
    exact momentum_ball_integral_one (2 * c0) (by positivity)
  calc (∫ q in d1Int c0, d1MainInt s c0 av M W q + d1QuartInt s c0 av M W q)
      ≤ ∫ q in d1Int c0, (2 * Real.pi * av + Real.pi / 2 * av) :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun q =>
            add_nonneg (d1MainInt_nonneg hs hav hM W q) (d1QuartInt_nonneg hs hav hM W q))
          (integrable_const (2 * Real.pi * av + Real.pi / 2 * av) :
            Integrable (fun _ : ℝ³ => 2 * Real.pi * av + Real.pi / 2 * av)
              ((volume : Measure ℝ³).restrict (d1Int c0)))
          (Eventually.of_forall fun q => hpt q)
    _ = (volume : Measure ℝ³).real (d1Int c0) * (2 * Real.pi * av + Real.pi / 2 * av) := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    _ = (2 * Real.pi * av + Real.pi / 2 * av)
          * ((4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3) := by
        rw [hvol]
        ring

/-- **the exterior quartic bound** (`pBdd_exterior_pow4_inv_sub_sq6_le` at the D1 coefficients). -/
lemma d1_exterior_quart_le {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 2 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av) :
    (∫ q in d1Ext c0, d1QuartInt s c0 av M W q)
      ≤ (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
          * (64 * (16 * Real.pi * av) ^ 4
              * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹)) := by
  have hs9 : (0 : ℝ) < s ^ 9 := by positivity
  have hM1 : (0 : ℝ) < M - 1 := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hc : (0 : ℝ) < 4 * s ^ 9 * (M - 1) ^ 3 := by positivity
  -- the pointwise bound
  have hpt : ∀ q : ℝ³, q ∈ d1Ext c0 → d1QuartInt s c0 av M W q
      ≤ (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
          * ((d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹) := by
    intro q hq
    have hq' : 2 * c0 ≤ ‖q‖ := hq
    have hFs : 0 < fsKinCoeff c0 ‖q‖ := by
      rw [fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)]
      have h : 0 < ‖q‖ - c0 := by linarith
      positivity
    have hFs3 : (fsKinCoeff c0 ‖q‖) ^ 3 = (‖q‖ - c0) ^ 6 := by
      rw [fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)]
      ring
    have hA : 0 < d1Acoef s c0 av M q := d1Acoef_pos (c0 := c0) hs hM hav q
    have hAg : s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M ≤ d1Acoef s c0 av M q := by
      unfold d1Acoef
      have h : 0 ≤ 2 * d1Ks * av := by have := d1Ks_pos; positivity
      linarith
    have h4A : 4 * (s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M) ^ 3 ≤ 4 * (d1Acoef s c0 av M q) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hAg 3) (by norm_num)
    have hkey : 1 / (4 * (d1Acoef s c0 av M q) ^ 3)
        ≤ M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3) * ((fsKinCoeff c0 ‖q‖) ^ 3)⁻¹ := by
      have ha : 1 / (4 * (d1Acoef s c0 av M q) ^ 3)
          ≤ 1 / (4 * (s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M) ^ 3) :=
        one_div_le_one_div_of_le (by positivity) (by linarith [h4A])
      have hb : 1 / (4 * (s ^ 3 * fsKinCoeff c0 ‖q‖ * (M - 1) / M) ^ 3)
          = M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3) * ((fsKinCoeff c0 ‖q‖) ^ 3)⁻¹ := by
        field_simp
      linarith [ha, hb]
    have hfin : d1QuartInt s c0 av M W q
        = (d1Bcoef W q) ^ 4 * (1 / (4 * (d1Acoef s c0 av M q) ^ 3)) := by
      unfold d1QuartInt
      rw [div_eq_mul_inv, inv_eq_one_div]
    rw [hfin]
    calc (d1Bcoef W q) ^ 4 * (1 / (4 * (d1Acoef s c0 av M q) ^ 3))
        ≤ (d1Bcoef W q) ^ 4
            * (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3) * ((fsKinCoeff c0 ‖q‖) ^ 3)⁻¹) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
            * ((d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹) := by
          rw [← hFs3]
          ring
  -- the dominating function is integrable on the exterior
  have h6 : Integrable (fun q : ℝ³ => ((‖q‖ : ℝ)⁻¹) ^ 6)
      ((volume : Measure ℝ³).restrict (d1Ext c0)) :=
    (integrableOn_inv_six_tail (by linarith : (0 : ℝ) < c0)).mono_set (d1Ext_subset hc0)
  have hdom : IntegrableOn (fun q : ℝ³ => (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
      * ((d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹)) (d1Ext c0) volume := by
    refine Integrable.mono' (μ := (volume : Measure ℝ³).restrict (d1Ext c0))
      (g := fun q : ℝ³ => (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3)) * (64 * (16 * Real.pi * av) ^ 4)
        * ((‖q‖ : ℝ)⁻¹) ^ 6)
      (h6.const_mul ((M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3)) * (64 * (16 * Real.pi * av) ^ 4)))
      ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      have hB : Measurable (fun q : ℝ³ => d1Bcoef W q) := hWmeas
      exact measurable_const.mul ((hB.pow_const 4).mul
        (((measurable_norm.sub measurable_const).pow_const 6).inv))
    · filter_upwards [ae_restrict_mem (measurableSet_d1Ext c0)] with q hq
      have hq' : 2 * c0 ≤ ‖q‖ := hq
      have hq1 : 0 < ‖q‖ := by linarith
      have hB2 : (d1Bcoef W q) ^ 2 ≤ (16 * Real.pi * av) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hWb q) 2
      have hB4 : (d1Bcoef W q) ^ 4 ≤ (16 * Real.pi * av) ^ 4 := by
        calc (d1Bcoef W q) ^ 4 = ((d1Bcoef W q) ^ 2) ^ 2 := by ring
          _ ≤ ((16 * Real.pi * av) ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hB2 2
          _ = (16 * Real.pi * av) ^ 4 := by ring
      have hhalf : ‖q‖ / 2 ≤ ‖q‖ - c0 := by linarith
      have h6le : ((‖q‖ - c0) ^ 6)⁻¹ ≤ 64 * ((‖q‖ : ℝ)⁻¹) ^ 6 := by
        have hc1 : 0 < ‖q‖ - c0 := by linarith
        have h1 : (0 : ℝ) < (‖q‖ - c0) ^ 6 := by positivity
        have h2 : (0 : ℝ) < (‖q‖ : ℝ) ^ 6 := by positivity
        have h3 : ((‖q‖ / 2) ^ 6 : ℝ) ≤ (‖q‖ - c0) ^ 6 :=
          pow_le_pow_left₀ (by positivity) hhalf 6
        have key : (64 : ℝ) * ((‖q‖ : ℝ)⁻¹) ^ 6 = ((‖q‖ ^ 6) / 64)⁻¹ := by
          rw [inv_pow, inv_div]
          ring
        rw [key, inv_le_inv₀ (a := (‖q‖ - c0) ^ 6) h1
          (by positivity : (0 : ℝ) < ‖q‖ ^ 6 / 64)]
        nlinarith [h3]
      have hnn : (0 : ℝ) ≤ (d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹ :=
        mul_nonneg (by positivity) (by positivity)
      rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
          * ((d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹))]
      have hle1 : (d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹
          ≤ (16 * Real.pi * av) ^ 4 * (64 * ((‖q‖ : ℝ)⁻¹) ^ 6) :=
        mul_le_mul hB4 h6le (by positivity) (by positivity)
      have hcst : (0 : ℝ) ≤ M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3) := by positivity
      calc (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3)) * ((d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹)
          ≤ (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
              * ((16 * Real.pi * av) ^ 4 * (64 * ((‖q‖ : ℝ)⁻¹) ^ 6)) :=
            mul_le_mul_of_nonneg_left hle1 hcst
        _ = (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3)) * (64 * (16 * Real.pi * av) ^ 4)
              * ((‖q‖ : ℝ)⁻¹) ^ 6 := by ring
  have hmono : (∫ q in d1Ext c0, d1QuartInt s c0 av M W q)
      ≤ ∫ q in d1Ext c0, (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
          * ((d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun q =>
      d1QuartInt_nonneg hs hav hM (c0 := c0) W q) hdom ?_
    filter_upwards [ae_restrict_mem (measurableSet_d1Ext c0)] with q hq
    exact hpt q hq
  have hpull : (∫ q in d1Ext c0, (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
        * ((d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹))
      = (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
        * (∫ q in d1Ext c0, (d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹) :=
    MeasureTheory.integral_const_mul _ _
  have hpBdd : (∫ q in d1Ext c0, (d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹)
      ≤ 64 * (16 * Real.pi * av) ^ 4 * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹) := by
    have h := pBdd_exterior_pow4_inv_sub_sq6_le (c := c0) (a := av) (C₀ := 16 * Real.pi)
      hc0 hav (by positivity) (F := d1Bcoef W) hWb
    simpa only [d1Ext] using h
  have hcst : (0 : ℝ) ≤ M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3) := by positivity
  calc (∫ q in d1Ext c0, d1QuartInt s c0 av M W q)
      ≤ (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
        * (∫ q in d1Ext c0, (d1Bcoef W q) ^ 4 * ((‖q‖ - c0) ^ 6)⁻¹) := by
        rw [← hpull]; exact hmono
    _ ≤ (M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
        * (64 * (16 * Real.pi * av) ^ 4 * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹)) :=
        mul_le_mul_of_nonneg_left hpBdd hcst


/-- **the exterior sharp bracket** (`pBracket_inv_sub_sq_le` at the D1 coefficients). -/
lemma d1_exterior_bracket_le {c0 av : ℝ} (hc0 : 0 < c0) (hav : 0 < av)
    (hdil : 2 * c0 * av ≤ 1) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av)
    (hInt : Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2)) :
    (∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
      ≤ (1 + 6 * c0 * av) * (∫ q : ℝ³, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2)
        + 6 * c0 * (16 * Real.pi * av) ^ 2 * (4 * Real.pi * Real.log ((2 * c0 * av)⁻¹)) := by
  have h := pBracket_inv_sub_sq_le (c := c0) (a := av) (C₀ := 16 * Real.pi) hc0 hav
    (by positivity) hdil (F := d1Bcoef W) hWmeas hWb hInt
  have hcongr : (∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
      = ∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / (‖q‖ - c0) ^ 2 := by
    refine setIntegral_congr_fun (measurableSet_d1Ext c0) (fun q hq => ?_)
    have hq' : 2 * c0 ≤ ‖q‖ := hq
    rw [fsKinCoeff_eq_of_le (by linarith : c0 ≤ ‖q‖)]
  rw [hcongr]
  simpa only [d1Ext] using h

/-- **the M1 bound at `W₁`**: `(2π)⁻³∫ℬ²/‖q‖² ≤ 2(1+6C(R/s)²)·g0w0Mass`. -/
lemma d1_M1_bound {v : ℝ³ → ℝ} {R s C r₁ : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hsR : R ≤ s * chiR0) (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hreg : R / s ≤ r₁) (hcond : C * (R / s) ^ 2 ≤ 1 / 2)
    (hWfin : Integrable (fun q : ℝ³ × ℝ³ =>
      wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹)) :
    ((2 * π) ^ 3)⁻¹ * ∫ q : ℝ³, (pairW (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2
      ≤ 2 * (1 + 6 * C * (R / s) ^ 2) * g0w0Mass (v := v) h := by
  have hWint : Integrable (fun z : ℝ³ => wScaled s (g0 v h) z) :=
    wScaled_g0_integrable hR hv_supp h hs hsR
  have hW0 : 0 ≤ᵐ[volume] (fun z : ℝ³ => wScaled s (g0 v h) z) :=
    wScaled_g0_nonneg_ae (ℓ := s) hR hv_nonneg hvrad hv_supp h
  have hWmeas : AEMeasurable (fun z : ℝ³ => wScaled s (g0 v h) z) volume :=
    hWint.aestronglyMeasurable.aemeasurable
  have hYne : (∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (wScaled s (g0 v h) x * wScaled s (g0 v h) y / ‖x - y‖)) ≠ ⊤ :=
    lintegral_lintegral_ne_top_of_integrable hW0 hWfin
  have hM1 := integral_pairW_sq_div_sq_le_newtonian_of_fin hWint hW0 hWmeas hYne
  have hmain := mainMassCoeff_le_coarse (v := v) (R := R) (s := s) (r₁ := r₁) (C := C)
    hR hs hv_nonneg hvrad hv_supp h hC hr₁ hT hreg hcond
  calc ((2 * π) ^ 3)⁻¹ * ∫ q : ℝ³, (pairW (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2
      ≤ (1 / (4 * π)) * ∫ x : ℝ³, ∫ y : ℝ³,
          wScaled s (g0 v h) x * wScaled s (g0 v h) y * (‖x - y‖ : ℝ)⁻¹ := hM1
    _ = 4 * ((1 / 2) * (1 / (8 * π)) * (∫ x : ℝ³, ∫ y : ℝ³,
          wScaled s (g0 v h) x * wScaled s (g0 v h) y * (‖x - y‖ : ℝ)⁻¹)) := by ring
    _ ≤ 4 * ((1 / 2) * (1 + 6 * C * (R / s) ^ 2) * g0w0Mass (v := v) h) :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 2 * (1 + 6 * C * (R / s) ^ 2) * g0w0Mass (v := v) h := by ring


/-! ## 8 STAGE 5 — the D1 target `lm_appbogolubov_pWord` -/

/-- the explicit error constant of the D1 target. -/
noncomputable def d1TargetC (Ct chi0 chiS Ks : ℝ) : ℝ :=
  max (6 * (2 * Real.pi) ^ 3)
    (max (36 * Ct * (2 * Real.pi) ^ 3 * chi0)
      (max (1536 * Real.pi ^ 3 * (1 + Real.log 2))
        (max (8 * (16 * Real.pi) ^ 4 * Real.pi / 3)
          (max (80 * Real.pi ^ 2 / 3) (4 * Ks * chiS ^ 2)))))

end BoseGases
end Submission
