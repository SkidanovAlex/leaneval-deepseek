import ChallengeDeps
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.autocorrIdentityClean
import Submission.Work.BoseFixB1B.autocorr_quotient_integrable
import Submission.Work.BoseFixB1B.chiMassDichotomy
import Submission.Work.BoseFixB1S.chiSmallB_autocorr_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Helpers for the core geometry

Three elementary facts are used by `autocorr_core_local` below:

* `sqrt3_core_arith` — the numerical inequality `√3·d/2 + √3/16 ≤ 1/4` for `d ≤ 1/16`
  (`3√3 ≤ 8`);
* `norm_d_smul_le` — the core hypothesis `|((ℓd)•u)_j| ≤ ℓ/16` gives `‖d•u‖ ≤ √3/16`;
* `chi_plateau_of_core` — on the small-box support (coordinatewise `≤ 1/2`) the argument
  `d•(w+u)` stays in `ball 0 (1/4)`, the plateau of the corpus bump, so `chi = chiSupAbs`. -/

/-- `√3·d/2 + s ≤ 1/4` for `d ≤ 1/16` and `s ≤ √3/16` (the bound `3√3 ≤ 8`). -/
private lemma sqrt3_core_arith {d s : ℝ} (hd : 0 < d) (hd16 : d ≤ 1 / 16)
    (hs : s ≤ Real.sqrt 3 * (1 / 16)) : Real.sqrt 3 * d / 2 + s ≤ 1 / 4 := by
  have hd32 : Real.sqrt 3 * d / 2 ≤ Real.sqrt 3 * (1 / 16) / 2 := by
    have := mul_le_mul_of_nonneg_left hd16 (Real.sqrt_nonneg 3)
    linarith
  have hs3 : 3 * Real.sqrt 3 ≤ 8 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3,
      sq_nonneg (Real.sqrt 3 - 2)]
  linarith

/-- The core hypothesis `|((ℓd)•u)_j| ≤ ℓ/16` gives `‖d•u‖ ≤ √3/16`. -/
private lemma norm_d_smul_le {ℓ d : ℝ} (hℓ : 0 < ℓ) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ ℓ / 16) :
    ‖d • u‖ ≤ Real.sqrt 3 * (1 / 16) := by
  refine Work.BoseFixB1S.norm_le_sqrt3_mul (by norm_num) ?_
  intro j
  have h1 : ((ℓ * d) • u).ofLp j = ℓ * (d • u).ofLp j := by
    rw [show (ℓ * d) • u = ℓ • (d • u) by rw [smul_smul]]
    rfl
  have h2 : ℓ * |(d • u).ofLp j| ≤ ℓ * (1 / 16) := by
    calc ℓ * |(d • u).ofLp j| = |((ℓ * d) • u).ofLp j| := by rw [h1, abs_mul, abs_of_pos hℓ]
      _ ≤ ℓ / 16 := hu j
      _ = ℓ * (1 / 16) := by ring
  have h3 : ℓ⁻¹ * (ℓ * |(d • u).ofLp j|) ≤ ℓ⁻¹ * (ℓ * (1 / 16)) :=
    mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hℓ))
  calc |(d • u).ofLp j| = ℓ⁻¹ * (ℓ * |(d • u).ofLp j|) := by field_simp
    _ ≤ ℓ⁻¹ * (ℓ * (1 / 16)) := h3
    _ = 1 / 16 := by field_simp

/-- On the small-box support of `χ_M(· − u)` (coordinatewise `≤ 1/2`) the argument
`d•(w + u)` of the corpus bump lies in `ball 0 (1/4)`, its plateau. -/
private lemma chi_plateau_of_core {d : ℝ} (hd : 0 < d) (hd16 : d ≤ 1 / 16)
    {u w : EuclideanSpace ℝ (Fin 3)} (hw : ∀ j : Fin 3, |w.ofLp j| ≤ 1 / 2)
    (hdu : ‖d • u‖ ≤ Real.sqrt 3 * (1 / 16)) :
    Submission.BoseGases.chi (d • (w + u)) = Submission.BoseGases.chiSupAbs := by
  have hwn : ‖w‖ ≤ Real.sqrt 3 / 2 := norm_le_sqrt_three_div_two hw
  have h1 : ‖d • w‖ ≤ Real.sqrt 3 * d / 2 := by
    rw [norm_smul, Real.norm_of_nonneg hd.le]
    calc d * ‖w‖ ≤ d * (Real.sqrt 3 / 2) := mul_le_mul_of_nonneg_left hwn hd.le
      _ = Real.sqrt 3 * d / 2 := by ring
  have h2 : ‖d • (w + u)‖ ≤ Real.sqrt 3 * d / 2 + Real.sqrt 3 * (1 / 16) := by
    calc ‖d • (w + u)‖ = ‖d • w + d • u‖ := by rw [smul_add]
      _ ≤ ‖d • w‖ + ‖d • u‖ := norm_add_le _ _
      _ ≤ Real.sqrt 3 * d / 2 + Real.sqrt 3 * (1 / 16) := add_le_add h1 hdu
  exact Work.BoseFixB1S.chi_eq_chiSupAbs_of_norm_le
    (le_trans h2 (sqrt3_core_arith hd hd16 le_rfl))

/-- **The exact autocorrelation of the sliding cutoff on the core.**

With the box centre `(ℓd)•u` in the cube of radius `ℓ/16` (so the whole box sits in the plateau
ball of the corpus bump `chi`) and `d ≤ 1/16`, the overlap of `χ_{B(u)}` with its translate by `z`
is *exactly* the plateau height squared times the box volume times the small-box self-convolution:

    `autocorr ℓ d u z = chiSupAbs²(ℓd)³ (χ_M⋆χ_M)((ℓd)⁻¹ z)`   for every lag `z`.

Route: the substitution `x = (ℓd)•w + (ℓd)•u` (translation + Haar scaling, factor `(ℓd)³`); on the
support of `χ_M(w)` and of `χ_M(w − s)`, `s = (ℓd)⁻¹z`, both `χ`-factors equal `chiSupAbs`
(`chi_plateau_of_core`, via `‖·‖ ≤ √3 d/2 + √3/16 ≤ 1/4`), so the integrand is
`chiSupAbs²·χ_M(w)χ_M(w − s)`; finally `∫_w χ_M(w)χ_M(w − s) = (χ_M⋆χ_M)(s)` by evenness of
`χ_M`.  No hypothesis on `z` is needed: where the small-box product vanishes both sides are `0`. -/
private theorem autocorr_core_local {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hd16 : d ≤ 1 / 16) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ ℓ / 16)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.autocorr (M := M) ℓ d u z
      = Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
          * Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • z) := by
  have hL : 0 < ℓ * d := mul_pos hℓ hd
  have hLne : ℓ * d ≠ 0 := ne_of_gt hL
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hdu : ‖d • u‖ ≤ Real.sqrt 3 * (1 / 16) := norm_d_smul_le hℓ hu
  set s : EuclideanSpace ℝ (Fin 3) := (ℓ * d)⁻¹ • z with hsdef
  have hz : (ℓ * d) • s = z := by
    rw [hsdef, smul_smul, mul_inv_cancel₀ hLne, one_smul]
  -- the pointwise value of the translated/translated pair
  have hpt : ∀ w : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiSmallB M ℓ d u ((ℓ * d) • w + (ℓ * d) • u)
        * Submission.BoseGases.chiSmallB M ℓ d u ((ℓ * d) • w + (ℓ * d) • u - z)
      = Submission.BoseGases.chiSupAbs ^ 2
          * (Submission.BoseGases.chiSmall M w * Submission.BoseGases.chiSmall M (w - s)) := by
    intro w
    have harg1 : (ℓ * d)⁻¹ • ((ℓ * d) • w + (ℓ * d) • u) - u = w := by
      rw [← smul_add, smul_smul, inv_mul_cancel₀ hLne, one_smul, add_sub_cancel_right]
    have harg2 : (ℓ * d)⁻¹ • ((ℓ * d) • w + (ℓ * d) • u - z) - u = w - s := by
      have h1 : (ℓ * d)⁻¹ • ((ℓ * d) • (w + u) - z) - u = (w + u) - s - u := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hLne, one_smul, hsdef]
      rw [show (ℓ * d) • w + (ℓ * d) • u - z = (ℓ * d) • (w + u) - z by rw [smul_add], h1]
      abel
    have hchi1 : Submission.BoseGases.chiScale ℓ ((ℓ * d) • w + (ℓ * d) • u)
        = Submission.BoseGases.chi (d • (w + u)) := by
      rw [show (ℓ * d) • w + (ℓ * d) • u = ℓ • (d • (w + u)) by
            rw [← smul_add, smul_smul]]
      exact Submission.BoseGases.chiScale_apply_smul hℓne (d • (w + u))
    have hchi2 : Submission.BoseGases.chiScale ℓ ((ℓ * d) • w + (ℓ * d) • u - z)
        = Submission.BoseGases.chi (d • (w + u - s)) := by
      rw [show (ℓ * d) • w + (ℓ * d) • u - z = ℓ • (d • (w + u - s)) by
            rw [← hz, ← smul_add, ← smul_sub, smul_smul]]
      exact Submission.BoseGases.chiScale_apply_smul hℓne (d • (w + u - s))
    simp only [Submission.BoseGases.chiSmallB, harg1, harg2, hchi1, hchi2]
    by_cases hw : Submission.BoseGases.chiSmall M w = 0
    · rw [hw] <;> ring
    by_cases hws : Submission.BoseGases.chiSmall M (w - s) = 0
    · rw [hws] <;> ring
    have hwn : ∀ j : Fin 3, |w.ofLp j| ≤ 1 / 2 := fun j => chiSmall_ne_zero_coord hM hw j
    have hwsn : ∀ j : Fin 3, |(w - s).ofLp j| ≤ 1 / 2 :=
      fun j => chiSmall_ne_zero_coord hM hws j
    have hA : Submission.BoseGases.chi (d • (w + u)) = Submission.BoseGases.chiSupAbs :=
      chi_plateau_of_core hd hd16 hwn hdu
    have hB : Submission.BoseGases.chi (d • (w + u - s)) = Submission.BoseGases.chiSupAbs := by
      have h := chi_plateau_of_core (d := d) hd hd16 (u := u) hwsn hdu
      rwa [show (w - s) + u = w + u - s by abel] at h
    rw [hA, hB] <;> ring
  -- the substitution `x = (ℓd)•w + (ℓd)•u`
  have hstep1 : (∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x
        * Submission.BoseGases.chiSmallB M ℓ d u (x - z))
      = (ℓ * d) ^ 3 * ∫ w : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.chiSmallB M ℓ d u ((ℓ * d) • w + (ℓ * d) • u)
            * Submission.BoseGases.chiSmallB M ℓ d u ((ℓ * d) • w + (ℓ * d) • u - z) := by
    set F : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
      Submission.BoseGases.chiSmallB M ℓ d u x
        * Submission.BoseGases.chiSmallB M ℓ d u (x - z) with hFdef
    have h1 : (∫ x : EuclideanSpace ℝ (Fin 3), F x)
        = ∫ x : EuclideanSpace ℝ (Fin 3), F (x + (ℓ * d) • u) :=
      (integral_add_right_eq_self F ((ℓ * d) • u)).symm
    have h2 : (∫ x : EuclideanSpace ℝ (Fin 3), F (x + (ℓ * d) • u))
        = (ℓ * d) ^ 3 * ∫ w : EuclideanSpace ℝ (Fin 3), F ((ℓ * d) • w + (ℓ * d) • u) :=
      Submission.BoseGases.integral_comp_smul_right
        (fun x : EuclideanSpace ℝ (Fin 3) => F (x + (ℓ * d) • u)) hL
    rw [h1, h2]
  have hstep2 : (∫ w : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.chiSmallB M ℓ d u ((ℓ * d) • w + (ℓ * d) • u)
          * Submission.BoseGases.chiSmallB M ℓ d u ((ℓ * d) • w + (ℓ * d) • u - z))
      = ∫ w : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSupAbs ^ 2
          * (Submission.BoseGases.chiSmall M w * Submission.BoseGases.chiSmall M (w - s)) := by
    apply integral_congr_ae
    filter_upwards with w
    exact hpt w
  have hconv : (∫ w : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.chiSmall M w * Submission.BoseGases.chiSmall M (w - s))
      = Submission.BoseGases.conv3Small M s := by
    rw [Submission.BoseGases.conv3Small]
    apply integral_congr_ae
    filter_upwards with w
    rw [show w - s = -(s - w) by abel, Submission.BoseGases.chiSmall_even hM]
  rw [Work.BoseFixB1.autocorr_apply, hstep1, hstep2, integral_const_mul, hconv] <;> ring

/-- **The core (deep-interior) mass bound for the sliding one-body kernel.**

`chiSmallB M ℓ d u x = chi(ℓ⁻¹•x)·chiSmall M ((ℓd)⁻¹•x − u)` is the corpus's sliding
cutoff, and `w1MassB h M ℓ d u = ∬ wSmall1Pair h M ℓ d u` its localised one-body mass.
If the box centre `(ℓd)•u` lies in the cube of radius `ℓ/16` (so the whole box
`B(u) = (ℓd)•u + cube(ℓd/2)` sits in `ball 0 (ℓ/4)`, where the corpus bump
`chi = chiBase/√chiNormSq` is at its plateau value `chiSupAbs`), then

    8π·(a v)·chiMass M ℓ d u ≤ w1MassB h M ℓ d u .

Intended route (all ingredients already in the corpus):
* general-`u` integrability of `psiPairKernel` for the numerator `g₀ v h` (the
  `u = 0` proof `Submission/Work/BoseFixB1S/w1MassB_zero_eq_single.lean`, private
  `integrable_psiPairKernel_g0`, carries over verbatim), then
  `Work.BoseFixB1.wSmallPair_integral_eq_autocorr` writes
  `w1MassB u = ∫_z (g₀ z / E z)·autocorr ℓ d u z`, `E = convScaleSmall M (ℓd)·convScale ℓ`;
* on the core `chiSmallB M ℓ d u x = chiSupAbs·chiSmall M ((ℓd)⁻¹•x − u)` for all `x`
  (`Work.BoseFixB1S.chi_eq_chiSupAbs_of_norm_le`), so the substitution
  `x = (ℓd)•u + (ℓd)•w` gives `autocorr ℓ d u z = chiSupAbs²·(ℓd)³·conv3Small M ((ℓd)⁻¹•z)`;
* restrict `z` to `‖z‖ ≤ R` (where `g₀ ≠ 0`), use
  `K z·conv3Small M ((ℓd)⁻¹•z) = g₀ z/convScale ℓ z` there
  (`Work.SmallBoxSliding.conv3Small_coord_lower`), `convScale ℓ ≤ 1`, `∫g₀ = 8π(a v)`;
* `chiMass M ℓ d u ≤ chiSupAbs²(ℓd)³` unconditionally (`chi ≤ chiSupAbs`, `∫chiSmall M² = 1`).

The per-`u` bound is FALSE without the core hypothesis (the box may meet `ball 0 (ℓ/2)`
tangentially) — the core hypothesis is what makes `chi` constant on the box. -/
theorem coreMassLower {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd16 : d ≤ 1 / 16)
    (hR16 : R ≤ ℓ * d / 16) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ ℓ / 16) :
    8 * Real.pi * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass M ℓ d u
      ≤ Work.BoseFixB1.w1MassB h M ℓ d u := by
  classical
  have hL : 0 < ℓ * d := mul_pos hℓ hd
  have hR2 : R ≤ ℓ / 16 := by nlinarith [hR16, hd16, hℓ]
  -- ## the core makes the `χ`-mass the box volume times the plateau height squared
  have hdup : ‖d • u‖ + Real.sqrt 3 * d / 2 ≤ 1 / 4 := by
    have hdu := norm_d_smul_le hℓ hu
    have hd32 : Real.sqrt 3 * d / 2 ≤ Real.sqrt 3 * (1 / 16) / 2 := by
      have := mul_le_mul_of_nonneg_left hd16 (Real.sqrt_nonneg 3)
      linarith
    have hs3 : 3 * Real.sqrt 3 ≤ 8 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3,
        sq_nonneg (Real.sqrt 3 - 2)]
    linarith
  have hchiMass : Work.SmallBoxSliding.chiMass M ℓ d u
      = Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3 :=
    chiMass_eq_deep hM hℓ hd hdup
  -- ## the lag identity and the integrability of its integrand
  have hident := w1MassB_eq_autocorr_gen (v := v) h hR hv_supp hM hℓ hd hR16 hR2 u
  have hqint := autocorr_quotient_integrable (v := v) h hR hv_supp hM hℓ hd hR16 hR2 u
  obtain ⟨c₀, hc₀pos, hc₀⟩ := Work.BoseFixB3.CS.Pieces.convScale_ge_of_norm_le
  have hCnn : 0 ≤ Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3 := by positivity
  -- ## the a.e. pointwise comparison
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3 * Submission.BoseGases.g0 v h z
        ≤ (Submission.BoseGases.g0 v h z
            / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
                * Submission.BoseGases.convScale ℓ z))
          * Work.BoseFixB1.autocorr (M := M) ℓ d u z := by
    filter_upwards [Submission.BoseGases.g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h]
      with z hgn
    by_cases hz0 : Submission.BoseGases.g0 v h z = 0
    · rw [hz0]
      simp
    · have hzR : ‖z‖ < R :=
        lt_of_not_ge fun hge => hz0 (Submission.BoseGases.g0_zero_of_norm_ge hv_supp hge h)
      have hzld : ‖z‖ ≤ ℓ * d / 16 := le_of_lt (lt_of_lt_of_le hzR hR16)
      have hs16 : ‖(ℓ * d)⁻¹ • z‖ ≤ 1 / 16 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
        calc (ℓ * d)⁻¹ * ‖z‖ ≤ (ℓ * d)⁻¹ * (ℓ * d / 16) :=
              mul_le_mul_of_nonneg_left hzld (inv_pos.mpr hL).le
          _ = 1 / 16 := by field_simp
      have hκlow : Work.SmallBoxSliding.smallConvLower M
          ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) z := by
        have hcoord : ∀ j : Fin 3, |((ℓ * d)⁻¹ • z).ofLp j| ≤ 1 / 16 := fun j =>
          le_trans (Submission.BoseGases.coord_abs_le_norm _ j) hs16
        simpa [Submission.BoseGases.convScaleSmall] using
          Work.SmallBoxSliding.conv3Small_coord_lower hM ((ℓ * d)⁻¹ • z) hcoord
      have hκpos : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) z :=
        lt_of_lt_of_le (Work.SmallBoxSliding.smallConvLower_pos M) hκlow
      have hz8 : ‖z‖ ≤ ℓ / 8 := by linarith [le_of_lt hzR]
      have hcvlow : c₀ ≤ Submission.BoseGases.convScale ℓ z := hc₀ ℓ hℓ z hz8
      have hcvpos : 0 < Submission.BoseGases.convScale ℓ z := lt_of_lt_of_le hc₀pos hcvlow
      have hcvle : Submission.BoseGases.convScale ℓ z ≤ 1 :=
        Submission.BoseGases.convScale_le_one ℓ z
      have hcore : Work.BoseFixB1.autocorr (M := M) ℓ d u z
          = Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
              * Submission.BoseGases.convScaleSmall M (ℓ * d) z := by
        simpa [Submission.BoseGases.convScaleSmall] using
          autocorr_core_local hM hℓ hd hd16 hu z
      have hrew : (Submission.BoseGases.g0 v h z
              / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
                  * Submission.BoseGases.convScale ℓ z))
            * (Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
                * Submission.BoseGases.convScaleSmall M (ℓ * d) z)
          = Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
            * (Submission.BoseGases.g0 v h z / Submission.BoseGases.convScale ℓ z) := by
        field_simp
      have hdiv : Submission.BoseGases.g0 v h z
          ≤ Submission.BoseGases.g0 v h z / Submission.BoseGases.convScale ℓ z := by
        rw [le_div_iff₀ hcvpos]
        nlinarith [hgn, hcvle]
      rw [hcore, hrew]
      exact mul_le_mul_of_nonneg_left hdiv hCnn
  -- ## integrate the comparison
  have hCae : (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ≤ᵐ[MeasureTheory.volume]
      fun z => Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
        * Submission.BoseGases.g0 v h z := by
    filter_upwards [Submission.BoseGases.g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h]
      with z hgn
    exact mul_nonneg hCnn hgn
  have hmono := integral_mono_of_nonneg hCae hqint hpoint
  have hg0int : (∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g0 v h z)
      = 8 * Real.pi * (_root_.BoseGases.a v) :=
    Submission.BoseGases.g0_integral (v := v) (R := R) hR hv_supp h
  have hval : (∫ z : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3 * Submission.BoseGases.g0 v h z)
      = Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
          * (8 * Real.pi * (_root_.BoseGases.a v)) := by
    rw [MeasureTheory.integral_const_mul, hg0int]
  calc 8 * Real.pi * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass M ℓ d u
      = Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
          * (8 * Real.pi * (_root_.BoseGases.a v)) := by
        rw [hchiMass] <;> ring
    _ = ∫ z : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3 * Submission.BoseGases.g0 v h z :=
        hval.symm
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.g0 v h z
              / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
                  * Submission.BoseGases.convScale ℓ z))
            * Work.BoseFixB1.autocorr (M := M) ℓ d u z := hmono
    _ = Work.BoseFixB1.w1MassB h M ℓ d u := hident.symm

end Work.BoseFixB1B
