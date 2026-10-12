import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.plateauAutocorr
import Submission.Work.BoseFixB1.PerBoxNames
import Submission.Work.BoseFixB1.regime_sideAt_ge
import Submission.Work.BoseFixB1B.coreMassLower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.w1MassB_ge_chiMass_plateau`

The per-`u` lower bound on the localised one-body mass for the sliding boxes that sit in the
**plateau** of the corpus bump `χ`:

    4π (a v) · chiMass M ℓ d u ≤ w1MassB h M ℓ d u

for every admissible diluteness `μ` (`ℓ = bSide v μ`, `d = bD v μ`, `M = bM v μ`) and every
sliding position `u` for which the two `χ_B`-factors collapse pointwise onto the plateau value of
the corpus bump,

    χ_{B(u)}(x) = chiSupAbs · χ_M((ℓd)⁻¹ • x − u)   for all x.

## Structure of the proof

The hypothesis is *exactly* what is missing in the general (unrestricted) per-`u` bound, which is
FALSE at grazing boxes (`Work.BoseFixB1/FINDING_w1MassB_ge_const_mul_chiMass.md`); it holds, for
instance, whenever the box `B(u)` lies in the plateau `‖·/ℓ‖ ≤ 1/4` of `χ` (which is what the
coordinatewise "core" condition `|((ℓd)•u)_j| ≤ ℓ/16` of `Work.BoseFixB1B.coreMassLower` — the
`8π(a v)`-form of this statement — guarantees).

The chain is the one of `Work.BoseFixB1B.coreMassLower`, with the core `autocorr` identity
replaced by its plateau version (`Work.BoseB1Cube.plateauAutocorr`):

* `Work.BoseFixB1B.w1MassB_eq_autocorr_gen` writes the box mass as the lag integral
  `w1MassB = ∫_z (g₀ z / (κ' z κ z)) · autocorr z`, with `κ' = convScaleSmall M (ℓd)`,
  `κ = convScale ℓ`;
* on the support of `g₀` (i.e. `‖z‖ < R ≤ ℓd/16`) the lag identity gives `autocorr z = C κ' z`
  with `C = chiSupAbs²(ℓd)³`, so the integrand collapses to `C · g₀ z / κ z` pointwise;
* `∫ g₀ = 8π(a v)` and `κ ≤ 1`, `g₀ ≥ 0` give `8π(a v) ≤ ∫ g₀/κ`;
* finally `chiMass ≤ C` (`Work.BoseFixB1B.chiMass_le_sup`), so `8π(a v) chiMass ≤ 8π(a v) C ≤ w1MassB`
  (`w1MassB_ge_chiMass_of_plateau`), and halving the constant via `chiMass ≥ 0` gives the target's
  `4π(a v) chiMass ≤ w1MassB`.

The numerical side — `d ≤ 1/16` and `R ≤ ℓd/16` for `μ(a v)³` small — is
`Work.BoseFixB1.regime_sideAt_ge` plus the closed form `d = (μa³)^{6/323}`.
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric
open scoped Real

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The plateau mass bound at explicit parameters.**

If the sliding cutoff collapses pointwise onto the plateau of the corpus bump,
`χ_{B(u)}(x) = chiSupAbs · χ_M((ℓd)⁻¹ • x − u)`, then

    8π (a v) · chiMass M ℓ d u ≤ w1MassB h M ℓ d u ,

provided the geometry is in the dilute window (`d ≤ 1/16`, `R ≤ ℓd/16`, `a v > 0`). -/
theorem w1MassB_ge_chiMass_of_plateau {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd16 : d ≤ 1 / 16)
    (hR16 : R ≤ ℓ * d / 16) {u : E3}
    (hχ : ∀ x : E3,
        Submission.BoseGases.chiSmallB M ℓ d u x
          = Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) :
    8 * Real.pi * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass M ℓ d u
      ≤ Work.BoseFixB1.w1MassB h M ℓ d u := by
  classical
  have hL : 0 < ℓ * d := mul_pos hℓ hd
  have hR2 : R ≤ ℓ / 16 := by nlinarith [hR16, hd16, hd]
  have hCnn : 0 ≤ Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3 := by positivity
  obtain ⟨c₀, hc₀pos, hc₀⟩ := Work.BoseFixB3.CS.Pieces.convScale_ge_of_norm_le
  -- ## integrability of `g₀/convScale ℓ` (the sole place where the support of `v` is used)
  have hint : Integrable (fun z : E3 => Submission.BoseGases.g0 v h z
      / Submission.BoseGases.convScale ℓ z) := by
    refine Integrable.mono' ((Submission.BoseGases.g0_integrable hR hv_supp h).norm.const_mul
      c₀⁻¹) ?_ ?_
    · exact ((Submission.BoseGases.g0_integrable hR hv_supp h).aemeasurable.div
        (Submission.BoseGases.convScale_continuous ℓ).aemeasurable).aestronglyMeasurable
    · filter_upwards with z
      by_cases hz : Submission.BoseGases.g0 v h z = 0
      · rw [hz]; simp
      · have hzn : ‖z‖ < R :=
          lt_of_not_ge fun hge => hz (Submission.BoseGases.g0_zero_of_norm_ge hv_supp hge h)
        have hcz : c₀ ≤ Submission.BoseGases.convScale ℓ z := hc₀ ℓ hℓ z (by linarith)
        have hcnn : 0 ≤ Submission.BoseGases.convScale ℓ z := le_trans hc₀pos.le hcz
        have hKn : c₀ ≤ ‖Submission.BoseGases.convScale ℓ z‖ := by
          rwa [Real.norm_of_nonneg hcnn]
        calc ‖Submission.BoseGases.g0 v h z / Submission.BoseGases.convScale ℓ z‖
            = ‖Submission.BoseGases.g0 v h z‖ / ‖Submission.BoseGases.convScale ℓ z‖ :=
              norm_div _ _
          _ ≤ ‖Submission.BoseGases.g0 v h z‖ / c₀ :=
              div_le_div_of_nonneg_left (norm_nonneg _) hc₀pos hKn
          _ = c₀⁻¹ * ‖Submission.BoseGases.g0 v h z‖ := by rw [div_eq_inv_mul]
  -- ## `∫ g₀ ≤ ∫ g₀/κ` (the plateau factor only helps)
  have hmono : (∫ z : E3, Submission.BoseGases.g0 v h z)
      ≤ ∫ z : E3, Submission.BoseGases.g0 v h z / Submission.BoseGases.convScale ℓ z := by
    refine integral_mono_of_nonneg (Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h)
      hint ?_
    filter_upwards [Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h] with z hz0
    by_cases hz : Submission.BoseGases.g0 v h z = 0
    · rw [hz]; simp
    · have hzn : ‖z‖ < R :=
        lt_of_not_ge fun hge => hz (Submission.BoseGases.g0_zero_of_norm_ge hv_supp hge h)
      have hcz : c₀ ≤ Submission.BoseGases.convScale ℓ z := hc₀ ℓ hℓ z (by linarith)
      have hcpos : 0 < Submission.BoseGases.convScale ℓ z := lt_of_lt_of_le hc₀pos hcz
      have hcle : Submission.BoseGases.convScale ℓ z ≤ 1 :=
        Submission.BoseGases.convScale_le_one ℓ z
      rw [le_div_iff₀ hcpos]
      nlinarith [hz0, hcle]
  -- ## the pointwise collapse of the lag integrand
  have hpt : ∀ z : E3,
      (Submission.BoseGases.g0 v h z
          / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
              * Submission.BoseGases.convScale ℓ z))
        * Work.BoseFixB1.autocorr (M := M) ℓ d u z
      = Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
          * (Submission.BoseGases.g0 v h z / Submission.BoseGases.convScale ℓ z) := by
    intro z
    have haut : Work.BoseFixB1.autocorr (M := M) ℓ d u z
        = Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
            * Submission.BoseGases.convScaleSmall M (ℓ * d) z := by
      simpa [Submission.BoseGases.convScaleSmall] using plateauAutocorr hM hℓ hd hχ z
    rw [haut]
    by_cases hz : Submission.BoseGases.g0 v h z = 0
    · rw [hz]; simp
    · have hzn : ‖z‖ < R :=
        lt_of_not_ge fun hge => hz (Submission.BoseGases.g0_zero_of_norm_ge hv_supp hge h)
      have hs : ‖(ℓ * d)⁻¹ • z‖ ≤ 1 / 16 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
        have h1 : (ℓ * d)⁻¹ * ‖z‖ ≤ (ℓ * d)⁻¹ * R :=
          mul_le_mul_of_nonneg_left hzn.le (inv_pos.mpr hL).le
        have h2 : (ℓ * d)⁻¹ * R ≤ (ℓ * d)⁻¹ * ((ℓ * d) / 16) :=
          mul_le_mul_of_nonneg_left hR16 (inv_pos.mpr hL).le
        have h3 : (ℓ * d)⁻¹ * ((ℓ * d) / 16) = 1 / 16 := by field_simp
        linarith [h1, h2, h3]
      have hCpos : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) z :=
        lt_of_lt_of_le (Work.SmallBoxSliding.smallConvLower_pos M)
          (Work.SmallBoxSliding.conv3Small_coord_lower hM _
            (fun j => le_trans (Submission.BoseGases.coord_abs_le_norm _ j) hs))
      have hKpos : 0 < Submission.BoseGases.convScale ℓ z :=
        lt_of_lt_of_le hc₀pos (hc₀ ℓ hℓ z (by linarith))
      have hCne : Submission.BoseGases.convScaleSmall M (ℓ * d) z ≠ 0 := ne_of_gt hCpos
      have hKne : Submission.BoseGases.convScale ℓ z ≠ 0 := ne_of_gt hKpos
      field_simp
  -- ## assemble
  rw [Work.BoseFixB1B.w1MassB_eq_autocorr_gen (v := v) (R := R) h hR hv_supp hM hℓ hd hR16 hR2 u]
  calc 8 * Real.pi * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass M ℓ d u
      ≤ 8 * Real.pi * (_root_.BoseGases.a v)
          * (Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3) :=
        mul_le_mul_of_nonneg_left (Work.BoseFixB1B.chiMass_le_sup hM hℓ hd u) (by positivity)
    _ = Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
          * (8 * Real.pi * (_root_.BoseGases.a v)) := by ring
    _ ≤ Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
          * (∫ z : E3, Submission.BoseGases.g0 v h z / Submission.BoseGases.convScale ℓ z) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnn
        rw [← Submission.BoseGases.g0_integral hR hv_supp h]
        exact hmono
    _ = ∫ z : E3, Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
          * (Submission.BoseGases.g0 v h z / Submission.BoseGases.convScale ℓ z) := by
        rw [MeasureTheory.integral_const_mul]
    _ = ∫ z : E3, (Submission.BoseGases.g0 v h z
          / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
              * Submission.BoseGases.convScale ℓ z))
          * Work.BoseFixB1.autocorr (M := M) ℓ d u z :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => (hpt z).symm)

theorem w1MassB_ge_chiMass_plateau {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        (∀ x : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u x
              = Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmall (Work.BoseFixB1.bM v μ)
                    ((Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)⁻¹ • x - u)) →
        4 * Real.pi * (_root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          ≤ Work.BoseFixB1.bW v h μ u := by
  classical
  obtain ⟨ε₀₁, hε₀₁, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀₁ ((1 / 16 : ℝ) ^ ((323 : ℝ) / 6)),
    lt_min hε₀₁ (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro μ hAdm u hχ
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ht := Work.BoseFixB1.adm_dilute hAdm
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀₁ := le_trans ht (min_le_left _ _)
  have ht3 : μ * (_root_.BoseGases.a v) ^ 3 ≤ (1 / 16 : ℝ) ^ ((323 : ℝ) / 6) :=
    le_trans ht (min_le_right _ _)
  obtain ⟨hR16raw, -⟩ := hreg μ hμ ht1
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := by
    rw [Work.BoseFixB1.bSide]
    exact Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := by
    rw [Work.BoseFixB1.bD]
    exact Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ Work.BoseFixB1.bM v μ := by
    rw [Work.BoseFixB1.bM, Work.BoseFixB1.paramsAt_eq_fsParams]
    norm_num [Work.BoseBox.fsParams, Work.BoseBox.mValue]
  have hd16 : Work.BoseFixB1.bD v μ ≤ 1 / 16 := by
    rw [Work.BoseFixB1.bD, Work.BoseFixB1.d_eq_fsXp, Work.BoseBox.fsXp]
    calc (μ * (_root_.BoseGases.a v) ^ 3) ^ ((6 : ℝ) / 323)
        ≤ ((1 / 16 : ℝ) ^ ((323 : ℝ) / 6)) ^ ((6 : ℝ) / 323) :=
          Real.rpow_le_rpow (by positivity) ht3 (by norm_num)
      _ = 1 / 16 := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 16)]
          norm_num
  have hR16 : R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16 := by
    rw [Work.BoseFixB1.bSide, Work.BoseFixB1.bD]
    exact hR16raw
  have hχ' : ∀ x : E3,
      Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u x
        = Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmall (Work.BoseFixB1.bM v μ)
              ((Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)⁻¹ • x - u) := fun x => hχ x
  have hmain := w1MassB_ge_chiMass_of_plateau (v := v) (R := R) h hv hvrad hR hv_supp hav
    hM1 hℓ hd hd16 hR16 hχ'
  rw [Work.BoseFixB1.bW]
  have h4 : 0 ≤ 4 * Real.pi * (_root_.BoseGases.a v)
      * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u :=
    mul_nonneg (mul_nonneg (by positivity) hav.le)
      (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _)
  linarith [hmain, h4]

end Work.BoseB1Cube
