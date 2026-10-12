import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.w1MassB_eq_autocorr_gen
import Submission.Work.BoseSWE.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

open MeasureTheory Metric
open scoped Real Topology BigOperators ENNReal

/-- **The `w₁`-mass row (`Regular`'s first conjunct) on massive boxes, from the pointwise defect.**

Assume that on every massive good box the sliding cutoff satisfies the pointwise autocorrelation
defect `(49/50)·χ_m ≤ ∫χ_B(x)χ_B(x−z)` for `‖z‖ ≤ R` (this is
`Work.BoseSWE.massiveDefect`, recalled verbatim as the hypothesis `hdef`).  Then the first mass row
`(49/50)·8π(a v)·χ_m ≤ bW v h μ u` holds for every massive good box.

Route: `Work.BoseFixB1B.w1MassB_eq_autocorr_gen` writes
`bW = ∫ z, (g₀ z / (convScaleSmall M (ℓd) z · convScale ℓ z))·autocorr z`, and
`Work.BoseFixB1S.wSmall1Pair_denom_bounds` gives `0 < cS·cℓ ≤ 1` for `‖z‖ ≤ R` (from
`R ≤ ℓd/16`, `R ≤ ℓ·chiR0`), so the integrand dominates `(49/50)·χ_m·g₀ z` pointwise
(`g₀ ≥ 0`, `g₀ = 0` off `ball 0 R`); integrating against
`∫ g₀ = 8π(a v)` (`Submission.BoseGases.g0_integral`) gives the row.  Integrability of the lag
integrand is `Work.BoseFixB1B.autocorr_quotient_integrable`; the regime side conditions come from
`Work.BoseFixB1.regime_sideAt_ge`. -/
theorem massiveBulkRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hdef : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (μ : ℝ), Work.BoseBoxFix.Adm v ε₁ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        (Work.BoseFixB1.bD v μ) ^ 108
            * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
          ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u →
        ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
          (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
              (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
            ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u x
                  * Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u (x - z)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        (Work.BoseFixB1.bD v μ) ^ 108
            * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
          ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u →
        (49 / 50) * (8 * Real.pi * _root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          ≤ Work.BoseFixB1.bW v h μ u := by
  classical
  obtain ⟨ε₁, hε₁pos, hdef₁⟩ := hdef
  obtain ⟨εr, hεrpos, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min (min ε₁ εr) 1, lt_min (lt_min hε₁pos hεrpos) one_pos, ?_⟩
  intro μ hAdm u hu hmass
  -- the two admissible points
  have hAdm1 : Work.BoseBoxFix.Adm v ε₁ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmr : Work.BoseBoxFix.Adm v εr μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hregμ := hreg μ (Work.BoseFixB1.adm_mu_pos hAdmr) (Work.BoseFixB1.adm_dilute hAdmr)
  -- the regime side conditions
  have hR1 : R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16 := hregμ.1
  have hRχ : R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0 := hregμ.2
  have hM : 1 ≤ Work.BoseFixB1.bM v μ := by
    simp [Work.BoseFixB1.bM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hd1 : Work.BoseFixB1.bD v μ ≤ 1 := by
    show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_le_one (mul_pos (Work.BoseFixB1.adm_mu_pos hAdm) (pow_pos hav 3))
      (Work.BoseFixB1.adm_dilute_le_one hAdm (min_le_right _ _)) (by norm_num)
  have hR2 : R ≤ Work.BoseFixB1.bSide v μ / 16 := by
    have hmul : Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ
        ≤ Work.BoseFixB1.bSide v μ * 1 := mul_le_mul_of_nonneg_left hd1 hℓ.le
    linarith [hR1, hmul]
  -- the `g₀ ≥ 0` input, and the χ-mass is nonnegative
  have hg0nn := Submission.BoseGases.g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h
  have hchi_nn : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  -- the lag identity for `bW` and the integrability of its integrand
  have hident := Work.BoseFixB1B.w1MassB_eq_autocorr_gen (v := v) h hR hv_supp hM hℓ hd hR1 hR2 u
  have hqint := Work.BoseFixB1B.autocorr_quotient_integrable (v := v) h hR hv_supp hM hℓ hd hR1 hR2 u
  -- the pointwise comparison
  have hpoint : ∀ᵐ z ∂(volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
        * Submission.BoseGases.g0 v h z
      ≤ (Submission.BoseGases.g0 v h z
          / (Submission.BoseGases.convScaleSmall (Work.BoseFixB1.bM v μ)
                (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) z
              * Submission.BoseGases.convScale (Work.BoseFixB1.bSide v μ) z))
        * Work.BoseFixB1.autocorr (M := Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u z := by
    filter_upwards [hg0nn] with z hgn
    by_cases hz0 : Submission.BoseGases.g0 v h z = 0
    · rw [hz0]
      simp
    · have hzR : ‖z‖ < R :=
        lt_of_not_ge fun hge => hz0 (Submission.BoseGases.g0_zero_of_norm_ge hv_supp hge h)
      have hzle : ‖z‖ ≤ R := le_of_lt hzR
      have hA := hdef₁ μ hAdm1 u hu hmass z hzle
      rw [Work.BoseFixB1.autocorr_apply]
      obtain ⟨hDpos, hDle⟩ := Work.BoseFixB1S.wSmall1Pair_denom_bounds
        (M := Work.BoseFixB1.bM v μ) hM hℓ hd hR1 hRχ hzle
      have hdiv : Submission.BoseGases.g0 v h z
          ≤ Submission.BoseGases.g0 v h z
            / (Submission.BoseGases.convScaleSmall (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) z
                * Submission.BoseGases.convScale (Work.BoseFixB1.bSide v μ) z) := by
        rw [le_div_iff₀ hDpos]
        nlinarith [hgn, hDle]
      have hqnn : 0 ≤ Submission.BoseGases.g0 v h z
            / (Submission.BoseGases.convScaleSmall (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) z
                * Submission.BoseGases.convScale (Work.BoseFixB1.bSide v μ) z) :=
        div_nonneg hgn hDpos.le
      calc (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
              (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
            * Submission.BoseGases.g0 v h z
          ≤ (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
                (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
              * (Submission.BoseGases.g0 v h z
                  / (Submission.BoseGases.convScaleSmall (Work.BoseFixB1.bM v μ)
                        (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) z
                      * Submission.BoseGases.convScale (Work.BoseFixB1.bSide v μ) z)) :=
            mul_le_mul_of_nonneg_left hdiv (mul_nonneg (by norm_num) hchi_nn)
        _ ≤ (∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u x
                  * Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u (x - z))
              * (Submission.BoseGases.g0 v h z
                  / (Submission.BoseGases.convScaleSmall (Work.BoseFixB1.bM v μ)
                        (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) z
                      * Submission.BoseGases.convScale (Work.BoseFixB1.bSide v μ) z)) :=
            mul_le_mul_of_nonneg_right hA hqnn
        _ = (Submission.BoseGases.g0 v h z
                  / (Submission.BoseGases.convScaleSmall (Work.BoseFixB1.bM v μ)
                        (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) z
                      * Submission.BoseGases.convScale (Work.BoseFixB1.bSide v μ) z))
              * (∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u x
                  * Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u (x - z)) := by ring
  -- integrability of the dominating function, and the a.e. nonnegativity input of the comparison
  have hfnn : (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ≤ᵐ[volume]
      fun z => (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
        * Submission.BoseGases.g0 v h z := by
    filter_upwards [hg0nn] with z hgn
    exact mul_nonneg (mul_nonneg (by norm_num) hchi_nn) hgn
  have hmono := integral_mono_of_nonneg hfnn hqint hpoint
  have hg0int : (∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g0 v h z)
      = 8 * Real.pi * (_root_.BoseGases.a v) :=
    Submission.BoseGases.g0_integral (v := v) (R := R) hR hv_supp h
  have hlint : (∫ z : EuclideanSpace ℝ (Fin 3),
        (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
          * Submission.BoseGases.g0 v h z)
      = (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
        * (8 * Real.pi * (_root_.BoseGases.a v)) := by
    rw [MeasureTheory.integral_const_mul, hg0int]
  show (49 / 50) * (8 * Real.pi * _root_.BoseGases.a v)
      * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u
    ≤ Work.BoseFixB1.w1MassB h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u
  calc (49 / 50) * (8 * Real.pi * _root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
      = (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
          * (8 * Real.pi * (_root_.BoseGases.a v)) := by ring
    _ = ∫ z : EuclideanSpace ℝ (Fin 3),
          (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
              (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
            * Submission.BoseGases.g0 v h z := hlint.symm
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.g0 v h z
            / (Submission.BoseGases.convScaleSmall (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) z
                * Submission.BoseGases.convScale (Work.BoseFixB1.bSide v μ) z))
          * Work.BoseFixB1.autocorr (M := Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u z := hmono
    _ = Work.BoseFixB1.w1MassB h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u := hident.symm

end Work.BoseSWE
