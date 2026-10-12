import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.aestronglyMeasurableNomDens
import Submission.Work.BoseB1Cube.countAbsorbArith
import Submission.Work.BoseB1Cube.integrableOnMulPsiWeight
import Submission.Work.BoseB1Cube.integrableOnWbMassMulNomDens
import Submission.Work.BoseB1Cube.nomJensen_integrated
import Submission.Work.BoseB1Cube.nomSplitRow
import Submission.Work.BoseB1Cube.rpsi_ge_affine
import Submission.Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet
import Submission.Work.BoseFixB1S.perBoxGapBranchB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.nomCountAbsorb` — FS's count absorption (`thm:aprioriHLambda`, step 4)
at the **nominal** (indicator-count) density

The nominal twin of the proved `Work.BoseB1Cube.CrudePlan.CountAbsorb`
(`Submission/Work/BoseB1Cube/countAbsorb_holds.lean`): FS's `U`-argument absorbs the particle
number of a box state into the mean-field scale `μ²(a v)ℓ³‖Φ‖²`, the step-4 remainder `R_Ψ`
(here its sharp-indicator spelling `nomRPsi`) and the excited count `⟨n₊⟩`:

    μ (a v) n ‖Φ‖² ≤ C ( μ² (a v) ℓ³ ‖Φ‖² + R_Ψ + μ (a v) ⟨n₊⟩ ) .

The three rows of the pure-real arithmetic `Work.BoseB1Cube.countAbsorbArith` are supplied by

* `Work.BoseB1Cube.affine_le_of_psiWeight` (the integrated Jensen inequality
  `Work.BoseB1Cube.nomJensen_integrated` together with the pointwise affine bound
  `psiWeight 1 μ t ≥ μt/3 − μ²`), whose two integrability inputs are the delegated
  `Work.BoseB1Cube.integrableOnWbMassMulNomDens` and
  `Work.BoseB1Cube.integrableOnMulPsiWeight` (the latter fed by
  `Work.BoseB1Cube.aestronglyMeasurableNomDens`);
* the `P/Q`-split `Work.BoseB1Cube.nomSplitRow` at `ε = 1/2` (the sharp-indicator twin of
  `Work.BoseB1Cube.pqsplit_ge`, using `sig_sharp_wbUSharp`, `integral_wbUSharp`,
  `wbUSharp_facts` and the Parseval identities `pSum_eq`/`qSum_eq`);
* the ratio bound `KU·ℓ³ ≤ C_s·W` from `Work.BoseFixB1.WB.wbW_lower` (`W ≥ π(a v)ℓ³`).

The parameter regime (`Work.BoseFixB1.WB.window_regime`, `mass_upper`, `mass_total2`) and the
sharp box-volume lower bound `μ⁻¹ ≤ |B(u)|` on the interior set
(`Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet`) are consumed exactly as in the smooth twin.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem nomCountAbsorb {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        μ * (_root_.BoseGases.a v) * (n : ℝ)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              + Work.BoseB1Cube.nomRPsi h μ (Φ : Submission.BoseGases.X n → ℝ)
              + μ * (_root_.BoseGases.a v)
                  * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Φ : Submission.BoseGases.X n → ℝ)) := by
  -- the pointwise localised-mass bound and the parameter regime
  obtain ⟨C₁₀, hC₁₀, hmassU₀⟩ :=
    Work.BoseFixB1.WB.mass_upper (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  set C₁ : ℝ := max C₁₀ 1 with hC₁def
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₁0 : 0 ≤ C₁ := le_of_lt hC₁pos
  obtain ⟨εR, hεR, hregime⟩ :=
    Work.BoseFixB1.WB.window_regime (v := v) (R := R) (C₁ := C₁) (C_A := 1) hav hR hC₁pos one_pos
  -- the universal constant of the conclusion
  set K₀ : ℝ := (chiSupAbs * chiSmallDecay Work.BoseBox.mValue) ^ 2 with hK₀def
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀def]; positivity
  have hCs0 : 0 ≤ C₁ * K₀ / Real.pi := div_nonneg (mul_nonneg hC₁0 hK₀0) Real.pi_pos.le
  refine ⟨εR, 6 / Real.pi + 6 + 1 + 6 * (C₁ * K₀ / Real.pi), hεR, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 6 / Real.pi := div_nonneg (by norm_num) Real.pi_pos.le
    have h2 : (0 : ℝ) ≤ 6 * (C₁ * K₀ / Real.pi) := mul_nonneg (by norm_num) hCs0
    linarith
  intro μ hAdm n Φ
  have hμ : 0 < μ := hAdm.1
  obtain ⟨hRchiR0, hRd16, hM3, ht1, hεhalf, hKB, hθ, hcomp⟩ := hregime μ hAdm
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := le_trans (by norm_num : 1 ≤ 3) hM3
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hAdm
  have ha0 : 0 ≤ a v := le_of_lt hav
  have hmassU : ∀ u : E3, wbMass v h μ u
      ≤ C₁ * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
    intro u
    have h1 := hmassU₀ hℓ hd hRd16 hRchiR0 u
    calc wbMass v h μ u
        = w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := rfl
      _ ≤ C₁₀ * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := h1
      _ ≤ C₁ * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
          have h2 : C₁₀ * (a v) ≤ C₁ * (a v) := mul_le_mul_of_nonneg_right (le_max_left _ _) ha0
          exact mul_le_mul_of_nonneg_right h2 (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _)
  have hmassL : ∀ u : E3, 0 ≤ wbMass v h μ u :=
    fun u => wbMass_nonneg (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hM1 hℓ hd u
  -- the total localised mass is `≍ 8π(a v)ℓ³`, hence `wbW ≥ π(a v)ℓ³`
  have htotal_raw := Work.BoseFixB1.WB.mass_total2 (v := v) (h := h) (R0 := R)
    (M := (paramsAt μ (a v)).M) hv_supp hR ha0 hM3 hℓ hd hRd16
    (chiR0_pos) hRchiR0 (fun x hx => chiR0_half x hx)
  have hπC : 0 < 8 * Real.pi * (a v) * (sideAt μ (a v)) ^ 3 := by positivity
  have htotal : 8 * Real.pi * (a v) * (sideAt μ (a v)) ^ 3 * (3 / 4)
      ≤ ∫ u : E3, wbMass v h μ u := by
    have h2 : |(∫ u : E3, wbMass v h μ u)
        - 8 * Real.pi * (a v) * (sideAt μ (a v)) ^ 3|
        ≤ (1 / 4) * (8 * Real.pi * (a v) * (sideAt μ (a v)) ^ 3) := by
      refine le_trans htotal_raw ?_
      have h4 : convDevC (paramsAt μ (a v)).M * (R / sideAt μ (a v)) ^ 2 ≤ 1 / 4 := hθ
      nlinarith [h4, hπC]
    have h3 := (abs_le.mp h2).1
    linarith
  have hWlow := Work.BoseFixB1.WB.wbW_lower (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ
    hav hM1 hℓ hd hC₁pos hmassU htotal hcomp
  -- the two nonnegative payers of the target's right-hand side
  have hRnn : 0 ≤ nomRPsi h μ (Φ : X n → ℝ) := by
    rw [nomRPsi]
    exact integral_nonneg fun u =>
      mul_nonneg (hmassL u) (nomBoxInner_nonneg hμ (Φ : X n → ℝ) u)
  have hKnn : 0 ≤ cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by
    rw [Submission.BoseGases.cnPlus]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hNn : 0 ≤ normB v μ n (Φ : X n → ℝ) := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact integral_nonneg fun x => sq_nonneg _
  rcases eq_or_lt_of_le hNn with hNz | hNpos
  · -- `N = 0`: the left side vanishes and the right side is nonnegative
    have hL2 : μ * (a v) * (n : ℝ) * normB v μ n (Φ : X n → ℝ) = 0 := by
      rw [← hNz]; ring
    rw [hL2]
    refine mul_nonneg (by positivity)
      (add_nonneg (add_nonneg ?_ hRnn)
        (mul_nonneg (mul_nonneg hμ.le hav.le) hKnn))
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le)
      (pow_nonneg hℓ.le 3)) hNn
  · -- `N > 0`: the Jensen/affine row, the `P/Q`-split and the ratio bound
    -- the regime fact `μ⁻¹ ≤ |B(u)|` on the interior set
    have hbu : ∀ u ∈ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
        μ⁻¹ ≤ boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
      intro u hu
      have htpos : 0 < μ * (a v) ^ 3 := by positivity
      have hreg : μ ^ (-(1 / 3 : ℝ)) ≤ sideAt μ (a v) * (paramsAt μ (a v)).d := by
        rw [mul_comm (sideAt μ (a v)) (paramsAt μ (a v)).d,
          Work.BoseFixB1.d_mul_sideAt_eq hav hμ, Work.BoseFixB1.mu_inv_third_eq hav hμ]
        exact mul_le_mul_of_nonneg_left
          (Work.BoseBox.fsXp_le_fsXp htpos ht1 (by norm_num)) hav.le
      have hd1 : (paramsAt μ (a v)).d ≤ 1 := by
        rw [Work.BoseFixB1.d_eq_fsXp]
        exact Work.BoseBox.fsXp_le_one htpos ht1 (by norm_num)
      have hvol := Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet hℓ hd hd1 hμ hreg
        (Work.SmallBoxSliding.interiorSet_subset_goodSet hμ hu)
      have hcube : μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 = 1 := by
        rw [← Real.rpow_natCast (μ ^ (-(1 / 3 : ℝ))) 3,
          ← Real.rpow_mul (x := μ) hμ.le (-(1 / 3)) ((3 : ℕ) : ℝ),
          show (-(1 / 3 : ℝ)) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
        exact mul_inv_cancel₀ (ne_of_gt hμ)
      calc μ⁻¹ = μ⁻¹ * 1 := by ring
        _ ≤ μ⁻¹ * (μ * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hμ.le)
            calc (1 : ℝ) = μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 := hcube.symm
              _ ≤ μ * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
                  mul_le_mul_of_nonneg_left hvol hμ.le
        _ = boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
            rw [show μ⁻¹ * (μ * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
                = (μ⁻¹ * μ) * boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u by ring,
              inv_mul_cancel₀ (ne_of_gt hμ), one_mul]
    -- (1) the Jensen row
    have hJ := Work.BoseB1Cube.nomJensen_integrated h hv hvrad hR hv_supp hμ hav hM1 hℓ hd hbu Φ
    have hmeasDens : AEStronglyMeasurable
        (fun u : E3 => nomDens h μ (Φ : X n → ℝ) u) (volume : Measure E3) :=
      aestronglyMeasurableNomDens Φ
    have hIg : IntegrableOn (fun u : E3 => wbMass v h μ u)
        (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
      Work.BoseFixB1.WB.integrableOn_wbMass_interior (v := v) (h := h) (R0 := R)
        hv hvrad hv_supp hR hμ hav hM1 hℓ hd
    have hIgt : IntegrableOn
        (fun u : E3 => wbMass v h μ u * nomDens h μ (Φ : X n → ℝ) u)
        (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
      integrableOnWbMassMulNomDens hv hvrad hv_supp hR hμ hav hM1 hℓ hd hC₁pos hmassU Φ hNpos
    have hIpsi : IntegrableOn
        (fun u : E3 => wbMass v h μ u * psiWeight 1 μ (nomDens h μ (Φ : X n → ℝ) u))
        (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
      integrableOnMulPsiWeight hμ
        (fun u _ => nomDens_nonneg (Φ : X n → ℝ) u)
        (fun u _ => hmassL u) hIg hIgt
        ((hmeasDens.mono_measure Measure.restrict_le_self).aemeasurable)
    have hsig : μ / 3 * (normB v μ n (Φ : X n → ℝ) * nomSig h μ (Φ : X n → ℝ))
        - μ ^ 2 * (normB v μ n (Φ : X n → ℝ) * wbW v h μ) ≤ nomRPsi h μ (Φ : X n → ℝ) :=
      affine_le_of_psiWeight
        (G := interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)
        (t := fun u : E3 => nomDens h μ (Φ : X n → ℝ) u)
        (g := fun u : E3 => wbMass v h μ u)
        (μ := μ) (N := normB v μ n (Φ : X n → ℝ)) (P := nomRPsi h μ (Φ : X n → ℝ))
        (Work.SmallBoxSliding.measurableSet_interiorSet _ _ _) hμ hNpos
        (fun u _ => nomDens_nonneg (Φ : X n → ℝ) u) (fun u _ => hmassL u)
        hIg hIgt hIpsi hJ
    -- (2) the `P/Q`-split row
    have hsplit := nomSplitRow hv hvrad hv_supp hR hμ hav hM1 hℓ hd hC₁pos hmassU Φ hNpos
    -- (3) the ratio bound
    have hKUW : (C₁ * K₀ * (a v)) * (sideAt μ (a v)) ^ 3 ≤ (C₁ * K₀ / Real.pi) * wbW v h μ := by
      have hkey : (C₁ * K₀ * (a v)) * (sideAt μ (a v)) ^ 3
          = (C₁ * K₀ / Real.pi) * (Real.pi * (a v) * (sideAt μ (a v)) ^ 3) := by
        field_simp
      rw [hkey]
      exact mul_le_mul_of_nonneg_left hWlow hCs0
    -- (4) the arithmetic
    exact countAbsorbArith (hμ := hμ) (ha := hav) (hℓ := hℓ) (hN0 := hNpos.le)
      (hK0 := hKnn) (hP0 := hRnn) (hW := hWlow) (hCs := hCs0) hsig hsplit hKUW

end Work.BoseB1Cube
