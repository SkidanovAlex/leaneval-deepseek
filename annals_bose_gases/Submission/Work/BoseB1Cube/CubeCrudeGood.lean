import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.CubeCrudeGood` — the crude per-`u` bound from the per-box row

The cube twin of the PROVED `Work.BoseFixB1S.perBoxCrudeLower_of_perBoxF`
(`Submission/Work/BoseFixB1S/perBoxCrudeLower_of_perBoxF.lean`): from the `F`-weighted per-box row
`Work.BoseB1Cube.CubePerBox` at the single cube cutoff one gets the crude per-`u` lower bound

    sbWordCube v h μ u Φ ≥ −C'·(μ²(a v)·χ_M(u) + μ(a v))·‖Φ‖²

on FS's good set (`Work.BoseB1Cube.CubeCrudeGood`), by

* dropping the manifest nonnegative `F`-remainder `c₁·(∬w_{1,B})·∫Φ²F` (`w1MassB_nonneg` for the
  mass, and `F(t) = (t−μ)²/(1+t/μ⁻¹) ≥ 0` for `t ≥ 0`);
* applying the proved per-`u` mass bound `∬w_{1,B} ≤ C(a v)·χ_M(u)`
  (`Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime`);
* collecting FS's regime bracket `Γ_B = (R/(dℓ))² + K_B³(μa³)^{1/2} ≤ 2` from `R ≤ ℓd/16`
  (`regime_sideAt_ge`) and `K_B³(μa³)^{1/2} ≤ 1` at small diluteness (`KB3_half_eq` +
  `fsXp_le_one`).

The whole computation is `perBoxCubeCrude_arith` below; the constant is `C' = Cm/2 + 3C`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- FS's weight `F(t) = c(t−μ)²/(1+tμ⁻¹)` is nonnegative on the physical range `t ≥ 0`. -/
private lemma psiWeight_nonneg_cube {c μ t : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ Work.SmallBoxSliding.psiWeight c μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  exact div_nonneg (mul_nonneg hc (sq_nonneg _)) (by positivity)

/-- The per-configuration small-box particle count is a sum of squares. -/
private lemma nCountB_nonneg_cube (M : ℕ) (ℓ d : ℝ) (u : E3) {n : ℕ} (x : X n) :
    0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
  rw [Work.BoseFixB1.nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **The arithmetic core** (verbatim the `perBoxCrude_arith` of
`Work.BoseFixB1S.perBoxCrudeLower_of_perBoxF`, which is `private` there). -/
private lemma perBoxCubeCrude_arith {c₁ W I G μ a V N C Cm sb : ℝ}
    (h : c₁ * (W * I) - (1 / 2) * μ ^ 2 * W * N - C * (μ ^ 2 * a * G * V * N + μ * a * N) ≤ sb)
    (hc₁ : 0 ≤ c₁) (hW : 0 ≤ W) (hI : 0 ≤ I) (hC : 0 ≤ C) (hCm : 0 ≤ Cm)
    (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hV : 0 ≤ V) (hN : 0 ≤ N)
    (hWb : W ≤ Cm * a * V) (hG : G ≤ 2) :
    -((Cm / 2 + 3 * C) * (μ ^ 2 * a * V + μ * a)) * N ≤ sb := by
  have hdrop : 0 ≤ c₁ * (W * I) := mul_nonneg hc₁ (mul_nonneg hW hI)
  have hX : 0 ≤ μ ^ 2 * a * V * N := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hV) hN
  have hY : 0 ≤ μ * a * N := mul_nonneg (mul_nonneg hμ ha) hN
  have hcoef : 0 ≤ (1 / 2 : ℝ) * μ ^ 2 * N :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg μ)) hN
  have h1 : (1 / 2) * μ ^ 2 * W * N ≤ (Cm / 2) * (μ ^ 2 * a * V * N) := by
    calc (1 / 2) * μ ^ 2 * W * N = ((1 / 2) * μ ^ 2 * N) * W := by ring
      _ ≤ ((1 / 2) * μ ^ 2 * N) * (Cm * a * V) := mul_le_mul_of_nonneg_left hWb hcoef
      _ = (Cm / 2) * (μ ^ 2 * a * V * N) := by ring
  have h2 : C * (μ ^ 2 * a * G * V * N) ≤ (2 * C) * (μ ^ 2 * a * V * N) := by
    have hstep : μ ^ 2 * a * G * V * N ≤ μ ^ 2 * a * 2 * V * N := by
      calc μ ^ 2 * a * G * V * N = (μ ^ 2 * a * V * N) * G := by ring
        _ ≤ (μ ^ 2 * a * V * N) * 2 := mul_le_mul_of_nonneg_left hG hX
        _ = μ ^ 2 * a * 2 * V * N := by ring
    calc C * (μ ^ 2 * a * G * V * N) ≤ C * (μ ^ 2 * a * 2 * V * N) :=
          mul_le_mul_of_nonneg_left hstep hC
      _ = (2 * C) * (μ ^ 2 * a * V * N) := by ring
  have hk1 : 0 ≤ C * (μ ^ 2 * a * V * N) := mul_nonneg hC hX
  have hk2 : 0 ≤ (Cm / 2) * (μ * a * N) := mul_nonneg (by linarith) hY
  have hk3 : 0 ≤ 2 * C * (μ * a * N) := mul_nonneg (by linarith) hY
  have hK : (1 / 2) * μ ^ 2 * W * N + C * (μ ^ 2 * a * G * V * N + μ * a * N)
      ≤ (Cm / 2 + 3 * C) * (μ ^ 2 * a * V + μ * a) * N := by
    nlinarith [h1, h2, hk1, hk2, hk3]
  linarith [h, hdrop, hK]

/-- **The crude per-`u` bound on FS's good set from the `F`-weighted per-box row.** -/
theorem cubeCrudeGood_of_cubePerBox {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hF : CubePerBox v h R) : CubeCrudeGood v h := by
  classical
  obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, hper⟩ := hF
  obtain ⟨εm, Cm, hεm, hCm, hmass⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀ (min εm (min εr 1)), Cm / 2 + 3 * C,
    lt_min hε₀ (lt_min hεm (lt_min hεr one_pos)), by positivity, ?_⟩
  intro J μ hAdm hJKB n Φ u hmem _
  have hAdm₀ : Adm v ε₀ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm_m : Adm v εm μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdil_r : μ * (a v) ^ 3 ≤ εr :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hdil_1 : μ * (a v) ^ 3 ≤ 1 :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have ht_pos : 0 < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hs := hper μ hAdm₀ n Φ u hmem
  rw [Work.BoseFixB1S.PerBoxFCube] at hs
  have hmassμ := hmass μ hAdm_m u
  obtain ⟨hR16, _⟩ := hreg μ hμ hdil_r
  have hℓd : 0 < sideAt μ (a v) * (paramsAt μ (a v)).d := mul_pos hℓ hd
  have hratio : R / (sideAt μ (a v) * (paramsAt μ (a v)).d) ≤ 1 / 16 := by
    rw [div_le_iff₀ hℓd]
    linarith
  have hsq : (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2 ≤ (1 / 16) ^ 2 := by
    have h0 : 0 ≤ R / (sideAt μ (a v) * (paramsAt μ (a v)).d) := by positivity
    nlinarith [hratio, h0]
  have hKB3 : (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 1 := by
    rw [Work.BoseFixB1.KB3_half_eq hav hμ]
    exact Work.BoseBox.fsXp_le_one ht_pos hdil_1 (by norm_num)
  have hG : (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 2 := by
    nlinarith [hsq, hKB3]
  have hW : 0 ≤ Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u :=
    Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  have hV : 0 ≤ Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hI : 0 ≤ ∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
      Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
          / Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg _)
      (psiWeight_nonneg_cube (by norm_num) hμ
        (div_nonneg (nCountB_nonneg_cube _ _ _ _ x) hV))
  have hN : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  exact perBoxCubeCrude_arith hs hc₁.le hW hI hC hCm hμ.le hav.le hV hN hmassμ hG

end Work.BoseB1Cube
