import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.perBoxCrudeLowerB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.perBoxCrudeGoodOfPerBoxF`

The **good-set** version of `Work.BoseFixB1S.perBoxCrudeLower_of_perBoxF`: from the
`F`-weighted per-box bound `Work.BoseFixB1.PerBoxF` — here assumed on the *whole* good set
`G` (`Work.SmallBoxSliding.goodSet`), which is where FS `thm:smallbox` is stated, rather than
only on the interior `I₋` — one gets the crude per-`u` lower bound

    sbWord h μ u Φ ≥ −C' (μ²(a v)·χ_M(u) + μ(a v))·‖Φ‖²

on the whole good set.

The argument is exactly the interior route: drop the manifestly nonnegative `F`-remainder
(`w1MassB_nonneg` × the nonnegative configuration integral), absorb the half-mass term with
the per-`u` mass law `w1MassB_le_const_mul_chiMass_regime`, and bound the FS error bracket
`Γ_B = (R/(dℓ))² + K_B³(μa³)^{1/2} ≤ 2` by `R ≤ ℓd/16` (`regime_sideAt_ge`) and
`K_B³(μa³)^{1/2} = fsXp t (287/2) ≤ 1` (`fsXp_le_one` at diluteness `t ≤ ε₀' ≤ 1`).
Nothing in it depends on the shape of the `u`-set: `u`'s membership is used only to invoke
`hper`, so the same proof covers `goodSet` (and in particular the bad band
`G ∖ I₋`).
-/

namespace Work.BoseFixB1B

open MeasureTheory

/-- FS's weight `F(t) = c(t−μ)²/(1+tμ⁻¹)` is nonnegative on the physical range `t ≥ 0`. -/
private lemma psiWeight_nonnegGood {c μ t : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ Work.SmallBoxSliding.psiWeight c μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  have hd : 0 < 1 + t * μ⁻¹ := by positivity
  exact div_nonneg (mul_nonneg hc (sq_nonneg _)) hd.le

/-- The per-configuration small-box particle count is a sum of squares, hence nonnegative. -/
private lemma nCountB_nonnegGood (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (x : Submission.BoseGases.X n) : 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
  rw [Work.BoseFixB1.nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **The arithmetic core.**  If the `F`-weighted per-box bound holds in the shape produced by
`PerBoxF`, then the crude lower bound `−C'(μ²(a v)χ + μ(a v))‖Φ‖² ≤ sbWord` follows with
`C' = Cm/2 + 3C`, where `Cm` is the constant of the mass bound `W ≤ Cm·a·V` (here `a = a v`,
`V = χ_M(u)`) and `2` dominates the FS error bracket. -/
private lemma perBoxCrude_arithGood {c₁ W I G μ a V N C Cm sb : ℝ}
    (h : c₁ * (W * I) - (1 / 2) * μ ^ 2 * W * N - C * (μ ^ 2 * a * G * V * N + μ * a * N) ≤ sb)
    (hc₁ : 0 ≤ c₁) (hW : 0 ≤ W) (hI : 0 ≤ I) (hC : 0 ≤ C) (hCm : 0 ≤ Cm)
    (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hV : 0 ≤ V) (hN : 0 ≤ N)
    (hWb : W ≤ Cm * a * V) (hG : G ≤ 2) :
    -((Cm / 2 + 3 * C) * (μ ^ 2 * a * V + μ * a)) * N ≤ sb := by
  -- the dropped `F`-remainder is nonnegative
  have hdrop : 0 ≤ c₁ * (W * I) := mul_nonneg hc₁ (mul_nonneg hW hI)
  have hX : 0 ≤ μ ^ 2 * a * V * N := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hV) hN
  have hY : 0 ≤ μ * a * N := mul_nonneg (mul_nonneg hμ ha) hN
  have hcoef : 0 ≤ (1 / 2 : ℝ) * μ ^ 2 * N :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg μ)) hN
  -- (i) the half-mass term against the mass bound
  have h1 : (1 / 2) * μ ^ 2 * W * N ≤ (Cm / 2) * (μ ^ 2 * a * V * N) := by
    calc (1 / 2) * μ ^ 2 * W * N = ((1 / 2) * μ ^ 2 * N) * W := by ring
      _ ≤ ((1 / 2) * μ ^ 2 * N) * (Cm * a * V) := mul_le_mul_of_nonneg_left hWb hcoef
      _ = (Cm / 2) * (μ ^ 2 * a * V * N) := by ring
  -- (ii) the error bracket against `G ≤ 2`
  have h2 : C * (μ ^ 2 * a * G * V * N) ≤ (2 * C) * (μ ^ 2 * a * V * N) := by
    have hstep : μ ^ 2 * a * G * V * N ≤ μ ^ 2 * a * 2 * V * N := by
      calc μ ^ 2 * a * G * V * N = (μ ^ 2 * a * V * N) * G := by ring
        _ ≤ (μ ^ 2 * a * V * N) * 2 := mul_le_mul_of_nonneg_left hG hX
        _ = μ ^ 2 * a * 2 * V * N := by ring
    calc C * (μ ^ 2 * a * G * V * N) ≤ C * (μ ^ 2 * a * 2 * V * N) :=
          mul_le_mul_of_nonneg_left hstep hC
      _ = (2 * C) * (μ ^ 2 * a * V * N) := by ring
  -- the two pieces against the allowance `(Cm/2 + 3C)(μ²aV + μa)N`
  have hk1 : 0 ≤ C * (μ ^ 2 * a * V * N) := mul_nonneg hC hX
  have hk2 : 0 ≤ (Cm / 2) * (μ * a * N) := mul_nonneg (by linarith) hY
  have hk3 : 0 ≤ 2 * C * (μ * a * N) := mul_nonneg (by linarith) hY
  have hK : (1 / 2) * μ ^ 2 * W * N + C * (μ ^ 2 * a * G * V * N + μ * a * N)
      ≤ (Cm / 2 + 3 * C) * (μ ^ 2 * a * V + μ * a) * N := by
    have h1' : (1 / 2) * μ ^ 2 * W * N ≤ (Cm / 2) * (μ ^ 2 * a * V * N) := h1
    have h2' : C * (μ ^ 2 * a * G * V * N) ≤ (2 * C) * (μ ^ 2 * a * V * N) := h2
    nlinarith [h1', h2', hk1, hk2, hk3]
  linarith [h, hdrop, hK]

theorem perBoxCrudeGoodOfPerBoxF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J)
    {ε₀ c₁ C : ℝ} (hε₀ : 0 < ε₀) (hc₁ : 0 < c₁) (hC : 0 ≤ C)
    (hper : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u) :
    ∃ ε₀' C' : ℝ, 0 < ε₀' ∧ 0 ≤ C' ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀' μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
            -(C' * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v)))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  -- the mass-bound threshold and constant
  obtain ⟨εm, Cm, hεm, hCm, hmass⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  -- the regime threshold `R ≤ ℓ d / 16`
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀ (min εm (min εr 1)), Cm / 2 + 3 * C,
    lt_min hε₀ (lt_min hεm (lt_min hεr one_pos)), by positivity, ?_⟩
  intro μ hAdm hJKB n Φ hlow u hmem
  -- ## the admissible data
  have hAdm₀ : Work.BoseBoxFix.Adm v ε₀ μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm_m : Work.BoseBoxFix.Adm v εm μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdil_m : μ * (_root_.BoseGases.a v) ^ 3 ≤ εm :=
    Work.BoseFixB1.adm_dilute hAdm_m
  have hdil_r : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hdil_1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have ht_pos : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  -- ## the `F`-weighted per-box bound (unfolded), on the good set
  have hs := hper μ hAdm₀ n Φ u hmem
  rw [Work.BoseFixB1.PerBoxF] at hs
  -- ## the mass bound at this `μ`
  have hmassμ := hmass μ hAdm_m u
  -- ## the FS regime bracket `Γ_B ≤ 2`
  obtain ⟨hR16, _hRχ⟩ := hreg μ hμ hdil_r
  have hℓd : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := mul_pos hℓ hd
  have hratio : R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ≤ 1 / 16 := by
    rw [div_le_iff₀ hℓd]
    linarith
  have hsq : (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2 ≤ (1 / 16) ^ 2 := by
    have h0 : 0 ≤ R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) := by positivity
    nlinarith [hratio, h0]
  have hKB3 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 1 := by
    rw [Work.BoseFixB1.KB3_half_eq hav hμ]
    exact Work.BoseBox.fsXp_le_one ht_pos hdil_1 (by norm_num)
  have hG : (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 2 := by
    nlinarith [hsq, hKB3]
  -- ## the nonnegativity facts
  have hW : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  have hV : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hI : 0 ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseFixB1.nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
          / Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg _)
      (psiWeight_nonnegGood (by norm_num) hμ
        (div_nonneg (nCountB_nonnegGood _ _ _ _ x) hV))
  have hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  -- ## the arithmetic
  exact perBoxCrude_arithGood hs hc₁.le hW hI hC hCm hμ.le hav.le hV hN hmassμ hG

end Work.BoseFixB1B
