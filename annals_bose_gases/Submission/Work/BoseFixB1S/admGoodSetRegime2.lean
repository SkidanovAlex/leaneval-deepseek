import ChallengeDeps
import Submission.Work.BoseFixB1.PerBoxNames
import Submission.Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet
import Submission.Work.BoseFixB1.regime_sideAt_ge
import Submission.Work.BoseFixB1S.boxMassLeDlCubeB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.admGoodSetRegime2`

The **regime at the sliding good set**, in the `bSide`/`bD`/`bV` vocabulary of
`Work.BoseFixB1.PerBoxNames`.  For every fixed potential support radius `R > 0`
there is a diluteness threshold `ε₀ > 0` such that for every *admissible*
chemical potential `μ` (`Work.BoseBoxFix.Adm v ε₀ μ`) and every
`u ∈ goodSet (bSide v μ) (bD v μ) μ`:

* the box side `ℓ = bSide v μ = sideAt μ (a v)` and the small-box parameter
  `d = bD v μ = (paramsAt μ (a v)).d` satisfy `16R ≤ ℓ`, `16R ≤ ℓd`,
  `0 < d ≤ 1`, `μ^{-1/3} ≤ ℓd`;
* the sliding box volume `bV v μ u = |B(u)|` satisfies `0 < |B(u)|`,
  `|B(u)| ≤ (ℓd)³`, `|B(u)| ≤ ℓ³` and `μ|B(u)| ≥ 1`.

All of this is pure regime bookkeeping on FS's monomials at the diluteness
`t = μ(a v)³`: `ℓ = a v·t^{-163/323}`, `d = t^{6/323}`
(`Work.BoseFixB1.RegimeAux`).  The threshold is a minimum of finitely many
explicit ones, so the lemma only needs `t ≤ ε₀`; `d ∈ (0,1]` for `t ≤ 1` and
`μ^{-1/3} ≤ ℓd` for `t ≤ 1`, while `16R ≤ ℓd` is the first conclusion of
`Work.BoseFixB1.regime_sideAt_ge`.

The box-volume part then uses the *proved* general facts
`Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet` (on the good set the box has
all three sides at least `μ^{-1/3}`, so `|B(u)| ≥ μ⁻¹`, i.e. `μ|B(u)| ≥ 1`) and
`Work.BoseFixB1S.boxMassLeDlCubeB1` (`|B(u)| ≤ (ℓd)³`).
-/

namespace Work.BoseFixB1S

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

theorem admGoodSetRegime2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ u : EuclideanSpace ℝ (Fin 3),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
            16 * R ≤ Work.BoseFixB1.bSide v μ
            ∧ 16 * R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ
            ∧ 0 < Work.BoseFixB1.bD v μ
            ∧ Work.BoseFixB1.bD v μ ≤ 1
            ∧ 0 < Work.BoseFixB1.bV v μ u
            ∧ Work.BoseFixB1.bV v μ u ≤ (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
            ∧ Work.BoseFixB1.bV v μ u ≤ (Work.BoseFixB1.bSide v μ) ^ 3
            ∧ 1 ≤ μ * Work.BoseFixB1.bV v μ u := by
  -- the diluteness threshold `ε₁` at which `16R ≤ ℓ·d`
  obtain ⟨ε₁, hε₁, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, ?_⟩
  intro μ hAdm u hu
  obtain ⟨hμ, ht, _hP⟩ := hAdm
  -- unfold the `bSide`/`bD`/`bV` abbreviations
  simp only [Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bV] at hu ⊢
  -- diluteness facts
  have ht₁ : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₁ := le_trans ht (min_le_left _ _)
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans ht (min_le_right _ _)
  have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (by positivity)
  -- `16R ≤ ℓ·d` (the first conclusion of `regime_sideAt_ge`)
  have hRd : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 := (hreg μ hμ ht₁).1
  have h16d : 16 * R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by linarith
  -- `0 < d ≤ 1`
  have hd_pos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    rw [Work.BoseFixB1.d_eq_fsXp]; exact Work.BoseBox.fsXp_pos ht0
  have hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
    rw [Work.BoseFixB1.d_eq_fsXp]; exact Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num)
  have hld_pos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    lt_of_lt_of_le (by linarith) h16d
  have hℓ_pos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    pos_of_mul_pos_left hld_pos hd_pos.le
  -- `16R ≤ ℓ`
  have h16ℓ : 16 * R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    calc 16 * R
        ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := h16d
      _ ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * 1 :=
          mul_le_mul_of_nonneg_left hd1 hℓ_pos.le
      _ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := mul_one _
  -- `μ^{-1/3} ≤ ℓ·d`
  have hreg_mu : μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    have h1 := Work.BoseFixB1.mu_inv_third_eq (A := _root_.BoseGases.a v) (μ := μ) hav hμ
    have h2 := Work.BoseFixB1.d_mul_sideAt_eq (A := _root_.BoseGases.a v) (μ := μ) hav hμ
    have h3 : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(323 / 3))
        ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157) :=
      Work.BoseBox.fsXp_le_fsXp ht0 ht1 (by norm_num)
    rw [h1, mul_comm (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d, h2]
    exact mul_le_mul_of_nonneg_left h3 hav.le
  -- the box volume: `μ⁻¹ ≤ |B(u)|`
  have hbm : (μ ^ (-(1 / 3 : ℝ))) ^ 3 ≤ Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u :=
    Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet hℓ_pos hd_pos hd1 hμ hreg_mu hu
  have hcube : (μ ^ (-(1 / 3 : ℝ))) ^ 3 = μ⁻¹ := by
    rw [← Real.rpow_natCast (μ ^ (-(1 / 3 : ℝ))) 3, ← Real.rpow_mul hμ.le,
      show (-(1 / 3 : ℝ)) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hbm' : μ⁻¹ ≤ Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u := by
    rwa [hcube] at hbm
  have hVpos : 0 < Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u :=
    lt_of_lt_of_le (inv_pos.mpr hμ) hbm'
  have hVle : Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u
      ≤ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3 :=
    Work.BoseFixB1S.boxMassLeDlCubeB1 u hld_pos
  have hVle2 : Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u
      ≤ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
    refine le_trans hVle ?_
    have hle : Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      calc Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * 1 :=
            mul_le_mul_of_nonneg_left hd1 hℓ_pos.le
        _ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := mul_one _
    exact pow_le_pow_left₀ hld_pos.le hle 3
  have hmuV : 1 ≤ μ * Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u := by
    have h := mul_le_mul_of_nonneg_left hbm' hμ.le
    rwa [mul_inv_cancel₀ hμ.ne'] at h
  exact ⟨h16ℓ, h16d, hd_pos, hd1, hVpos, hVle, hVle2, hmuV⟩

end Work.BoseFixB1S
