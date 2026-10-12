import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.honestBogOpBoundFS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honestThresholdRow` — FS's threshold row `hc₁` at the honest family

This module proves the `hc₁` row of `Submission.Work.BoseBogFS.honestNumericRows`:

    (sℓ)⁻¹ + √(2ρ·16πa/(1 − ε_T)) ≤ 4K_L√(μa)

for every admissible chemical potential `μ` (i.e. for every sufficiently small diluteness
`t = μa³`) in the close region `|ρ − μ| ≤ μK_ℓ⁻²/(2¹⁴π)`, at the honest family
`HonestBoxFam`.

## The reduction

The view pins every scalar of the honest `Q3Env` (`RViewFS` conjuncts 2–9) and `FSParamsView`
pins the rest (`Kl = fsXp t (−3/2)`, `s = fsXp t 1`, `d = fsXp t 6`, `eT = fsXp t (23/4)`,
`KL = (Kl·d²)⁻¹`), so with `t = μa³` and `u = √(μ·a v) > 0` the two sides are

    (sℓ)⁻¹ = u·t^{1/646},        √(2ρ·16πa/(1−eT)) = u·√(32π(ρ/μ)/(1−t^{23/1292})),
    4K_L√(μa) = u·4t^{−21/646},

i.e. the whole row reduces to the *pure real* inequality

    t^{1/646} + √(32π(ρ/μ)/(1 − t^{23/1292})) ≤ 4t^{−21/646}   (0 < t ≤ 2^{−1000}, 0 < ρ ≤ 2μ)

which is `thresholdArith` below.  The numerical content is that `ε_T = t^{23/1292} ≤ 1/2`,
`ρ/μ ≤ 2`, `t^{1/646} ≤ 1` and `4t^{−21/646} ≥ 4·2^{32}` — the margin is enormous.

The diluteness threshold `ε₀ = 2^{−1000}` is the one delivered by the theorem; FS's own
requirement is `ε₀ ≲ 10^{−14}` (the ratio is `¼t^{11/323} + O(t^{21/646})`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## 1. Two elementary power comparisons -/

/-- `ε_T = t^{23/1292} ≤ 1/2` for `0 < t ≤ 2^{-1000}` (indeed `≤ 2^{-17.8}`). -/
theorem rpow_23_le_half {t : ℝ} (ht₀ : 0 < t) (htε : t ≤ (1 / 2) ^ 1000) :
    t ^ ((23 : ℝ) / 1292) ≤ 1 / 2 := by
  have hz : (0 : ℝ) ≤ (23 : ℝ) / 1292 := by norm_num
  have h₁ : t ^ ((23 : ℝ) / 1292) ≤ ((1 / 2 : ℝ) ^ 1000) ^ ((23 : ℝ) / 1292) :=
    Real.rpow_le_rpow ht₀.le htε hz
  have h₂ : ((1 / 2 : ℝ) ^ 1000) ^ ((23 : ℝ) / 1292) = (1 / 2 : ℝ) ^ ((5750 : ℝ) / 323) := by
    rw [← Real.rpow_natCast (x := (1 / 2 : ℝ)) (n := 1000),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    norm_num
  rw [h₂] at h₁
  refine le_trans h₁ ?_
  have h3 : (1 : ℝ) ≤ (5750 : ℝ) / 323 := by norm_num
  calc (1 / 2 : ℝ) ^ ((5750 : ℝ) / 323) ≤ (1 / 2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) h3
    _ = 1 / 2 := Real.rpow_one _

/-- `1024 ≤ t^{−21/646}` for `0 < t ≤ 2^{-1000}` (indeed `≥ 2^{32.5}`). -/
theorem rpow_neg21_ge {t : ℝ} (ht₀ : 0 < t) (htε : t ≤ (1 / 2) ^ 1000) :
    (1024 : ℝ) ≤ t ^ (-(21 / 646 : ℝ)) := by
  have h₁ : ((1 / 2 : ℝ) ^ 1000) ^ (-(21 / 646 : ℝ)) ≤ t ^ (-(21 / 646 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ht₀ htε (by norm_num)
  have h₂ : ((1 / 2 : ℝ) ^ 1000) ^ (-(21 / 646 : ℝ)) = (1 / 2 : ℝ) ^ (-(10500 / 323 : ℝ)) := by
    rw [← Real.rpow_natCast (x := (1 / 2 : ℝ)) (n := 1000),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    norm_num
  have h3 : -(10500 / 323 : ℝ) ≤ -(10 : ℝ) := by norm_num
  have h₄ : (1 / 2 : ℝ) ^ (-(10 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(10500 / 323 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) h3
  have h₅ : (1 / 2 : ℝ) ^ (-(10 : ℝ)) = 1024 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  linarith

/-! ## 2. The pure arithmetic core -/

/-- **The threshold arithmetic.**  For `0 < t ≤ 2^{-1000}` and `0 < ρ ≤ 2μ`,

    t^{1/646} + √(32π(ρ/μ)/(1 − t^{23/1292})) ≤ 4t^{−21/646}.

The three ingredients are `t^{23/1292} ≤ 1/2` (so `1 − ε_T ≥ 1/2`), the bound `ρ/μ ≤ 2`
(so the square root is at most `√(128π) < 23`) and `4t^{−21/646} ≥ 4·2^{32}`. -/
theorem thresholdArith {t ρ μ : ℝ} (hμ : 0 < μ) (ht₀ : 0 < t)
    (htε : t ≤ (1 / 2) ^ 1000) (hρ0 : 0 < ρ) (hρμ : ρ / μ ≤ 2) :
    t ^ (1 / 646 : ℝ) + Real.sqrt (32 * π * (ρ / μ) / (1 - t ^ ((23 : ℝ) / 1292)))
      ≤ 4 * t ^ (-(21 / 646 : ℝ)) := by
  have heT := rpow_23_le_half ht₀ htε
  have hden : (1 : ℝ) / 2 ≤ 1 - t ^ ((23 : ℝ) / 1292) := by linarith
  have hsqrt : Real.sqrt (32 * π * (ρ / μ) / (1 - t ^ ((23 : ℝ) / 1292))) ≤ 23 := by
    have hy_le : 32 * π * (ρ / μ) / (1 - t ^ ((23 : ℝ) / 1292)) ≤ 23 ^ 2 := by
      have h₁ : 32 * π * (ρ / μ) / (1 - t ^ ((23 : ℝ) / 1292)) ≤ 32 * π * (ρ / μ) / (1 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      have h₂ : 32 * π * (ρ / μ) / (1 / 2) = 64 * π * (ρ / μ) := by ring
      have h₃ : 64 * π * (ρ / μ) ≤ 64 * π * 2 := by nlinarith [Real.pi_pos]
      have h₄ : 64 * π * 2 = 128 * π := by ring
      have h₅ : 128 * π < 23 ^ 2 := by
        have hπ : π < 4 := Real.pi_lt_four
        nlinarith
      linarith
    calc Real.sqrt (32 * π * (ρ / μ) / (1 - t ^ ((23 : ℝ) / 1292)))
        ≤ Real.sqrt (23 ^ 2) := Real.sqrt_le_sqrt hy_le
      _ = 23 := Real.sqrt_sq (by norm_num)
  have h1st : t ^ (1 / 646 : ℝ) ≤ 1 := by
    have ht1 : t ≤ 1 := le_trans htε (pow_le_one₀ (by norm_num) (by norm_num))
    exact Real.rpow_le_one ht₀.le ht1 (by norm_num)
  have hpow := rpow_neg21_ge ht₀ htε
  linarith

/-! ## 3. The row at an abstract family with the view -/

/-- **The threshold row at a `KzDatum` with the (canonical) view.**  All the scalars are pinned
by the view (`RViewFS` conjuncts 2–9) and `FSParamsView`, so with `t = μa³`, `u = √(μ·a v)`:

    (sℓ)⁻¹ = u·t^{1/646},   √(2ρ·16πa/(1−ε_T)) = u·√(32π(ρ/μ)/(1−t^{23/1292})),
    4K_L√(μa) = u·4t^{−21/646},

and `thresholdArith` (with `ρ > 0`, `ρ ≤ 2μ` from the close condition) gives the result. -/
theorem threshold_of_viewFS {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ ρ : ℝ} {D : Work.BoseFixR.KzDatum}
    (hav : 0 < _root_.BoseGases.a v) (hadm : Adm v ((1 / 2) ^ 1000) μ)
    (hview : D.viewFS v h μ) (hclose : CloseCondFS v μ ρ) :
    (D.E.s * D.E.ell)⁻¹
        + Real.sqrt (2 * ρ * (16 * π * _root_.BoseGases.a v) / (1 - D.E.eT))
      ≤ 4 * (D.E.KL * Real.sqrt (D.E.mu * D.E.aScat)) := by
  have hμ : 0 < μ := hadm.1
  have hav' : 0 < _root_.BoseGases.a v := hav
  have hε₀1 : (1 / 2 : ℝ) ^ 1000 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hρ0 : 0 < ρ := rho_pos_of_close v hε₀1 hav hadm hclose
  have hρ2 : ρ ≤ 2 * μ := rho_le_two_of_close v hε₀1 hav hadm hclose
  have hρμ : ρ / μ ≤ 2 := (div_le_iff₀ hμ).mpr hρ2
  obtain ⟨pv⟩ := hview.1
  have hmu_eq : D.E.mu = μ := hview.2.1
  have haSc_eq : D.E.aScat = _root_.BoseGases.a v := hview.2.2.1
  have hpvt_pos : 0 < pv.t := pv.t_pos
  have ht_eq : pv.t = μ * (_root_.BoseGases.a v) ^ 3 := by
    rw [← pv.mu_eq, hmu_eq, haSc_eq]
  have htε : pv.t ≤ (1 / 2) ^ 1000 := by rw [ht_eq]; exact hadm.2.1
  have hWpos : 0 < D.E.mu * D.E.aScat := by
    rw [hmu_eq, haSc_eq]; exact mul_pos hμ hav'
  -- the explicit pinning of the scalars
  have heTv : D.E.eT = pv.t ^ ((23 : ℝ) / 1292) := by
    rw [pv.eT_eq, Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hKLv : D.E.KL = pv.t ^ (-(21 / 646 : ℝ)) := by
    have h6 : (Work.BoseBox.fsXp pv.t 6) ^ 2 = Work.BoseBox.fsXp pv.t 12 := by
      rw [Work.BoseBox.fsXp_pow pv.t_pos.le 6 2]
      congr 1
      norm_num
    have h8 : Work.BoseBox.fsXp pv.t (-(3 / 2)) * Work.BoseBox.fsXp pv.t 12
        = Work.BoseBox.fsXp pv.t (21 / 2) := by
      rw [Work.BoseBox.fsXp_mul pv.t_pos (-(3 / 2)) 12]
      congr 1
      norm_num
    have h9 : (Work.BoseBox.fsXp pv.t (21 / 2))⁻¹ = Work.BoseBox.fsXp pv.t (-(21 / 2)) :=
      Work.BoseBox.fsXp_inv pv.t_pos (21 / 2)
    have h10 : Work.BoseBox.fsXp pv.t (-(21 / 2)) = pv.t ^ (-(21 / 646 : ℝ)) := by
      rw [Work.BoseBox.fsXp]
      congr 1
      norm_num
    rw [pv.KL_eq, Work.BoseB7.KL, pv.Kl_eq, pv.d_eq, Real.rpow_neg_one, h6, h8, h9, h10]
  have hS1 : D.E.s * D.E.ell
      = (Work.BoseBox.fsXp pv.t 1 * Work.BoseBox.fsXp pv.t (-(3 / 2)))
        * (D.E.mu * D.E.aScat) ^ (-(1 / 2 : ℝ)) := by
    rw [pv.s_eq, pv.ell_eq, Work.BoseB7.side, pv.Kl_eq]
    ring
  have hS2 : Work.BoseBox.fsXp pv.t 1 * Work.BoseBox.fsXp pv.t (-(3 / 2))
      = pv.t ^ (-(1 / 646 : ℝ)) := by
    rw [Work.BoseBox.fsXp_mul pv.t_pos 1 (-(3 / 2)), Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hS3 : (D.E.mu * D.E.aScat) ^ (-(1 / 2 : ℝ))
      = (Real.sqrt (D.E.mu * D.E.aScat))⁻¹ := by
    rw [Real.rpow_neg hWpos.le (1 / 2), Real.sqrt_eq_rpow]
  have hSe : D.E.s * D.E.ell
      = pv.t ^ (-(1 / 646 : ℝ)) * (Real.sqrt (D.E.mu * D.E.aScat))⁻¹ := by
    rw [hS1, hS2, hS3]
  have hA : (D.E.s * D.E.ell)⁻¹
      = Real.sqrt (D.E.mu * D.E.aScat) * pv.t ^ (1 / 646 : ℝ) := by
    rw [hSe, mul_inv, inv_inv, ← Real.rpow_neg pv.t_pos.le, neg_neg]
    ring
  have hden_ne : (1 : ℝ) - pv.t ^ ((23 : ℝ) / 1292) ≠ 0 := by
    have h := rpow_23_le_half hpvt_pos htε
    intro hc
    linarith
  have harg : 2 * ρ * (16 * π * _root_.BoseGases.a v) / (1 - D.E.eT)
      = (D.E.mu * D.E.aScat)
        * (32 * π * (ρ / μ) / (1 - pv.t ^ ((23 : ℝ) / 1292))) := by
    rw [heTv, hmu_eq, haSc_eq]
    field_simp
    ring
  have hB : Real.sqrt (2 * ρ * (16 * π * _root_.BoseGases.a v) / (1 - D.E.eT))
      = Real.sqrt (D.E.mu * D.E.aScat)
        * Real.sqrt (32 * π * (ρ / μ) / (1 - pv.t ^ ((23 : ℝ) / 1292))) := by
    rw [harg, Real.sqrt_mul hWpos.le]
  have hC : 4 * (D.E.KL * Real.sqrt (D.E.mu * D.E.aScat))
      = Real.sqrt (D.E.mu * D.E.aScat) * (4 * pv.t ^ (-(21 / 646 : ℝ))) := by
    rw [hKLv]
    ring
  have harith := thresholdArith (t := pv.t) (ρ := ρ) (μ := μ) hμ hpvt_pos htε hρ0 hρμ
  have hmul := mul_le_mul_of_nonneg_left harith (Real.sqrt_nonneg (D.E.mu * D.E.aScat))
  calc (D.E.s * D.E.ell)⁻¹
        + Real.sqrt (2 * ρ * (16 * π * _root_.BoseGases.a v) / (1 - D.E.eT))
      = Real.sqrt (D.E.mu * D.E.aScat) * pv.t ^ (1 / 646 : ℝ)
        + Real.sqrt (D.E.mu * D.E.aScat)
          * Real.sqrt (32 * π * (ρ / μ) / (1 - pv.t ^ ((23 : ℝ) / 1292))) := by rw [hA, hB]
    _ = Real.sqrt (D.E.mu * D.E.aScat)
          * (pv.t ^ (1 / 646 : ℝ)
            + Real.sqrt (32 * π * (ρ / μ) / (1 - pv.t ^ ((23 : ℝ) / 1292)))) := by ring
    _ ≤ Real.sqrt (D.E.mu * D.E.aScat) * (4 * pv.t ^ (-(21 / 646 : ℝ))) := hmul
    _ = 4 * (D.E.KL * Real.sqrt (D.E.mu * D.E.aScat)) := by rw [hKLv]; ring

/-- **FS's threshold row `hc₁` at the honest family.**  There is `ε₀ > 0` such that every
admissible `μ` (`μa³ ≤ ε₀`), every honest box family with the view and every `ρ` in the close
region satisfies `(sℓ)⁻¹ + √(2ρ·16πa/(1−ε_T)) ≤ 4K_L√(μa)`. -/
theorem honestThresholdRow (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ → ∀ ρ : ℝ,
      Work.BoseBogFS.CloseCondFS v μ ρ →
      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.s
          * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell)⁻¹
        + Real.sqrt (2 * ρ * (16 * π * _root_.BoseGases.a v)
            / (1 - (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT))
      ≤ 4 * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL
          * Real.sqrt ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.mu
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.aScat)) := by
  refine ⟨(1 / 2) ^ 1000, pow_pos (by norm_num) 1000, ?_⟩
  intro μ hadm hview ρ hclose
  exact threshold_of_viewFS (D := Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ) hav hadm hview
    hclose

end Work.BoseBogFS
