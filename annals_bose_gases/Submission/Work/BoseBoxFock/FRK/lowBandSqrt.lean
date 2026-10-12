import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.FRK.honestLowBandWSum
import Submission.Work.BoseBoxFock.FRK.lowBandSqrt_exists
import Submission.Work.BoseBoxFock.viewFS_of_gate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.lowBandSqrt` — the √-currency assembly of the cubic low band

The lead-frozen repair (`Submission/Work/BoseBoxFock/LEAD_DESIGN_lowband.md`, review
`REVIEW_lowband.md`) of `FRK.PotCubicLowBandG`.  Everything here is PROVED and axiom-clean; the
single analytic input is the leaf `Work.BoseBoxFock.FRK.lowBandSqrt_exists` (LB1√, the ε-Cauchy–
Schwarz bound of FS `lem:Q3-splitting2` in the √-currency defined in `lowBandSqrtDefs.lean`).

    `FRK.PotCubicLowBandG_holds_sqrt`  (the exact type of the live leaf
      `Work.BoseBoxFock.PotCubicLowBandG_holds`)
        ⟸ `FRK.lowBandSqrt_exists`  (the one remaining analytic leaf)
        + `FRK.lowBandSqrtArith_exists`  (PROVED here: every prescribed `K ≥ 1` is absorbed by the
          diluteness threshold `ε₀ = min 1 (1000K)^{-1292}`)

Never route through `PotCubicLowBandG_of_nplus`: its input `LowBandNPlusLinear` (LB1) is FALSE.
-/

noncomputable section
open MeasureTheory
namespace Work.BoseBoxFock.FRK

local notation "Ω" => EuclideanSpace ℝ (Fin 3)
open Work.BoseB4 Work.BoseDict
/-- **LowBandG from LB1√ + LB2√** (`C = 0`). -/
theorem PotCubicLowBandG_of_sqrt {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R J : ℝ} {Nmin : ℝ → ℕ} {ε₀ K : ℝ}
    (hS : LowBandSqrt v h fc fu J Nmin ε₀ K) (hA : LowBandSqrtArith v h fc fu Nmin ε₀ K) :
    PotCubicLowBandG v h fc fu R J Nmin ε₀ 0 := by
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  have hl := hS HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  have ha := hA HM hNmin μ hAdm
  have hc := cnPlus_nonneg' (Work.BoseBox.sideAt μ (BoseGases.a v))
    (Φ : Submission.BoseGases.X n → ℝ)
  have h0 : Work.BoseFixR.errKafz v R μ 0 = 0 := by simp [Work.BoseFixR.errKafz]
  rw [h0]
  have := mul_le_mul_of_nonneg_right ha hc
  nlinarith [this]

theorem LowBandSqrt_anti {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {J : ℝ} {Nmin : ℝ → ℕ} {ε₀ ε₁ K : ℝ} (hε : ε₁ ≤ ε₀)
    (hS : LowBandSqrt v h fc fu J Nmin ε₀ K) : LowBandSqrt v h fc fu J Nmin ε₁ K := by
  intro HM hNmin μ hAdm
  exact hS HM hNmin μ ⟨hAdm.1, hAdm.2.1.trans hε, hAdm.2.2⟩

theorem LowBandSqrtArith_anti {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {Nmin : ℝ → ℕ} {ε₀ ε₁ K : ℝ} (hε : ε₁ ≤ ε₀)
    (hA : LowBandSqrtArith v h fc fu Nmin ε₀ K) : LowBandSqrtArith v h fc fu Nmin ε₁ K := by
  intro HM hNmin μ hAdm
  exact hA HM hNmin μ ⟨hAdm.1, hAdm.2.1.trans hε, hAdm.2.2⟩

theorem LowBandSqrt_mono_K {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} (hav : 0 < BoseGases.a v)
    {fc fu : Work.BoseBoxFix.LowCut} {J : ℝ} {Nmin : ℝ → ℕ} {ε₀ K K' : ℝ} (hKK : K ≤ K')
    (hS : LowBandSqrt v h fc fu J Nmin ε₀ K) : LowBandSqrt v h fc fu J Nmin ε₀ K' := by
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  have hl := hS HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  refine le_trans hl ?_
  have hℓ := Work.BoseBox.sideAt_pos hAdm.1 hav
  have hc := cnPlus_nonneg' (Work.BoseBox.sideAt μ (BoseGases.a v))
    (Φ : Submission.BoseGases.X n → ℝ)
  apply mul_le_mul_of_nonneg_right _ hc
  apply mul_le_mul_of_nonneg_right hKK
  positivity

/-- **Assembly of the target** `PotCubicLowBandG_holds` from LB1√ and LB2√. -/
theorem PotCubicLowBandG_holds_of_sqrt {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    (hav : 0 < BoseGases.a v) {fc fu : Work.BoseBoxFix.LowCut} {R J : ℝ} {Nmin : ℝ → ℕ}
    (hS : ∃ ε₁ K : ℝ, 0 < ε₁ ∧ LowBandSqrt v h fc fu J Nmin ε₁ K)
    (hA : ∀ K : ℝ, 1 ≤ K → ∃ ε₂ : ℝ, 0 < ε₂ ∧ LowBandSqrtArith v h fc fu Nmin ε₂ K) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ PotCubicLowBandG v h fc fu R J Nmin ε₀ C := by
  obtain ⟨ε₁, K, hε₁, hS⟩ := hS
  obtain ⟨ε₂, hε₂, hA⟩ := hA (max K 1) (le_max_right _ _)
  refine ⟨min ε₁ ε₂, 0, lt_min hε₁ hε₂, le_refl _, ?_⟩
  exact PotCubicLowBandG_of_sqrt
    (LowBandSqrt_anti (min_le_left _ _) (LowBandSqrt_mono_K hav (le_max_left K 1) hS))
    (LowBandSqrtArith_anti (min_le_right _ _) hA)

end Work.BoseBoxFock.FRK

noncomputable section
namespace Work.BoseBoxFock.FRK

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

private lemma lbs_card_const : 27 * (1 + 4 * Real.pi) ^ 3 ≤ 40 * (4 * Real.pi) ^ 3 := by
  have hx : (12:ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  obtain ⟨y, hy0, hy⟩ : ∃ y : ℝ, 0 ≤ y ∧ 4 * Real.pi = 12 + y := ⟨4 * Real.pi - 12, by linarith, by ring⟩
  rw [hy]
  nlinarith [pow_nonneg hy0 2, pow_nonneg hy0 3]

/-- The monomial core of LB2√ (`W = t^{-1/1292}`). -/
private lemma lbs_core {K a W ℓ μ M c : ℝ} (hK : 1 ≤ K) (ha : 0 < a) (hW : 1000 * K ≤ W)
    (hℓ : ℓ = a * W ^ 652) (hμ : μ * (a ^ 3 * W ^ 1292) = 1) (hM : M = W ^ 327)
    (hc0 : 0 ≤ c) (hc : c ≤ 40 * W ^ 309) :
    K * (a * (ℓ ^ 3)⁻¹ * Real.sqrt (2 * μ * ℓ ^ 3 * M * c)) ≤ (3 / 200) * ℓ ^ (-2 : ℤ) := by
  have hWpos : 0 < W := by linarith
  have hμeq : μ = 1 / (a ^ 3 * W ^ 1292) := by
    rw [eq_div_iff (by positivity)]; exact hμ
  have hZ : 2 * μ * ℓ ^ 3 * M * c ≤ (9 * W ^ 650) ^ 2 := by
    have e : 2 * μ * ℓ ^ 3 * M = 2 * W ^ 991 := by
      rw [hℓ, hM, hμeq]; field_simp
    rw [e]
    have h1 : 2 * W ^ 991 * c ≤ 2 * W ^ 991 * (40 * W ^ 309) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    have h2 : (0:ℝ) ≤ W ^ 1300 := by positivity
    calc 2 * W ^ 991 * c ≤ 2 * W ^ 991 * (40 * W ^ 309) := h1
      _ = 80 * W ^ 1300 := by ring
      _ ≤ 81 * W ^ 1300 := by linarith
      _ = (9 * W ^ 650) ^ 2 := by ring
  have hsq : Real.sqrt (2 * μ * ℓ ^ 3 * M * c) ≤ 9 * W ^ 650 := by
    calc Real.sqrt (2 * μ * ℓ ^ 3 * M * c) ≤ Real.sqrt ((9 * W ^ 650) ^ 2) := Real.sqrt_le_sqrt hZ
      _ = 9 * W ^ 650 := Real.sqrt_sq (by positivity)
  have hℓpos : 0 < ℓ := by rw [hℓ]; positivity
  have hK0 : 0 < K := by linarith
  calc K * (a * (ℓ ^ 3)⁻¹ * Real.sqrt (2 * μ * ℓ ^ 3 * M * c))
      ≤ K * (a * (ℓ ^ 3)⁻¹ * (9 * W ^ 650)) := by gcongr
    _ = 9 * K / (a ^ 2 * W ^ 1306) := by rw [hℓ]; field_simp
    _ ≤ 3 / (200 * (a ^ 2 * W ^ 1304)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hW2 : 600 * K ≤ W ^ 2 := by nlinarith
      have hP : (0:ℝ) ≤ 3 * (a ^ 2 * W ^ 1304) := by positivity
      calc 9 * K * (200 * (a ^ 2 * W ^ 1304)) = 3 * (a ^ 2 * W ^ 1304) * (600 * K) := by ring
        _ ≤ 3 * (a ^ 2 * W ^ 1304) * W ^ 2 := mul_le_mul_of_nonneg_left hW2 hP
        _ = 3 * (a ^ 2 * W ^ 1306) := by ring
    _ = (3 / 200) * ℓ ^ (-2 : ℤ) := by
      rw [hℓ, zpow_neg, zpow_ofNat]; field_simp

/-- **LB2√ (PROVED)**: every prescribed `K ≥ 1` is absorbed by the diluteness threshold;
the margin is `t^{2/1292} = √X`. -/
theorem lowBandSqrtArith_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (Nmin : ℝ → ℕ) :
    ∀ K : ℝ, 1 ≤ K → ∃ ε₀ : ℝ, 0 < ε₀ ∧ LowBandSqrtArith v h fc fu Nmin ε₀ K := by
  intro K hK
  have hK0 : 0 < K := by linarith
  set D : ℝ := (1 / (1000 * K)) ^ (1292 : ℝ) with hD
  have hDpos : 0 < D := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min 1 D, lt_min one_pos hDpos, ?_⟩
  intro HM hNmin μ hAdm
  obtain ⟨hμ, htε, hOK⟩ := hAdm
  set t : ℝ := μ * BoseGases.a v ^ 3 with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := htε.trans (min_le_left _ _)
  have htD : t ≤ D := htε.trans (min_le_right _ _)
  set W : ℝ := t ^ (-(1 / 1292 : ℝ)) with hWdef
  have hWpos : 0 < W := Real.rpow_pos_of_pos ht0 _
  have hWpow : ∀ c : ℕ, W ^ c = t ^ (-((c : ℝ) / 1292)) := by
    intro c
    rw [hWdef, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    congr 1; ring
  have hW : 1000 * K ≤ W := by
    have h1 : t ^ (1 / 1292 : ℝ) ≤ (1000 * K)⁻¹ := by
      calc t ^ (1 / 1292 : ℝ) ≤ D ^ (1 / 1292 : ℝ) := Real.rpow_le_rpow ht0.le htD (by norm_num)
        _ = (1000 * K)⁻¹ := by
          rw [hD, ← Real.rpow_mul (by positivity)]; norm_num
    have h3 : 0 < t ^ (1 / 1292 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have h2 : W = (t ^ (1 / 1292 : ℝ))⁻¹ := by rw [hWdef, Real.rpow_neg ht0.le]
    rw [h2]
    exact (le_inv_comm₀ (by positivity) h3).2 h1
  have hW1 : 1 ≤ W := by linarith
  -- closed forms
  have hℓ : Work.BoseBox.sideAt μ (BoseGases.a v) = BoseGases.a v * W ^ 652 := by
    rw [Work.BoseBox.sideAt_eq_rpow hav hμ, ← htdef, hWpow 652]
    norm_num
  have hμW : μ * (BoseGases.a v ^ 3 * W ^ 1292) = 1 := by
    rw [hWpow 1292, show (-(((1292 : ℕ) : ℝ) / 1292)) = -1 by norm_num, Real.rpow_neg_one,
      ← mul_assoc, ← htdef]
    exact mul_inv_cancel₀ ht0.ne'
  have hM : Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
      = W ^ 327 := by
    simp only [Work.BoseBox.bigM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams,
      Work.BoseBox.fsXp]
    rw [← htdef, ← Real.rpow_add ht0, hWpow 327]
    norm_num
  -- the lattice count of the low band
  obtain ⟨hv'⟩ := nonempty_fsParamsView_HonestBoxFam (v := v) (h := h) (fc := fc) (fu := fu)
    (HM := HM) (μ := μ) hμ hav ht1
  have ht_eq : hv'.t = t := by rw [htdef, ← hv'.mu_eq]; rfl
  have hKH : (HonestBoxFam v h fc fu HM μ).E.KH = W ^ 549 := by
    rw [Work.BoseB7.KH_val _ hv', ht_eq, hWpow 549]
    simp only [Work.BoseBox.fsXp]
    norm_num
  have hEell : (HonestBoxFam v h fc fu HM μ).E.ell = Work.BoseBox.sideAt μ (BoseGases.a v) := rfl
  have hfrac : (HonestBoxFam v h fc fu HM μ).E.ell
      / (4 * Real.pi * (HonestBoxFam v h fc fu HM μ).E.KH * BoseGases.a v)
      = W ^ 103 / (4 * Real.pi) := by
    rw [hEell, hℓ, hKH]
    field_simp
  have hell : Work.BoseBoxFock.ellH v μ = (HonestBoxFam v h fc fu HM μ).E.ell := by
    rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
    rfl
  have hkm : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).F.kmom k
        = kmomLab (HonestBoxFam v h fc fu HM μ).E.ell (HM μ).N k :=
    fun k => by rw [← hell]; rfl
  have hℓE : 0 < (HonestBoxFam v h fc fu HM μ).E.ell := by
    rw [← hell]; exact Work.BoseBoxFock.ellH_pos v μ
  have hy : 1 / (4 * Real.pi) ≤ (HonestBoxFam v h fc fu HM μ).E.ell
      / (4 * Real.pi * (HonestBoxFam v h fc fu HM μ).E.KH * BoseGases.a v) := by
    rw [hfrac]
    have : (1:ℝ) ≤ W ^ 103 := one_le_pow₀ hW1
    exact div_le_div_of_nonneg_right this (by positivity)
  have hcard := lowBand_card_le (HM μ).N (HonestBoxFam v h fc fu HM μ).F
    (HonestBoxFam v h fc fu HM μ).E hℓE hkm hy
  have hcard' : ((((Work.BoseB7.excited (Lab (HM μ).N))
      \ (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E).card : ℕ) : ℝ)
      ≤ 40 * W ^ 309 := by
    refine hcard.trans ?_
    have hfrac' : (HonestBoxFam v h fc fu HM μ).E.ell
        / (4 * Real.pi * (HonestBoxFam v h fc fu HM μ).E.KH
          * (HonestBoxFam v h fc fu HM μ).E.aScat) = W ^ 103 / (4 * Real.pi) := hfrac
    rw [hfrac', div_pow, ← pow_mul]
    have h4 : (0:ℝ) < (4 * Real.pi) ^ 3 := by positivity
    rw [show 27 * (1 + 4 * Real.pi) ^ 3 * (W ^ (103 * 3) / (4 * Real.pi) ^ 3)
        = (27 * (1 + 4 * Real.pi) ^ 3 / (4 * Real.pi) ^ 3) * W ^ 309 by ring]
    have hc : 27 * (1 + 4 * Real.pi) ^ 3 / (4 * Real.pi) ^ 3 ≤ 40 := by
      rw [div_le_iff₀ h4]; exact lbs_card_const
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hb : (Work.BoseBox.paramsAt μ (BoseGases.a v)).b = 1 / 16 := rfl
  have hγ : (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 4
      - (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100 = 3 / 200 := by rw [hb]; norm_num
  rw [hγ]
  exact lbs_core hK hav hW hℓ hμW hM (Nat.cast_nonneg _) hcard'

end Work.BoseBoxFock.FRK

namespace Work.BoseBoxFock.FRK
/-- The target `PotCubicLowBandG_holds` (same binders), from LB1√ alone. -/
theorem PotCubicLowBandG_holds_sqrt (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (Nmin : ℝ → ℕ) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.FRK.PotCubicLowBandG v h fc fu R J Nmin ε₀ C :=
  PotCubicLowBandG_holds_of_sqrt hav
    (lowBandSqrt_exists v h hv hv1 hvrad hR hv_supp hav fc fu J hB3 Nmin)
    (lowBandSqrtArith_exists v h hav fc fu Nmin)


end Work.BoseBoxFock.FRK

#print axioms Work.BoseBoxFock.FRK.PotCubicLowBandG_holds_of_sqrt
#print axioms Work.BoseBoxFock.FRK.lowBandSqrtArith_exists
#print axioms Work.BoseBoxFock.FRK.PotCubicLowBandG_holds_sqrt

