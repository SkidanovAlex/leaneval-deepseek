import ChallengeDeps
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseFixR.All.FarKernelRowsB
import Submission.Work.BoseFixR.All.FarResidAux
import Submission.Work.BoseFixR.All.epsFar_le_inv_eight
import Submission.Work.BoseFixR.All.farEnvSideB
import Submission.Work.BoseFixR.FarResidBaux.farEnvSideB
import Submission.Work.BoseFixR.FarThreeQSlots
import Submission.Work.BoseFixR.absBpSumSmulLe
import Submission.Work.BoseFixR.farLatRow
import Submission.Work.BoseFixR.farLinArith
import Submission.Work.BoseFixR.farRadSlot
import Submission.Work.BoseFixR.qwPairLinEq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/All/farZPGen.lean`

The far leg's zero-point slot with the lattice-row constant kept **free**, in the `All`
vocabulary (`viewFSAll`, `FarCondFS`, `All.farEnv`, `All.epsFar`), and the far-leg assembly
`farZPGen` that consumes it.

The target `Work.BoseFixR.All.farZPGen` is `FarZPSumFixW` (`Work.BoseFixR`, constant `6`) and
`farZPWin` (constant `C₀ = (1+64√ε)(1+100√ε)`) with the row hypothesis relaxed to an arbitrary
constant:

  `hLat : Σ_{k∈excited} Ŵ₁(k)²/(2‖kmom k‖²) ≤ C·ℓ³·Mcont`,  `Mcont := (2π)^{-3}∫Ŵ₁(q)²/(2q²)dq`,

and conclusion `−(Cρ²ℓ³Mcont + ErrRes/2)‖f‖² ≤ ⟨f, KzBogFS F (farEnv E v μ ρ) ρ f⟩`.

Route (verbatim `farRadSlot_gen`, with the vocabulary swapped and the constant kept as `C`):
split `KzBogFS` into the quadratic and linear halves; the quadratic half costs `Σ_k½𝒵_k`, the
linear half costs `ErrRes/4`; and `Σ_k½𝒵_k ≤ Cρ²ℓ³Mcont + ErrRes/4` is proved by splitting the
mode sum at the fixed scale `10·(2sℓ)^{-1}` — the low modes are charged crudely to `ErrRes/4`
(the count is `CardKmomLabLt`), and on the tail `τ̃` is comparable to `‖kmom k‖²` with the
*exact* constant `25/(8A₀)` (`farRadLatCmp`), whose product with the `ε`-factor `1/4+32√ε` is
`≤ 1` (`farRadABound`), so the tail is priced exactly by the row at the constant `C`.
-/

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Small helpers in the `All` vocabulary -/

/-- The momentum of the label `0` vanishes (`kmom (-k) = -kmom k` at `k = 0`). -/
private lemma kmom_zeroGen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) : F.kmom 0 = 0 := by
  have h := F.kmom_neg 0
  rw [neg_zero] at h
  have h2 : (2 : ℝ) • F.kmom 0 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Positivity of `ε = √(𝓜/((ρ+μ)ℓ³))` at `0 ≤ ρ` (the version in `All.FarEnvPos` needs
`0 < ρ`). -/
lemma epsFar_pos_of_nonnegGen {v : E3 → ℝ} {μ ρ : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (hρ : 0 ≤ ρ) : 0 < epsFar v μ ρ := by
  have hM : 0 < bigMV v μ := Work.BoseBox.bigM_pos_of_params hμ hav
  have hℓ : 0 < ell v μ := by
    rw [ell]
    exact Work.BoseBox.sideAt_pos hμ hav
  rw [epsFar]
  exact Real.sqrt_pos_of_pos (div_pos hM (mul_pos (by linarith) (pow_pos hℓ 3)))

/-- `√ε ≤ 1/100` and `ε^{−1/2} ≥ 1` at the admissible box data (`All`-twin of
`farRadCountAux.epsFarSqrtBound`). -/
lemma epsFarSqrtBoundGen {v : E3 → ℝ} {ε₀ μ ρ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hav : 0 < a v) (hρ : 0 ≤ ρ) (hfar : FarCondFS v μ ρ) :
    Real.sqrt (epsFar v μ ρ) ≤ 1 / 100
      ∧ (1 : ℝ) ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
  have hμ : 0 < μ := hAdm.1
  have hεle : epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
    FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρ hfar
  have hpos : 0 < epsFar v μ ρ := epsFar_pos_of_nonnegGen hμ hav hρ
  refine ⟨?_, ?_⟩
  · have h2 : epsFar v μ ρ ≤ (1 / 100 : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) / 10 ^ 8 ≤ (1 / 100 : ℝ) ^ 2 := by norm_num
      linarith
    calc Real.sqrt (epsFar v μ ρ)
        ≤ Real.sqrt ((1 / 100 : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
      _ = 1 / 100 := Real.sqrt_sq (by norm_num)
  · have h1 : Real.sqrt (epsFar v μ ρ) ≤ 1 := by
      refine Real.sqrt_le_one.mpr ?_
      have h2 : (1 : ℝ) / 10 ^ 8 ≤ 1 := by norm_num
      linarith
    have h3 : (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (epsFar v μ ρ))⁻¹ := by
      rw [Real.rpow_neg hpos.le (1 / 2), ← Real.sqrt_eq_rpow]
    rw [h3]
    exact (one_le_inv₀ (Real.sqrt_pos_of_pos hpos)).mpr h1

/-- **The two scalar slacks of the far leg**: at the admissible box data
`(1 − ε)(1 − ε_T) ≥ 9/10` (`All`-twin of `farRadABound`). -/
lemma farRadABoundGen {v : E3 → ℝ} {ε₀ μ ρ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hav : 0 < a v) (hρ : 0 ≤ ρ) (hfar : FarCondFS v μ ρ) :
    9 / 10 ≤ (1 - epsFar v μ ρ) * (1 - (paramsAt μ (a v)).eT) := by
  have hE : epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
    FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρ hfar
  have hT : (paramsAt μ (a v)).eT ≤ 1 / 100 :=
    paramsAt_eT_le_inv_hundred hAdm.1 hav (hAdm.2.1.trans hε₀)
  have hE1 : epsFar v μ ρ ≤ 1 := by linarith
  calc (9 : ℝ) / 10 ≤ (1 - 1 / 10 ^ 8) * (1 - 1 / 100) := by norm_num
    _ ≤ (1 - epsFar v μ ρ) * (1 - (paramsAt μ (a v)).eT) :=
        mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)

/-- **The low-mode count budget** (`All`-twin of `farRadCountB`). -/
lemma farRadCountBGen {v : E3 → ℝ} {ε₀ μ ρ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hav : 0 < a v) (hρ : 0 < ρ) (hfar : FarCondFS v μ ρ) :
    ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
        * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
        * (2 * (16 * Real.pi * BoseGases.a v) ^ 2
            / (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v))
      ≤ ErrRes v μ ρ / 4 := by
  have hμ : 0 < μ := hAdm.1
  have hAr : 0 < BoseGases.a v := hav
  have hMpos : 0 < bigMV v μ := Work.BoseBox.bigM_pos_of_params hμ hav
  have ht0 : 0 < μ * BoseGases.a v ^ 3 := by positivity
  have htle : μ * BoseGases.a v ^ 3 ≤ (10 : ℝ) ^ (-(4000 : ℤ)) := hAdm.2.1.trans hε₀
  have ht1 : μ * BoseGases.a v ^ 3 ≤ 1 := by
    have h1 : (10 : ℝ) ^ (-(4000 : ℤ)) ≤ 1 := by
      rw [show (10 : ℝ) ^ (-(4000 : ℤ)) = ((10 : ℝ) ^ 4000)⁻¹ by norm_num]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10))
    linarith
  have hs : (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
      = Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) 1 := rfl
  have hs_pos : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).s := by
    rw [hs]; exact Work.BoseBox.fsXp_pos ht0
  have hC0 : (10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1
      ≤ 1000 * bigMV v μ := by
    have hM : bigMV v μ = Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-1)
        * (μ * BoseGases.a v ^ 3) ^ (-(1 / 4 : ℝ)) := by
      simp only [bigMV, Work.BoseBox.bigM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    rw [hs, hM]
    exact farRadCountAux.c0Bound ht0 ht1
  obtain ⟨hsqrtE, hEinvg1⟩ := epsFarSqrtBoundGen hAdm hε₀ hav (le_of_lt hρ) hfar
  have hEinvgpos : 0 < (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := lt_of_lt_of_le zero_lt_one hEinvg1
  have hfac : 1 / 4 + 32 * Real.sqrt (epsFar v μ ρ) ≤ 1 := by nlinarith [hsqrtE]
  have hErr : (10 : ℝ) ^ 300 * ((ρ + μ) * BoseGases.a v * bigMV v μ) ≤ ErrRes v μ ρ := by
    rw [ErrRes]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine le_add_of_nonneg_right ?_
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) (3 / 2)) (le_of_lt hAr))
      (Real.sqrt_nonneg _)
  have hErrpos : 0 < ErrRes v μ ρ := lt_of_lt_of_le (by positivity) hErr
  have hcore : ρ * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
        * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
        * (2 * (16 * Real.pi * BoseGases.a v) ^ 2)
      ≤ ErrRes v μ ρ / 4 * BoseGases.a v := by
    have hpre1 : ρ * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ)) ≤ ρ * 1 :=
      mul_le_mul_of_nonneg_left hfac (le_of_lt hρ)
    have hC0nn : 0 ≤ (10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3
        + 1 := by
      have hx : (0 : ℝ) ≤ 10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1 := by
        positivity
      linarith [pow_nonneg hx 3]
    have hpre : ρ * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
          * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
        ≤ ρ * 1 * (1000 * bigMV v μ) := by
      have h1 := mul_le_mul_of_nonneg_right hpre1 hC0nn
      have h2 : ρ * 1 * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3
            + 1) ≤ ρ * 1 * (1000 * bigMV v μ) :=
        mul_le_mul_of_nonneg_left hC0 (by positivity)
      linarith [h1, h2]
    have hFnn : 0 ≤ 2 * (16 * Real.pi * BoseGases.a v) ^ 2 := by positivity
    have hstep2 := mul_le_mul_of_nonneg_right hpre hFnn
    have hnum : (512000 : ℝ) * Real.pi ^ 2 ≤ (10 : ℝ) ^ 300 / 4 := by
      have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
      have h3 : (512000 : ℝ) * 16 ≤ (10 : ℝ) ^ 10 / 4 := by norm_num
      have h4 : (512000 : ℝ) * Real.pi ^ 2 ≤ (10 : ℝ) ^ 10 / 4 := by nlinarith [hpi2, h3]
      have h5 : (10 : ℝ) ^ 10 / 4 ≤ (10 : ℝ) ^ 300 / 4 := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
        exact pow_le_pow_right₀ (by norm_num) (by norm_num)
      exact le_trans h4 h5
    have hstep3 : ρ * 1 * (1000 * bigMV v μ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2)
        ≤ (10 : ℝ) ^ 300 / 4 * (ρ * BoseGases.a v ^ 2 * bigMV v μ) := by
      rw [show ρ * 1 * (1000 * bigMV v μ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2)
          = 512000 * Real.pi ^ 2 * (ρ * BoseGases.a v ^ 2 * bigMV v μ) by ring]
      exact mul_le_mul_of_nonneg_right hnum (by positivity)
    have hstep4 : (10 : ℝ) ^ 300 / 4 * (ρ * BoseGases.a v ^ 2 * bigMV v μ)
        ≤ ErrRes v μ ρ / 4 * BoseGases.a v := by
      have h2 : (10 : ℝ) ^ 300 / 4 * ((ρ + μ) * BoseGases.a v * bigMV v μ)
          ≤ ErrRes v μ ρ / 4 := by linarith [hErr]
      have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt hAr)
      have h4 : (10 : ℝ) ^ 300 / 4 * (ρ * BoseGases.a v ^ 2 * bigMV v μ)
          ≤ (10 : ℝ) ^ 300 / 4 * ((ρ + μ) * BoseGases.a v ^ 2 * bigMV v μ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hμ, hρ, hAr, hMpos]
      have h5 : (10 : ℝ) ^ 300 / 4 * ((ρ + μ) * BoseGases.a v * bigMV v μ)
            * BoseGases.a v
          = (10 : ℝ) ^ 300 / 4 * ((ρ + μ) * BoseGases.a v ^ 2 * bigMV v μ) := by ring
      linarith [h3, h4, h5]
    linarith [hstep2, hstep3, hstep4]
  have hDpos : 0 < ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by positivity
  rw [mul_div_assoc', div_le_iff₀ hDpos]
  have hE4nn : 0 ≤ ErrRes v μ ρ / 4 := by linarith [hErrpos]
  calc ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
        * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
        * (2 * (16 * Real.pi * BoseGases.a v) ^ 2)
      = ρ * (ρ * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
        * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
        * (2 * (16 * Real.pi * BoseGases.a v) ^ 2)) := by ring
    _ ≤ ρ * (ErrRes v μ ρ / 4 * BoseGases.a v) :=
        mul_le_mul_of_nonneg_left hcore (le_of_lt hρ)
    _ ≤ ρ * (ErrRes v μ ρ / 4 * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hρ)
        have h1 : ErrRes v μ ρ / 4 * 1 ≤ ErrRes v μ ρ / 4 * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hEinvg1 hE4nn
        simpa using mul_le_mul_of_nonneg_right h1 (le_of_lt hAr)
    _ = ErrRes v μ ρ / 4 * (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) := by ring

/-! ## 2. The zero-point slot at a free constant -/

/-- **The zero-point slot, constant kept free** (`All`-twin of `farRadSlot_gen`).

`Σ_k ½𝒵_k ≤ C·ρ²ℓ³·Mcont + ErrRes/4` at the `ε`-split environment `farEnv E v μ ρ`, given
the lattice row `Σ_{k≠0} Ŵ₁(k)²/(2‖kmom k‖²) ≤ C·ℓ³·Mcont`. -/
theorem zeroPointSum_leGen {v : E3 → ℝ} (h : ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < a v) (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ))) (hAdm : Adm v ε₀ μ)
    (hview : (HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hW1 : ∀ k : Lab (HM μ).N,
        |(HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * a v)
    (hchi : ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 ≤ 100)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hfar : FarCondFS v μ ρ)
    (C : ℝ) (hC : 0 ≤ C)
    (hLat : (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
          / (2 * ‖(HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2))
        ≤ C * (ell v μ) ^ 3 * farMass v h μ) :
    zeroPointSum (HonestBoxFam v h fc fu HM μ).F
        (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ
      ≤ C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ + ErrRes v μ ρ / 4 := by
  classical
  have hμ : 0 < μ := hAdm.1
  have hℓpos : 0 < ell v μ := by
    rw [ell]; exact Work.BoseBox.sideAt_pos hμ hav
  have hspos : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).s := by
    have := Work.BoseBox.fsXp_pos (t := μ * BoseGases.a v ^ 3) (c := 1) (by positivity)
    simpa [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using this
  rcases eq_or_lt_of_le hρ with hρ0 | hρpos
  · -- ## the degenerate case `ρ = 0`
    have hρ0' : ρ = 0 := hρ0.symm
    subst hρ0'
    have hzero : zeroPointSum (HonestBoxFam v h fc fu HM μ).F
        (farEnv (HonestBoxFam v h fc fu HM μ).E v μ 0) 0 = 0 := by
      rw [zeroPointSum]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      have hεle : epsFar v μ 0 ≤ 1 :=
        le_trans (FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav le_rfl hfar) (by norm_num)
      have hτ : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.tau k :=
        farEnvPos_tau_nonneg _ hview k
      have hA : (KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ 0) 0).A k
          = (1 - epsFar v μ 0) * (HonestBoxFam v h fc fu HM μ).E.tau k := by
        simp [KzEnvAt, farEnv]
      have hB : (KzEnvAt (farEnv (HonestBoxFam v h fc fu HM μ).E v μ 0) 0).B k = 0 := by
        simp [KzEnvAt, farEnv]
      rw [hA, hB]
      have hnn : 0 ≤ (1 - epsFar v μ 0) * (HonestBoxFam v h fc fu HM μ).E.tau k :=
        mul_nonneg (by linarith) hτ
      have hzp : Work.BoseB6.bogZeroPoint
          ((1 - epsFar v μ 0) * (HonestBoxFam v h fc fu HM μ).E.tau k) 0 = 0 := by
        simp only [Work.BoseB6.bogZeroPoint]
        rw [show ((1 - epsFar v μ 0) * (HonestBoxFam v h fc fu HM μ).E.tau k) ^ 2 - 0 ^ 2
            = ((1 - epsFar v μ 0) * (HonestBoxFam v h fc fu HM μ).E.tau k) ^ 2 from by ring]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn, sub_self]
      rw [hzp, mul_zero]
    rw [hzero]
    have hzeroC : C * (0 : ℝ) ^ 2 * (ell v μ) ^ 3 * farMass v h μ = 0 := by ring
    rw [hzeroC, zero_add]
    have hlerr : 0 ≤ ErrRes v μ 0 / 4 :=
      div_nonneg (ErrRes_nonneg hμ hav le_rfl hℓpos.le) (by norm_num)
    simpa using hlerr
  · -- ## the main case `0 < ρ`
    have hεle : epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
      FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρpos.le hfar
    have hεpos : 0 < epsFar v μ ρ := farEnvPos_eps_pos hμ hav hρpos
    have hsqε : Real.sqrt (epsFar v μ ρ) ≤ 1 / 10 ^ 4 := by
      have h1 : Real.sqrt (epsFar v μ ρ) ≤ Real.sqrt (1 / 10 ^ 8 : ℝ) :=
        Real.sqrt_le_sqrt hεle
      have h2 : Real.sqrt (1 / 10 ^ 8 : ℝ) = 1 / 10 ^ 4 := by
        rw [show (1 / 10 ^ 8 : ℝ) = (1 / 10 ^ 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    have hεbig : (10 : ℝ) ^ 4 ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) :=
      farEnvPos_rpow_ge hεpos hεle
    have hτnonneg : ∀ k : Lab (HM μ).N,
        0 ≤ (HonestBoxFam v h fc fu HM μ).E.tau k :=
      fun k => farEnvPos_tau_nonneg _ hview k
    have heTb0 : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.eT
        ∧ (HonestBoxFam v h fc fu HM μ).E.eT ≤ 1 :=
      farEnvPos_eT_bounds _ hview
    have hτnn : ∀ k : Lab (HM μ).N,
        0 ≤ (1 - epsFar v μ ρ) * (HonestBoxFam v h fc fu HM μ).E.tau k :=
      fun k => mul_nonneg (by linarith) (hτnonneg k)
    have hstep1 := sum_half_bogZeroPoint_le (HonestBoxFam v h fc fu HM μ).E
      v μ ρ hεpos.le hεle hεpos hρpos hav hτnn hW1
    unfold KzDatum.viewFSAll RViewFSAll at hview
    obtain ⟨-, -, -, -, -, -, -, -, heTpin, -, -, htaupin, -⟩ := hview
    -- ## abbreviations
    set E := (HonestBoxFam v h fc fu HM μ).E with hE
    set F := (HonestBoxFam v h fc fu HM μ).F with hF
    set c1 := (2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s * ell v μ)⁻¹ with hc1
    set A0 := (1 - epsFar v μ ρ) * (1 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT) with hA0
    set B0 := ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v with hB0
    set L := ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        E.W1 k ^ 2 / (2 * ‖F.kmom k‖ ^ 2) with hLdef
    set S1 := (Finset.univ : Finset (Lab (HM μ).N)).filter
        (fun k => ‖F.kmom k‖ < 10 * c1) with hS1
    set S2 := (Finset.univ : Finset (Lab (HM μ).N)).filter
        (fun k => ¬ (‖F.kmom k‖ < 10 * c1)) with hS2
    have heTb : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
        ∧ (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT ≤ 1 := by
      rw [← heTpin]; exact heTb0
    have htau_pt : ∀ k : Lab (HM μ).N,
        E.tau k = tauSm (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).d (ell v μ)
            (F.kmom k) := fun k => congrFun htaupin k
    have hc1pos : 0 < c1 := by rw [hc1]; positivity
    have hAB : (9 : ℝ) / 10 ≤ A0 := by
      have hh := farRadABoundGen (v := v) hAdm hε₀ hav hρpos.le hfar
      rwa [← hA0] at hh
    have hA0pos : 0 < A0 := by linarith
    have hB0pos : 0 < B0 := by
      rw [hB0]; exact mul_pos (mul_pos hρpos (Real.rpow_pos_of_pos hεpos _)) hav
    have hLnn : 0 ≤ L := by rw [hLdef]; positivity
    have hCℓM : 0 ≤ C * (ell v μ) ^ 3 * farMass v h μ := by
      linarith [hLnn, hLat]
    -- ## (0) the small `Ŵ₁`-tail vs `B0`
    have h16 : 16 * Real.pi * BoseGases.a v
        ≤ (1 / 100) * ((epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) := by
      have h1600 : 1600 * Real.pi ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) :=
        le_trans (by nlinarith [Real.pi_lt_four]) hεbig
      have h := mul_le_mul_of_nonneg_right h1600 hav.le
      nlinarith [h]
    have hup' : ρ * (16 * Real.pi * BoseGases.a v) ≤ (1 / 100) * B0 := by
      rw [hB0]
      nlinarith [h16, hρpos, mul_le_mul_of_nonneg_left h16 hρpos.le]
    have hup : ∀ k : Lab (HM μ).N, ρ * E.W1 k ≤ (1 / 100) * B0 := by
      intro k
      have hle := (abs_le.mp (hW1 k)).2
      nlinarith [hle, hρpos, hup']
    -- ## (1) the diagonal (`𝒜₁`) lower bound
    have hτge : ∀ k : Lab (HM μ).N,
        (1 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT)
            * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2 ≤ E.tau k := by
      intro k
      rw [htau_pt k, hc1]
      exact farRadTauSm heTb.1 heTb.2 hspos hℓpos (F.kmom k)
    have hA1lb : ∀ k : Lab (HM μ).N,
        A0 * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2 + (98 / 100) * B0
          ≤ (1 - epsFar v μ ρ) * E.tau k + B0 := by
      intro k
      have hA1eq : (KzEnvAt (farEnv E v μ ρ) ρ).A k
          = (1 - epsFar v μ ρ) * E.tau k + B0 + ρ * E.W1 k := rfl
      have h1 : A0 * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2
          ≤ (1 - epsFar v μ ρ) * E.tau k := by
        have h0 := mul_le_mul_of_nonneg_left (hτge k)
          (by linarith : (0:ℝ) ≤ 1 - epsFar v μ ρ)
        calc A0 * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2
            = (1 - epsFar v μ ρ)
                * ((1 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT)
                    * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2) := by rw [hA0]; ring
          _ ≤ (1 - epsFar v μ ρ) * E.tau k := h0
      have h2 : -(1 / 100) * B0 ≤ ρ * E.W1 k := by
        have h3 : ρ * (-(16 * Real.pi * BoseGases.a v)) ≤ ρ * E.W1 k :=
          mul_le_mul_of_nonneg_left (abs_le.mp (hW1 k)).1 hρpos.le
        linarith [h3, hup']
      have hfull : A0 * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2 + (99 / 100) * B0
          ≤ (KzEnvAt (farEnv E v μ ρ) ρ).A k := by
        rw [hA1eq]
        linarith [h1, h2]
      rw [hA1eq] at hfull
      linarith [hfull, hup k]
    -- ## (2) the crude per-mode bound
    have hcrude : ∀ k : Lab (HM μ).N,
        E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0)
          ≤ 2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0 := by
      intro k
      have hden : (98 / 100) * B0 ≤ (1 - epsFar v μ ρ) * E.tau k + B0 := by
        have h0 : 0 ≤ A0 * (max 0 (‖F.kmom k‖ - 2 * c1)) ^ 2 :=
          mul_nonneg hA0pos.le (sq_nonneg _)
        linarith [hA1lb k, h0]
      have hdenpos : 0 < (98 / 100) * B0 := by linarith
      have hw : E.W1 k ^ 2 ≤ (16 * Real.pi * BoseGases.a v) ^ 2 := by
        have h16' := hW1 k
        have h16nn : (0:ℝ) ≤ 16 * Real.pi * BoseGases.a v := by positivity
        have := abs_le.mp h16'
        nlinarith [this.1, this.2, h16nn]
      have hcr1 : E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0)
          ≤ E.W1 k ^ 2 / ((98 / 100) * B0) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hdenpos hden
      have hcr2 : E.W1 k ^ 2 / ((98 / 100) * B0) ≤ 2 * E.W1 k ^ 2 / B0 := by
        have hnum : E.W1 k ^ 2 / ((98 / 100) * B0) = (100 / 98) * (E.W1 k ^ 2 / B0) := by
          field_simp
        rw [hnum]
        have hbase : 0 ≤ E.W1 k ^ 2 / B0 := by positivity
        have h100 : (100 / 98 : ℝ) ≤ 2 := by norm_num
        calc (100 / 98) * (E.W1 k ^ 2 / B0) ≤ 2 * (E.W1 k ^ 2 / B0) :=
              mul_le_mul_of_nonneg_right h100 hbase
          _ = 2 * E.W1 k ^ 2 / B0 := by rw [mul_div_assoc]
      calc E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0)
          ≤ E.W1 k ^ 2 / ((98 / 100) * B0) := hcr1
        _ ≤ 2 * E.W1 k ^ 2 / B0 := hcr2
        _ ≤ 2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0 :=
            div_le_div_of_nonneg_right (by linarith [hw]) hB0pos.le
    -- ## (3) the count of the low region
    have hcount : (S1.card : ℝ)
        ≤ (10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1 := by
      have h0 := CardKmomLabLt (ℓ := ellH v μ) (κ := 10 * c1)
        (ellH_pos v μ) (by positivity) (HM μ).N
      have hellH : ellH v μ = ell v μ := by
        rw [ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav), ell]
      have hFkm : F.kmom = kmomLab (ellH v μ) (HM μ).N := by
        rw [hF]; rfl
      have hS1eq : S1 = (Finset.univ : Finset (Lab (HM μ).N)).filter
          (fun k => ‖kmomLab (ellH v μ) (HM μ).N k‖ < 10 * c1) := by
        simp only [hS1, hFkm]
        rfl
      rw [hS1eq, hellH]
      rw [hellH] at h0
      refine le_trans h0 ?_
      rw [hc1]
      have hsne : (Work.BoseBox.paramsAt μ (BoseGases.a v)).s ≠ 0 := ne_of_gt hspos
      have hlne : ell v μ ≠ 0 := ne_of_gt hℓpos
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hsimp : 2 * ell v μ
          * (10 * (2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s * ell v μ)⁻¹)
          / Real.pi
          = 10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) := by
        field_simp
      rw [hsimp]
      exact le_add_of_nonneg_right (by norm_num)
    -- ## (4) the tail bound
    have hS2sub : S2 ⊆ Work.BoseB7.excited (Lab (HM μ).N) := by
      intro k hk
      have hk2 : ¬ (‖F.kmom k‖ < 10 * c1) := by
        rw [hS2] at hk
        exact (Finset.mem_filter.mp hk).2
      have hk0 : k ≠ 0 := by
        intro h0
        exact hk2 (by rw [h0, kmom_zeroGen F, norm_zero]
                      exact mul_pos (by norm_num) hc1pos)
      exact Finset.mem_erase.mpr ⟨hk0, Finset.mem_univ k⟩
    have htail : ∀ k ∈ S2,
        E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0)
          ≤ (25 / (8 * A0)) * (E.W1 k ^ 2 / (2 * ‖F.kmom k‖ ^ 2)) := by
      intro k hk
      have hk2 : ¬ (‖F.kmom k‖ < 10 * c1) := by
        rw [hS2] at hk
        exact (Finset.mem_filter.mp hk).2
      have hx : 10 * c1 ≤ ‖F.kmom k‖ := not_lt.mp hk2
      have hden : A0 * (‖F.kmom k‖ - 2 * c1) ^ 2 + (98 / 100) * B0
          ≤ (1 - epsFar v μ ρ) * E.tau k + B0 := by
        have h := hA1lb k
        have hmax : max 0 (‖F.kmom k‖ - 2 * c1) = ‖F.kmom k‖ - 2 * c1 :=
          max_eq_right (by linarith)
        rwa [hmax] at h
      have hdenpos : 0 < A0 * (‖F.kmom k‖ - 2 * c1) ^ 2 + (98 / 100) * B0 := by
        have h0 : 0 < (98 / 100) * B0 := by linarith
        have h1 : 0 ≤ A0 * (‖F.kmom k‖ - 2 * c1) ^ 2 :=
          mul_nonneg hA0pos.le (sq_nonneg _)
        linarith
      have hcmp := farRadLatCmp (A := A0) (B := (98 / 100) * B0) (W := E.W1 k)
        (x := ‖F.kmom k‖) (c1 := c1) hA0pos (by linarith) hc1pos hx
      exact le_trans (div_le_div_of_nonneg_left (sq_nonneg _) hdenpos hden) hcmp
    -- ## (5) the two budget pieces
    have hXnn : 0 ≤ 2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0 := by positivity
    have hS1card :
        (S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0)
          ≤ ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
              * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0) :=
      mul_le_mul_of_nonneg_right hcount hXnn
    have hcnt := farRadCountBGen (v := v) hAdm hε₀ hav hρpos hfar
    have hbud1 : ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
        * ((S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0))
          ≤ ErrRes v μ ρ / 4 := by
      refine le_trans (mul_le_mul_of_nonneg_left hS1card (by positivity)) ?_
      rw [show 2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0
          = 2 * (16 * Real.pi * BoseGases.a v) ^ 2
              / (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) from by
        rw [hB0]]
      simpa only [mul_assoc] using hcnt
    have hfac : (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ)) * (25 / 8) ≤ A0 := by
      have h1 : (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ)) * (25 / 8) ≤ 9 / 10 := by
        nlinarith [hsqε, Real.sqrt_nonneg (epsFar v μ ρ)]
      linarith
    have hc : (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ)) * (25 / (8 * A0)) ≤ 1 := by
      rw [show (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ)) * (25 / (8 * A0))
          = ((1 / 4 + 32 * Real.sqrt (epsFar v μ ρ)) * (25 / 8)) / A0 from by
        field_simp]
      rw [div_le_one hA0pos]
      exact hfac
    have hbud2 : ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
        * ((25 / (8 * A0)) * L)
          ≤ C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ := by
      have hpos2 : (0 : ℝ)
          ≤ C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ := by
        calc (0 : ℝ) = (C * (ell v μ) ^ 3 * farMass v h μ) * 0 := by ring
          _ ≤ (C * (ell v μ) ^ 3 * farMass v h μ) * ρ ^ 2 :=
              mul_le_mul_of_nonneg_left (sq_nonneg ρ) hCℓM
          _ = C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ := by ring
      calc ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
            * ((25 / (8 * A0)) * L)
          ≤ ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
              * ((25 / (8 * A0))
                  * (C * (ell v μ) ^ 3 * farMass v h μ)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLat ?_) ?_
            · positivity
            · positivity
        _ = (C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ)
              * ((1 / 4 + 32 * Real.sqrt (epsFar v μ ρ)) * (25 / (8 * A0))) := by
            ring
        _ ≤ (C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ) * 1 :=
            mul_le_mul_of_nonneg_left hc hpos2
        _ = C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ := by ring
    -- ## (6) the assembly
    have hzp : zeroPointSum F (farEnv E v μ ρ) ρ
        = ∑ k : Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
            ((KzEnvAt (farEnv E v μ ρ) ρ).A k)
            ((KzEnvAt (farEnv E v μ ρ) ρ).B k) := rfl
    have h1 : zeroPointSum F (farEnv E v μ ρ) ρ
        ≤ ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
            * (∑ k : Lab (HM μ).N,
                E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0)) := by
      rw [hzp]; exact hstep1
    have h2 : (∑ k : Lab (HM μ).N,
            E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0))
        = (∑ k ∈ S1, E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0))
          + (∑ k ∈ S2, E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0)) := by
      rw [hS1, hS2]
      exact (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k : Lab (HM μ).N => ‖F.kmom k‖ < 10 * c1)
        (fun k => E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0))).symm
    have h3 : (∑ k ∈ S1, E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0))
        ≤ (S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0) := by
      calc (∑ k ∈ S1, E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0))
          ≤ ∑ _k ∈ S1, (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0) :=
            Finset.sum_le_sum (fun k _ => hcrude k)
        _ = (S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have h5 : (∑ k ∈ S2, E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0))
        ≤ (25 / (8 * A0)) * L := by
      calc (∑ k ∈ S2, E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0))
          ≤ ∑ k ∈ S2, (25 / (8 * A0)) * (E.W1 k ^ 2 / (2 * ‖F.kmom k‖ ^ 2)) :=
            Finset.sum_le_sum (fun k hk => htail k hk)
        _ = (25 / (8 * A0)) * (∑ k ∈ S2, E.W1 k ^ 2 / (2 * ‖F.kmom k‖ ^ 2)) := by
            rw [Finset.mul_sum]
        _ ≤ (25 / (8 * A0)) * L := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hLdef]
            exact Finset.sum_le_sum_of_subset_of_nonneg hS2sub (fun k _ _ => by positivity)
    calc zeroPointSum F (farEnv E v μ ρ) ρ
        ≤ ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
            * (∑ k : Lab (HM μ).N,
                E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0)) := h1
      _ = ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
            * ((∑ k ∈ S1, E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0))
              + (∑ k ∈ S2, E.W1 k ^ 2 / ((1 - epsFar v μ ρ) * E.tau k + B0))) := by
            rw [h2]
      _ ≤ ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
            * ((S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0)
              + (25 / (8 * A0)) * L) :=
            mul_le_mul_of_nonneg_left (add_le_add h3 h5) (by positivity)
      _ = ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
              * ((S1.card : ℝ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2 / B0))
            + ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
              * ((25 / (8 * A0)) * L) := by ring
      _ ≤ ErrRes v μ ρ / 4
            + C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ :=
            add_le_add hbud1 hbud2
      _ = C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ
            + ErrRes v μ ρ / 4 := by ring

/-! ## 3. The quadratic and linear slots in the `All` vocabulary -/

/-- The label `0` has vanishing momentum — used to place `0` in the bit of `excited`. -/
private lemma kmom_zeroGen' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) : F.kmom 0 = 0 := kmom_zeroGen F

/-- `0 ≤ ⟨f, (n_k + n_{−k}) f⟩`. -/
private lemma qw_nOp_add_neg_nonnegGen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (k : Mode) (f : F.H) :
    0 ≤ F.qw f (F.nOp k + F.nOp (-k)) := by
  rw [FockData.qw_add]
  refine add_nonneg ?_ ?_
  · rw [FockData.qw]
    rw [show F.nOp k = F.aDag k ∘ₗ F.a k from rfl, LinearMap.comp_apply, FockData.aDag_adjoint]
    exact F.bp_nonneg _
  · rw [FockData.qw]
    rw [show F.nOp (-k) = F.aDag (-k) ∘ₗ F.a (-k) from rfl, LinearMap.comp_apply,
      FockData.aDag_adjoint]
    exact F.bp_nonneg _

/-- At vanishing density `KzBogFS` is a sum of nonnegative multiples of `n_k + n_{−k}`. -/
private lemma KzBogFS_rho0_eqGen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode) :
    KzBogFS F E 0 = ∑ k : Mode, (1 / 2 : ℝ) • ((E.tau k) • (F.nOp k + F.nOp (-k))) := by
  simp only [KzBogFS]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp

private lemma qw_KzBogFS_rho0_nonnegGen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode) (f : F.H)
    (hτ : ∀ k : Mode, 0 ≤ E.tau k) :
    0 ≤ F.qw f (KzBogFS F E 0) := by
  rw [KzBogFS_rho0_eqGen]
  rw [qw_sum_smul_zp]
  refine Finset.sum_nonneg (fun k _ => ?_)
  rw [FockData.qw_smul]
  exact mul_nonneg (by norm_num) (mul_nonneg (hτ k) (qw_nOp_add_neg_nonnegGen F k f))

/-- **The summed per-pair quadratic ground bound**: `Σ_k½𝒵_k` is the price of
`Σ_k½⟨f, pairQuad_k f⟩`. -/
theorem sum_pairQuad_groundGen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ)
    (hA : ∀ k : Mode, 0 < (KzEnvAt E ρ).A k)
    (hB : ∀ k : Mode, |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k)
    (hAB : ∀ k : Mode, 0 < (KzEnvAt E ρ).A k + (KzEnvAt E ρ).B k)
    (hAe : ∀ k : Mode, (KzEnvAt E ρ).A (-k) = (KzEnvAt E ρ).A k)
    (hBe : ∀ k : Mode, (KzEnvAt E ρ).B (-k) = (KzEnvAt E ρ).B k)
    (hccr : ∀ k : Mode, F.ccrK k k + F.ccrK (-k) (-k) ≤ 2) (f : F.H) :
    -((∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
        ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k))) * F.normSq f
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * F.qw f (pairQuad F E ρ k) := by
  have hper : ∀ k : Mode,
      -((1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k))
          * F.normSq f
        ≤ (1 / 2 : ℝ) * F.qw f (pairQuad F E ρ k) := by
    intro k
    have h := pairQuad_ground F E ρ k (hA k) (hB k) (hAB k) (hAe k) (hBe k) (hccr k) f
    nlinarith [h]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Mode)) => hper k)
  refine le_trans (le_of_eq ?_) hsum
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]

/-- **The lower bound for the summed linear word** (the reversed `χ̂` trick). -/
theorem linWord_lowerGen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (ρ Cn M : ℝ)
    (hCn0 : 0 ≤ Cn) (hCn16 : Cn ≤ 16)
    (hCn : ∀ g : F.H, F.bp ((∑ k : Mode, F.nOp k) g) g ≤ Cn * F.bp (T.N g) g)
    (hM : 0 ≤ M) (f : F.H) (hf : T.NWindow M f) :
    -(8 * Real.sqrt (∑ k : Mode, (cCoefFar E ρ k) ^ 2) * Real.sqrt M * F.normSq f)
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * cCoefFar E ρ k * F.qw f (pairLin F k) := by
  set G : Q3Env Mode := { E with hatChi := fun k => -E.hatChi k } with hG
  have hcoef : ∀ k : Mode, cCoefFar G ρ k = -cCoefFar E ρ k := by
    intro k
    have h1 : G.mu = E.mu := by simp [hG]
    have h2 : G.W1 0 = E.W1 0 := by simp [hG]
    have h3 : G.hatChi k = -E.hatChi k := by simp [hG]
    have h4 : (KzEnvAt G ρ).z = (KzEnvAt E ρ).z := by simp [hG, KzEnvAt]
    rw [cCoefFar, cCoefFar, h1, h2, h3, h4]
    ring
  have hsq : (∑ k : Mode, (cCoefFar G ρ k) ^ 2) = ∑ k : Mode, (cCoefFar E ρ k) ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcoef k, neg_sq]
  have h := linWord_le F T G ρ Cn M hCn0 hCn16 hCn hM f hf
  rw [hsq] at h
  have hneg : -(∑ k : Mode, (1 / 2 : ℝ) * cCoefFar E ρ k * F.qw f (pairLin F k))
      = ∑ k : Mode, (1 / 2 : ℝ) * cCoefFar G ρ k * F.qw f (pairLin F k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcoef k]
    ring
  linarith [h, hneg]

/-- **`√(Σ_k𝒞_k²)` against the parameters.**  At `E' = farEnv E v μ ρ` the coefficient is
`𝒞_k = (ρ−μ)Ŵ₁(0)χ̂_k√(ρℓ³)`, and `Σ_kχ̂_k² ≤ 101`. -/
theorem cCoefFar_sqrt_sum_leGen {v : E3 → ℝ} {μ ρ : ℝ} (D : KzDatum)
    (hav : 0 < a v) (hρ : 0 ≤ ρ) (hmuE : D.E.mu = μ)
    (hellpos : 0 < D.E.ell)
    (hW1 : ∀ k : D.Mode, |D.E.W1 k| ≤ 16 * Real.pi * a v)
    (hchi : ∑ k ∈ Work.BoseB7.excited D.Mode, (D.E.hatChi k) ^ 2 ≤ 100)
    (hchi0 : |D.E.hatChi (0 : D.Mode)| ≤ 1) :
    8 * Real.sqrt (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2) * Real.sqrt D.E.bigM
      ≤ 128 * Real.pi * Real.sqrt 101 * |ρ - μ| * a v * Real.sqrt (ρ * D.E.ell ^ 3)
          * Real.sqrt D.E.bigM := by
  have hcoef : ∀ k : D.Mode,
      cCoefFar (farEnv D.E v μ ρ) ρ k
        = (ρ - μ) * D.E.W1 0 * D.E.hatChi k * Real.sqrt (ρ * D.E.ell ^ 3) := by
    intro k
    simp only [cCoefFar, farEnv, KzEnvAt]
    rw [hmuE]
  have hX : 0 ≤ ρ * D.E.ell ^ 3 := mul_nonneg hρ (pow_nonneg (le_of_lt hellpos) 3)
  have hsumsq : (∑ k : D.Mode, (D.E.hatChi k) ^ 2) ≤ 101 := by
    have hsplit : (∑ k : D.Mode, (D.E.hatChi k) ^ 2)
        = (D.E.hatChi (0 : D.Mode)) ^ 2
          + ∑ k ∈ Work.BoseB7.excited D.Mode, (D.E.hatChi k) ^ 2 := by
      have hh := (Finset.add_sum_erase (Finset.univ : Finset D.Mode)
        (fun k => (D.E.hatChi k) ^ 2) (a := (0 : D.Mode)) (Finset.mem_univ 0)).symm
      simpa only [Work.BoseB7.excited] using hh
    have h0 : (D.E.hatChi (0 : D.Mode)) ^ 2 ≤ 1 := by
      have h1 := abs_le.mp hchi0
      nlinarith [h1.1, h1.2]
    rw [hsplit]
    linarith
  have hsumC : (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2)
      = ((ρ - μ) * D.E.W1 0) ^ 2 * (ρ * D.E.ell ^ 3)
          * (∑ k : D.Mode, (D.E.hatChi k) ^ 2) := by
    have hterm : ∀ k : D.Mode,
        ((ρ - μ) * D.E.W1 0 * D.E.hatChi k * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2
          = ((ρ - μ) * D.E.W1 0) ^ 2 * (ρ * D.E.ell ^ 3) * (D.E.hatChi k) ^ 2 := by
      intro k
      simp only [mul_pow, Real.sq_sqrt hX]
      ring
    rw [Finset.sum_congr rfl (fun k _ => by rw [hcoef k, hterm k]), ← Finset.mul_sum]
    try ring
  have hSle : (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2)
      ≤ ((|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2 * 101) := by
    rw [hsumC]
    have hW : (D.E.W1 0) ^ 2 ≤ (16 * Real.pi * a v) ^ 2 := by
      have h := hW1 0
      have h2 := abs_le.mp h
      nlinarith [h2.1, h2.2, sq_abs (D.E.W1 0), Real.pi_pos]
    have hsq : ((ρ - μ) * D.E.W1 0) ^ 2 ≤ (|ρ - μ| * (16 * Real.pi * a v)) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs (ρ - μ)]
      exact mul_le_mul_of_nonneg_left hW (sq_nonneg _)
    have hkey : ((ρ - μ) * D.E.W1 0) ^ 2 * (ρ * D.E.ell ^ 3) * (∑ k, (D.E.hatChi k) ^ 2)
        ≤ (|ρ - μ| * (16 * Real.pi * a v)) ^ 2 * (ρ * D.E.ell ^ 3) * 101 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hsq hX) hsumsq
        (Finset.sum_nonneg fun k _ => sq_nonneg _) (by positivity)
    calc ((ρ - μ) * D.E.W1 0) ^ 2 * (ρ * D.E.ell ^ 3) * (∑ k, (D.E.hatChi k) ^ 2)
        ≤ (|ρ - μ| * (16 * Real.pi * a v)) ^ 2 * (ρ * D.E.ell ^ 3) * 101 := hkey
      _ = (|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2 * 101 := by
          have h2 : (|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2
              = |ρ - μ| ^ 2 * (16 * Real.pi * a v) ^ 2 * (ρ * D.E.ell ^ 3) := by
            simp only [mul_pow, Real.sq_sqrt hX]
            try ring
          rw [h2]
          ring
  have hX0 : 0 ≤ |ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3) := by positivity
  have hY0 : 0 ≤ |ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)
      * Real.sqrt 101 := mul_nonneg hX0 (Real.sqrt_nonneg _)
  have hsleq : Real.sqrt (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2)
      ≤ |ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3) * Real.sqrt 101 := by
    have heq : ((|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2 * 101)
        = (|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)
            * Real.sqrt 101) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 101)]
      try ring
    calc Real.sqrt (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2)
        ≤ Real.sqrt ((|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3)) ^ 2
            * 101) := Real.sqrt_le_sqrt hSle
      _ = |ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3) * Real.sqrt 101 := by
          rw [heq, Real.sqrt_sq hY0]
  calc 8 * Real.sqrt (∑ k : D.Mode, (cCoefFar (farEnv D.E v μ ρ) ρ k) ^ 2) * Real.sqrt D.E.bigM
      ≤ 8 * (|ρ - μ| * (16 * Real.pi * a v) * Real.sqrt (ρ * D.E.ell ^ 3) * Real.sqrt 101)
          * Real.sqrt D.E.bigM :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsleq (by norm_num))
          (Real.sqrt_nonneg _)
    _ = 128 * Real.pi * Real.sqrt 101 * |ρ - μ| * a v * Real.sqrt (ρ * D.E.ell ^ 3)
          * Real.sqrt D.E.bigM := by ring

/-- `zeroPointSum` unfolded at the `ε`-split environment. -/
lemma zeroPointSum_eq_sumGen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) :
    zeroPointSum F (farEnv E v μ ρ) ρ
      = ∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
          ((KzEnvAt (farEnv E v μ ρ) ρ).A k) ((KzEnvAt (farEnv E v μ ρ) ρ).B k) := rfl

theorem farZPGen {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ))) (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hW1 : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * BoseGases.a v)
    (hchi : ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 ≤ 100)
    (C : ℝ) (hC : 0 ≤ C)
    (hLat : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k) ^ 2
          / (2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2))
        ≤ C * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hfar : Work.BoseBoxFock.FarCondFS v μ ρ)
    (f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H)
    (hf : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f) :
    -(C * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ
        + Work.BoseFixR.ErrRes v μ ρ / 2)
        * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
          (Work.BoseBoxFock.KzBogFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseFixR.All.farEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ) := by
  classical
  have hμ : 0 < μ := hAdm.1
  have hℓpos : 0 < ell v μ := ell_pos_of_le hR hRℓ
  have hεle : epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
    FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρ hfar
  have hns : 0 ≤ (HonestBoxFam v h fc fu HM μ).F.normSq f :=
    (HonestBoxFam v h fc fu HM μ).F.normSq_nonneg f
  rcases eq_or_lt_of_le hρ with hρ0 | hρpos
  · -- ## the vanishing density `ρ = 0`
    have hρzero : ρ = 0 := hρ0.symm
    have hτ0 : ∀ k : Lab (HM μ).N,
        0 ≤ (farEnv (HonestBoxFam v h fc fu HM μ).E v μ 0).tau k := by
      intro k
      have h1 : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.tau k := farEnvPos_tau_nonneg _ hview k
      have h2 : 0 ≤ 1 - epsFar v μ 0 := by
        have h3 := FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav (le_refl 0)
          (by rw [← hρzero]; exact hfar)
        linarith
      simp only [farEnv]
      nlinarith [h1, h2]
    have hq : 0 ≤ (HonestBoxFam v h fc fu HM μ).F.qw f
        (KzBogFS (HonestBoxFam v h fc fu HM μ).F
          (farEnv (HonestBoxFam v h fc fu HM μ).E v μ 0) 0) :=
      qw_KzBogFS_rho0_nonnegGen _ _ f hτ0
    rw [hρzero]
    rw [show C * (0 : ℝ) ^ 2 * (ell v μ) ^ 3 * farMass v h μ = 0 from by ring]
    rw [zero_add]
    have hErr : 0 ≤ ErrRes v μ 0 := ErrRes_nonneg hμ hav (le_refl 0) hℓpos.le
    have h1 : -(ErrRes v μ 0 / 2) * (HonestBoxFam v h fc fu HM μ).F.normSq f ≤ 0 := by
      nlinarith [hErr, hns]
    linarith [hq, h1]
  · -- ## the positive density `0 < ρ`
    have hvw := hview
    unfold KzDatum.viewFSAll RViewFSAll at hview
    obtain ⟨hFSP, hmuE, haSc, hellE, hbigME, hb, hd, hs, heT, hM, hg0, htauE, hAenv, hBenv,
      hW1pin, hW1o, hW1o0, hchiE, hchiSqE, hfL, hNH, hBessel, hKK⟩ := hview
    have hbigM1 : 1 ≤ bigMV v μ := by
      have h := (Classical.choice hFSP).one_le_bigM
      rw [hbigME] at h
      exact h
    have hchi0 : |(HonestBoxFam v h fc fu HM μ).E.hatChi (0 : Lab (HM μ).N)| ≤ 1 := by
      obtain ⟨K₀, b₀, -, -, -, hker⟩ := hKK
      simpa only [KzEnvAt] using (hker μ (closeCondFS_self hμ hav)).hatChi_le (0 : Lab (HM μ).N)
    have hposE : 0 < (HonestBoxFam v h fc fu HM μ).E.ell := by rw [hellE]; exact hℓpos
    obtain ⟨hA, hB, hAB, hAe, hBe, hCe, hccr⟩ :=
      FarResidBaux.farEnvSideB (v := v) (D := HonestBoxFam v h fc fu HM μ)
        hεle hav hμ hρpos hvw hW1
    -- ## the quadratic/linear split of `KzBogFS`
    have hdecomp : (HonestBoxFam v h fc fu HM μ).F.qw f
          (KzBogFS (HonestBoxFam v h fc fu HM μ).F
            (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ)
        = (∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
            (pairQuad (HonestBoxFam v h fc fu HM μ).F
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k))
          + (∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (cCoefFar
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
              * (HonestBoxFam v h fc fu HM μ).F.qw f
                  (pairLin (HonestBoxFam v h fc fu HM μ).F k)) := by
      have hsum1 : (∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
            (pairOpFar (HonestBoxFam v h fc fu HM μ).F
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k))
          = ∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
              (pairQuad (HonestBoxFam v h fc fu HM μ).F
                  (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k
                + (cCoefFar (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) •
                    pairLin (HonestBoxFam v h fc fu HM μ).F k) :=
        Finset.sum_congr rfl (fun k _ => by rfl)
      have hstep : ∀ k : (HonestBoxFam v h fc fu HM μ).Mode,
          (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
              (pairQuad (HonestBoxFam v h fc fu HM μ).F
                  (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k
                + (cCoefFar (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) •
                    pairLin (HonestBoxFam v h fc fu HM μ).F k)
            = (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
                (pairQuad (HonestBoxFam v h fc fu HM μ).F
                  (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
              + (1 / 2 : ℝ) * (cCoefFar
                    (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                  * (HonestBoxFam v h fc fu HM μ).F.qw f
                      (pairLin (HonestBoxFam v h fc fu HM μ).F k) := by
        intro k
        rw [FockData.qw_add, FockData.qw_smul]
        ring
      have hsumstep : (∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
              (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
                (pairQuad (HonestBoxFam v h fc fu HM μ).F
                    (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k
                  + (cCoefFar (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) •
                      pairLin (HonestBoxFam v h fc fu HM μ).F k))
          = ∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
              ((1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
                  (pairQuad (HonestBoxFam v h fc fu HM μ).F
                    (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                + (1 / 2 : ℝ) * (cCoefFar
                      (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                    * (HonestBoxFam v h fc fu HM μ).F.qw f
                        (pairLin (HonestBoxFam v h fc fu HM μ).F k)) :=
        Finset.sum_congr rfl (fun k _ => hstep k)
      have hcomb : (∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
              ((1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
                  (pairQuad (HonestBoxFam v h fc fu HM μ).F
                    (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                + (1 / 2 : ℝ) * (cCoefFar
                      (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                    * (HonestBoxFam v h fc fu HM μ).F.qw f
                        (pairLin (HonestBoxFam v h fc fu HM μ).F k)))
          = (∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
              (pairQuad (HonestBoxFam v h fc fu HM μ).F
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k))
            + (∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (cCoefFar
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
                * (HonestBoxFam v h fc fu HM μ).F.qw f
                    (pairLin (HonestBoxFam v h fc fu HM μ).F k)) := by
        rw [Finset.sum_add_distrib]
      have hfirst : (HonestBoxFam v h fc fu HM μ).F.qw f
            (KzBogFS (HonestBoxFam v h fc fu HM μ).F
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ)
          = ∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
              (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
              (pairOpFar (HonestBoxFam v h fc fu HM μ).F
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) := by
        rw [KzBogFS_eq_sum_pairOpFar, qw_sum_smul_zp]
      exact hfirst.trans (hsum1.trans (hsumstep.trans hcomb))
    -- ## the zero-point slot and the quadratic half
    have hzp := zeroPointSum_leGen (h := h) hv hv1 hvrad hR hv_supp hav fc fu HM hε₀ hAdm hvw
      hRℓ hW1 hchi ρ hρpos.le hfar C hC hLat
    have hquad := sum_pairQuad_groundGen (HonestBoxFam v h fc fu HM μ).F
      (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ hA hB hAB hAe hBe hccr f
    have hquad' : -(C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ + ErrRes v μ ρ / 4)
        * (HonestBoxFam v h fc fu HM μ).F.normSq f
        ≤ ∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
            (pairQuad (HonestBoxFam v h fc fu HM μ).F
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) := by
      have hq' : -(zeroPointSum (HonestBoxFam v h fc fu HM μ).F
            (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ)
            * (HonestBoxFam v h fc fu HM μ).F.normSq f
          ≤ ∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
              (pairQuad (HonestBoxFam v h fc fu HM μ).F
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) := hquad
      have h1 := mul_le_mul_of_nonneg_right hzp hns
      have h2 := neg_le_neg h1
      calc -(C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ + ErrRes v μ ρ / 4)
            * (HonestBoxFam v h fc fu HM μ).F.normSq f
          = -((C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ + ErrRes v μ ρ / 4)
              * (HonestBoxFam v h fc fu HM μ).F.normSq f) := by ring
        _ ≤ -(zeroPointSum (HonestBoxFam v h fc fu HM μ).F
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ
              * (HonestBoxFam v h fc fu HM μ).F.normSq f) := h2
        _ = -(zeroPointSum (HonestBoxFam v h fc fu HM μ).F
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ)
              * (HonestBoxFam v h fc fu HM μ).F.normSq f := by ring
        _ ≤ ∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (HonestBoxFam v h fc fu HM μ).F.qw f
            (pairQuad (HonestBoxFam v h fc fu HM μ).F
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) := hq'
    -- ## the linear half
    obtain ⟨Cn, hCn0, hCn16, hCn⟩ := hBessel
    have hMnn : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.bigM := le_trans zero_le_one hbigM1
    have hlin := linWord_lowerGen (HonestBoxFam v h fc fu HM μ).F
      (HonestBoxFam v h fc fu HM μ).T (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ Cn
      (HonestBoxFam v h fc fu HM μ).E.bigM hCn0 hCn16 hCn hMnn f hf
    have harith : 8 * Real.sqrt (∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (cCoefFar
          (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) ^ 2)
        * Real.sqrt (HonestBoxFam v h fc fu HM μ).E.bigM ≤ ErrRes v μ ρ / 4 := by
      have h1 := cCoefFar_sqrt_sum_leGen (v := v) (μ := μ) (ρ := ρ)
        (HonestBoxFam v h fc fu HM μ) hav hρ hmuE hposE hW1 hchi hchi0
      rw [hellE, hbigME] at h1
      have h2 : 128 * Real.pi * Real.sqrt 101 * |ρ - μ| * a v * Real.sqrt (ρ * (ell v μ) ^ 3)
            * Real.sqrt (bigMV v μ)
          ≤ ErrRes v μ ρ / 4 := by
        have h3 := farLinArith (ρ := ρ) (μ := μ) (ℓ := ell v μ) (M := bigMV v μ) (a := a v)
          hρ hμ hℓpos.le (le_trans zero_le_one hbigM1) hav
        have h4 : ErrRes v μ ρ / 4
            = 10 ^ 300 / 4 * ((ρ + μ) * a v * bigMV v μ
                + (ρ + μ) ^ (3 / 2 : ℝ) * a v * Real.sqrt ((ell v μ) ^ 3 * bigMV v μ)) := by
          rw [ErrRes]; ring
        rw [h4]
        exact h3
      exact le_trans h1 h2
    have hlin' : -(ErrRes v μ ρ / 4) * (HonestBoxFam v h fc fu HM μ).F.normSq f
        ≤ ∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (cCoefFar
            (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
            * (HonestBoxFam v h fc fu HM μ).F.qw f
                (pairLin (HonestBoxFam v h fc fu HM μ).F k) := by
      have h5 := mul_le_mul_of_nonneg_right harith hns
      have h6 : -(ErrRes v μ ρ / 4 * (HonestBoxFam v h fc fu HM μ).F.normSq f)
          ≤ -(8 * Real.sqrt (∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (cCoefFar
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) ^ 2)
              * Real.sqrt (HonestBoxFam v h fc fu HM μ).E.bigM
              * (HonestBoxFam v h fc fu HM μ).F.normSq f) := neg_le_neg h5
      calc -(ErrRes v μ ρ / 4) * (HonestBoxFam v h fc fu HM μ).F.normSq f
          = -(ErrRes v μ ρ / 4 * (HonestBoxFam v h fc fu HM μ).F.normSq f) := by ring
        _ ≤ -(8 * Real.sqrt (∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (cCoefFar
                (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k) ^ 2)
              * Real.sqrt (HonestBoxFam v h fc fu HM μ).E.bigM
              * (HonestBoxFam v h fc fu HM μ).F.normSq f) := h6
        _ ≤ ∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (1 / 2 : ℝ) * (cCoefFar
              (farEnv (HonestBoxFam v h fc fu HM μ).E v μ ρ) ρ k)
              * (HonestBoxFam v h fc fu HM μ).F.qw f
                  (pairLin (HonestBoxFam v h fc fu HM μ).F k) := hlin
    rw [hdecomp]
    have key := add_le_add hquad' hlin'
    have heq : -(C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ + ErrRes v μ ρ / 4)
          * (HonestBoxFam v h fc fu HM μ).F.normSq f
        + -(ErrRes v μ ρ / 4) * (HonestBoxFam v h fc fu HM μ).F.normSq f
        = -(C * ρ ^ 2 * (ell v μ) ^ 3 * farMass v h μ + ErrRes v μ ρ / 2)
          * (HonestBoxFam v h fc fu HM μ).F.normSq f := by ring
    rw [← heq]
    exact key

end Work.BoseFixR.All
