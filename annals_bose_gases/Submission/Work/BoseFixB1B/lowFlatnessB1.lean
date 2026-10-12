import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.perBoxCrudeLower
import Submission.Work.BoseFixB1S.flatArmSlidingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.lowFlatnessB1` — the **flatness** of the sliding box at positive
# deficit

Written by the holder of `Submission/Work/BoseFixB1B/lowState_count_leAlt.lean`.

## What this module contains

The sliding word `sbWord h μ u Φ` at FS's parameters splits as

    sbWord = sbKin + pairSum − μ·fibSum       (`sbPot_split`),

so the *deficit* `deficitSliding := μ·fibSum − sbKin − pairSum` (`flatArmSlidingDefs`) is
`−sbWord`.  On the part of the state space where the deficit is **positive** — the *flat arm* of
the crude per-box bound (`Work.BoseFixB1S.FlatArmSliding`) — the box is *flat*: the excited
(variance) count `Q = boxQCount` is a super-polynomially small fraction of the in-box count
`S + Q = boxFlatCount + boxQCount`.

The mechanism (`FINDING_SESSION2_holeVoidCostCountQuadGood.md` §A1) is one line: the kinetic word
of the box **is** the gap coefficient times the excited count plus a nonnegative spectral word,

    sbKin = tbGapCoeff (ℓd) ε_T · boxQCount + tBwordKinInd      (`rfl` + `tBwordKinInd_nonneg`),

and the fibre loss is dominated by the box mass (`fibSum_le` + `chiSum_le_countCs`, or the sharper
`PerBoxFibRedB1`).  Hence, with `deficitSliding > 0` (so `sbKin < μ·fibSum`) and `pairSum ≥ 0`,

    tbGapCoeff (ℓd) ε_T · Q  ≤  sbKin  <  μ·fibSum  ≤  K·μ(a v)·(S + Q) .

At FS's parameters `μ(a v)/tbGapCoeff(ℓd)ε_T = 2(1+π⁻²)·(μ(a v)(ℓd)²/ε_T) = 2(1+π⁻²)t^{13/1292}`
(`Work.BoseFixB1S.a_mu_side_d_sq_div_eT_le_one`), which is `≤ 1/2` once `ε₀` is small
(`t = μ(a v)³`), so the flat arm has `2Q ≤ S + Q`, i.e. `Q ≤ S` and `S + Q ≤ 2S`.  That is the
*proved* part of step 1 of `Submission/Work/Analysis/HoleVoidCost/FINDING_SESSION2_…md` §C (the
file `deficitFlatCount.lean` in that chapter states the same inequality); the capacity/void part
of the chapter is what remains.

## Contents

* `sbKin_ge_gapCoeff_mul_boxQCount` — the definitional decomposition, as an inequality;
* `deficitFlatB1` — the flatness inequality `G·Q ≤ K·μ(a v)·(S+Q)` at positive deficit;
* `deficitFlatB1_halves` — its numeric corollary `2Q ≤ S + Q`, stated against the explicit
  parameter hypothesis `2Kμ(a v) ≤ G` (which the caller discharges with
  `Work.BoseFixB1S.a_mu_side_d_sq_div_eT_le_one` and `ε₀` small).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **`sbKin` is the gap coefficient times the box excited count plus a nonnegative spectral
word.**  Definitional unfolding of `Work.BoseFixB1.sbKin = tBwordBInd` and
`tBwordInd = tbGapCoeff·cnPlusBoxInd + tBwordKinInd`, plus `tBwordKinInd ≥ 0`. -/
theorem sbKin_ge_gapCoeff_mul_boxQCount {v : E3 → ℝ} {μ : ℝ} {n : ℕ} (M : ℕ) (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.SmallBoxTBWord.tbGapCoeff
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ
      ≤ Work.BoseFixB1.sbKin (v := v) μ M u Φ := by
  have h := Work.BoseFixB1.tBwordKinInd_nonneg
    (a := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (A := Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (volA := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (χ := Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ
  simp only [Work.BoseFixB1.sbKin, Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd]
  linarith

/-- **The flatness of the sliding box at positive deficit.**  There are `ε₀ > 0` and `K ≥ 0` such
that at every admissible `μ`, every box state and every `u`, a *positive* deficit forces

    tbGapCoeff (ℓd) ε_T · Q  ≤  K · μ · (a v) · (S + Q) ,

with `Q = boxQCount`, `S = boxFlatCount` the sliding box counts.  Equivalently
`deficitSliding = −sbWord > 0` implies the box is flat: the excited count is a fraction
`K·μ(a v)/tbGapCoeff(ℓd)ε_T` of the in-box count (super-polynomially small at FS's parameters,
see `deficitFlatB1_halves`). -/
theorem deficitFlatB1 {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K : ℝ, 0 < ε₀ ∧ 0 ≤ K ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : E3),
          0 < Work.BoseFixB1S.deficitSliding (v := v) h μ (Φ : Submission.BoseGases.X n → ℝ) u →
          Work.SmallBoxTBWord.tbGapCoeff
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            * Work.BoseFixB1S.boxQCount
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ)
          ≤ K * μ * (_root_.BoseGases.a v)
              * (Work.BoseFixB1S.boxFlatCount
                    (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Φ : Submission.BoseGases.X n → ℝ)
                + Work.BoseFixB1S.boxQCount
                    (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Φ : Submission.BoseGases.X n → ℝ)) := by
  classical
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨εr,
    (16 * Real.pi * chiSupAbs * chiSmallDecay Work.BoseBox.mValue
        / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue)
      * (chiSupAbs * chiSmallDecay Work.BoseBox.mValue), hεr,
    mul_nonneg
      (div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) chiSupAbs_nonneg)
          (chiSmallDecay_nonneg _))
        (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos _)))
      (mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg _)), ?_⟩
  intro μ hAdm n Φ u hdec
  have hμm : 0 < μ := hAdm.1
  have hμnn : 0 ≤ μ := le_of_lt hμm
  have hann : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  obtain ⟨hR16, hRχ⟩ := hreg μ hμm hAdm.2.1
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have hMm : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = Work.BoseBox.mValue := rfl
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [hMm, Work.BoseBox.mValue]; norm_num
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- (1) the gap pays the excited count
  have hgap := sbKin_ge_gapCoeff_mul_boxQCount (v := v) (μ := μ) (n := n)
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u (Φ : Submission.BoseGases.X n → ℝ)
  -- (2) the deficit is positive, and the pair term is nonnegative
  have hpair : 0 ≤ Work.BoseFixB1.pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.pairSum_nonneg (v := v) hv
      (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) (u := u)
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (Φ : Submission.BoseGases.X n → ℝ)
  have hdef : 0 < μ * Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
      - Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
          (Φ : Submission.BoseGases.X n → ℝ)
      - Work.BoseFixB1.pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ) := by
    simpa only [Work.BoseFixB1S.deficitSliding, Work.BoseFixB1S.chemicalDebit] using hdec
  -- (3) the fibre loss is dominated by the box counts
  have hfib := Work.BoseFixB1.fibSum_le (v := v) (h := h) (R0 := R) hv hvrad hR hv_supp
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM hℓ hd hR16 hRχ u hΦc
  rw [hMm] at hfib
  have hchi := chiSum_le_countCs
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM hℓ hd u hΦc
  rw [hMm] at hchi
  have hsplit := Work.BoseFixR.SlabCountSplit (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ hd u hΦc
  have hchi' : Work.BoseFixB1.chiSum Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
      ≤ (chiSupAbs * chiSmallDecay Work.BoseBox.mValue)
        * (Work.BoseFixB1S.boxFlatCount
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseFixB1S.boxQCount
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)) := by
    rw [Work.BoseFixB1B.chiCs] at hchi
    rw [hsplit] at hchi
    exact hchi
  -- (4) the chain
  set Kav : ℝ := 16 * Real.pi * chiSupAbs * chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue with hKavdef
  set S : ℝ := Work.BoseFixB1S.boxFlatCount
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ) with hSdef
  set Q : ℝ := Work.BoseFixB1S.boxQCount
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ) with hQdef
  set G : ℝ := Work.SmallBoxTBWord.tbGapCoeff
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with hGdef
  have hKav0 : 0 ≤ Kav := by
    rw [hKavdef]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) chiSupAbs_nonneg)
        (chiSmallDecay_nonneg _))
      (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos _))
  have step1 : G * Q ≤ Work.BoseFixB1.sbKin (v := v) μ
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [hGdef, hQdef]
    exact hgap
  have step2 : Work.BoseFixB1.sbKin (v := v) μ
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u (Φ : Submission.BoseGases.X n → ℝ)
      ≤ μ * Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ) := by
    linarith [hdef, hpair]
  have step3 : μ * Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
      ≤ μ * (Kav * (_root_.BoseGases.a v)
          * Work.BoseFixB1.chiSum Work.BoseBox.mValue
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)) := by
    rw [hKavdef]
    exact mul_le_mul_of_nonneg_left hfib hμnn
  have step4 : μ * (Kav * (_root_.BoseGases.a v)
        * Work.BoseFixB1.chiSum Work.BoseBox.mValue
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ))
      ≤ μ * (Kav * (_root_.BoseGases.a v)
          * ((chiSupAbs * chiSmallDecay Work.BoseBox.mValue) * (S + Q))) := by
    refine mul_le_mul_of_nonneg_left ?_ hμnn
    exact mul_le_mul_of_nonneg_left hchi'
      (mul_nonneg hKav0 hann)
  have step5 : μ * (Kav * (_root_.BoseGases.a v)
        * ((chiSupAbs * chiSmallDecay Work.BoseBox.mValue) * (S + Q)))
      = (Kav * (chiSupAbs * chiSmallDecay Work.BoseBox.mValue)) * μ * (_root_.BoseGases.a v)
          * (S + Q) := by ring
  have hfinal := le_trans (le_trans (le_trans step1 step2) step3) (le_trans step4 (le_of_eq step5))
  rw [hGdef, hQdef, hSdef] at hfinal
  have hKdef : Kav * (chiSupAbs * chiSmallDecay Work.BoseBox.mValue)
      = (16 * Real.pi * chiSupAbs * chiSmallDecay Work.BoseBox.mValue
          / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue)
        * (chiSupAbs * chiSmallDecay Work.BoseBox.mValue) := by rw [hKavdef]
  rw [← hKdef]
  exact hfinal

/-- **The gap regime in the `c·μ(a v) ≤ tbGapCoeff` form.**  `Work.BoseFixB1.gapRegime_of_adm`
at `c' = √c` says `2(1+π⁻²)(ℓd√c√(μ(a v)))² ≤ ε_T`, i.e.
`c·μ(a v) ≤ ½(1+π⁻²)⁻¹ε_T(ℓd)⁻² = tbGapCoeff (ℓd) ε_T`.  The threshold depends only on `c`, so
*any* fixed multiple of `μ(a v)` is dominated by the gap coefficient once the diluteness is small
— this is what makes `deficitFlatB1_halves` unconditional. -/
lemma mul_mu_le_tbGapCoeff {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v) {c : ℝ} (hc : 0 ≤ c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      c * μ * (_root_.BoseGases.a v) ≤ Work.SmallBoxTBWord.tbGapCoeff
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
  obtain ⟨ε₀, hε₀, hg⟩ := Work.BoseFixB1.gapRegime_of_adm (v := v) hav (c' := Real.sqrt c)
    (Real.sqrt_nonneg c)
  refine ⟨ε₀, hε₀, ?_⟩
  intro μ hAdm
  have hg' := hg μ hAdm
  have hμ : 0 < μ := hAdm.1
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hsq : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Real.sqrt c
        * Real.sqrt (μ * (_root_.BoseGases.a v))
      = ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) * Real.sqrt c)
        * Real.sqrt (μ * (_root_.BoseGases.a v)) := by ring
  rw [hsq] at hg'
  have hsq2 : (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) * Real.sqrt c)
        * Real.sqrt (μ * (_root_.BoseGases.a v))) ^ 2
      = (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
        * (c * μ * (_root_.BoseGases.a v)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hc, Real.sq_sqrt (mul_nonneg hμ.le ha)]
    ring
  rw [hsq2] at hg'
  have hkey : c * μ * (_root_.BoseGases.a v)
      ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        / (2 * (1 + (Real.pi ^ 2)⁻¹)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hg']
  have heq : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        / (2 * (1 + (Real.pi ^ 2)⁻¹)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)
      = (1 / 2) * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        * (1 + (Real.pi ^ 2)⁻¹)⁻¹
        * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)⁻¹ := by
    field_simp
  rw [Work.SmallBoxTBWord.tbGapCoeff, Work.SmallBoxTBWord.tbPiFactor]
  linarith [hkey, heq]

/-- **The arithmetic core** of the flatness corollary: if `G > 0`, `S + Q ≥ 0`,
`G·Q ≤ Kμa(S+Q)` and `2Kμa ≤ G`, then `2Q ≤ S + Q`. -/
lemma two_mul_le_add_of_mul_le (G K μ a S Q : ℝ) (hG : 0 < G) (hSQ : 0 ≤ S + Q)
    (h0 : G * Q ≤ K * μ * a * (S + Q)) (hp : 2 * K * μ * a ≤ G) :
    2 * Q ≤ S + Q := by
  have h1 : 2 * (G * Q) ≤ 2 * (K * μ * a * (S + Q)) := mul_le_mul_of_nonneg_left h0 (by norm_num)
  have h2 : 2 * (K * μ * a * (S + Q)) = (2 * K * μ * a) * (S + Q) := by ring
  have h3 : (2 * K * μ * a) * (S + Q) ≤ G * (S + Q) := mul_le_mul_of_nonneg_right hp hSQ
  have h4 : G * (2 * Q) = 2 * (G * Q) := by ring
  have h5 : G * (2 * Q) ≤ G * (S + Q) := by
    rw [h4]
    exact le_trans h1 (le_trans (le_of_eq h2) h3)
  exact le_of_mul_le_mul_left h5 hG

/-- **The numeric corollary of `deficitFlatB1`**: with the flatness constant `K` of
`deficitFlatB1`, a positive deficit forces `2Q ≤ S + Q` (i.e. `Q ≤ S` and `S + Q ≤ 2S`, so the
excited count is at most half the in-box count).  **No parameter hypothesis is needed**: the
smallness `2Kμ(a v) ≤ tbGapCoeff (ℓd) ε_T` is produced by `mul_mu_le_tbGapCoeff` at
`c = 2K`, i.e. by the gap regime `Work.BoseFixB1.gapRegime_of_adm` — which holds for *every*
fixed `c` once the diluteness threshold is small. -/
theorem deficitFlatB1_halves {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K : ℝ, 0 < ε₀ ∧ 0 ≤ K ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : E3),
          0 < Work.BoseFixB1S.deficitSliding (v := v) h μ (Φ : Submission.BoseGases.X n → ℝ) u →
          2 * Work.BoseFixB1S.boxQCount
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1S.boxFlatCount
                    (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Φ : Submission.BoseGases.X n → ℝ)
                + Work.BoseFixB1S.boxQCount
                    (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨ε₀, K, hε₀, hK, hflat⟩ := deficitFlatB1 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εg, hεg, hgap⟩ := mul_mu_le_tbGapCoeff (v := v) hav (c := 2 * K) (by linarith)
  refine ⟨min ε₀ εg, K, lt_min hε₀ hεg, hK, ?_⟩
  intro μ hAdm n Φ u hdec
  have hAdmf : Work.BoseBoxFix.Adm v ε₀ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hp : 2 * K * μ * (_root_.BoseGases.a v) ≤ Work.SmallBoxTBWord.tbGapCoeff
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := hgap μ hAdmg
  have h0 := hflat μ hAdmf n Φ u hdec
  have hS0 : 0 ≤ Work.BoseFixB1S.boxFlatCount
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseFixB1S.boxFlatCount]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hQ0 : 0 ≤ Work.BoseFixB1S.boxQCount
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseFixB1S.boxQCount]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hGpos : 0 < Work.SmallBoxTBWord.tbGapCoeff
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
    rw [Work.SmallBoxTBWord.tbGapCoeff]
    have hπ : 0 < Work.SmallBoxTBWord.tbPiFactor := Work.SmallBoxTBWord.tbPiFactor_pos
    have hε : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
      Work.BoseFixB1.adm_eT_pos hAdm
    have h1 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
    have h2 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
      Work.BoseFixB1.adm_d_pos hAdm
    have hs : 0 < (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 := by positivity
    positivity
  exact two_mul_le_add_of_mul_le _ K μ (_root_.BoseGases.a v) _ _ hGpos (add_nonneg hS0 hQ0) h0 hp

end Work.BoseFixB1B
