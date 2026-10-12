import ChallengeDeps
import Submission.Work.BoseFixB1S.boxJointCoreB1
import Submission.Work.BoseFixB1S.boxPeelGen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!

# `Work.BoseFixB1S.boxPayA0A2SlidingAdm` — the joint rung `(T)` at the sliding box, in `Adm`

The statement is the tree's established repair of FS `lm:appinteractionestimate` at FS's
parameters, i.e. `Work.BoseFixB1S.a0A2QJointNormB1` *at* `ℓ = sideAt μ (a v)`,
`d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`, with the two regime conditions
`R ≤ ℓd/16`, `R ≤ ℓ·chiR0` discharged into the existential `ε₀`, and with `Φ : BoxState n ℓ`
supplying continuity.  The packaging below (the two regime lemmas + the `ε₀` choice + the
`M`-instance matchings) is the same as in the *unnormalised* sibling
`Submission/Work/BoseFixB1S/boxPayA0A2Sliding.lean`.

The mathematical content is supplied by
`Work.BoseFixB1S.boxJointIneqSlidingB1` (`Submission/Work/BoseFixB1S/boxJointCoreB1.lean`),
the assembly of the joint core at the sliding parameters from the corpus's proved analytic
pieces: the scalar ledger `boxJointLedgerB1`, the `μ`-line split `boxCrossPartZsplitB1`, the
completion-of-squares split `boxZpSplitB1`, the fibre-weighted AM–GM `boxSharpPairingAMGMB1`,
the oscillation commutator bound `commutatorPairingOscB1`, and the moment bounds
`boxQMassLeFibreB1`, `boxPMassCsB1`, `boxQmassNeutralB1`, `boxMtMomentBoundsB1`,
`boxMtCrudeBoundB1`, `boxFibVarLeCfM1B1`.

**Import-cone note.** This file may not import `a0A2QPayNormB1` (nor anything whose cone
contains `boxQCount_eq_sum_compT`): that module redeclares `Work.BoseFixB1S.goodState_finset_sum`,
already declared in `Work.BoseFixB1S.exclFunOpAux`, which the analytic pieces above require.
Hence the explicit, cone-compatible import list and the local `Adm`-packaging.

-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

/-! ## The geometric extraction from `Adm` (copied from the sibling `boxPayA0A2Sliding.lean`) -/

/-- `(paramsAt μ a).d = (μ a³)^{6/323}` at FS's parameters. -/
private lemma paramsAt_d_eq {μ a : ℝ} :
    (Work.BoseBox.paramsAt μ a).d = (μ * a ^ 3) ^ ((6 : ℝ) / 323) := by
  simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]

/-- `ℓ·d = a(μa³)^{-157/323}` at the sliding parameters. -/
private lemma sideAt_mul_d_eq {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d
      = a * (μ * a ^ 3) ^ (-(157 / 323 : ℝ)) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  rw [Work.BoseBox.sideAt_eq_rpow ha hμ, paramsAt_d_eq, mul_assoc, ← Real.rpow_add ht]
  congr 1
  norm_num

/-- The small-box condition `R ≤ ℓ·d/16` of the sliding parameters, at an explicit diluteness
cut-off. -/
private lemma adm_R_le_sideAt_d {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ R : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hav : 0 < _root_.BoseGases.a v) (hR : 0 < R)
    (hε : ε₀ ≤ (_root_.BoseGases.a v / (16 * R)) ^ (323 / 157 : ℝ)) :
    R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 := by
  have ha := hav
  have hμ : 0 < μ := hAdm.1
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ := hAdm.2.1
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have htp : 0 < (μ * (_root_.BoseGases.a v) ^ 3) ^ (157 / 323 : ℝ) :=
    Real.rpow_pos_of_pos ht _
  have hεpos : 0 < ε₀ := lt_of_lt_of_le ht hdil
  have h1 : (μ * (_root_.BoseGases.a v) ^ 3) ^ (157 / 323 : ℝ)
      ≤ _root_.BoseGases.a v / (16 * R) := by
    have hT : 0 < _root_.BoseGases.a v / (16 * R) := by positivity
    calc (μ * (_root_.BoseGases.a v) ^ 3) ^ (157 / 323 : ℝ)
        ≤ ε₀ ^ (157 / 323 : ℝ) := Real.rpow_le_rpow ht.le hdil (by norm_num)
      _ ≤ ((_root_.BoseGases.a v / (16 * R)) ^ (323 / 157 : ℝ)) ^ (157 / 323 : ℝ) :=
            Real.rpow_le_rpow hεpos.le hε (by norm_num)
      _ = _root_.BoseGases.a v / (16 * R) := by
            rw [← Real.rpow_mul hT.le]
            norm_num
  have hkey : 16 * R ≤ _root_.BoseGases.a v
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(157 / 323) : ℝ) := by
    rw [Real.rpow_neg ht.le, ← div_eq_mul_inv]
    rw [le_div_iff₀ htp]
    have h4 : 16 * R * (μ * (_root_.BoseGases.a v) ^ 3) ^ (157 / 323 : ℝ)
        ≤ 16 * R * (_root_.BoseGases.a v / (16 * R)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : 16 * R * (_root_.BoseGases.a v / (16 * R)) = _root_.BoseGases.a v := by
      field_simp
    linarith [h4, h5]
  rw [sideAt_mul_d_eq hμ ha, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
  linarith [hkey]

/-- The large-box condition `R ≤ ℓ·chiR0` of the sliding parameters, at an explicit diluteness
cut-off. -/
private lemma adm_R_le_sideAt_chiR0 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ R : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hav : 0 < _root_.BoseGases.a v) (hR : 0 < R)
    (hε : ε₀ ≤ (_root_.BoseGases.a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ)) :
    R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 := by
  have ha := hav
  have hχ : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have hμ : 0 < μ := hAdm.1
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ := hAdm.2.1
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have htp : 0 < (μ * (_root_.BoseGases.a v) ^ 3) ^ (163 / 323 : ℝ) :=
    Real.rpow_pos_of_pos ht _
  have hεpos : 0 < ε₀ := lt_of_lt_of_le ht hdil
  have h1 : (μ * (_root_.BoseGases.a v) ^ 3) ^ (163 / 323 : ℝ)
      ≤ _root_.BoseGases.a v * Submission.BoseGases.chiR0 / R := by
    have hT : 0 < _root_.BoseGases.a v * Submission.BoseGases.chiR0 / R :=
      div_pos (mul_pos hav hχ) hR
    calc (μ * (_root_.BoseGases.a v) ^ 3) ^ (163 / 323 : ℝ)
        ≤ ε₀ ^ (163 / 323 : ℝ) := Real.rpow_le_rpow ht.le hdil (by norm_num)
      _ ≤ ((_root_.BoseGases.a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ))
            ^ (163 / 323 : ℝ) := Real.rpow_le_rpow hεpos.le hε (by norm_num)
      _ = _root_.BoseGases.a v * Submission.BoseGases.chiR0 / R := by
            rw [← Real.rpow_mul hT.le]
            norm_num
  have hkey : R ≤ _root_.BoseGases.a v * Submission.BoseGases.chiR0
      / (μ * (_root_.BoseGases.a v) ^ 3) ^ (163 / 323 : ℝ) := by
    rw [le_div_iff₀ htp]
    have h4 : R * (μ * (_root_.BoseGases.a v) ^ 3) ^ (163 / 323 : ℝ)
        ≤ R * (_root_.BoseGases.a v * Submission.BoseGases.chiR0 / R) :=
      mul_le_mul_of_nonneg_left h1 hR.le
    have h5 : R * (_root_.BoseGases.a v * Submission.BoseGases.chiR0 / R)
        = _root_.BoseGases.a v * Submission.BoseGases.chiR0 := by field_simp
    linarith [h4, h5]
  rw [Work.BoseBox.sideAt_eq_rpow ha hμ, Real.rpow_neg ht.le,
    show _root_.BoseGases.a v * ((μ * (_root_.BoseGases.a v) ^ 3) ^ (163 / 323 : ℝ))⁻¹
        * Submission.BoseGases.chiR0
        = _root_.BoseGases.a v * Submission.BoseGases.chiR0
          / (μ * (_root_.BoseGases.a v) ^ 3) ^ (163 / 323 : ℝ) from by
      rw [div_eq_mul_inv]; ring]
  exact hkey

theorem boxPayA0A2SlidingAdm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          0 < Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u →
          (1 : ℝ) ≤ μ * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u →
          (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
            (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
              ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
          0 ≤ Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
          Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h)) →
          0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
              * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
            - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v)
              (Submission.BoseGases.omC (Classical.choose h)) (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            * ((1 / 4) * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
                  / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u - μ) ^ 2
                + (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
                    / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + μ)
                  / (2 * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                + 1 / (4 * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u ^ 2))
          + (1 / 2) * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h))
              / (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) ^ 2)
              * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
          - (1 / 2) * (Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              / (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) ^ 2)
              * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ))
          + C * (_root_.BoseGases.a v)
              * (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
                  / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
        ≥ 2 * μ * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) i (Φ : Submission.BoseGases.X n → ℝ) x)
                * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) i (Φ : Submission.BoseGases.X n → ℝ) x)
                * (Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (x i)))
          + μ * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) i (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
                * (Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (x i))) := by
  classical
  have hχpos : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  set ε₀ : ℝ := min 1 (min ((_root_.BoseGases.a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ))
      ((_root_.BoseGases.a v / (16 * R)) ^ (323 / 157 : ℝ))) with hεdef
  have hε₀pos : 0 < ε₀ := by
    rw [hεdef]
    exact lt_min one_pos (lt_min
      (Real.rpow_pos_of_pos (div_pos (mul_pos hav hχpos) hR) _)
      (Real.rpow_pos_of_pos (div_pos hav (by positivity : (0 : ℝ) < 16 * R)) _))
  have hε16 : ε₀ ≤ (_root_.BoseGases.a v / (16 * R)) ^ (323 / 157 : ℝ) := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hεχ : ε₀ ≤ (_root_.BoseGases.a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ) := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have ha := hav
  -- the corpus's established joint core at the sliding parameters
  obtain ⟨C, hC0, hC⟩ := Work.BoseFixB1S.boxJointIneqSlidingB1 (v := v) (R0 := R)
    hv_supp hR hv hvrad hv1 h ha (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  refine ⟨ε₀, C, hε₀pos, hC0, ?_⟩
  intro μ hAdm n Φ u hvol hμv hnorm hsupp hM1nn hM2 hPcnn hcS2
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseBox.sideAt_pos hμ ha
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    rw [paramsAt_d_eq]; exact Real.rpow_pos_of_pos (by positivity) _
  have hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 :=
    adm_R_le_sideAt_d hAdm ha hR hε16
  have hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 :=
    adm_R_le_sideAt_chiR0 hAdm ha hR hεχ
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  exact hC hℓ hd hμ hR16 hRχ u hvol hμv hΦc hnorm hsupp hM1nn hM2 hPcnn hcS2

end Work.BoseFixB1S
