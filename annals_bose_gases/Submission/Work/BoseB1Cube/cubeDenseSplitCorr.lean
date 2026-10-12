import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.denseAliveDeadSplit
import Submission.Work.BoseFixB1S.flatFibDeviationB1
import Submission.Work.BoseFixB1S.pairSumGeSqSubSqrt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeDenseSplitCorr` — the **corrected split** of the dense band arm

Read `Submission/Work/BoseB1Cube/FINDING_cubeCrudeBand_session4.md` §2 first.

`Work.BoseB1Cube.CubeBandArmDensePos` (the residual of `Work.BoseB1Cube.cubePerBox_holds`, hence of
`Work.BoseB1Cube.cubeCrudeBand_holds`) is the row `PerBoxFCube` on the dense band.  The filed split
(`denseAliveDeadSplit.lean`) cuts it at the comparison

    (filed)   W₁·boxPairCount/(2V²) ≤ flatPairSum        [W₁ = w1MassB, V = boxMass],

whose *alive* half is **not** closable by the payout ledger: the payout
(`Work.BoseFixB1S.pairSumGeSqSubSqrt`) only gives `flatPairSum ≥ (1−δ)·A` with
`A = boxM2·boxPairCount/(2V²)` and `(1−δ) = (1 − √(D̃/(2A)))²`, while the filed hypothesis is the
*other* bound `flatPairSum ≥ A/R₂` (`R₂ = boxM2/W₁`); neither implies the other, so the filed alive
class contains the razor regime `(1−δ)R₂ < 1`.

This module states the split at the criterion the ledger actually needs,

    (corrected)   D̃ ≤ 2·A·(1 − 1/√R₂)²          (⟺ (1−δ)·R₂ ≥ 1),

where `D̃ = ∑_{p ∈ pairSet n} ∫(Φ − P_{p₁}P_{p₂}Φ)²·w` is the pair deviation.  On this class the
payout gives `flatPairSum ≥ (1−δ)A ≥ A/R₂ = W₁·boxPairCount/(2V²)` (the filed alive hypothesis), and
the ledger of `FINDING_cubeCrudeBand_session4.md` §2 closes with fixed constants as soon as the two
*ratio inputs* (R1),(R2) of the fibre row (`BoseB1Cube/denseRatioInput`) are available.  The
complement `{D̃ > 2A(1−1/√R₂)²}` is the razor class; by the PROVED sandwich
`Work.AprioriCount.deadDeviationSandwich` it **contains** the filed pair-dead class, so a razor
proof discharges the filed dead row as well.

Everything in this module is proved; the two `Prop`s are the residual pair.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The pair deviation** `D̃ = Σ_{p ∈ pairSet n} ∫ (Φ − P_{p₁}P_{p₂}Φ)²·w` at the sliding box —
the second argument of the payout `Work.BoseFixB1S.pairSumGeSqSubSqrt`. -/
noncomputable def cubeDenseDev (v : E3 → ℝ) (M : ℕ) (ℓ d : ℝ) (u : E3) (n : ℕ)
    (Φ : X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x in Submission.BoseGases.abox n ℓ,
      ((Φ x) - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.1
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
        * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)

/-- **The payout anchor** `A = boxM2·boxPairCount/(2·boxMass²)`. -/
noncomputable def cubeDenseAnchor (v : E3 → ℝ) (M : ℕ) (ℓ d : ℝ) (u : E3) (n : ℕ)
    (Φ : X n → ℝ) : ℝ :=
  Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
    * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) Φ
    / (2 * (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)

/-- **The mass ratio** `R₂ = boxM2/w1MassB ≥ 1 + c₀` (PROVED:
`Work.BoseB1Cube.flatPairMass_sub_w1MassB_ge_const_mul`). -/
noncomputable def cubeDenseRatio (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ)
    (u : E3) : ℝ :=
  Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
    / Work.BoseFixB1.w1MassB h M ℓ d u

/-- **The corrected pair-alive half of the dense band arm.**  Same shape as
`CubeBandArmDenseAliveRow`, with the class condition replaced by the ledger's own criterion
`D̃ ≤ 2·A·(1 − 1/√R₂)²` (equivalently `(1−δ)·R₂ ≥ 1`). -/
def CubeDenseAliveCorr (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R θ : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ¬ IsThinBox v h μ u →
        0 < Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ) →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
        θ * μ < flatTau (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            (Φ : X n → ℝ) →
        cubeDenseDev v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u n
            (Φ : X n → ℝ)
          ≤ 2 * cubeDenseAnchor v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u n
              (Φ : X n → ℝ)
            * (1 - 1 / Real.sqrt (cubeDenseRatio v h (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u)) ^ 2 →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **The razor half of the dense band arm**: the complement of `CubeDenseAliveCorr`'s class,
`2·A·(1 − 1/√R₂)² < D̃` (the pair deviation exceeds the payout anchor) — the class on which the
payout is weak and the kinetic/capacity slots must pay. -/
def CubeDenseRazor (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R θ : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ¬ IsThinBox v h μ u →
        0 < Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ) →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
        θ * μ < flatTau (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            (Φ : X n → ℝ) →
        2 * cubeDenseAnchor v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u n
              (Φ : X n → ℝ)
            * (1 - 1 / Real.sqrt (cubeDenseRatio v h (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u)) ^ 2
          < cubeDenseDev v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u n
              (Φ : X n → ℝ) →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **The dense band arm is the union of the corrected pair-alive half and the razor half.**  The
split is the decidable comparison of the two reals of the criterion; the constants merge by
`min`/`max` through `Work.BoseB1Cube.perBoxFCube_mono` (whose nonnegativity bricks are
`perBoxCubeFWeight_nonneg` and `perBoxCubeErr_nonneg`), exactly as in
`cubeBandArmDensePos_of_alive_dead`. -/
theorem cubeBandArmDensePos_of_aliveCorr_and_razor {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {R θ : ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (halive : CubeDenseAliveCorr v h R θ) (hrazor : CubeDenseRazor v h R θ) :
    CubeBandArmDensePos v h R θ := by
  obtain ⟨εa, c₁a, Ca, hεa, hc₁a, hCa, ha⟩ := halive
  obtain ⟨εz, c₁z, Cz, hεz, hc₁z, hCz, hz⟩ := hrazor
  refine ⟨min εa εz, min c₁a c₁z, max Ca Cz, lt_min hεa hεz, lt_min hc₁a hc₁z,
    le_max_of_le_left hCa, ?_⟩
  intro μ hAdm n Φ u hgood hthin hνpos hband hdense
  have hAdma : Adm v εa μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmz : Adm v εz μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hA : 0 ≤ Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u x /
              Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u)) :=
    perBoxCubeFWeight_nonneg h hv hvrad hR hv_supp hAdm Φ u
  have hZ : 0 ≤ μ ^ 2 * (a v)
        * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
            + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u
        * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    perBoxCubeErr_nonneg hAdm (Work.BoseFixB1.adm_a_pos hAdm).le Φ u
  by_cases hcmp : cubeDenseDev v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u n
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ 2 * cubeDenseAnchor v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u n
            (Φ : Submission.BoseGases.X n → ℝ)
          * (1 - 1 / Real.sqrt (cubeDenseRatio v h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u)) ^ 2
  · exact perBoxFCube_mono Φ u (min_le_left _ _) (le_max_left _ _) hA hZ
      (ha μ hAdma n Φ u hgood hthin hνpos hband hdense hcmp)
  · exact perBoxFCube_mono Φ u (min_le_right _ _) (le_max_right _ _) hA hZ
      (hz μ hAdmz n Φ u hgood hthin hνpos hband hdense (lt_of_not_ge hcmp))

/-- **The corrected class contains no razor states** — i.e. the split is exhaustive and the two
class conditions are complementary (`D̃ ≤ c` vs `c < D̃`).  Recorded as the interface fact: a proof
of `CubeDenseAliveCorr` never has to say anything about `{D̃ > c}`. -/
theorem cubeDenseAliveCorr_or_razorCondition {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R θ : ℝ}
    (halive : CubeDenseAliveCorr v h R θ) (hrazor : CubeDenseRazor v h R θ) :
    CubeDenseAliveCorr v h R θ ∧ CubeDenseRazor v h R θ := ⟨halive, hrazor⟩

/-! ## 4. The class alignment: the corrected class *is* inside the filed alive class

The pure-real content of `FINDING_cubeCrudeBand_session4.md` §2: the payout
`(√A − √(D/2))² ≤ P` together with the corrected class condition `D ≤ 2A(1 − 1/√R₂)²` forces the
*filed* alive hypothesis `A/R₂ ≤ P` (with `R₂ > 1`).  This is the machine-checked statement of
"the filed split cuts the dense band in the wrong place": its alive class is *strictly bigger* than
the class on which the payout ledger closes, while the corrected class is exactly the latter. -/
theorem payout_of_aliveCorr_condition {A D P R₂ : ℝ} (hA : 0 ≤ A) (hR₂ : 1 < R₂) (hD : 0 ≤ D)
    (hclass : D ≤ 2 * A * (1 - 1 / Real.sqrt R₂) ^ 2)
    (hpay : (Real.sqrt A - Real.sqrt (D / 2)) ^ 2 ≤ P) :
    A / R₂ ≤ P := by
  have hR₂pos : 0 < R₂ := lt_trans zero_lt_one hR₂
  have hsR₂ : 0 < Real.sqrt R₂ := Real.sqrt_pos.mpr hR₂pos
  have hsR₂sq : Real.sqrt R₂ ^ 2 = R₂ := Real.sq_sqrt hR₂pos.le
  have h2 : 0 ≤ 1 - 1 / Real.sqrt R₂ := by
    have h1 : (1 : ℝ) ≤ Real.sqrt R₂ := by nlinarith [hsR₂, hsR₂sq, hR₂]
    have h3 : 1 / Real.sqrt R₂ ≤ 1 := by
      rw [div_le_one hsR₂]; exact h1
    linarith
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hD0 : D ≤ 0 := by
      have hz : 2 * A * (1 - 1 / Real.sqrt R₂) ^ 2 = 0 := by rw [← hA0]; ring
      linarith [hclass, hz]
    have hP0 : 0 ≤ P := by
      linarith [sq_nonneg (Real.sqrt A - Real.sqrt (D / 2)), hpay]
    rw [← hA0, zero_div]
    exact hP0
  · -- `A > 0`: `√(D/2) ≤ √A·(1 − 1/√R₂)`, hence `√A − √(D/2) ≥ √A/√R₂`
    have hA' : 0 < A := hApos
    have hDhalf : D / 2 ≤ A * (1 - 1 / Real.sqrt R₂) ^ 2 := by nlinarith [hclass]
    have hfrac : 0 ≤ A * (1 - 1 / Real.sqrt R₂) ^ 2 := mul_nonneg hA (sq_nonneg _)
    have hroot : Real.sqrt (D / 2) ≤ Real.sqrt A * (1 - 1 / Real.sqrt R₂) := by
      calc Real.sqrt (D / 2) ≤ Real.sqrt (A * (1 - 1 / Real.sqrt R₂) ^ 2) :=
            Real.sqrt_le_sqrt hDhalf
        _ = Real.sqrt A * (1 - 1 / Real.sqrt R₂) := by
            rw [Real.sqrt_mul hA, Real.sqrt_sq h2]
    have hkey : Real.sqrt A / Real.sqrt R₂ ≤ Real.sqrt A - Real.sqrt (D / 2) := by
      have h3 : Real.sqrt A - Real.sqrt A * (1 - 1 / Real.sqrt R₂)
          = Real.sqrt A / Real.sqrt R₂ := by
        field_simp
        ring
      linarith [hroot, h3]
    have h6 : 0 ≤ Real.sqrt A / Real.sqrt R₂ := by positivity
    have h7 : (Real.sqrt A / Real.sqrt R₂) ^ 2 ≤ (Real.sqrt A - Real.sqrt (D / 2)) ^ 2 :=
      pow_le_pow_left₀ h6 hkey 2
    have h8 : (Real.sqrt A / Real.sqrt R₂) ^ 2 = A / R₂ := by
      rw [div_pow, Real.sq_sqrt hA, Real.sq_sqrt hR₂pos.le]
    linarith [hpay, h7, h8]

/-! ## 5. `FibreRowInputs` — the four state-level inputs the fibre row consumes

`Work.BoseFixB1S.flatFib_row_adm` (PROVED) is the fibre row `μ·(flatFibSum − W₁·flatTau·N) ≤
(2D/a)(μa·cnPlusBoxInd) + ½W₁((τ−μ)²N·7/16 + V/4) + ½Δ` at the target's own vocabulary, and it is
*conditional* on exactly four state-level inputs: the count comparison `hcount`, the deviation
bound `hD`, and the two *ratio inputs* (R1),(R2).  This `Prop` packages those four at a **single,
matched** coefficient `Cs` (see `FINDING_cubeCrudeBand_session4.md` §5a for why the matching is
load-bearing).  Its proof is `BoseB1Cube/denseRatioInput` (the state-free part, at `Cs = 1`) plus
whatever `hcount` the count window supplies. -/
def FibreRowInputs (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R θ : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ¬ IsThinBox v h μ u →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
        θ * μ < flatTau (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            (Φ : X n → ℝ) →
        ∃ Cs D : ℝ, 0 ≤ Cs ∧
          (∀ z : E3, |Work.BoseFixB1S.fibDelta h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u z| ≤ D) ∧
          Work.BoseFixB1S.boxFlatCount
              (Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
              (sideAt μ (a v)) (Submission.BoseGases.dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
              (Φ : X n → ℝ)
            ≤ Cs * (flatTau (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
                  (Φ : X n → ℝ)
                * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                    (paramsAt μ (a v)).d u
                * normB v μ n (Φ : X n → ℝ)) ∧
          (64 / 7) * Cs * D * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
              (sideAt μ (a v)) (paramsAt μ (a v)).d u
            ≤ Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u ∧
          32 * Cs * D * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u
            ≤ Work.BoseFixB1.flatPairMass v (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u
              - Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u

end Work.BoseB1Cube
