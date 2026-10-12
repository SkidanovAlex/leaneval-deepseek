import ChallengeDeps
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_A0A2QJointSharpImp
import Submission.Work.BoseFixB1B.matchedWindowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix
  Work.SmallBoxSliding

/-- **The scalar content of the pair-condensate surplus.**  The sharp joint rung
(`Work.BoseFixB1S.a0A2QJointSharpImp`) supplies the credit
`(1/4)(M₁/V²)·((S+1−μV)² + (Pc − S² + S) + 1)`; the target needs the *larger* credit
`M₁·G + (1/2)(M₁/V²)(Pc − S² + S)`, `G = ¼(S/V−μ)² + (S/V+μ)/(2V) + 1/(4V²)`.  Writing
`φ := (Pc − S² + S)`, the difference of the two is `(1/4)(M₁/V²)(φ + 1 − 4μV)`, which is
nonpositive because `1 ≤ μV` and `0 ≤ φ`. -/
private lemma rowM1_le {V μ M1 Pc S : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M1) (hμV : 1 ≤ μ * V)
    (hVar : 0 ≤ Pc - S ^ 2 + S) :
    (1 / 4) * (M1 / V ^ 2) * ((S + 1 - μ * V) ^ 2 + (Pc - S ^ 2 + S) + 1)
      ≤ M1 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + (1 / 2) * (M1 / V ^ 2) * (Pc - S ^ 2 + S) := by
  have hid : (1 / 4) * (M1 / V ^ 2) * ((S + 1 - μ * V) ^ 2 + (Pc - S ^ 2 + S) + 1)
      = M1 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + (1 / 4) * (M1 / V ^ 2) * ((Pc - S ^ 2 + S) + 1 - 4 * (μ * V)) := by
    field_simp
    ring
  rw [hid]
  have hc4 : (0 : ℝ) ≤ (1 / 4) * (M1 / V ^ 2) := by
    have : (0 : ℝ) < V ^ 2 := by positivity
    positivity
  -- `1 − 4μV ≤ 0 ≤ Var`, hence `Var + 1 − 4μV ≤ 2·Var`
  have hle : (Pc - S ^ 2 + S) + 1 - 4 * (μ * V) ≤ 2 * (Pc - S ^ 2 + S) := by linarith
  calc M1 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + (1 / 4) * (M1 / V ^ 2) * ((Pc - S ^ 2 + S) + 1 - 4 * (μ * V))
      ≤ M1 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + (1 / 4) * (M1 / V ^ 2) * (2 * (Pc - S ^ 2 + S)) := by
        have h := mul_le_mul_of_nonneg_left hle hc4
        linarith [h]
    _ = M1 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + (1 / 2) * (M1 / V ^ 2) * (Pc - S ^ 2 + S) := by ring

/-- **The pair-condensate surplus is exactly the part of the `pcb`-credit that the sharp rung
leaves unused.**  The target's surplus `(Pc/2V²)(M₂−M₁)` equals `pcb − (1/2)(M₁/V²)Var`, where
`pcb = (1/2)(M₂/V²)Pc − (1/2)(M₁/V²)(S²−S)` is the pair-condensate slack of the `A₀`-step and
`Var = Pc − S² + S` is the `n₀`-variance.  (Pure algebra, no hypotheses beyond `V ≠ 0`.) -/
private lemma pcb_sub_variance_eq_surplus {V M1 M2 Pc S : ℝ} (hV : 0 < V) :
    (1 / 2) * (M2 / V ^ 2) * Pc - (1 / 2) * (M1 / V ^ 2) * (S ^ 2 - S)
      - (1 / 2) * (M1 / V ^ 2) * (Pc - S ^ 2 + S)
    = Pc / (2 * V ^ 2) * (M2 - M1) := by
  have hV2 : V ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **L1 of the lead's cube design (`LEAD_DESIGN_cube.md` §3, Step L1): the chained bound with the
pair-condensate surplus restored.**

This is the PROVED `Work.BoseFixB1B.sbWordCube_ge_a0Main_add_boxA2` — hypothesis block lifted
verbatim — with the single extra left-hand term

    `boxPairCount V ℓ A Φ / (2 * V²) * (M₂ − M₁)` ,      `V = boxMass ℓ d u`,

which that proof dropped when it replaced `M₂` by `M₁`.

**Proved route (both reviewers confirmed it; use it, do not re-derive the payment).**  The on-disk
identity `boxQ0 − a0MainLocBox = M₁·G + ½(M₂/V²)·Pc − ½(M₁/V²)(S²−S)`
(`Work.BoseFixB1S.boxQ0_sub_a0MainLocBox_eq`, from the sorry-free `Work.BoseFixB1S.boxQ0_value`)
together with the PROVED M₂-keeping payment `Work.BoseFixB1S.interEstKeepM2B1`
(`boxQ0 − M₁G + boxA2 − C·(a v)·(μ + S/V)·n₊ ≤ boxQSum`) gives
`a0MainLocBox + ½(M₂/V²)Pc − ½(M₁/V²)(S²−S) + boxA2 − C·(a v)(μ+S/V)·n₊ ≤ boxQSum`; subtracting the
surplus `½(M₂−M₁)Pc/V²` leaves the nonnegative `½M₁(Pc − (S²−S))/V²`, which is the hypothesis
`hcS2` (`S²−S ≤ Pc`) together with `hM1nn` and `hvol`.  Finish with the PROVED `bqPotsplit`
(`sbPot = −μ·fibSum + pairSum`) and the source file's final `linarith`.

Consumed by Step L4 (design §3): the row `½s²(M₂−M₁) − ½(1+η)Dκ·s²` is what step 3 of the
normalised (`N = 1`) ledger needs.  Note (reviewer 1): this is the `boxPairCount`-form of the
surplus, which is `≥ ½(S²−S)(M₂−M₁)/V²`; the design's literal `½s²(M₂−M₁)` needs the extra
`½S(M₂−M₁)/V²`, so L4's error rows must absorb that (or L4 uses `Pc` directly). -/
theorem sbWordCube_ge_a0Main_surplus {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R : ℝ} (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
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
          Work.BoseFixB1.a0MainLocBox (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) μ
              (Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))
              (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ))
            + Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
              / (2 * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u ^ 2)
              * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h))
                - Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))
            + Work.BoseFixB1.boxA2 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ)
            + Work.BoseFixB1B.sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ)
            - C * (_root_.BoseGases.a v)
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
          ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  -- ## the PROVED sharp joint rung at the cube cutoff (the `n₀`-scalarised FS
  --    `lm:appinteractionestimate`), taken at `M = mValue` (the constant value of `paramsAt … .M`)
  obtain ⟨C, hC, hjoint⟩ :=
    Work.BoseFixB1S.a0A2QJointSharpImp (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨εg, hεg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨εg, C, hεg, hC, ?_⟩
  intro μ hAdm n Φ u hvol hμv hnorm hsupp hM1nn hM2 hPcnn hcS2
  -- ## expose the pair mass in the goal and normalise its spelling to the constant `mValue`
  rw [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB]
  rw [Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)] at hM1nn hM2 ⊢
  -- ## the sliding-box data
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hR16, hRχ⟩ := hreg μ hAdm.1 (Work.BoseFixB1.adm_dilute hAdm)
  have hMv : 1 ≤ Work.BoseBox.mValue := by norm_num [Work.BoseBox.mValue]
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hΦm : Measurable (Φ : Submission.BoseGases.X n → ℝ) := hΦc.measurable
  -- ## the two side hypotheses of the sharp rung: boundedness on the (compact) box, and the
  --    a.e. box-count identity, which is the a.e. box-support hypothesis for a.e. `Φ ≠ 0`
  obtain ⟨Cb, hCb⟩ :=
    (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  have hΦb : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      |(Φ : Submission.BoseGases.X n → ℝ) x| ≤ Cb := by
    intro x hx
    simpa [Real.norm_eq_abs] using hCb x hx
  have hcount : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
      Work.FockBridge.boxCount (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) x
        * ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
      = (n : ℝ) * ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
    filter_upwards [hsupp] with x hx
    by_cases h0 : (Φ : Submission.BoseGases.X n → ℝ) x = 0
    · simp [h0]
    · have hall : ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := hx h0
      have hbc : Work.FockBridge.boxCount (Submission.BoseGases.dlBox
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) x = (n : ℝ) := by
        rw [Work.FockBridge.boxCount_eq_sum_indicator]
        simp [hall]
      rw [hbc]
  -- ## the sharp rung at this state
  have hsh := hjoint (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ)
    hℓ hd hμ hR16 hRχ u hvol hμv (N := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ))
    hΦm (Cb := Cb) hΦb hnorm (c := (n : ℝ)) hcount hM1nn hM2 hPcnn hcS2
  -- ## the geometry of the sliding box
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hvolA : Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAc : Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      ⊆ Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :=
    Work.SmallBoxSliding.dlBox_subset_acube _ _ _
  -- ## the integrability bundle (proved, cycle-free copies of the corpus modules)
  obtain ⟨hint0, hint1, hint2, hint3, hint4, hint5⟩ :=
    Work.BoseFixB1.Clean.boxFragmentsIntegrable (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
      hMv hℓ hd hR16 hRχ u (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hΦc
  obtain ⟨hBlk, hSq, hCr⟩ :=
    Work.BoseFixB1.boxPairBlockIntegrable (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
      hMv hℓ hd hR16 hRχ u (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hΦc
  obtain ⟨hW2i, hFib⟩ :=
    Work.BoseFixB1.boxQ0SlackIntegrable (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
      hMv hℓ hd hR16 hRχ u
  -- ## the kernel identities (`w₁ = w(1−ω)`, `w₂ = w(1−ω²)`, symmetry of `w` and `ω`)
  have hw1 : ∀ x y : E3, Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y
      = Submission.BoseGases.wSmallPair Work.BoseBox.mValue
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y
        * (1 - Submission.BoseGases.omC (Classical.choose h) x y) := by
    intro x y
    rw [Work.BoseFixB1.wSmall1Pair_eq_mul h u x y]
    simp only [Submission.BoseGases.omC]
  have hw2 : ∀ x y : E3, Submission.BoseGases.wSmallPair Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h) x y
      = Submission.BoseGases.wSmallPair Work.BoseBox.mValue
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y
        * (1 - Submission.BoseGases.omC (Classical.choose h) x y ^ 2) := by
    intro x y
    rw [Work.BoseFixB1.wSmallPair_g2_eq_mul h u x y, Work.BoseFixB1.wSmall1Pair_eq_mul h u x y]
    simp only [Submission.BoseGases.omC]
    ring
  have hwsym : ∀ x y : E3, Submission.BoseGases.wSmallPair Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y
      = Submission.BoseGases.wSmallPair Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v y x :=
    fun x y => Submission.BoseGases.wSmallPair_symm hMv u (Submission.BoseGases.radial_even hvrad) x y
  have homsym : ∀ x y : E3, Submission.BoseGases.omC (Classical.choose h) x y
      = Submission.BoseGases.omC (Classical.choose h) y x := by
    intro x y
    have hw0 : ∀ z : E3, Classical.choose h (-z) = Classical.choose h z :=
      Submission.BoseGases.radial_even (Classical.choose_spec h).1
    simp only [Submission.BoseGases.omC]
    rw [show y - x = -(x - y) from by abel, hw0]
  -- ## (R1): the sum-level reduction `Qsum − A2 + (2μP + μQ) = Q0 + (Sq + L)`
  have hred0 := Work.BoseFixB1S.Clean.boxQSum_sub_boxA2_blockSum (N := n)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (volA := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (μ := μ) (A := Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    hℓ hvol hAmeas hvolA hAc
    (w := Submission.BoseGases.wSmallPair Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v)
    (w₁ := Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (w₂ := Submission.BoseGases.wSmallPair Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h))
    (om := Submission.BoseGases.omC (Classical.choose h))
    hw1 hw2 hwsym homsym hΦc hint0 hint1 hint2 hint3 hint4 hint5
  have hred1 := Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum (N := n)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (volA := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (A := Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (w := Submission.BoseGases.wSmallPair Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v)
    (w₁ := Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (om := Submission.BoseGases.omC (Classical.choose h))
    (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hSq hCr hBlk hw1
  -- ## the exact `A₀`-slack (the pair-condensate term with mass `M₂`)
  have hslack := Work.BoseFixB1.Clean.boxQ0_sub_a0MainLocBox_eq (N := n)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (volA := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (μ := μ) (A := Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    hℓ hvol hAmeas hvolA hAc hW2i hFib hΦc
  -- ## the potential split `sbPot = qLHSwordB = Qsum`
  have hpot := Work.BoseFixB1.bqPotsplit (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
    (M := Work.BoseBox.mValue) hMv
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ)
    hℓ hd hR16 hRχ u hvol (N := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hΦc
  -- ## the two scalar inputs
  have hVar : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
      - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) ^ 2
      + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) := by
    linarith [hcS2]
  have hrow := rowM1_le
    (V := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (μ := μ)
    (M1 := Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))
    (Pc := Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ))
    (S := Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ))
    hvol hM1nn hμv hVar
  have hid := pcb_sub_variance_eq_surplus
    (V := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (M1 := Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))
    (M2 := Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Submission.BoseGases.wSmallPair Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h)))
    (Pc := Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ))
    (S := Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ))
    hvol
  -- ## assembly
  linarith [hsh, hrow, hid, hred0, hred1, hslack, hpot]

end Work.BoseB1Cube
