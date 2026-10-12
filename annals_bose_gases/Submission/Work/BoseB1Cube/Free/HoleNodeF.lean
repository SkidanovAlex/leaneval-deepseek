import ChallengeDeps
import Submission.Work.BoseB1Cube.Free.FlatArmF
import Submission.Work.BoseB1Cube.Free.GapArmF
import Submission.Work.BoseB1Cube.Free.Props
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.smallWinHolePD` — THE single remaining Bose node

Installation of §2 of the lead's design `sources/boseCubeEndgame/bose_cube_endgame.md`
(+ `.lean`) into this area, with clash-free names in `Work.BoseB1Cube`:

* `SmallWinHolePDF v h` — the hole row of `Work.BoseB1Cube.SmallWinNode`, in its **weakest filed
  form**: (a) the threshold `c₀` is chosen *per window constant* `Cn` (the uniform
  `∃c₀ ∀Cn` of `smallWinHoleRow` is a gratuitous strengthening — reviewer 1's fix), and (b) the
  state is **pair-dead** (`pairSum − μ·fibSum < demand`), the complementary case being the PROVED
  pair arm `Work.BoseB1Cube.sbWordCube_ge_demand_of_pairSum`.
  This is also L15600's `HoleRowOnePD` at the node's window `[Cnμ|B|, 2Cnμ|B|]` (rather than
  `[4μ|B|, 5μ|B|)`), normalised, in the `b*` vocabulary — so one proof serves both routes.
* `smallWinPropF_of_holePDF : SmallWinHolePDF v h → SmallWinPropF v h R` — **PROVED**: the gap arm
  (`smallWinGapArmGenF` at `c = min c₀ 10⁻⁶`), the flat arm (`flatArm37RowNodeF`, itself PROVED) and
  the pair arm (`sbWordCube_ge_demand_of_pairSum`).

With it, `Work.BoseB1Cube.SmallWinNode` (`Submission/Work/BoseB1Cube/SmallWinNode.lean`) has exactly
one open leaf: `SmallWinHolePDF v h`.  See `FINDING_SmallWinNode_session3.md` for the four routes
through it that are recorded as short/false, and for the box-data form it is equivalent to.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The one remaining Bose node (merged hole row, pair-dead form).**  `SmallWinNode`'s hole arm,
with (a) the threshold `c₀` chosen *per window constant* `Cn`, and (b) the extra hypothesis that the
state is *pair-dead* — the complementary case is the PROVED pair arm
`Work.BoseB1Cube.sbWordCube_ge_demand_of_pairSum`. -/
def SmallWinHolePDF (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ c₀ ε₀ : ℝ, 0 < c₀ ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        Work.BoseFixB1.bQ v μ Ψ u < c₀ →
        ¬ Work.BoseB1Cube.FlatArm37 v h μ n Ψ u →
        Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Ψ
            - μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Ψ
          < (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **PROVED reduction**: the merged hole node closes `SmallWinPropF` (gap arm
`smallWinGapArmGenF` at `c = min c₀ 10⁻⁶`, flat arm `flatArm37RowNodeF`, pair arm
`sbWordCube_ge_demand_of_pairSum` with the regime from `regime_sideAt_ge`). -/
theorem smallWinPropF_of_holePDF {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hPD : SmallWinHolePDF v h) : Work.BoseB1Cube.SmallWinPropF v h R := by
  intro Cn hCn
  obtain ⟨c₀, εh, hc₀, hεh, hhole⟩ := hPD Cn hCn
  set c : ℝ := min c₀ (1 / 10 ^ 6) with hcdef
  have hcpos : 0 < c := lt_min hc₀ (by norm_num)
  obtain ⟨εg, hεg, hgap⟩ :=
    Work.BoseB1Cube.smallWinGapArmGenF (v := v) h hv hv1 hvrad hR hv_supp hav Cn hCn c hcpos
  obtain ⟨εf, hεf, hflat⟩ :=
    Work.BoseB1Cube.flatArm37RowNodeF (v := v) h hv hv1 hvrad hR hv_supp hav Cn hCn
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min (min εg εf) (min εh εr), lt_min (lt_min hεg hεf) (lt_min hεh hεr), ?_⟩
  intro μ hAdm n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
  have hAg : Work.BoseBoxFix.Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAf : Work.BoseBoxFix.Adm v εf μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAh : Work.BoseBoxFix.Adm v εh μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  by_cases hQ : c ≤ Work.BoseFixB1.bQ v μ Ψ u
  · exact hgap μ hAg n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2 hQ
  · have hQlt : Work.BoseFixB1.bQ v μ Ψ u < c := lt_of_not_ge hQ
    by_cases hF : Work.BoseB1Cube.FlatArm37 v h μ n Ψ u
    · exact hflat μ hAf n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
        (lt_of_lt_of_le hQlt (min_le_right _ _)) hF
    · by_cases hpd : Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ
          - μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ
          < (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
      · exact hhole μ hAh n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
          (lt_of_lt_of_le hQlt (min_le_left _ _)) hF hpd
      · have hμpos : 0 < μ := hAdm.1
        have hAr : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr :=
          le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
        obtain ⟨hRd, hRχ⟩ := hreg μ hμpos hAr
        exact Work.BoseB1Cube.sbWordCube_ge_demand_of_pairSum (R := R) (εr := _) hv_supp hR
          hv hvrad hv1 hAdm hRd hRχ hΨc.continuous u (le_of_not_gt hpd)

end Work.BoseB1Cube
