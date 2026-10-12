import ChallengeDeps
import Submission.Work.BoseB1Cube.AdmGate
import Submission.Work.BoseB1Cube.CutSmallBPort
import Submission.Work.BoseB1Cube.cubeKinPeel
import Submission.Work.BoseFixB1B.fibreWord_tendsto_cutProd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem tendsto_sbWordCube_cutProd {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3), u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) μ →
      ∀ (k : ℕ) (ψ : Submission.BoseGases.X k → ℝ) {K Cb : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ},
        ContDiff ℝ (⊤ : ENat) ψ → 0 ≤ Cb →
        (∀ x ∈ Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), |ψ x| ≤ Cb) →
        Work.BoseFixB1B.IsCutFamily (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u K γ →
        Filter.Tendsto (fun δ : ℝ =>
            Work.BoseFixB1B.sbWordCube v h μ u (Work.BoseFixB1B.cutProd (γ δ) ψ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (Work.BoseFixB1B.sbWordCube v h μ u
            (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u) ψ))) := by
  obtain ⟨ε₀, hε₀, hGate⟩ := admGate (v := v) (R := R) hR hav
  refine ⟨ε₀, hε₀, fun μ hμ => ?_⟩
  intro u hu k ψ K Cb γ hψ hCb hψb hcut
  -- the parameter facts (from the diluteness gate)
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := (hGate μ hμ).2.1
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := (hGate μ hμ).2.2.1
  have hM : 4 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := (hGate μ hμ).2.2.2.1
  have hRd : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 := (hGate μ hμ).2.2.2.2.1
  have hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 :=
    (hGate μ hμ).2.2.2.2.2
  -- the potential integrability
  have hpot := admGate_integrable_qLHSden (v := v) (h := h) (R := R) (ε₀ := ε₀) (k := k)
    hR hav hv1 hv_supp hε₀ hμ hRd hRχ u
  -- the three convergences
  have h1 := (Work.BoseFixB1B.tendsto_cnPlusBoxInd_cutSharp (k := k)
      (L := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (u := u)
      hℓ hd hcut hψ hCb hψb).const_mul (Work.BoseFixB1.bGapCoeff v μ)
  have h2 := Work.BoseB1Cube.CutPort.tendsto_tBdiagFormInd_cutSmallB (k := k)
    (L := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hℓ hd hM u hcut hψ hCb hψb
  have h3 := Work.BoseFixB1B.tendsto_qLHSwordB_cutProd (v := v) (h := h)
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) (k := k)
    (L := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ) (u := u)
    hℓ hd hcut hψ hCb hψb hpot
  have hall := (h1.add h2).add h3
  simpa only [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube, Work.BoseFixB1B.cubeSpectral,
    Work.UBBInputs8.tBwordKinInd, Work.BoseFixB1.sbPot, Work.BoseFixB1.bM, Work.BoseFixB1.bSide,
    Work.BoseFixB1.bD, Work.BoseFixB1.bA, Work.BoseFixB1.bV] using hall

end Work.BoseB1Cube
