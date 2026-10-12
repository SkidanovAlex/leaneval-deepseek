import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.tendsto_cnPlusBoxInd_cutSharp
import Submission.Work.BoseFixB1B.tendsto_qLHSwordB_cutProd
import Submission.Work.BoseFixB1B.tendsto_tBdiagFormInd_cutB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

theorem fibreWord_tendsto_cutProd {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (M k : ℕ) (L d ε c μ : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : Submission.BoseGases.X k → ℝ} {K Cb : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hL : 0 < L) (hd : 0 < d)
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox k L, |ψ x| ≤ Cb)
    (hpot : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X k =>
        Submission.BoseGases.qLHSden k L μ (Submission.BoseGases.wSmallPair M L d u v)
          (Submission.BoseGases.wSmall1Pair h M L d u) x) (Submission.BoseGases.abox k L)) :
    Filter.Tendsto (fun δ : ℝ => Work.SlotWord.fibreWord h M k L d ε c μ u
        (Work.BoseFixB1B.cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Work.SlotWord.fibreWord h M k L d ε c μ u
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))) := by
  have hkin : Filter.Tendsto (fun δ : ℝ => Work.UBBInputs8.tBwordBInd k L d ε c u
      (Work.BoseFixB1B.cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Work.UBBInputs8.tBwordBInd k L d ε c u
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))) := by
    have hgap := (tendsto_cnPlusBoxInd_cutSharp (k := k) (L := L) (d := d) (u := u)
      (ψ := ψ) (K := K) (Cb := Cb) hL hd hcut hψ hCb hψb).const_mul
      (Work.SmallBoxTBWord.tbGapCoeff (L * d) ε)
    have hspec := tendsto_tBdiagFormInd_cutB (k := k) (L := L) (d := d) (c := c) (u := u)
      (ψ := ψ) (K := K) (Cb := Cb) hL hd hcut hψ hCb hψb
    have h := hgap.add hspec
    simpa only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
      Work.UBBInputs8.tBwordKinInd] using h
  have hpot' := tendsto_qLHSwordB_cutProd (v := v) (h := h) (M := M) (k := k) (L := L) (d := d)
    (μ := μ) (u := u) (ψ := ψ) (K := K) (Cb := Cb) hL hd hcut hψ hCb hψb hpot
  have h := hkin.add hpot'
  simpa only [Work.SlotWord.fibreWord] using h

end Work.BoseFixB1B
