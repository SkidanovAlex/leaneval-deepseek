import Mathlib
import Submission.Work.EKLProd.ProdFlowerAssemblyDefs
import Submission.Work.EKLProd.ProdFlowerLemmas

namespace Work.EKLProd

open MeasureTheory Topology Filter
open Work.EKLContract

theorem prodFlowerLTP_apply {H T U : Subgroup Work.EKLContract.SL3} {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    (νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (x : Work.EKLContract.X3)
    {ψ : Work.EKLContract.SL3 → Work.EKLContract.SL3 × Work.EKLContract.SL3} (hψ : Measurable ψ)
    (hψae : ψ =ᵐ[Work.EKLProd.prodFlowerΛ hf n νH x]
      (fun g : Work.EKLContract.SL3 => (Work.EKLProd.hT T U g, Work.EKLProd.hU T U g)))
    {A B : Set Work.EKLContract.SL3} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Work.EKLProd.prodFlowerΛTP hf n νH x (A ×ˢ B) =
      (νH x) (Work.EKLContract.shape (hf.mH n) H x ∩
        {h : Work.EKLContract.SL3 | ψ (h * hf.co n x) ∈ A ×ˢ B}) := by
  have hmap : Measure.map ψ (prodFlowerΛ hf n νH x)
      = Measure.map (fun g : SL3 => (hT T U g, hU T U g)) (prodFlowerΛ hf n νH x) :=
    Measure.map_congr hψae
  rw [prodFlowerΛTP, ← hmap, Measure.map_apply hψ (hA.prod hB)]
  rw [prodFlowerΛ]
  rw [Measure.map_apply (continuous_mul_const (hf.co n x)).measurable
        ((hA.prod hB).preimage hψ)]
  rw [Measure.restrict_apply
        (((hA.prod hB).preimage hψ).preimage (continuous_mul_const (hf.co n x)).measurable)]
  congr 1
  ext h
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  tauto

end Work.EKLProd
