import Mathlib
import Submission.Work.EKLProd.ProdFlowerAssemblyDefs
import Submission.Work.EKLRelProduct.Defs
import Submission.Work.EKLRelProduct.measurable_hT_hU_pair

/-!
# `Work.EKLRelProduct.map_snd_prodFlowerLambdaTP_eq_uMarg`

The `U`-marginal of the joint `(T,U)`-law `prodFlowerΛTP` of the plaque coordinate is the
pushforward `uMarg` of the shape measure `(νH x) ↾ shape (mH n) H x` under the `U`-part of the
plaque coordinate `co n` of the flower.

The only mathematical ingredient is `ProdFlowerFam.co_smul`: inside the shape
`shape (mH n) H x = {h ∈ H | h • x ∈ atom (mH n) x}` the coordinate satisfies
`co n (h • x) = h * co n x`, so `hU T U (co n (h • x)) = hU T U (h * co n x)` and the two
`Measure.map`s of the *same* restricted measure coincide.  Measurability of the maps involved
comes from `Work.EKLRelProduct.measurable_hT_hU_pair`, and measurability of the shape from the
`IsPlaqueAlgebra` field of the flower (`shape = O ∩ H` with `O` open and `H` closed).
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelProduct

open Work.EKLContract Work.EKLProd

/-- The `U`-marginal of the joint `(T,U)`-law `prodFlowerΛTP hf n νH x` is the pushforward of
`(νH x) ↾ shape (mH n) H x` under `h ↦ hU T U (co n (h • x))`, i.e. the `uMarg` of the `U`-side
development.  This is `Measure.map_map` plus the identity
`hU T U (co n (h • x)) = hU T U (h * co n x)` on the shape, supplied by `co_smul`. -/
theorem map_snd_prodFlowerLambdaTP_eq_uMarg {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    (νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    {x : Work.EKLContract.X3} (hx : x ∈ hf.Z n) :
    (Work.EKLProd.prodFlowerΛTP hf n νH x).map Prod.snd
      = Work.EKLRelProduct.uMarg hf νH n x := by
  classical
  have hpair : Measurable (fun g : Work.EKLContract.SL3 =>
      (Work.EKLProd.hT T U g, Work.EKLProd.hU T U g)) :=
    Work.EKLRelProduct.measurable_hT_hU_pair hTH hUH hnorm hcop hdisj hHc hTc hUc
  have hUmeas : Measurable (fun g : Work.EKLContract.SL3 => Work.EKLProd.hU T U g) :=
    measurable_snd.comp hpair
  have hSmeas : MeasurableSet (Work.EKLContract.shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOsh⟩ := ((hf.plaqH n).2.2.2 x hx).2.2.1
    rw [hOsh]
    exact hOo.measurableSet.inter hHc.measurableSet
  have hcoe : ∀ h ∈ Work.EKLContract.shape (hf.mH n) H x,
      Work.EKLProd.hU T U (h * hf.co n x) = Work.EKLProd.hU T U (hf.co n (h • x)) := by
    intro h hh
    rw [hf.co_smul n x hx h hh.1 hh.2]
  calc (Work.EKLProd.prodFlowerΛTP hf n νH x).map Prod.snd
      = (Work.EKLProd.prodFlowerΛ hf n νH x).map
          (fun g : Work.EKLContract.SL3 => Work.EKLProd.hU T U g) := by
        rw [Work.EKLProd.prodFlowerΛTP, MeasureTheory.Measure.map_map measurable_snd hpair]
        rfl
    _ = (((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)).map
          (fun h : Work.EKLContract.SL3 => h * hf.co n x)).map
            (fun g : Work.EKLContract.SL3 => Work.EKLProd.hU T U g) := by
        rw [Work.EKLProd.prodFlowerΛ]
    _ = ((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)).map
          ((fun g : Work.EKLContract.SL3 => Work.EKLProd.hU T U g) ∘
            (fun h : Work.EKLContract.SL3 => h * hf.co n x)) := by
        rw [MeasureTheory.Measure.map_map hUmeas (continuous_mul_const (hf.co n x)).measurable]
    _ = ((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)).map
          (fun h => Work.EKLProd.hU T U (hf.co n (h • x))) := by
        have hae : ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)),
            ((fun g : Work.EKLContract.SL3 => Work.EKLProd.hU T U g) ∘
              (fun h : Work.EKLContract.SL3 => h * hf.co n x)) h
              = Work.EKLProd.hU T U (hf.co n (h • x)) := by
          rw [MeasureTheory.ae_restrict_iff' hSmeas]
          exact Filter.Eventually.of_forall (fun h hh => hcoe h hh)
        exact MeasureTheory.Measure.map_congr hae
    _ = Work.EKLRelProduct.uMarg hf νH n x := by rw [Work.EKLRelProduct.uMarg]

end Work.EKLRelProduct
