import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.growth_le_atomInfo_sandwich
import Submission.Work.EKLC6Core.lintegral_atomInfo_le
import Submission.Work.EKLC6Core.atomInfo_aemeasurable
import Submission.Work.EKLC6Core.ent_ge_HcondSig_le
import Submission.Work.EKLContract.All

/-!
# `EKLC6Core.ent_ge_growth_assembly` — the chain, with the geometry isolated

`ent_ge_growth` follows by chaining

`ofReal (∫ growthFun) ≤ ∫⁻ ofReal ∘ atomInfo ≤ HcondSig μ A (comap (aDiag t ·) A) ≤ ent μ (aDiag t ·)`

where the three links are `growth_le_atomInfo_sandwich`, `lintegral_atomInfo_le` and
`ent_ge_HcondSig_le`.  This file performs the assembly from the *geometry package*

* `A`, `Z` with `IsPlaqueAlgebra U Z A`, `comap (aDiag t ·) A ≤ A`, `μ Zᶜ = 0`
  (from `EKLC6Core.exists_desc_subordinate`, still being closed by the C6 prover), and
* a countable "good family" `Y k` with radii `δ k`, `R k` on which the atom shapes are
  `δ k`-comparable to balls and which is visited infinitely often a.e.
  (from `EKLC6Core.goodset_of_cut`, which turns the null leaf-cut `C` of the geometry into
  such a family).

So the only remaining mathematical inputs are the *geometric* ones; everything analytic is
proved.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The chain**, conditional on the geometry package. -/
theorem ent_ge_growth_of_goodset {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ X''ᶜ = 0)
    (t : Fin 3 → ℝ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (hAinv : Work.EKLContract.IsAInvariant μ)
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun U ν t) μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    (hdec : MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hZ : μ Zᶜ = 0)
    {Y : ℕ → Set Work.EKLContract.X3} {δ R : ℕ → ℝ}
    (hYmeas : ∀ k : ℕ, @MeasurableSet Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 (Y k))
    (hδ : ∀ k, 0 < δ k) (hR : ∀ k, 0 < R k)
    (hY : ∀ (k : ℕ) (y : Work.EKLContract.X3), y ∈ Y k →
      (Work.EKLContract.V (δ k) ∩ (U : Set Work.EKLContract.SL3)) ⊆
          Work.EKLContract.shape A U y ∧
        Work.EKLContract.shape A U y ⊆ Work.EKLContract.V (R k))
    (hvisit : ∀ᵐ x ∂μ, ∃ k : ℕ, ∃ᶠ n in Filter.atTop,
      (Work.EKLContract.aDiag t ^ n) • x ∈ Y k) :
    ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun U ν t x ∂μ) ≤
      @Work.EKLContract.ent Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) := by
  have hmp := hAinv t
  have h1 := growth_le_atomInfo_sandwich (t := t) hL hU hcov hX'' hAinv hint hcontr hplaq
    hdec hZ (atomInfo_aemeasurable (t := t) hL hU hplaq) hYmeas hδ hR hY hvisit
  have h2 := lintegral_atomInfo_le (t := t) hL hU hcov hX'' hAinv hplaq hdec hZ
  have h3 := @ent_ge_HcondSig_le Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ _
    (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) hmp A hdec
  exact le_trans h1 (le_trans h2 h3)

end Work.EKLC6Core

end
