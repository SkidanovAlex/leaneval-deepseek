import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.LeafCtor
import Submission.Work.EKLRelCross.glue_pieces
import Submission.Work.EKLRelCross.FlowerCopy.LocalInput
import Submission.Work.EKLRelCross.flowerData_of_localFlower
import Submission.Work.EKLRelCross.leafwise_base_fields_free
import Submission.Work.EKLRelCross.leafwise_measurable_field_free
import Submission.Work.EKLRelCross.leafwise_equivariant_field_free
import Submission.Work.EKLRelCross.condexp_field_free
import Submission.Work.EKLRelCross.free_orbits_of_contracting

/-!
# `Work.EKLRelCross.leafwise_exists`

Pisa Theorem 6.3: for a horospherical subgroup `U ≤ SL₃(ℝ)`, a probability measure `μ` on the
space of lattices `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by the diagonal element `aDiag t0` and contracted
by it along `U`, there is a system of leaf-wise measures `ν : X₃ → Measure SL₃` on a conull set
`X'`, i.e. an `IsLeafwise μ U ν X'`.

## The construction

The leaf-wise measures are the patched family `nuFull U μ D.Z D.m D.G` of `LeafCtor.lean`, built
from a countable family of flowers `D : FlowerData U μ` (Pisa 6.14/6.15): for each level `k` the
conditional measures of the flowers of level `k`, pushed to the group `U` and normalised on
`Box1 U`, are patched over the annuli `piece U k`.

## The inputs

* the flower family exists by Pisa 6.7 + 6.9–6.15: the local flower
  (`Work.EKLRelCross.W.W_flower_local`, via `FlowerCopy/LocalInput.localFlowerInput_of`) plus the
  countable cover by a fixed countable basis of `X₃` gives `FlowerData`
  (`flowerData_of_localFlower`);
* Pisa 5.17 + 6.17 (`ProporPiece`, from `Work.EKLComp.plaque_propor`) and Pisa 6.20
  (`PosPiece`, from `Work.EKLComp.condExpKernel_pos`) — `glue_pieces`;
* a.e. freeness of the `U`-orbits (`free_orbits_of_contracting`, Poincaré recurrence).

## The nine fields of `IsLeafwise`

* `meas_dom`/`conull` and the pointwise fields `radon`, `carried`, `normalised`, `pos`:
  `leafwise_base_fields_free`;
* `measurable`: `leafwise_measurable_field_free`;
* `equivariant`: `leafwise_equivariant_field_free`;
* `condexp`: `condexp_field_free`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- Almost every `U`-orbit is free, in the form of injectivity of the orbit map on `U`
(equivalent to the pointwise form `u • x = x → u = 1` used by `ae_free_orbit`). -/
theorem leafwise_exists_ae_injective {U : Subgroup Work.EKLContract.SL3}
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (h : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1) :
    ∀ᵐ x ∂μ, Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x) := by
  filter_upwards [h] with x hx u₁ u₂ h12
  have h12' : (u₁ : Work.EKLContract.SL3) • x = (u₂ : Work.EKLContract.SL3) • x := h12
  have h2 : (((u₂⁻¹ * u₁ : U)) : Work.EKLContract.SL3) • x = x := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h12', inv_smul_smul]
  have h3 : (((u₂⁻¹ * u₁ : U)) : Work.EKLContract.SL3) = 1 :=
    hx ((u₂⁻¹ * u₁ : U)) (u₂⁻¹ * u₁).2 h2
  have h4 : (u₂⁻¹ * u₁ : U) = 1 := Subtype.ext h3
  calc u₁ = u₂ * (u₂⁻¹ * u₁) := by group
    _ = u₂ * 1 := by rw [h4]
    _ = u₂ := mul_one u₂

theorem leafwise_exists (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1)) :
    ∃ (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3), Work.EKLContract.IsLeafwise μ U ν X' := by
  classical
  -- a.e. freeness of the `U`-orbits, in the pointwise and the injective form
  have hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 :=
    free_orbits_of_contracting h2 hU t0 ht0 hcontr
  have hinj : ∀ᵐ x ∂μ,
      Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x) :=
    leafwise_exists_ae_injective hfree
  -- the flower family, and the two measure-theoretic inputs (Pisa 5.17 + 6.17, Pisa 6.20)
  obtain ⟨D⟩ := flowerData_of_localFlower (localFlowerInput_of h2 hU) hfree
  have hprop : ProporPiece U μ := proporPiece_of_horo hU
  have hpos : PosPiece U μ := posPiece_of_horo hU
  -- the fields of `IsLeafwise`: the base fields, and the equivariance
  obtain ⟨X₁, hX₁meas, hX₁null, -, hX₁⟩ := leafwise_base_fields_free hU.1 D hpos hinj
  obtain ⟨X₂, hX₂meas, hX₂null, -, hX₂⟩ := leafwise_equivariant_field_free hU.1 D hprop hpos hinj
  refine ⟨nuFull U μ D.Z D.m D.G, X₁ ∩ X₂, hX₁meas.inter hX₂meas, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.compl_inter]
    exact measure_union_null hX₁null hX₂null
  · intro x hx; exact (hX₁ x hx.1).1
  · intro x hx; exact (hX₁ x hx.1).2.1
  · intro x hx; exact (hX₁ x hx.1).2.2.1
  · intro f; exact leafwise_measurable_field_free hU.1 D hinj f
  · intro x hx δ hδ; exact (hX₁ x hx.1).2.2.2 δ hδ
  · intro x hx u hu hux; exact hX₂ x hx.2 u hu hux.2
  · exact condexp_field_free U hU.1 D hprop hpos hinj

end Work.EKLRelCross
