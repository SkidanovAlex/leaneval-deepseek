import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

/-!
# `EKLC6Core.Growth` — elementary facts about `growthFun`

`growthFun U ν t x = -log (ν x (conjBox U t)).toReal`.  The contracted box contains the identity
(`conjBox_nhds`), so a trivial leaf-wise measure gives zero growth.  This is the "easy half" of
Pisa 7.6(iii) that the `⇒` direction of `P_EntropyLeaf` needs (in contrapositive form).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The identity lies in the contracted box. -/
theorem one_mem_conjBox {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ) :
    (1 : SL3) ∈ conjBox U t := by
  obtain ⟨δ, hδ, hsub⟩ := conjBox_nhds hU t
  exact hsub 1 (by intro i j; simpa using hδ) U.one_mem

/-- A trivial leaf-wise measure has zero growth. -/
theorem growthFun_eq_zero_of_eq_dirac {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ)
    {ν : X3 → Measure SL3} (x : X3) (hx : ν x = Measure.dirac 1) :
    growthFun U ν t x = 0 := by
  rw [growthFun, hx, Measure.dirac_apply_of_mem (one_mem_conjBox hU t), ENNReal.toReal_one,
    Real.log_one, neg_zero]

/-- `Uij` is contracted by `aDiag t` when `t i < t j` (the `hcontr` hypothesis of
`ent_ge_growth`, in terms of elements rather than the parametrisation). -/
theorem tendsto_conj_mem_Uij (t : Fin 3 → ℝ) {i j : Fin 3} (hij : i ≠ j) (ht : t i < t j) :
    ∀ u ∈ Uij hij,
      Filter.Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) := by
  intro u hu
  have hu' : u ∈ Set.range (fun s : ℝ => uij hij s) := by
    rwa [← Work.EKLContract.Lemmas.Uij_range]
  obtain ⟨s, rfl⟩ := hu'
  exact Work.EKLContract.Lemmas.horoUij_tendsto_conj t hij ht s

/-- **U3 of `P_Leafwise`, extracted**: a leaf-wise system is trivial a.e. exactly on the
cross-sections of the corresponding subgroup.  This is the bridge between
`¬ CrossSection μ U` and the hypothesis `∀ᵐ x, ν x ≠ δ₁` of `growth_pos_of_nontrivial`. -/
theorem crossSection_iff_dirac_of_leafwise (hLeaf : Work.EKLContract.P_Leafwise)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hAinv : Work.EKLContract.IsAInvariant μ) {U : Subgroup Work.EKLContract.SL3}
    (hU : Work.EKLContract.IsHoro U)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.CrossSection μ U ↔ ∀ᵐ x ∂μ, ν x = MeasureTheory.Measure.dirac 1 := by
  obtain ⟨t0, ht0⟩ := hU.2.2
  have hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ := hAinv t0
  exact ((hLeaf μ U hU t0 hmp ht0).2 ν X' hL).2.2.1

end Work.EKLC6Core

end
