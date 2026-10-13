/-
Copyright: work module for the Elgindi finite-time singularity project.

# Measurability of the source pairing for data given by `IsBslSol`

The transfer `Work.Spaces.HkMem α 0 F → Work.Spaces.L2Mem (F · w)` and the integrability of the
source pairing `z ↦ w z² ∫_θ |F z θ Φ z θ|` (the `hintG`/`hhint` hypothesis of the radial energy
identity) both need *measurability* of `F`, which the data class of the chapter does **not**
assume: the only hypothesis linking `F` to a smooth object is `IsBslSol α F Ψ`, i.e.
`bslOp α Ψ = F` on the *open* quadrant.

This module supplies it: `F` agrees with the smooth `bslOp α Ψ` off the boundary
`{z = 0} ∪ {θ = 0} ∪ {θ = π/2} ∪ (Iz × Iθ)ᶜ`, a null set for the product of the restricted
measures, so the two `AEStronglyMeasurable` statements follow from continuity of `bslOp α Ψ · Ψ`
on the open quadrant (hypothesis `hcont`, supplied by
`Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp`) and from
`AEStronglyMeasurable.integral_prod_right'`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

theorem measurable_w_sq : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
  have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
  rw [h]
  exact (((measurable_const.add measurable_id).pow_const 2).div
    (measurable_id.pow_const 2)).pow_const 2

/-- **The measurability input of the radial energy identity for a source `F` known only through
`IsBslSol`.**  Off the (null) boundary of the quadrant `F` agrees with `bslOp α Ψ`, so `|F · Ψ|`
is a.e. strongly measurable for the product of the restricted measures, and the angular integral
`z ↦ w z² ∫_θ |F z θ Ψ z θ|` is a.e. strongly measurable for `(dz)|_{Iz}`. -/
theorem aesm_abs_mul_and_w_sq_integral (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p.1 p.2 * Ψ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |F p.1 p.2 * Ψ p.1 p.2|)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ∧ MeasureTheory.AEStronglyMeasurable
          (fun z => (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, |F z θ * Ψ z θ|)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  set μz := MeasureTheory.volume.restrict Work.Spaces.Iz with hμz
  set μθ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hμθ
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hkey : ∀ p : ℝ × ℝ, p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ → p.1 ≠ 0 → p.2 ≠ 0 →
      p.2 ≠ π / 2 → Work.Elliptic.bslOp α Ψ p.1 p.2 = F p.1 p.2 := by
    rintro ⟨z, θ⟩ hp hz0 hθ0 hθπ
    obtain ⟨hz, hθ⟩ := hp
    exact hsol.1 z (lt_of_le_of_ne (Set.mem_Ici.mp hz) (Ne.symm hz0)) θ
      (lt_of_le_of_ne (Set.mem_Icc.mp hθ).1 (Ne.symm hθ0))
      (lt_of_le_of_ne (Set.mem_Icc.mp hθ).2 hθπ)
  have hsub : {p : ℝ × ℝ | Work.Elliptic.bslOp α Ψ p.1 p.2 ≠ F p.1 p.2} ⊆
      (({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}) ∪ {p : ℝ × ℝ | p.2 = π / 2})
        ∪ {p : ℝ × ℝ | p ∉ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ} := by
    rintro p hp
    by_cases hpI : p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
    · by_cases h1 : p.1 = 0
      · exact Or.inl (Or.inl (Or.inl h1))
      · by_cases h2 : p.2 = 0
        · exact Or.inl (Or.inl (Or.inr h2))
        · by_cases h3 : p.2 = π / 2
          · exact Or.inl (Or.inr h3)
          · exact absurd (hkey p hpI h1 h2 h3) hp
    · exact Or.inr hpI
  have hz0 : μz {0} = 0 := by simp [hμz]
  have hθ0 : μθ {0} = 0 := by simp [hμθ]
  have hθπ : μθ {π / 2} = 0 := by simp [hμθ]
  have hnull : μz.prod μθ ((({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0})
      ∪ {p : ℝ × ℝ | p.2 = π / 2})
      ∪ {p : ℝ × ℝ | p ∉ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ}) = 0 := by
    have hA : μz.prod μθ {p : ℝ × ℝ | p.1 = 0} = 0 := by
      rw [show {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ Set.univ from by ext p; simp,
        MeasureTheory.Measure.prod_prod ({0} : Set ℝ) Set.univ, hz0, zero_mul]
    have hB : μz.prod μθ {p : ℝ × ℝ | p.2 = 0} = 0 := by
      rw [show {p : ℝ × ℝ | p.2 = 0} = Set.univ ×ˢ ({0} : Set ℝ) from by ext p; simp,
        MeasureTheory.Measure.prod_prod Set.univ ({0} : Set ℝ), hθ0, mul_zero]
    have hC : μz.prod μθ {p : ℝ × ℝ | p.2 = π / 2} = 0 := by
      rw [show {p : ℝ × ℝ | p.2 = π / 2} = Set.univ ×ˢ ({π / 2} : Set ℝ) from by ext p; simp,
        MeasureTheory.Measure.prod_prod Set.univ ({π / 2} : Set ℝ), hθπ, mul_zero]
    have hAB : μz.prod μθ ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}) = 0 :=
      le_antisymm (le_trans (measure_union_le _ _) (by rw [hA, hB, add_zero])) bot_le
    have hD : μz.prod μθ {p : ℝ × ℝ | p ∉ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ} = 0 := by
      have hsub2 : {p : ℝ × ℝ | p ∉ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ} ⊆
          (Work.Spaces.Izᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Work.Spaces.Iθᶜ) := by
        rintro ⟨z, θ⟩ hp
        simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_union, Set.mem_compl_iff,
          Set.mem_univ, and_true, true_and] at hp ⊢
        tauto
      refine MeasureTheory.measure_mono_null hsub2 ?_
      have hE : μz.prod μθ (Work.Spaces.Izᶜ ×ˢ Set.univ) = 0 := by
        rw [MeasureTheory.Measure.prod_prod (Work.Spaces.Izᶜ) Set.univ, hμz,
          MeasureTheory.Measure.restrict_apply hIzm.compl, Set.compl_inter_self, measure_empty,
          zero_mul]
      have hF : μz.prod μθ (Set.univ ×ˢ Work.Spaces.Iθᶜ) = 0 := by
        rw [MeasureTheory.Measure.prod_prod Set.univ (Work.Spaces.Iθᶜ), hμθ,
          MeasureTheory.Measure.restrict_apply hIθm.compl, Set.compl_inter_self, measure_empty,
          mul_zero]
      exact le_antisymm (le_trans (measure_union_le _ _) (by rw [hE, hF, add_zero])) bot_le
    refine le_antisymm ?_ bot_le
    calc μz.prod μθ ((({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0})
        ∪ {p : ℝ × ℝ | p.2 = π / 2}) ∪ {p : ℝ × ℝ | p ∉ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ})
        ≤ μz.prod μθ (({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0})
            ∪ {p : ℝ × ℝ | p.2 = π / 2})
          + μz.prod μθ {p : ℝ × ℝ | p ∉ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ} := measure_union_le _ _
      _ ≤ (μz.prod μθ ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0})
            + μz.prod μθ {p : ℝ × ℝ | p.2 = π / 2}) + 0 := by
          rw [hD]
          exact add_le_add (measure_union_le _ _) le_rfl
      _ = 0 := by rw [hAB, hC, add_zero, add_zero]
  have hae : (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p.1 p.2) =ᵐ[μz.prod μθ]
      (fun p : ℝ × ℝ => F p.1 p.2) :=
    MeasureTheory.ae_iff.2 (MeasureTheory.measure_mono_null hsub hnull)
  have hAabs : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => |Work.Elliptic.bslOp α Ψ p.1 p.2 * Ψ p.1 p.2|) (μz.prod μθ) :=
    Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => |Work.Elliptic.bslOp α Ψ p.1 p.2 * Ψ p.1 p.2|) hcont.abs
  have hAeq : (fun p : ℝ × ℝ => |Work.Elliptic.bslOp α Ψ p.1 p.2 * Ψ p.1 p.2|)
      =ᵐ[μz.prod μθ] (fun p : ℝ × ℝ => |F p.1 p.2 * Ψ p.1 p.2|) :=
    hae.mono fun p hp => congrArg (fun x => |x * Ψ p.1 p.2|) hp
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => |F p.1 p.2 * Ψ p.1 p.2|) (μz.prod μθ) := hAabs.congr hAeq
  refine ⟨h1, ?_⟩
  exact (measurable_w_sq.aestronglyMeasurable).mul h1.integral_prod_right'

/-- Continuity of `bslOp α Ψ · Ψ` on the open quadrant, from `SmoothNbhd Ψ`: the hypothesis
`hcont` of `aesm_abs_mul_and_w_sq_integral`. -/
theorem continuousOn_bslOp_mul (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p.1 p.2 * Ψ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hb : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp α Ψ hΨ
  have hΨo : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.Cert.smoothNbhd_smoothOpen_bsl hΨ
  exact ((hb.forall 0).continuousOn).mul ((hΨo.forall 0).continuousOn)

/-- **The measurability input in the shape required by the field-extraction.**  This is the
statement of the placeholder `tmp_aesmF` of
`Submission/Work/FTS/EllipticEst/ellHyp_L2Mem_fields.lean`, with the continuity hypothesis
discharged: replacing that placeholder by

    exact Work.FTS.EllipticEst.aesm_abs_mul_and_w_sq_integral_uncond α F Ψ hsm hsol

leaves the file sorry-free. -/
theorem aesm_abs_mul_and_w_sq_integral_uncond (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |F p.1 p.2 * Ψ p.1 p.2|)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ∧ MeasureTheory.AEStronglyMeasurable
          (fun z => (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, |F z θ * Ψ z θ|)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  aesm_abs_mul_and_w_sq_integral α F Ψ (continuousOn_bslOp_mul α Ψ hsm) hsol

end Work.FTS.EllipticEst
