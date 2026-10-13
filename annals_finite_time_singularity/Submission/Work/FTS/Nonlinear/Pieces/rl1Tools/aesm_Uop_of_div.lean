/-
# `aesm_Uop_of_div` — dividing by `s2 θ = sin(2θ)` loses no measurability

If the quotient `(z,θ) ↦ Uop α Ψ z θ / s2 θ` is a.e. strongly measurable for the product
measure `QdMeas = volume ↾ (0,∞) ⊗ volume ↾ Iθ`, then so is `(z,θ) ↦ Uop α Ψ z θ`.

The point is that the divisor `s2 θ = sin(2θ)` depends on `θ` alone and vanishes only on the
countable set `{nπ/2 : n ∈ ℤ}`, which is null for `volume ↾ Iθ` (and `Iθ = [0,π/2]`
contributes only `θ = 0` and `θ = π/2` to it).  Hence `QdMeas`-a.e. the division is
invertible, `Uop α Ψ = (Uop α Ψ / s2) * s2`, and the right-hand side is a.e. strongly
measurable as a product of two such functions.
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.QuadMeasAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

theorem aesm_Uop_of_div {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (Work.Construction.Uop α Ψ))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas := by
  -- `s2 θ = sin(2θ)` is continuous
  have hs2cont : Continuous fun θ : ℝ => Work.Construction.s2 θ := by
    simp only [Work.Construction.s2]; fun_prop
  -- its zero set is countable, hence null
  have hzero : MeasureTheory.volume {θ : ℝ | Work.Construction.s2 θ = 0} = 0 := by
    have hsub : {θ : ℝ | Work.Construction.s2 θ = 0}
        ⊆ Set.range (fun n : ℤ => (n : ℝ) * π / 2) := by
      intro θ hθ
      change Work.Construction.s2 θ = 0 at hθ
      simp only [Work.Construction.s2] at hθ
      rw [Real.sin_eq_zero_iff] at hθ
      obtain ⟨n, hn⟩ := hθ
      refine ⟨n, ?_⟩
      rw [div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)]
      linarith
    exact measure_mono_null hsub ((Set.countable_range _).measure_zero MeasureTheory.volume)
  -- the same set is null for `volume ↾ Iθ`
  have hIθzero : (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      {θ : ℝ | Work.Construction.s2 θ = 0} = 0 := by
    rw [MeasureTheory.Measure.restrict_apply (t := {θ : ℝ | Work.Construction.s2 θ = 0})
      (hs2cont.measurable (measurableSet_singleton 0))]
    exact measure_mono_null Set.inter_subset_left hzero
  have hsin : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Construction.s2 θ ≠ 0 := by
    rw [MeasureTheory.ae_iff,
      show {θ : ℝ | ¬ Work.Construction.s2 θ ≠ 0}
          = {θ : ℝ | Work.Construction.s2 θ = 0} from by
        ext θ; simp only [ne_eq, not_not]]
    exact hIθzero
  -- hence `s2 p.2 ≠ 0` for `QdMeas`-a.e. `p`
  have hmeasP : MeasurableSet {p : ℝ × ℝ | Work.Construction.s2 p.2 ≠ 0} :=
    (hs2cont.measurable.comp measurable_snd) ((measurableSet_singleton (0 : ℝ)).compl)
  have hae : ∀ᵐ p ∂QdMeas, Work.Construction.s2 p.2 ≠ 0 := by
    rw [QdMeas, MeasureTheory.Measure.ae_prod_iff_ae_ae hmeasP]
    exact Filter.Eventually.of_forall fun _ => hsin
  -- on that full-measure set the division can be undone
  have hEq : (fun p : ℝ × ℝ => Function.uncurry (fun z θ =>
        Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) p * Work.Construction.s2 p.2)
      =ᵐ[QdMeas] (fun p : ℝ × ℝ => Function.uncurry (Work.Construction.Uop α Ψ) p) := by
    filter_upwards [hae] with p hp
    show (Work.Construction.Uop α Ψ p.1 p.2 / Work.Construction.s2 p.2)
        * Work.Construction.s2 p.2 = Work.Construction.Uop α Ψ p.1 p.2
    exact div_mul_cancel₀ _ hp
  have hK : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Construction.s2 p.2)
      QdMeas := (hs2cont.measurable.comp measurable_snd).aestronglyMeasurable
  exact (h.mul hK).congr hEq

end Work.FTS.Nonlinear.Pieces.rl1Tools
