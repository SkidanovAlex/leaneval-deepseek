import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top angular slot `Tk` only sees the values of `f` on the open quadrant

`Tk α k f = ∫_0^∞ ∫_0^{π/2} (D_θ^k f · W)² dθ dz` is the iterated integral over the closed
quadrant `[0,∞) × [0,π/2]` of a function whose pointwise value at an *interior* point
`z > 0`, `0 < θ < π/2` only depends on the values of `f` near that point.  Hence if two
functions agree on the open quadrant `(0,∞) × (0,π/2)`, then `D_θ^k f` and `D_θ^k g` agree
there (`Work.FTS.EllipticEst.AgreeOnQ.DthIter`), so the two integrands agree off the null
set `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}` and the iterated integrals coincide.

This mirrors `Work.FTS.EllipticEst.HkSq_congr_open`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllipticEst.remov.Baux

/-- Two integrands that agree on the open quadrant have the same iterated integral over
`[0,∞) × [0,π/2]`: the difference set is `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`. -/
private lemma pairIntegral_congr_of_openQuadrant {φ ψ : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → φ z θ = ψ z θ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, φ z θ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ψ z θ := by
  -- For each `z > 0` the two inner integrands agree off the two endpoints `θ = 0`,
  -- `θ = π/2` of `[0,π/2]`.
  have hinner : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, φ z θ) = ∫ θ in Work.Spaces.Iθ, ψ z θ := by
    intro z hz
    apply integral_congr_ae
    show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), φ z θ = ψ z θ
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ) ∪ {Real.pi / 2}) ?_ ?_
    · intro θ hθ
      simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Icc, Work.Spaces.Iθ,
        Set.mem_union, Set.mem_singleton_iff] at hθ ⊢
      obtain ⟨⟨h0, h1⟩, hne⟩ := hθ
      rcases eq_or_lt_of_le h0 with h0' | h0'
      · exact Or.inl h0'.symm
      · refine Or.inr ?_
        by_contra h2
        exact hne (h z θ hz h0' (lt_of_le_of_ne h1 h2))
    · exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
        (MeasureTheory.measure_singleton (Real.pi / 2))
  -- The outer integrands then agree for every `z ∈ [0,∞)` with `z ≠ 0`.
  apply integral_congr_ae
  show ∀ᵐ a ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, φ a θ) = ∫ θ in Work.Spaces.Iθ, ψ a θ
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ)) ?_
    (MeasureTheory.measure_singleton 0)
  intro z hz
  simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Ici, Work.Spaces.Iz,
    Set.mem_singleton_iff] at hz ⊢
  obtain ⟨h0, hne⟩ := hz
  by_contra h1
  exact hne (hinner z (lt_of_le_of_ne h0 (Ne.symm h1)))

/-- `D_θ^k f` and `D_θ^k g` agree on the open quadrant when `f` and `g` do. -/
private lemma mixed_zero_congr {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed 0 k f z θ = Work.Spaces.mixed 0 k g z θ :=
  (show Work.FTS.EllipticEst.AgreeOnQ f g from h).mixed 0 k

theorem Tk_congr_open {k : ℕ} {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.remov.Step.Tk α k f = Work.FTS.EllipticEst.remov.Step.Tk α k g := by
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.mixed 0 k g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    intro z θ hz hθ hlt
    rw [mixed_zero_congr h z θ hz hθ hlt]
  show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2)
    = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed 0 k g z θ * Work.Spaces.Wt α z θ) ^ 2
  exact pairIntegral_congr_of_openQuadrant hpt

end Work.FTS.EllipticEst.remov.Baux
