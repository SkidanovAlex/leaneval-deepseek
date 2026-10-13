import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.slice_ang_outer
import Submission.Work.FTS.EllipticEst.remov.slice_ang_split

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `slice_ang_gen`: reduction to the far region `[3π/8, π/2]`

This file reduces the target `Work.FTS.EllipticEst.remov.slice_ang_gen` to

* the **outer region** `Icc 0 (3π/8)`, which is *proved* in
  `Submission/Work/FTS/EllipticEst/remov/slice_ang_outer.lean` (via the two pointwise bounds
  `near_pointwise_bound` / `mid_pointwise_bound`), and
* the **far region** `Icc (3π/8) (π/2)`, which is the only remaining input
  (`SliceAngFar` below; see `NOTES_slice_ang_gen_REFINED.md` for its structure and the two
  remaining obstructions).

The reduction itself is the interval splitting `Iθ = Icc 0 (3π/8) ∪ Icc (3π/8) (π/2)` (the two
pieces overlap only in the null set `{3π/8}`), which is the proved lemma
`remov/slice_ang_split`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- The right hand side `R` of the target estimate. -/
noncomputable def AngRHS (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
    + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
        (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
    + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
    + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
    + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)

/-- The **far-region input**: the target's estimate restricted to `Icc (3π/8) (π/2)`, with the
same (`Iθ`-) right hand side. -/
def SliceAngFar (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * AngRHS k γ u g

/-- **The target, given the far region.**  `slice_ang_gen` follows from the proved outer-region
estimate (`remov/slice_ang_outer`) and the far-region input `SliceAngFar`. -/
theorem slice_ang_gen_of_far (k : ℕ) (hk : 2 ≤ k) (hfar : SliceAngFar k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * AngRHS k γ u g := by
  obtain ⟨C₂, hC₂, hfar'⟩ := hfar
  obtain ⟨C₁, hC₁, houter⟩ := slice_ang_outer k hk
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro γ u g hγ1 hγ2 hu hcont hu0 hupi hg hInt_k2 hInt_gk hInt_high hInt_2 hInt_1 hInt_0
  have hsplit := slice_ang_split k γ hInt_k2
  have ho := houter γ u g hγ1 hγ2 hu hcont hu0 hupi hg
    hInt_k2 hInt_gk hInt_high hInt_2 hInt_1 hInt_0
  have hf := hfar' γ u g hγ1 hγ2 hu hcont hu0 hupi hg
    hInt_k2 hInt_gk hInt_high hInt_2 hInt_1 hInt_0
  rw [hsplit]
  calc (∫ θ in Set.Icc 0 (3 * Real.pi / 8), (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        + (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), (iteratedDeriv (k + 2) u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      ≤ C₁ * AngRHS k γ u g + C₂ * AngRHS k γ u g := add_le_add ho hf
    _ = (C₁ + C₂) * AngRHS k γ u g := by ring

end Work.FTS.EllipticEst.remov
