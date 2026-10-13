import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.SourceBound.SliceAlgebra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ESW.Defs`: the vocabulary of the top angular slot `Tk α k (∂_θθΨ)`

This file sets up the abbreviations used by the induction step `TT.est_step_weak` and proves the
elementary bookkeeping lemmas (the slice form of the equation, the `η`-slot bound, the low-order
`(u')²`/`u²` bound).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular second derivative `B = ∂_θθΨ`. -/
abbrev Bsl (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ

/-- The radial second derivative `A = z²∂_zzΨ`. -/
abbrev Asl (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- The angular source `G = F + α²A + α(5+α)D_zΨ` of the sliced equation. -/
abbrev Gsl (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => F z θ + α ^ 2 * Asl Ψ z θ + (α * (5 + α)) * Work.Spaces.Dz Ψ z θ

/-- `sin(2θ) ≤ 1` on `Iθ`. -/
theorem sin_two_le_one {θ : ℝ} (_hθ : θ ∈ Work.Spaces.Iθ) : Real.sin (2 * θ) ≤ 1 :=
  Real.sin_le_one _

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- **The sliced equation in the form used below**: on the open quadrant,
`Lzero1 (Ψ z ·) = G = F + α²A + α(5+α)D_zΨ`. -/
theorem slice_source_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ = Gsl α F Ψ z θ := by
  have h := Work.FTS.EllipticEst.remov.Lzero1_slice_eq_source
    (α := α) (F := F) (Ψ := Ψ) heq hΨ hz hθ
  have h2 := Work.FTS.EllipticEst.remov.srcB_DzIter_two_eq Ψ hΨ hz hθ
  simp only [Gsl]
  rw [h, h2]
  simp only [Work.Spaces.Dz, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  ring

/-- The one-dimensional angular estimate of the paper's §"General `ℋ^k` case", with the
dimension fixed: this is the type of `remov.slice_ang_gen k` after its `2 ≤ k` argument. -/
def OneD (k : ℕ) : Prop :=
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
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (iteratedDeriv j u θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))


end Work.FTS.EllipticEst.TT.ESW
