import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.slice_ang_reduce
import Submission.Work.FTS.EllipticEst.remov.ang_ode_iterate

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Assembly lemmas for `slice_ang_gen`

See `NOTES_slice_ang_v_bound.md`.  The target `remov/slice_ang_gen` is reduced to

* `ang_ode_iterate` (proved): `∂^{k+1}(tan θ·u) = u^{(k+2)} + 6u^{(k)} + g^{(k)}`;
* `slice_ang_A_le` (proved): the pairing `A = ∫∂^{k+1}(tan θ·u)u^{(k+2)}q` satisfies
  `A ≤ ½∫(u^{(k+2)})²q + C·R`, given the weighted `v = u/cos θ` bounds
  `∫(v^{(m)})²q ≤ CK·R`, `m ≤ k+1`;
* the weighted `v`-bounds themselves: `slice_ang_v_outer` / `slice_ang_v_far`.

This file contains the elementary bookkeeping: the pointwise AM–GM, the nonnegativity of `AngRHS`,
the splitting of an `Iθ`-integral into the outer and far windows, the reduction
`∫(u^{(k)})²q ≤ AngRHS`, and the final combination.
-/

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma sin_two_nonneg_Iθ_asm {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The full hypothesis bundle of the target `slice_ang_gen` (`k` is the fixed order). -/
def SliceHyp (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : Prop :=
  1 ≤ γ ∧ γ ≤ 5 / 4
    ∧ ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2))
    ∧ ContinuousOn u (Set.Icc 0 (Real.pi / 2))
    ∧ u 0 = 0 ∧ u (Real.pi / 2) = 0
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ)
    ∧ MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
    ∧ (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
        (fun θ => (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ

lemma Iθ_measurable_asm : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-- Each of the last four terms of `AngRHS` is nonnegative. -/
lemma angRHS_rest_nonneg (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    (0 ≤ ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
    ∧ (0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
    ∧ (0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
    ∧ (0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
  refine ⟨Finset.sum_nonneg fun j _ => ?_, ?_, ?_, ?_⟩
  · exact MeasureTheory.setIntegral_nonneg Iθ_measurable_asm
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_asm hθ) _))
  · exact MeasureTheory.setIntegral_nonneg Iθ_measurable_asm
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_asm hθ) _))
  · exact MeasureTheory.setIntegral_nonneg Iθ_measurable_asm (fun θ _ => sq_nonneg _)
  · exact MeasureTheory.setIntegral_nonneg Iθ_measurable_asm (fun θ _ => sq_nonneg _)

/-- `AngRHS` is nonnegative. -/
lemma angRHS_nonneg (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : 0 ≤ AngRHS k γ u g := by
  obtain ⟨hB, hC, hD, hE⟩ := angRHS_rest_nonneg k γ u g
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg Iθ_measurable_asm
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_asm hθ) _))
  unfold AngRHS
  linarith

/-- The `g^{(k)}`-slot is dominated by `AngRHS`. -/
lemma g_slot_le_angRHS (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) ≤ AngRHS k γ u g := by
  obtain ⟨hB, hC, hD, hE⟩ := angRHS_rest_nonneg k γ u g
  unfold AngRHS
  linarith

/-- Splitting an `Iθ`-integral over the outer and far windows. -/
lemma integral_split_Iθ (f : ℝ → ℝ)
    (h1 : MeasureTheory.IntegrableOn f (Set.Icc 0 (3 * Real.pi / 8)))
    (h2 : MeasureTheory.IntegrableOn f (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ, f θ)
      = (∫ θ in Set.Icc 0 (3 * Real.pi / 8), f θ)
        + (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), f θ) := by
  have h3 : (0 : ℝ) ≤ 3 * Real.pi / 8 := by positivity
  have h3' : 3 * Real.pi / 8 ≤ Real.pi / 2 := by
    have := Real.pi_pos; linarith
  have hsub1 : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨hx.1, le_trans hx.2 h3'⟩
  have hsub2 : Set.Icc (3 * Real.pi / 8) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_trans h3 hx.1, hx.2⟩
  have hU : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ∪ Set.Icc (3 * Real.pi / 8) (Real.pi / 2)
      = Work.Spaces.Iθ := by
    ext x; constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, le_trans hx.2 h3'⟩
      · exact ⟨le_trans h3 hx.1, hx.2⟩
    · intro hx
      rcases le_total x (3 * Real.pi / 8) with h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨h, hx.2⟩
  have hdisj : MeasureTheory.AEDisjoint MeasureTheory.volume
      (Set.Icc (0 : ℝ) (3 * Real.pi / 8)) (Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) := by
    show MeasureTheory.volume (Set.Icc (0 : ℝ) (3 * Real.pi / 8)
      ∩ Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) = 0
    refine MeasureTheory.measure_mono_null (t := ({3 * Real.pi / 8} : Set ℝ))
      (fun x hx => ?_) (Real.volume_singleton (a := 3 * Real.pi / 8))
    rw [Set.mem_inter_iff] at hx
    exact le_antisymm hx.1.2 hx.2.1
  rw [← hU]
  exact MeasureTheory.setIntegral_union₀ hdisj (measurableSet_Icc.nullMeasurableSet) h1 h2

end Work.FTS.EllipticEst.remov
