import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-- Monotonicity of the `H^k`-integrand in `k`: every summand occurring in
`HkIntegrand α k f` also occurs in `HkIntegrand α (k+1) f` (with the same value), and
all summands are squares, hence nonnegative. -/
theorem Work.Spaces.HkIntegrand_mono (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α (k + 1) f z θ := by
  set Z : ℕ → ℝ := fun i =>
    (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    with hZdef
  set ψ : ℕ → ℕ → ℝ := fun i j =>
    (if 1 ≤ i ∧ i + j ≤ k + 1 then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
    with hψdef
  have key : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) ≤ ψ i j := by
    intro i j
    show (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (if 1 ≤ i ∧ i + j ≤ k + 1 then
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left h, ite_eq_left ⟨h.1, by omega⟩]
    · rw [ite_eq_right h]
      split_ifs with h2
      · exact sq_nonneg _
      · exact le_refl 0
  have hψnn : ∀ i j, 0 ≤ ψ i j := by
    intro i j
    show 0 ≤ (if 1 ≤ i ∧ i + j ≤ k + 1 then
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
    split_ifs with h2
    · exact sq_nonneg _
    · exact le_refl 0
  have hA : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), ψ i j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
  have hB : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), ψ i j)
      ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 + 1), ψ i j) :=
    Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega)
        (fun j _ _ => hψnn i j)
  have hC : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 + 1), ψ i j)
      ≤ (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1 + 1), ψ i j) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega)
      (fun i _ _ => Finset.sum_nonneg fun j _ => hψnn i j)
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1 + 1), ψ i j) :=
    le_trans hA (le_trans hB hC)
  have hZ : (∑ i ∈ Finset.range (k + 1), Z i) ≤ (∑ i ∈ Finset.range (k + 1 + 1), Z i) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega)
      (fun i _ _ => by
        show 0 ≤ (Work.Spaces.DzIter i f z θ *
          (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        exact sq_nonneg _)
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  exact add_le_add hZ hM

namespace Work.Coercivity

theorem HkSq_mono (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : Spaces.HkMem α (k + 1) f) :
    Spaces.HkSq α k f ≤ Spaces.HkSq α (k + 1) f := by
  rw [Spaces.HkSq, Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Spaces.HkIntegrand_nonneg α k f z θ)
    h.2 ?_
  show ∀ᵐ z ∂(volume.restrict Spaces.Iz),
    (∫ θ in Spaces.Iθ, Spaces.HkIntegrand α k f z θ)
      ≤ ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α (k + 1) f z θ
  exact MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Spaces.Iz from measurableSet_Ici)
    fun z hz => MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Spaces.HkIntegrand_nonneg α k f z θ)
      (h.1 z hz)
      (Eventually.of_forall fun θ => Spaces.HkIntegrand_mono α k f z θ)

end Work.Coercivity
