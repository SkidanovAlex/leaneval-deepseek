import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

/-- A finite sum (evaluated pointwise) of a.e. strongly measurable real functions is a.e.
strongly measurable. -/
private lemma aesm_finsetSum_apply {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ}
    (hf : ∀ i ∈ s, MeasureTheory.AEStronglyMeasurable (f i) μ) :
    MeasureTheory.AEStronglyMeasurable (fun a : ℝ => ∑ i ∈ s, f i a) μ := by
  have h := Finset.aestronglyMeasurable_sum (M := ℝ) (f := f) s hf
  refine h.congr (Filter.Eventually.of_forall fun a => ?_)
  exact Finset.sum_apply a s f

theorem aesm_HkIntegrand_of_slots {μ : MeasureTheory.Measure ℝ} {B : ℝ → ℝ → ℝ → ℝ}
    {α : ℝ} {k : ℕ} {z θ : ℝ}
    (h : ∀ j i : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.mixed j i (B s) z θ) μ) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.HkIntegrand α k (B s) z θ) μ := by
  unfold Work.Spaces.HkIntegrand
  have hA : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (B s) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) μ :=
    aesm_finsetSum_apply (fun i _ => ((h i 0).mul_const
      (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))).pow 2)
  have hB : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) μ :=
    aesm_finsetSum_apply (fun i _ => aesm_finsetSum_apply (fun j _ => by
      by_cases hh : 1 ≤ i ∧ i + j ≤ k
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun s : ℝ => (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
          funext fun s => ite_eq_left hh
        rw [hthis]
        exact (((h j i).mul_const (Work.Spaces.Wt α z θ)).pow 2)
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun _ : ℝ => (0:ℝ) :=
          funext fun s => ite_eq_right hh
        rw [hthis]
        exact MeasureTheory.aestronglyMeasurable_const))
  exact hA.add hB

end Work.FTS.EpsEngine
