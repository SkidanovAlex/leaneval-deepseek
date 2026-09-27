import Mathlib
import Submission.Work.EKLComp.HopfDefs

namespace Work.EKLComp

open MeasureTheory

/-- **Hopf's maximal ergodic inequality, integral form (one-sided positivity).**

If `T` preserves `μ` and `f` is integrable, then on the set
`hopfA f T n = {x | 0 < hopfG f T n x}` (where the `n`-th Hopf maximal function
`hopfG f T n = max_{0 ≤ k ≤ n} ∑_{j<k} f (T^[j] x)` is positive) the integral of `f`
is nonnegative.

The proof is the classical one: on `hopfA f T (n+1)` the Hopf recursion inverts,
`f x = hopfG f T (n+1) x - hopfG f T n (T x)`, while off that set `hopfG f T (n+1)`
vanishes.  Hence, with `A = hopfA f T (n+1)`,
`∫_A f = ∫ hopfG f T (n+1) - ∫ A.indicator (hopfG f T n ∘ T)`, and the second
term is at most `∫ hopfG f T n ∘ T = ∫ hopfG f T n ≤ ∫ hopfG f T (n+1)`. -/
theorem hopf_setIntegral_nonneg {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (T : X → X) (hT : MeasureTheory.MeasurePreserving T μ μ) (f : X → ℝ)
    (hf : MeasureTheory.Integrable f μ)
    (hAEM : ∀ n : ℕ, AEMeasurable (hopfG f T n) μ)
    (hInt : ∀ n : ℕ, MeasureTheory.Integrable (hopfG f T n) μ) (n : ℕ) :
    0 ≤ ∫ x in hopfA f T n, f x ∂μ := by
  -- Change of variables for a measure preserving map, in integral form.
  have hcomp_eq : ∀ g : X → ℝ, MeasureTheory.AEStronglyMeasurable g μ →
      ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ := by
    intro g hg
    have h := MeasureTheory.integral_map (φ := T) hT.aemeasurable (f := g) (by rwa [hT.map_eq])
    rw [hT.map_eq] at h
    exact h.symm
  rcases n with _ | m
  · -- `hopfA f T 0 = ∅`
    have h0 : hopfA f T 0 = ∅ := by ext x; simp [hopfA, hopfG_zero]
    rw [h0]; simp
  · set A : Set X := hopfA f T (m+1) with hA
    have hAnull : NullMeasurableSet A μ := by
      rw [hA]
      exact (hAEM (m+1)).nullMeasurableSet_preimage (s := Set.Ioi (0:ℝ)) measurableSet_Ioi
    have hInt_f : MeasureTheory.Integrable (A.indicator f) μ := hf.indicator₀ hAnull
    -- The pointwise identity `1_A f = G (m+1) - 1_A (G m ∘ T)`.
    have hind : ∀ x, A.indicator f x
        = hopfG f T (m+1) x - A.indicator (fun y => hopfG f T m (T y)) x := by
      intro x
      by_cases hx : x ∈ A
      · have hx' : 0 < hopfG f T (m+1) x := by rw [hA] at hx; simpa [hopfA] using hx
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        exact hopfG_sub_eq_of_pos f T m x hx'
      · have hx' : ¬ 0 < hopfG f T (m+1) x := by rw [hA] at hx; simpa [hopfA] using hx
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
            hopfG_eq_zero_of_not_pos f T (m+1) x hx']
        ring
    have hInt_g : MeasureTheory.Integrable (A.indicator (fun x => hopfG f T m (T x))) μ := by
      refine ((hInt (m+1)).sub hInt_f).congr ?_
      filter_upwards with x
      have hx := hind x
      simp only [Pi.sub_apply] at hx ⊢
      linarith
    have hInt_comp : MeasureTheory.Integrable (fun x => hopfG f T m (T x)) μ :=
      hT.integrable_comp_of_integrable (hInt m)
    -- The indicator is dominated by the function itself (`hopfG` is nonnegative).
    have hle : A.indicator (fun x => hopfG f T m (T x)) ≤ fun x => hopfG f T m (T x) := by
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact hopfG_nonneg f T m (T x)
    have hmono1 : ∫ x, A.indicator (fun x => hopfG f T m (T x)) x ∂μ
        ≤ ∫ x, hopfG f T m (T x) ∂μ := MeasureTheory.integral_mono hInt_g hInt_comp hle
    have hcompm : ∫ x, hopfG f T m (T x) ∂μ = ∫ x, hopfG f T m x ∂μ :=
      hcomp_eq _ (hInt m).aestronglyMeasurable
    have hmono2 : ∫ x, hopfG f T m x ∂μ ≤ ∫ x, hopfG f T (m+1) x ∂μ :=
      MeasureTheory.integral_mono (hInt m) (hInt (m+1)) (fun x => hopfG_le_succ f T m x)
    rw [← MeasureTheory.integral_indicator₀ hAnull (f := f)]
    calc 0 ≤ ∫ x, hopfG f T (m+1) x ∂μ - ∫ x, hopfG f T m x ∂μ := by linarith
      _ = ∫ x, hopfG f T (m+1) x ∂μ - ∫ x, hopfG f T m (T x) ∂μ := by rw [hcompm]
      _ ≤ ∫ x, hopfG f T (m+1) x ∂μ
            - ∫ x, A.indicator (fun x => hopfG f T m (T x)) x ∂μ := by linarith
      _ = ∫ x, (hopfG f T (m+1) x - A.indicator (fun x => hopfG f T m (T x)) x) ∂μ := by
            rw [MeasureTheory.integral_sub (hInt (m+1)) hInt_g]
      _ = ∫ x, A.indicator f x ∂μ := by
            congr 1
            funext x
            exact (hind x).symm

end Work.EKLComp
