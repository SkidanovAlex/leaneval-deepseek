import Mathlib
import Submission.Work.EKLComp.HopfDefs
import Submission.Work.EKLComp.hopf_setIntegral_nonneg
import Submission.Work.EKLComp.hopf_measure_iUnion_step

/-!
# Hopf's maximal ergodic inequality (discrete time)

Weak `(1,1)` bound for the maximal function `sup_n (1/n) ∑_{k<n} g (T^[k] x)` of a
measure preserving transformation `T`.

Let `hopfG f T n x = max_{0 ≤ k ≤ n} ∑_{j<k} f (T^[j] x)` (see `HopfDefs.lean`), and
let `hopfA f T n = {x | 0 < hopfG f T n x}`.  The proof has three ingredients.

* The *finite level* maximal inequality `Work.EKLComp.hopf_setIntegral_nonneg`:
  for every integrable `f`, `0 ≤ ∫_{hopfA f T n} f`.  It is proved from the recursion
  `hopfG f T (n+1) x = max 0 (f x + hopfG f T n (T x))`, which inverts on
  `hopfA f T (n+1)` to `f x = hopfG f T (n+1) x - hopfG f T n (T x)`.
* Applying it to `f = g - α` gives, for every `n`,
  `α * (μ (hopfA f T n)).toReal ≤ ∫_{hopfA f T n} g ≤ ∫ g`.
* `⋃ n, hopfA f T n` is exactly the set of the statement, and by continuity of a
  measure from below (`Work.EKLComp.hopf_measure_iUnion_step`) the bound passes to
  the union.
-/

open MeasureTheory Filter

namespace Work.EKLComp

variable {X : Type*}

section Helpers

variable [MeasurableSpace X] (μ : MeasureTheory.Measure X)

/-- The `n`-th Hopf maximal function is almost everywhere measurable. -/
theorem hopfG_aemeasurable (T : X → X) (hT : MeasureTheory.MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : AEMeasurable f μ) (n : ℕ) : AEMeasurable (hopfG f T n) μ := by
  induction n with
  | zero => exact (aemeasurable_const : AEMeasurable (fun _ : X => (0 : ℝ)) μ)
  | succ n ih =>
    rw [hopfG_succ]
    exact AEMeasurable.max aemeasurable_const
      (hf.add (ih.comp_quasiMeasurePreserving hT.quasiMeasurePreserving))

/-- Birkhoff sums of an integrable function are integrable. -/
theorem integrable_birkhoffSum (T : X → X) (hT : MeasureTheory.MeasurePreserving T μ μ)
    {g : X → ℝ} (hg : Integrable g μ) (n : ℕ) : Integrable (fun x => birkhoffSum T g n x) μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (fun x => birkhoffSum T g (n + 1) x)
        = fun x => birkhoffSum T g n x + g (T^[n] x) := by
      funext x; rw [birkhoffSum_succ]; all_goals rfl
    rw [h1]
    exact ih.add ((hT.iterate n).integrable_comp_of_integrable hg)

/-- The `n`-th Hopf maximal function of an integrable function is integrable. -/
theorem hopfG_integrable (T : X → X) (hT : MeasureTheory.MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : Integrable f μ) (n : ℕ) : Integrable (hopfG f T n) μ := by
  refine Integrable.mono' (integrable_birkhoffSum μ T hT hf.abs (n + 1)) ?_ ?_
  · exact (hopfG_aemeasurable μ T hT f hf.aemeasurable n).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hopfG_nonneg f T n x)]
    exact hopfG_le_abs f T n x

/-- Set integral of `g - c` over a set, in terms of the set integral of `g`. -/
theorem setIntegral_sub_const [IsFiniteMeasure μ] {g : X → ℝ} (hg : Integrable g μ)
    (c : ℝ) (s : Set X) :
    ∫ x in s, (g x - c) ∂μ = ∫ x in s, g x ∂μ - (μ s).toReal * c := by
  have hA : Integrable g (μ.restrict s) := hg.mono_measure Measure.restrict_le_self
  have hB : Integrable (fun _ : X => c) (μ.restrict s) := by
    refine integrableOn_const (C := c) ?_ ?_ <;> simp
  rw [integral_sub hA hB, setIntegral_const]
  simp [Measure.real, smul_eq_mul]

end Helpers

section SetIdentity

variable [MeasurableSpace X]

/-- The union of the finite level Hopf maximal sets for `g - α` is the set appearing
in the statement of Hopf's inequality. -/
theorem iUnion_hopfA_sub (g : X → ℝ) (T : X → X) (α : ℝ) :
    (⋃ n, hopfA (fun y => g y - α) T n)
      = {x | ∃ n : ℕ, 0 < n ∧ α * n < ∑ k ∈ Finset.range n, g (T^[k] x)} := by
  rw [iUnion_hopfA]
  ext x
  constructor
  · rintro ⟨k, hk⟩
    rw [birkhoffSum_sub_const] at hk
    cases k with
    | zero => simp at hk
    | succ j =>
      refine ⟨j + 1, Nat.succ_pos j, ?_⟩
      simp only [birkhoffSum] at hk ⊢
      push_cast at hk ⊢
      linarith
  · rintro ⟨n, hn, hlt⟩
    refine ⟨n, ?_⟩
    rw [birkhoffSum_sub_const]
    simp only [birkhoffSum] at hlt ⊢
    linarith

end SetIdentity

-- Hopf's maximal ergodic inequality (discrete time): weak (1,1) bound for the maximal function
-- sup_n (1/n) ∑_{k<n} g (T^[k] x) of a measure preserving transformation T.
-- Proof: let F n x := max_{0 ≤ k ≤ n} (∑_{j<k} g (T^[j] x) - α*k) and M n := {x | 0 < F n x}.
-- (i) F n x = max 0 (g x - α + F (n-1) (T x)); hence on M n: g x - α = F n x - F (n-1) (T x).
-- (ii) F n ≥ F (n-1) ≥ 0 pointwise, and F n = 0 off M n.
-- (iii) So ∫_{M n} (g - α) = ∫ (F n - F (n-1) ∘ T) + ∫_{M nᶜ} F (n-1) ∘ T ≥ ∫ F n - ∫ F (n-1) ≥ 0.
-- (iv) M n is increasing with union the set in the statement; conclude by monotone convergence.
theorem hopf_maximal_inequality {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (T : X → X) (hT : MeasureTheory.MeasurePreserving T μ μ)
    (g : X → ℝ) (hgi : MeasureTheory.Integrable g μ) (hgn : ∀ x, 0 ≤ g x) (α : ℝ) (hα : 0 < α) :
    μ {x | ∃ n : ℕ, 0 < n ∧ α * n < ∑ k ∈ Finset.range n, g (T^[k] x)}
      ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / α) := by
  set f : X → ℝ := fun y => g y - α with hfdef
  have hfint : Integrable f μ := by
    rw [hfdef]
    exact hgi.sub (integrable_const α)
  have hAEM : ∀ n : ℕ, AEMeasurable (hopfG f T n) μ :=
    fun n => hopfG_aemeasurable μ T hT f hfint.aemeasurable n
  have hInt : ∀ n : ℕ, Integrable (hopfG f T n) μ :=
    fun n => hopfG_integrable μ T hT f hfint n
  have hset : (⋃ n, hopfA f T n)
      = {x | ∃ n : ℕ, 0 < n ∧ α * n < ∑ k ∈ Finset.range n, g (T^[k] x)} := by
    rw [hfdef]
    exact iUnion_hopfA_sub g T α
  -- the finite level bound: `α * μ (hopfA f T n) ≤ ∫ g`
  have hbound : ∀ n : ℕ, (μ (hopfA f T n)).toReal ≤ (∫ x, g x ∂μ) / α := by
    intro n
    have h1 : 0 ≤ ∫ x in hopfA f T n, f x ∂μ :=
      hopf_setIntegral_nonneg μ T hT f hfint hAEM hInt n
    have h2 : ∫ x in hopfA f T n, f x ∂μ
        = ∫ x in hopfA f T n, g x ∂μ - (μ (hopfA f T n)).toReal * α := by
      rw [hfdef]
      exact setIntegral_sub_const μ hgi α (hopfA f T n)
    have h3 : ∫ x in hopfA f T n, g x ∂μ ≤ ∫ x, g x ∂μ :=
      setIntegral_le_integral hgi (Eventually.of_forall hgn)
    have h4 : (μ (hopfA f T n)).toReal * α ≤ ∫ x, g x ∂μ := by linarith
    rw [le_div_iff₀ hα]
    linarith [h4, mul_comm ((μ (hopfA f T n)).toReal) α]
  have hfin := hopf_measure_iUnion_step μ (hopfA_mono f T) hbound
  rwa [hset] at hfin

end Work.EKLComp
