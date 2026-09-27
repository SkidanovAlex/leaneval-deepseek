import Mathlib
import Submission.Work.EKLComp.HopfDefs

/-!
# Hopf's maximal ergodic inequality (union form)

This file proves the maximal ergodic inequality of G. D. Birkhoff / E. Hopf in the form used
to derive the pointwise ergodic theorem:

`0 ≤ ∫_{⋃_n {x | 0 < hopfG f T n x}} f`,

where `hopfG f T n x = max_{0 ≤ k ≤ n} ∑_{j < k} f (T^[j] x)` is the Hopf maximal function
(`Submission.Work.EKLComp.HopfDefs`), and `f` is integrable with respect to a measure `μ`
preserved by `T`.  The set `⋃_n {0 < hopfG f T n}` is exactly `{x | ∃ n, 0 < birkhoffSum T f n x}`.
No finiteness of `μ` is needed.

The argument is the classical one.  Write `G n = hopfG f T n`.  Since
`G (n+1) = max 0 (f + G n ∘ T)`, on the set `A = {0 < G (n+1)}` one has
`f = G (n+1) - G n ∘ T`; moreover `G (n+1)` vanishes off `A`.  Hence
`∫_A f = ∫ G (n+1) - ∫_A (G n ∘ T) ≥ ∫ G (n+1) - ∫ (G n ∘ T) = ∫ G (n+1) - ∫ G n ≥ 0`,
using `G n ≥ 0` and `G n ≤ G (n+1)`.  The sets `A n` increase, so
`MeasureTheory.tendsto_setIntegral_of_monotone₀` (which works with the null measurable sets
`{0 < G n}` available from `AEMeasurable (G n)`) gives the result.
-/

open MeasureTheory Filter

namespace Work.EKLComp

variable {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X} {T : X → X}

/-- The Hopf maximal function is a.e. measurable as soon as `f` is. -/
theorem hopfIneq_aemeasurable (hT : MeasureTheory.MeasurePreserving T μ μ) {f : X → ℝ}
    (hf : AEMeasurable f μ) (n : ℕ) : AEMeasurable (hopfG f T n) μ := by
  induction n with
  | zero => rw [hopfG_zero_fun]; exact aemeasurable_const
  | succ n ih =>
    rw [hopfG_succ]
    exact (aemeasurable_const.max (hf.add
      (ih.comp_quasiMeasurePreserving hT.quasiMeasurePreserving)))

/-- Birkhoff sums of an integrable function are integrable. -/
theorem hopfIneq_integrable_birkhoffSum (hT : MeasureTheory.MeasurePreserving T μ μ) {g : X → ℝ}
    (hg : MeasureTheory.Integrable g μ) (n : ℕ) :
    MeasureTheory.Integrable (fun x => birkhoffSum T g n x) μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (fun x => birkhoffSum T g (n + 1) x)
        = fun x => birkhoffSum T g n x + g (T^[n] x) := by
      funext x; rw [birkhoffSum_succ]; all_goals rfl
    rw [h1]
    exact ih.add ((hT.iterate n).integrable_comp_of_integrable hg)

/-- The Hopf maximal function of an integrable `f` is integrable. -/
theorem hopfIneq_integrable (hT : MeasureTheory.MeasurePreserving T μ μ) {f : X → ℝ}
    (hf : MeasureTheory.Integrable f μ) (n : ℕ) : MeasureTheory.Integrable (hopfG f T n) μ := by
  refine Integrable.mono' (hopfIneq_integrable_birkhoffSum hT hf.abs (n + 1)) ?_ ?_
  · exact (hopfIneq_aemeasurable hT hf.aemeasurable n).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hopfG_nonneg f T n x)]
    exact hopfG_le_abs f T n x

/-- The composition `hopfG f T n ∘ T` is integrable. -/
theorem hopfIneq_integrable_comp (hT : MeasureTheory.MeasurePreserving T μ μ) {f : X → ℝ}
    (hf : MeasureTheory.Integrable f μ) (n : ℕ) :
    MeasureTheory.Integrable (fun x => hopfG f T n (T x)) μ :=
  hT.integrable_comp_of_integrable (hopfIneq_integrable hT hf n)

/-- `∫ (G n ∘ T) = ∫ G n` for a measure preserving `T`. -/
theorem hopfIneq_integral_comp (hT : MeasureTheory.MeasurePreserving T μ μ) {f : X → ℝ}
    (hf : MeasureTheory.Integrable f μ) (n : ℕ) :
    ∫ x, hopfG f T n (T x) ∂μ = ∫ x, hopfG f T n x ∂μ := by
  have h1 : AEStronglyMeasurable (hopfG f T n) (Measure.map T μ) := by
    rw [hT.map_eq]
    exact (hopfIneq_aemeasurable hT hf.aemeasurable n).aestronglyMeasurable
  have h2 := integral_map (μ := μ) (φ := T) hT.measurable.aemeasurable (f := hopfG f T n) h1
  rw [hT.map_eq] at h2
  exact h2.symm

/-- **Hopf's inequality, one step.**  For every `n` the integral of `f` over the set where the
`n`-th Hopf maximal function is positive is nonnegative. -/
theorem hopfIneq_setIntegral_nonneg (hT : MeasureTheory.MeasurePreserving T μ μ) {f : X → ℝ}
    (hf : MeasureTheory.Integrable f μ) (n : ℕ) :
    0 ≤ ∫ x in hopfA f T n, f x ∂μ := by
  cases n with
  | zero =>
    have h0 : hopfA f T 0 = ∅ := by ext x; simp [hopfA]
    rw [h0]; simp
  | succ n =>
    set A := hopfA f T (n + 1) with hAdef
    have hA : NullMeasurableSet A μ :=
      (hopfIneq_aemeasurable hT hf.aemeasurable (n + 1)).nullMeasurableSet_preimage measurableSet_Ioi
    -- On `A`, `f` equals the difference `G (n+1) - G n ∘ T`.
    have heq : ∫ x in A, f x ∂μ
        = ∫ x in A, (hopfG f T (n + 1) x - hopfG f T n (T x)) ∂μ :=
      setIntegral_congr_fun₀ hA (fun x hx => hopfG_sub_eq_of_pos f T n x hx)
    rw [heq, integral_sub (hopfIneq_integrable hT hf (n + 1)).integrableOn
      (hopfIneq_integrable_comp hT hf n).integrableOn]
    -- `G (n+1)` vanishes off `A`, so its integral over `A` is its full integral.
    have h1 : ∫ x in A, hopfG f T (n + 1) x ∂μ = ∫ x, hopfG f T (n + 1) x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hopfG_eq_zero_of_not_pos f T (n + 1) x hx)
    -- `G n ∘ T ≥ 0`, so its integral over `A` is at most its full integral.
    have h2 : ∫ x in A, hopfG f T n (T x) ∂μ ≤ ∫ x, hopfG f T n x ∂μ := by
      have hle : ∫ x in A, hopfG f T n (T x) ∂μ ≤ ∫ x, hopfG f T n (T x) ∂μ :=
        setIntegral_le_integral (hopfIneq_integrable_comp hT hf n)
          (Eventually.of_forall fun x => hopfG_nonneg f T n (T x))
      rw [hopfIneq_integral_comp hT hf n] at hle
      exact hle
    -- `G n ≤ G (n+1)` pointwise.
    have h3 : ∫ x, hopfG f T n x ∂μ ≤ ∫ x, hopfG f T (n + 1) x ∂μ :=
      integral_mono (hopfIneq_integrable hT hf n) (hopfIneq_integrable hT hf (n + 1))
        (fun x => hopfG_le_succ f T n x)
    rw [h1]
    linarith

/-- Hopf's maximal ergodic inequality, in the "union of the maximal sets" form used by
Birkhoff's pointwise ergodic theorem.  Standard proof: put `M n x = max_{0 ≤ k ≤ n} ∑_{j<k} f (T^[j] x)`;
one shows `M (n+1) x = max 0 (f x + M n (T x))` (from `birkhoffSum_succ'`), hence on
`{M (n+1) > 0}` one has `f x = M (n+1) x - M n (T x)`; integrating over `{M (n+1) > 0}`, using
`M n ≤ M (n+1)`, `M n ≥ 0` and `∫ (M n ∘ T) = ∫ M n` (via `integral_map` and `hT.map_eq`) gives
`0 ≤ ∫_{M (n+1) > 0} f`.  The sets `{M n > 0}` increase to `{∃ n, 0 < birkhoffSum T f n x}` and `f`
is integrable, so `MeasureTheory.tendsto_setIntegral_of_monotone` (or dominated convergence for
the indicators via `tendsto_integral_of_dominated_convergence`) yields the claim.  No finiteness
of `μ` is needed. -/
theorem Hopf_inequality {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X) (T : X → X)
    (hT : MeasureTheory.MeasurePreserving T μ μ) (f : X → ℝ) (hf : MeasureTheory.Integrable f μ) :
    0 ≤ ∫ x in {x | ∃ n : ℕ, 0 < birkhoffSum T f n x}, f x ∂μ := by
  have hnull : ∀ n : ℕ, NullMeasurableSet (hopfA f T n) μ := fun n =>
    (hopfIneq_aemeasurable hT hf.aemeasurable n).nullMeasurableSet_preimage measurableSet_Ioi
  have htend := tendsto_setIntegral_of_monotone₀ (f := f) hnull (hopfA_mono f T) hf.integrableOn
  have hlim : 0 ≤ ∫ x in ⋃ n, hopfA f T n, f x ∂μ :=
    ge_of_tendsto htend (Eventually.of_forall (hopfIneq_setIntegral_nonneg hT hf))
  rwa [iUnion_hopfA] at hlim

/-! ### Corollary: the weak `(1,1)` maximal inequality

The union form of Hopf's inequality proved above is exactly what is needed to deduce the weak
`(1,1)` bound for the Hopf maximal function of a nonnegative integrable `g`: applied to
`f = g - α` (`α > 0`) on the maximal set `A = ⋃_n {0 < hopfG f T n}` it gives
`α · μ A ≤ ∫_A f + α · μ A = ∫_A g ≤ ∫ g`, whence `μ A ≤ (∫ g)/α`.  This is the estimate used
in the proof of Birkhoff's pointwise ergodic theorem on a probability space.

The lemma is stated for a finite measure `μ` (this is what makes `μ A` finite); no
`σ`-finiteness, ergodicity or invertibility of `T` is needed.

The name is deliberately distinct from `Work.EKLComp.hopf_maximal_inequality` so that both may
be imported together. -/

/-- The set appearing in the weak `(1,1)` maximal inequality is the union of the Hopf maximal
sets of `g - α`. -/
theorem hopfIneq_iUnion_sub_const {X : Type*} [MeasurableSpace X] (g : X → ℝ) (T : X → X)
    (α : ℝ) :
    (⋃ n, hopfA (fun y => g y - α) T n)
      = {x | ∃ n : ℕ, 0 < n ∧ α * n < birkhoffSum T g n x} := by
  rw [iUnion_hopfA]
  ext x
  constructor
  · rintro ⟨k, hk⟩
    rw [birkhoffSum_sub_const] at hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0] at hk; simp at hk
    · exact ⟨k, hkpos, by nlinarith⟩
  · rintro ⟨n, hn, hlt⟩
    refine ⟨n, ?_⟩
    rw [birkhoffSum_sub_const]
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    nlinarith

/-- **Weak `(1,1)` maximal inequality.**  For a measure preserving `T` on a finite measure space
and a nonnegative integrable `g`, the Hopf maximal set `{∃ n > 0, α n < ∑_{j<n} g (T^[j] ·)}`
has measure at most `(∫ g)/α`. -/
theorem hopfIneq_maximal_weak_type {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (T : X → X) (hT : MeasureTheory.MeasurePreserving T μ μ)
    (g : X → ℝ) (hgi : MeasureTheory.Integrable g μ) (hgn : ∀ x, 0 ≤ g x) (α : ℝ) (hα : 0 < α) :
    μ {x | ∃ n : ℕ, 0 < n ∧ α * n < birkhoffSum T g n x}
      ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / α) := by
  set f : X → ℝ := fun y => g y - α with hfdef
  have hfint : MeasureTheory.Integrable f μ := hgi.sub (integrable_const α)
  have hset : (⋃ n, hopfA f T n)
      = {x | ∃ n : ℕ, 0 < n ∧ α * n < birkhoffSum T g n x} := by
    rw [hfdef]
    exact hopfIneq_iUnion_sub_const g T α
  have hconstOn : MeasureTheory.IntegrableOn (fun _ : X => α) (⋃ n, hopfA f T n) μ :=
    integrableOn_const (C := α) (measure_ne_top μ _) (by simp)
  -- Hopf's inequality on the maximal set, for `f = g - α`.
  have h1 : 0 ≤ ∫ x in ⋃ n, hopfA f T n, f x ∂μ := by
    rw [iUnion_hopfA]; exact Hopf_inequality μ T hT f hfint
  -- Split the integral of `g = f + α` on the maximal set.
  have h2 : ∫ x in ⋃ n, hopfA f T n, g x ∂μ
      = ∫ x in ⋃ n, hopfA f T n, f x ∂μ
        + (μ (⋃ n, hopfA f T n)).toReal * α := by
    have hg : g = fun x => f x + α := by funext x; simp [hfdef]
    rw [hg, integral_add hfint.integrableOn hconstOn, setIntegral_const]
    simp [Measure.real, smul_eq_mul]
  have h3 : ∫ x in ⋃ n, hopfA f T n, g x ∂μ ≤ ∫ x, g x ∂μ :=
    setIntegral_le_integral hgi (Eventually.of_forall hgn)
  have h4 : (μ (⋃ n, hopfA f T n)).toReal * α ≤ ∫ x, g x ∂μ := by linarith
  have h5 : (μ (⋃ n, hopfA f T n)).toReal ≤ (∫ x, g x ∂μ) / α := by
    rw [le_div_iff₀ hα]
    linarith
  have h6 : μ (⋃ n, hopfA f T n) ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / α) :=
    calc μ (⋃ n, hopfA f T n)
        = ENNReal.ofReal ((μ (⋃ n, hopfA f T n)).toReal) :=
          (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / α) := ENNReal.ofReal_le_ofReal h5
  rwa [hset] at h6

end Work.EKLComp
