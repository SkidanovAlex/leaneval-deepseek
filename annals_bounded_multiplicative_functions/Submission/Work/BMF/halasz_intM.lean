import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.IntM.abel_id

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.BMF

open Finset Real MeasureTheory
open scoped Topology

/-!
# Ramaré's inequality `(ineqMg1)`

We prove that the logarithmic average of `‖Mf f t‖` is controlled by the (unweighted)
average of `‖Kf f t‖`, with constant `2` and an absolute additive constant:

  `∫_1^x ‖Mf f t‖ log t / t² dt ≤ 2 ∫_1^x ‖Kf f t‖ / t² dt + C`.

The proof follows Ramaré's book (`Wirsing-Halasz.tex`, Proposition `LineqMg`), with the
integration by parts replacing the interchange of the two integrals.  Writing
`A t = ‖Mf f t‖`, `B t = ‖Kf f t‖` and `G t = ∫_1^t A u / u du`, the Abel identity gives
`A t log t ≤ B t + G t`; integrating against `1/t²` over `[e², x]` and using
`∫_{e²}^x G t/t² dt = ∫_{e²}^x A t/t² dt - G x/x + G (e²)/e²` (integration by parts,
`d/dt (G t / t) = A t/t² - G t/t²`) yields the claim, the constant `2` coming from
`log t ≥ 2` on `[e², ∞)`.
-/

/-! ## Elementary facts about `Mf` -/

/-- `Mf f` depends on `t` only through `⌊t⌋₊`. -/
private lemma Mf_eq_of_floor_eq {x y : ℝ} (f : ℕ → ℂ) (h : ⌊x⌋₊ = ⌊y⌋₊) : Mf f x = Mf f y := by
  unfold Mf
  rw [h]

lemma Mf_eq_floor (f : ℕ → ℂ) (x : ℝ) : Mf f x = Mf f (⌊x⌋₊ : ℝ) :=
  Mf_eq_of_floor_eq f (Nat.floor_natCast ⌊x⌋₊).symm

lemma measurable_Mf (f : ℕ → ℂ) : Measurable (fun t : ℝ => Mf f t) := by
  have h : (fun t : ℝ => Mf f t)
      = (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) ∘ (fun t : ℝ => ⌊t⌋₊) := rfl
  rw [h]
  exact (measurable_of_countable _).comp Nat.measurable_floor

lemma measurable_Kf (f : ℕ → ℂ) : Measurable (fun t : ℝ => Kf f t) := by
  have h : (fun t : ℝ => Kf f t)
      = (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k * (Real.log k : ℂ)) ∘
        (fun t : ℝ => ⌊t⌋₊) := rfl
  rw [h]
  exact (measurable_of_countable _).comp Nat.measurable_floor

lemma norm_Mf_le_sum (f : ℕ → ℂ) (x : ℝ) :
    ‖Mf f x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f n‖ := norm_sum_le _ _

lemma norm_Mf_le_sum_of_le (f : ℕ → ℂ) {t b : ℝ} (h : t ≤ b) :
    ‖Mf f t‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ := by
  refine (norm_Mf_le_sum f t).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.floor_mono h))
    (fun n _ _ => norm_nonneg _)

lemma norm_Kf_le_sum (f : ℕ → ℂ) (x : ℝ) :
    ‖Kf f x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f n‖ * |Real.log n| := by
  rw [Kf]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

lemma norm_Kf_le_sum_of_le (f : ℕ → ℂ) {t b : ℝ} (h : t ≤ b) :
    ‖Kf f t‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ * |Real.log n| := by
  refine (norm_Kf_le_sum f t).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.floor_mono h))
    (fun n _ _ => mul_nonneg (norm_nonneg _) (abs_nonneg _))

/-- The trivial bound `‖Mf f t‖ ≤ t` for a `1`-bounded `f` and `t ≥ 0`. -/
lemma norm_Mf_le_of_norm_le_one (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖Mf f t‖ ≤ t := by
  refine (norm_Mf_le_sum f t).trans ?_
  have h : (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ‖f n‖) ≤ ∑ _n ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) :=
    Finset.sum_le_sum fun n _ => hb n
  have h2 : (∑ _n ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ)) = (⌊t⌋₊ : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc]
    simp
  rw [h2] at h
  exact h.trans (Nat.floor_le ht)

/-! ## Integrability of the integrands -/

/-- A measurable function bounded by a constant on `Ι a b` is interval integrable. -/
lemma intervalIntegrable_of_bound {g : ℝ → ℝ} {a b C : ℝ}
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.uIoc a b)))
    (hbdd : ∀ t ∈ Set.uIoc a b, |g t| ≤ C) : IntervalIntegrable g volume a b := by
  refine IntervalIntegrable.mono_fun' (f := g) (g := fun _ => C) intervalIntegrable_const hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc hbdd] with t ht
  rwa [Real.norm_eq_abs]

lemma intervalIntegrable_norm_Mf_div (f : ℕ → ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t) volume a b := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  refine intervalIntegrable_of_bound (C := (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖) / a) ?_ ?_
  · exact ((measurable_Mf f).norm.div (by fun_prop)).aestronglyMeasurable
  · intro t ht
    rw [Set.uIoc_of_le hab] at ht
    have ht0 : 0 < t := lt_trans ha0 ht.1
    have hb' : ‖Mf f t‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ :=
      norm_Mf_le_sum_of_le f ht.2
    have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ :=
      Finset.sum_nonneg fun n _ => norm_nonneg _
    have hnn : 0 ≤ ‖Mf f t‖ / t := div_nonneg (norm_nonneg _) (le_of_lt ht0)
    rw [abs_of_nonneg hnn]
    exact (div_le_div_of_nonneg_right hb' (le_of_lt ht0)).trans
      (div_le_div_of_nonneg_left hS ha0 (le_of_lt ht.1))

lemma intervalIntegrable_norm_Mf_div_sq (f : ℕ → ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t ^ 2) volume a b := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  refine intervalIntegrable_of_bound (C := (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖) / a ^ 2) ?_ ?_
  · exact ((measurable_Mf f).norm.div (by fun_prop)).aestronglyMeasurable
  · intro t ht
    rw [Set.uIoc_of_le hab] at ht
    have ht0 : 0 < t := lt_trans ha0 ht.1
    have hb' : ‖Mf f t‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ :=
      norm_Mf_le_sum_of_le f ht.2
    have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ :=
      Finset.sum_nonneg fun n _ => norm_nonneg _
    have hnn : 0 ≤ ‖Mf f t‖ / t ^ 2 := div_nonneg (norm_nonneg _) (by positivity)
    rw [abs_of_nonneg hnn]
    have h2 : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (le_of_lt ha0) (le_of_lt ht.1) 2
    exact (div_le_div_of_nonneg_right hb' (by positivity)).trans
      (div_le_div_of_nonneg_left hS (by positivity) h2)

lemma intervalIntegrable_norm_Mf_log_div_sq (f : ℕ → ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ * Real.log t / t ^ 2) volume a b := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  refine intervalIntegrable_of_bound
    (C := (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖) * Real.log b / a ^ 2) ?_ ?_
  · exact (((measurable_Mf f).norm.mul Real.measurable_log).div (by fun_prop)).aestronglyMeasurable
  · intro t ht
    rw [Set.uIoc_of_le hab] at ht
    have ht0 : 0 < t := lt_trans ha0 ht.1
    have ht1 : (1 : ℝ) ≤ t := le_trans ha (le_of_lt ht.1)
    have hb' : ‖Mf f t‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ :=
      norm_Mf_le_sum_of_le f ht.2
    have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ :=
      Finset.sum_nonneg fun n _ => norm_nonneg _
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hlogb : Real.log t ≤ Real.log b :=
      Real.log_le_log ht0 ht.2
    have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (le_trans ha hab)
    have hnn : 0 ≤ ‖Mf f t‖ * Real.log t / t ^ 2 := by positivity
    rw [abs_of_nonneg hnn]
    have h1 : ‖Mf f t‖ * Real.log t ≤ (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖) * Real.log b :=
      mul_le_mul hb' hlogb hlogt hS
    calc ‖Mf f t‖ * Real.log t / t ^ 2
        ≤ (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖) * Real.log b / t ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖) * Real.log b / a ^ 2 := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          exact pow_le_pow_left₀ (le_of_lt ha0) (le_of_lt ht.1) 2

lemma intervalIntegrable_norm_Kf_div_sq (f : ℕ → ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => ‖Kf f t‖ / t ^ 2) volume a b := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  refine intervalIntegrable_of_bound
    (C := (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ * |Real.log n|) / a ^ 2) ?_ ?_
  · exact ((measurable_Kf f).norm.div (by fun_prop)).aestronglyMeasurable
  · intro t ht
    rw [Set.uIoc_of_le hab] at ht
    have ht0 : 0 < t := lt_trans ha0 ht.1
    have hb' : ‖Kf f t‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ * |Real.log n| :=
      norm_Kf_le_sum_of_le f ht.2
    have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, ‖f n‖ * |Real.log n| :=
      Finset.sum_nonneg fun n _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
    have hnn : 0 ≤ ‖Kf f t‖ / t ^ 2 := div_nonneg (norm_nonneg _) (by positivity)
    rw [abs_of_nonneg hnn]
    have h2 : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (le_of_lt ha0) (le_of_lt ht.1) 2
    exact (div_le_div_of_nonneg_right hb' (by positivity)).trans
      (div_le_div_of_nonneg_left hS (by positivity) h2)

lemma intervalIntegrable_log_div {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Real.log t / t) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  refine ContinuousOn.div (Real.continuousOn_log.mono ?_) continuousOn_id ?_
  · intro t ht
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_trans ha ht.1))
  · intro t ht
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_trans ha ht.1))

/-! ## The elementary integral `∫_1^Y log t / t = (log Y)²/2` -/

lemma integral_log_div_self {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ t in (1 : ℝ)..Y, Real.log t / t) = (Real.log Y) ^ 2 / 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) Y,
      HasDerivAt (fun s : ℝ => Real.log s * Real.log s / 2) (Real.log t / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hY] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
    have h2 : HasDerivAt (fun s : ℝ => Real.log s * Real.log s)
        (t⁻¹ * Real.log t + Real.log t * t⁻¹) t := h1.mul h1
    have h3 : HasDerivAt (fun s : ℝ => Real.log s * Real.log s / 2)
        ((t⁻¹ * Real.log t + Real.log t * t⁻¹) / 2) t := h2.div_const 2
    have heq : (t⁻¹ * Real.log t + Real.log t * t⁻¹) / 2 = Real.log t / t := by ring
    rwa [heq] at h3
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_log_div le_rfl hY)
  simpa [pow_two, Real.log_one] using h

/-! ## Right continuity of `t ↦ ‖Mf f t‖ / t` -/

/-- `Mf f` is constant on `[x, x + δ)`: it is right continuous. -/
lemma eventually_Mf_eq (f : ℕ → ℂ) (x : ℝ) (hx : 0 ≤ x) :
    ∀ᶠ t in 𝓝[>] x, Mf f t = Mf f x := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [IsOpen.mem_nhds isOpen_Ioo (show x ∈ Set.Ioo (x - 1) ((⌊x⌋₊ : ℝ) + 1) from
    ⟨by linarith, Nat.lt_floor_add_one x⟩)] with t ht htx
  have ht0 : 0 ≤ t := le_trans hx (le_of_lt htx)
  have hfl : ⌊t⌋₊ = ⌊x⌋₊ := by
    refine le_antisymm ?_ (Nat.floor_mono (le_of_lt htx))
    have hlt : ⌊t⌋₊ < ⌊x⌋₊ + 1 := by
      rw [Nat.floor_lt ht0]
      push_cast
      linarith [ht.2]
    omega
  rw [Mf_eq_of_floor_eq f hfl]

lemma continuousWithinAt_norm_Mf_div (f : ℕ → ℂ) (x : ℝ) (hx : 0 < x) :
    ContinuousWithinAt (fun t : ℝ => ‖Mf f t‖ / t) (Set.Ioi x) x := by
  have hev : (fun t : ℝ => ‖Mf f x‖ / t) =ᶠ[𝓝[>] x] (fun t : ℝ => ‖Mf f t‖ / t) := by
    filter_upwards [eventually_Mf_eq f x (le_of_lt hx)] with t ht
    rw [ht]
  have hc : ContinuousWithinAt (fun t : ℝ => ‖Mf f x‖ / t) (Set.Ioi x) x :=
    (continuousWithinAt_const (b := ‖Mf f x‖)).div continuousWithinAt_id (ne_of_gt hx)
  exact hc.congr_of_eventuallyEq hev.symm rfl

/-! ## The derivative of the primitive of `A t / t` -/

lemma hasDerivWithinAt_primitive (f : ℕ → ℂ) (x : ℝ) (hx : 1 ≤ x) :
    HasDerivWithinAt (fun u => ∫ t in (1 : ℝ)..u, ‖Mf f t‖ / t)
      (‖Mf f x‖ / x) (Set.Ioi x) x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hInt : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t) volume (1 : ℝ) x :=
    intervalIntegrable_norm_Mf_div f le_rfl hx
  have hmeas : StronglyMeasurableAtFilter (fun t : ℝ => ‖Mf f t‖ / t) (𝓝[>] x) volume :=
    (((measurable_Mf f).norm.div (by fun_prop)).aestronglyMeasurable).stronglyMeasurableAtFilter
  have hcont : ContinuousWithinAt (fun t : ℝ => ‖Mf f t‖ / t) (Set.Ioi x) x :=
    continuousWithinAt_norm_Mf_div f x hx0
  haveI : intervalIntegral.FTCFilter x (𝓝[Set.Ici x] x) (𝓝[Set.Ioi x] x) :=
    intervalIntegral.FTCFilter.nhdsRight x
  have hmain : HasDerivWithinAt (fun u => ∫ t in (1 : ℝ)..u, ‖Mf f t‖ / t)
      (‖Mf f x‖ / x) (Set.Ici x) x :=
    intervalIntegral.integral_hasDerivWithinAt_right hInt hmeas hcont
  exact hmain.mono Set.Ioi_subset_Ici_self

lemma continuousOn_primitive_norm_Mf_div (f : ℕ → ℂ) {a X : ℝ} (ha : 1 ≤ a) (haX : a ≤ X) :
    ContinuousOn (fun t : ℝ => ∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) (Set.uIcc a X) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans ha haX
  have h1 : IntegrableOn (fun u : ℝ => ‖Mf f u‖ / u) (Set.Icc (1 : ℝ) X) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hX1).mp
      (intervalIntegrable_norm_Mf_div f le_rfl hX1)
  have h2 : ContinuousOn (fun t : ℝ => ∫ u in Set.Ioc (1 : ℝ) t, ‖Mf f u‖ / u)
      (Set.Icc (1 : ℝ) X) := intervalIntegral.continuousOn_primitive h1
  have h3 : ContinuousOn (fun t : ℝ => ∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u)
      (Set.Icc (1 : ℝ) X) :=
    h2.congr (fun t ht => by rw [intervalIntegral.integral_of_le ht.1])
  rw [Set.uIcc_of_le haX]
  exact h3.mono (Set.Icc_subset_Icc ha le_rfl)

lemma intervalIntegrable_primitive_div_sq (f : ℕ → ℂ) {a X : ℝ} (ha : 1 ≤ a) (haX : a ≤ X) :
    IntervalIntegrable (fun t : ℝ => (∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) / t ^ 2) volume a X := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  refine ContinuousOn.intervalIntegrable ?_
  refine (continuousOn_primitive_norm_Mf_div f ha haX).div
    ((continuousOn_id.pow 2).mono (by rw [Set.uIcc_of_le haX])) ?_
  rw [Set.uIcc_of_le haX]
  intro t ht
  exact ne_of_gt (pow_pos (lt_of_lt_of_le ha0 ht.1) 2)

/-! ## The Abel pointwise bound -/

/-- Pointwise form of the Abel identity: `A t log t ≤ B t + ∫_1^t A u/u du`. -/
lemma norm_Mf_mul_log_le (f : ℕ → ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖Mf f t‖ * Real.log t ≤ ‖Kf f t‖ + ∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have habel := Work.BMF.IntM.abel_id f t ht
  have h1 : Mf f t * (Real.log t : ℂ) = Kf f t + ∫ u in (1 : ℝ)..t, Mf f u / u := by
    rw [sub_eq_iff_eq_add] at habel
    rw [add_comm] at habel
    exact habel
  have h2 : ‖Mf f t * (Real.log t : ℂ)‖ = ‖Mf f t‖ * Real.log t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  have h3 : ‖∫ u in (1 : ℝ)..t, Mf f u / u‖
      ≤ ∫ u in (1 : ℝ)..t, ‖Mf f u / u‖ :=
    intervalIntegral.norm_integral_le_integral_norm ht
  have h4 : (∫ u in (1 : ℝ)..t, ‖Mf f u / u‖) = ∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    show ‖Mf f u / (u : ℂ)‖ = ‖Mf f u‖ / u
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
  calc ‖Mf f t‖ * Real.log t = ‖Mf f t * (Real.log t : ℂ)‖ := h2.symm
    _ = ‖Kf f t + ∫ u in (1 : ℝ)..t, Mf f u / u‖ := by rw [h1]
    _ ≤ ‖Kf f t‖ + ‖∫ u in (1 : ℝ)..t, Mf f u / u‖ := norm_add_le _ _
    _ ≤ ‖Kf f t‖ + ∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u := by
        rw [← h4]
        linarith

/-! ## The elementary bounds at the scales `1` and `e²` -/

/-- `A t ≤ t` gives `∫_1^Y A t log t/t² ≤ ∫_1^Y log t/t`, and for `Y ≤ e²` the latter is `≤ 2`. -/
lemma integral_norm_Mf_log_div_sq_le_two (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {Y : ℝ}
    (hY1 : 1 ≤ Y) (hY : Y ≤ Real.exp 2) :
    (∫ t in (1 : ℝ)..Y, ‖Mf f t‖ * Real.log t / t ^ 2) ≤ 2 := by
  have hexp1 : (1 : ℝ) ≤ Real.exp 2 := by
    have h : (1 : ℝ) < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have hstep1 : (∫ t in (1 : ℝ)..Y, ‖Mf f t‖ * Real.log t / t ^ 2)
      ≤ ∫ t in (1 : ℝ)..Y, Real.log t / t := by
    refine intervalIntegral.integral_mono_on hY1
      (intervalIntegrable_norm_Mf_log_div_sq f le_rfl hY1)
      (intervalIntegrable_log_div le_rfl hY1) ?_
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht.1
    have hA : ‖Mf f t‖ / t ≤ 1 :=
      (div_le_one ht0).mpr (norm_Mf_le_of_norm_le_one f hb (le_of_lt ht0))
    have hlt : 0 ≤ Real.log t / t := div_nonneg hlog (le_of_lt ht0)
    calc ‖Mf f t‖ * Real.log t / t ^ 2 = Real.log t / t * (‖Mf f t‖ / t) := by
          field_simp
      _ ≤ Real.log t / t * 1 := mul_le_mul_of_nonneg_left hA hlt
      _ = Real.log t / t := by ring
  have hstep2 : (∫ t in (1 : ℝ)..Y, Real.log t / t)
      ≤ ∫ t in (1 : ℝ)..Real.exp 2, Real.log t / t := by
    have hsplit : (∫ t in (1 : ℝ)..Real.exp 2, Real.log t / t)
        = (∫ t in (1 : ℝ)..Y, Real.log t / t)
          + (∫ t in Y..Real.exp 2, Real.log t / t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_log_div (a := 1) (b := Y) le_rfl hY1)
        (intervalIntegrable_log_div (a := Y) (b := Real.exp 2) hY1 hY)).symm
    have hnn : 0 ≤ ∫ t in Y..Real.exp 2, Real.log t / t :=
      intervalIntegral.integral_nonneg hY
        (fun t ht => div_nonneg (Real.log_nonneg (le_trans hY1 ht.1))
          (by linarith [ht.1]))
    linarith [hsplit]
  have h3 : (∫ t in (1 : ℝ)..Real.exp 2, Real.log t / t) = 2 := by
    rw [integral_log_div_self (le_trans hY1 hY), Real.log_exp]
    norm_num
  linarith

/-- `(∫_1^{e²} A u/u du)/e² ≤ 1`. -/
lemma integral_primitive_div_exp_two_le_one (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) :
    (∫ u in (1 : ℝ)..Real.exp 2, ‖Mf f u‖ / u) / Real.exp 2 ≤ 1 := by
  have hexp1 : (1 : ℝ) ≤ Real.exp 2 := by
    have h : (1 : ℝ) < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have hexppos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have h1 : (∫ u in (1 : ℝ)..Real.exp 2, ‖Mf f u‖ / u) ≤ Real.exp 2 - 1 := by
    have h2 : (∫ u in (1 : ℝ)..Real.exp 2, ‖Mf f u‖ / u)
        ≤ ∫ _u in (1 : ℝ)..Real.exp 2, (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on hexp1
        (intervalIntegrable_norm_Mf_div f le_rfl hexp1) intervalIntegrable_const ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
      rw [div_le_one ht0]
      exact norm_Mf_le_of_norm_le_one f hb (le_of_lt ht0)
    simpa using h2
  have h3 : (∫ u in (1 : ℝ)..Real.exp 2, ‖Mf f u‖ / u) / Real.exp 2
      ≤ (Real.exp 2 - 1) / Real.exp 2 :=
    div_le_div_of_nonneg_right h1 (le_of_lt hexppos)
  have h4 : (Real.exp 2 - 1) / Real.exp 2 ≤ 1 := by
    rw [div_le_one hexppos]
    linarith
  linarith

/-! ## The integration by parts identity -/

/-- Integration by parts: `∫_a^X G t/t² dt = ∫_a^X A t/t² dt - G X/X + G a/a`
where `G t = ∫_1^t A u/u du` and `A t = ‖Mf f t‖`. -/
lemma integral_primitive_div_sq_identity (f : ℕ → ℂ) {a X : ℝ} (ha : 1 ≤ a) (haX : a ≤ X) :
    (∫ t in a..X, (∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) / t ^ 2)
      = (∫ t in a..X, ‖Mf f t‖ / t ^ 2)
        - (∫ u in (1 : ℝ)..X, ‖Mf f u‖ / u) / X
        + (∫ u in (1 : ℝ)..a, ‖Mf f u‖ / u) / a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hderiv : ∀ x ∈ Set.Ioo (min a X) (max a X),
      HasDerivWithinAt (fun t : ℝ => ∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u)
        (‖Mf f x‖ / x) (Set.Ioi x) x := by
    intro x hx
    rw [min_eq_left haX, max_eq_right haX] at hx
    exact hasDerivWithinAt_primitive f x (le_trans ha (le_of_lt hx.1))
  have hcont : ContinuousOn (fun t : ℝ => ∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u)
      (Set.uIcc a X) := continuousOn_primitive_norm_Mf_div f ha haX
  have hIntA : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t) volume a X :=
    intervalIntegrable_norm_Mf_div f ha haX
  have hIntSq : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume a X := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le haX]
    refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_
    intro t ht
    exact ne_of_gt (pow_pos (lt_of_lt_of_le ha0 ht.1) 2)
  have hcontv : ContinuousOn (fun t : ℝ => (-1) / t) (Set.uIcc a X) := by
    rw [Set.uIcc_of_le haX]
    exact ContinuousOn.div continuousOn_const continuousOn_id
      (fun t ht => ne_of_gt (lt_of_lt_of_le ha0 ht.1))
  have hderivv : ∀ x ∈ Set.Ioo (min a X) (max a X),
      HasDerivWithinAt (fun t : ℝ => (-1) / t) (1 / x ^ 2) (Set.Ioi x) x := by
    intro x hx
    rw [min_eq_left haX, max_eq_right haX] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 (le_of_lt hx.1))
    have h2 : HasDerivAt (fun t : ℝ => (-1) / t) ((0 * x - (-1) * 1) / x ^ 2) x :=
      (hasDerivAt_const (x := x) (-1)).div (hasDerivAt_id x) hx0
    have heq : (0 * x - (-1) * 1) / x ^ 2 = 1 / x ^ 2 := by ring
    rw [heq] at h2
    exact h2.hasDerivWithinAt
  have hIBP := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
      (u := fun t : ℝ => ∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u)
      (u' := fun t : ℝ => ‖Mf f t‖ / t)
      (v := fun t : ℝ => (-1) / t) (v' := fun t : ℝ => 1 / t ^ 2)
      hcont hcontv hderiv hderivv hIntA hIntSq
  have hGint : IntervalIntegrable
      (fun t : ℝ => (∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) / t ^ 2) volume a X :=
    intervalIntegrable_primitive_div_sq f ha haX
  have hAsq : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t ^ 2) volume a X :=
    intervalIntegrable_norm_Mf_div_sq f ha haX
  have hpt : ∀ t ∈ Set.uIcc a X,
      ((∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) - ‖Mf f t‖) / t ^ 2
        = (‖Mf f t‖ / t) * ((-1) / t) + (∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) * (1 / t ^ 2) := by
    intro t ht
    rw [Set.uIcc_of_le haX] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 ht.1)
    field_simp
    ring
  have hsub : (∫ t in a..X, ((∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) - ‖Mf f t‖) / t ^ 2)
      = (∫ t in a..X, (∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) / t ^ 2)
        - (∫ t in a..X, ‖Mf f t‖ / t ^ 2) := by
    rw [← intervalIntegral.integral_sub hGint hAsq]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hkey : (∫ t in a..X, ((∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) - ‖Mf f t‖) / t ^ 2)
      = - (∫ u in (1 : ℝ)..X, ‖Mf f u‖ / u) / X
        + (∫ u in (1 : ℝ)..a, ‖Mf f u‖ / u) / a := by
    rw [intervalIntegral.integral_congr hpt, hIBP]
    ring
  rw [hsub] at hkey
  ring_nf at hkey ⊢
  linarith [hkey]

/-! ## The main theorem -/

/-- The logarithmic average of `‖Mf f t‖` is controlled by the (unweighted) average of
`‖Kf f t‖`: this is Ramaré's inequality `(ineqMg1)`. -/
theorem halasz_intM :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x : ℝ, 1 ≤ x →
      (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) ≤
        2 * (∫ t in (1 : ℝ)..x, ‖Work.BMF.Kf f t‖ / t ^ 2) + C := by
  refine ⟨4, by norm_num, ?_⟩
  intro f hb x hx
  have hexp1 : (1 : ℝ) ≤ Real.exp 2 := by
    have h : (1 : ℝ) < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have hexppos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hQnonneg : 0 ≤ ∫ t in (1 : ℝ)..x, ‖Kf f t‖ / t ^ 2 :=
    intervalIntegral.integral_nonneg hx (fun t ht => div_nonneg (norm_nonneg _) (by positivity))
  by_cases hxE : x ≤ Real.exp 2
  · have h1 := integral_norm_Mf_log_div_sq_le_two f hb hx hxE
    linarith
  · rw [not_le] at hxE
    have hEx : Real.exp 2 ≤ x := le_of_lt hxE
    -- integrability of all the pieces
    have hA1 : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ * Real.log t / t ^ 2)
        volume (1 : ℝ) x := intervalIntegrable_norm_Mf_log_div_sq f le_rfl hx
    have hAE : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ * Real.log t / t ^ 2)
        volume (1 : ℝ) (Real.exp 2) := intervalIntegrable_norm_Mf_log_div_sq f le_rfl hexp1
    have hAEx : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ * Real.log t / t ^ 2)
        volume (Real.exp 2) x := intervalIntegrable_norm_Mf_log_div_sq f hexp1 hEx
    have hB1 : IntervalIntegrable (fun t : ℝ => ‖Kf f t‖ / t ^ 2) volume (1 : ℝ) x :=
      intervalIntegrable_norm_Kf_div_sq f le_rfl hx
    have hBE : IntervalIntegrable (fun t : ℝ => ‖Kf f t‖ / t ^ 2) volume (1 : ℝ) (Real.exp 2) :=
      intervalIntegrable_norm_Kf_div_sq f le_rfl hexp1
    have hBEx : IntervalIntegrable (fun t : ℝ => ‖Kf f t‖ / t ^ 2) volume (Real.exp 2) x :=
      intervalIntegrable_norm_Kf_div_sq f hexp1 hEx
    have hGEx : IntervalIntegrable
        (fun t : ℝ => (∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) / t ^ 2) volume (Real.exp 2) x :=
      intervalIntegrable_primitive_div_sq f hexp1 hEx
    have hAsqEx : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t ^ 2) volume (Real.exp 2) x :=
      intervalIntegrable_norm_Mf_div_sq f hexp1 hEx
    -- split the left-hand side at `e²`
    have hdecomp : (∫ t in (1 : ℝ)..x, ‖Mf f t‖ * Real.log t / t ^ 2)
        = (∫ t in (1 : ℝ)..Real.exp 2, ‖Mf f t‖ * Real.log t / t ^ 2)
          + (∫ t in Real.exp 2..x, ‖Mf f t‖ * Real.log t / t ^ 2) :=
      (intervalIntegral.integral_add_adjacent_intervals hAE hAEx).symm
    have hL1 : (∫ t in (1 : ℝ)..Real.exp 2, ‖Mf f t‖ * Real.log t / t ^ 2) ≤ 2 :=
      integral_norm_Mf_log_div_sq_le_two f hb hexp1 le_rfl
    -- the main estimate on `[e², x]`
    have hlog2 : ∀ t ∈ Set.Icc (Real.exp 2) x, (2 : ℝ) ≤ Real.log t := by
      intro t ht
      rw [← Real.log_exp 2]
      exact Real.log_le_log hexppos ht.1
    have hP1 : (∫ t in Real.exp 2..x, ‖Mf f t‖ * Real.log t / t ^ 2)
        ≤ (∫ t in Real.exp 2..x, ‖Kf f t‖ / t ^ 2)
          + (∫ t in Real.exp 2..x, (∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) / t ^ 2) := by
      have hstep : (∫ t in Real.exp 2..x, ‖Mf f t‖ * Real.log t / t ^ 2)
          ≤ ∫ t in Real.exp 2..x, (‖Kf f t‖ / t ^ 2
              + (∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) / t ^ 2) := by
        refine intervalIntegral.integral_mono_on hEx hAEx (hBEx.add hGEx) ?_
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := le_trans hexp1 ht.1
        have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
        have h := norm_Mf_mul_log_le f ht1
        have hdiv : ‖Mf f t‖ * Real.log t / t ^ 2
            ≤ (‖Kf f t‖ + (∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u)) / t ^ 2 :=
          div_le_div_of_nonneg_right h (by positivity)
        rwa [add_div] at hdiv
      rw [intervalIntegral.integral_add hBEx hGEx] at hstep
      exact hstep
    have hP2 : (∫ t in Real.exp 2..x, (∫ u in (1 : ℝ)..t, ‖Mf f u‖ / u) / t ^ 2)
        ≤ (∫ t in Real.exp 2..x, ‖Mf f t‖ / t ^ 2) + 1 := by
      have hibp := integral_primitive_div_sq_identity f hexp1 hEx
      have hGx : 0 ≤ (∫ u in (1 : ℝ)..x, ‖Mf f u‖ / u) / x :=
        div_nonneg (intervalIntegral.integral_nonneg hx
          (fun t ht => div_nonneg (norm_nonneg _) (by linarith [ht.1]))) (by linarith)
      have hGE := integral_primitive_div_exp_two_le_one f hb
      linarith [hibp]
    have hP3 : (∫ t in Real.exp 2..x, ‖Mf f t‖ / t ^ 2)
        ≤ (1 / 2) * (∫ t in Real.exp 2..x, ‖Mf f t‖ * Real.log t / t ^ 2) := by
      have hstep : (∫ t in Real.exp 2..x, ‖Mf f t‖ / t ^ 2)
          ≤ ∫ t in Real.exp 2..x, (1 / 2) * (‖Mf f t‖ * Real.log t / t ^ 2) := by
        refine intervalIntegral.integral_mono_on hEx hAsqEx (hAEx.const_mul (1 / 2)) ?_
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hexppos ht.1
        have hA : 0 ≤ ‖Mf f t‖ := norm_nonneg _
        have hlog := hlog2 t ht
        have h1 : (1 : ℝ) ≤ Real.log t / 2 := by linarith
        have h2 : (1 : ℝ) / t ^ 2 ≤ (Real.log t / 2) / t ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
        have h3 : ‖Mf f t‖ * (1 / t ^ 2) ≤ ‖Mf f t‖ * ((Real.log t / 2) / t ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hA
        calc ‖Mf f t‖ / t ^ 2 = ‖Mf f t‖ * (1 / t ^ 2) := by ring
          _ ≤ ‖Mf f t‖ * ((Real.log t / 2) / t ^ 2) := h3
          _ = (1 / 2) * (‖Mf f t‖ * Real.log t / t ^ 2) := by ring
      rwa [intervalIntegral.integral_const_mul] at hstep
    have hP4 : (∫ t in Real.exp 2..x, ‖Kf f t‖ / t ^ 2)
        ≤ (∫ t in (1 : ℝ)..x, ‖Kf f t‖ / t ^ 2) := by
      have hsplit : (∫ t in (1 : ℝ)..x, ‖Kf f t‖ / t ^ 2)
          = (∫ t in (1 : ℝ)..Real.exp 2, ‖Kf f t‖ / t ^ 2)
            + (∫ t in Real.exp 2..x, ‖Kf f t‖ / t ^ 2) :=
        (intervalIntegral.integral_add_adjacent_intervals hBE hBEx).symm
      have hnn : 0 ≤ ∫ t in (1 : ℝ)..Real.exp 2, ‖Kf f t‖ / t ^ 2 :=
        intervalIntegral.integral_nonneg hexp1 (fun t ht => div_nonneg (norm_nonneg _) (by positivity))
      linarith [hsplit]
    have hP : (∫ t in Real.exp 2..x, ‖Mf f t‖ * Real.log t / t ^ 2)
        ≤ 2 * (∫ t in (1 : ℝ)..x, ‖Kf f t‖ / t ^ 2) + 2 := by
      linarith [hP1, hP2, hP3, hP4]
    rw [hdecomp]
    linarith [hL1, hP]

end Work.BMF
