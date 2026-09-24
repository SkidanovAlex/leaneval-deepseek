import Mathlib

open scoped BigOperators
open MeasureTheory
open intervalIntegral

namespace Work.NumberTheory.Chen.BTermCount

/-!
# Abel/Mertens partial summation for prime sums: auxiliary lemmas

This file develops the analytic toolkit for `prime_sum_le_integral`:

* `primeRecipSum n = Σ_{p ≤ n} 1/p` and its right-continuous step extension
  `primeRecipStep t = Σ_{p ≤ ⌊t⌋} 1/p`;
* the discrete Abel summation identity
  `Σ_{p ≤ N} f p / p = primeRecipSum N * f N - Σ_{i < N} primeRecipSum i * (f (i+1) - f i)`
  and its interval version (`sum_Ico_primes_div_eq`);
* the identification of `∫_A^B primeRecipStep t * g t` with the corresponding Riemann sum
  (`integral_primeRecipStep_mul_deriv`);
* the integration-by-parts identity
  `∫_A^B (log log t + L₀) * g t = (log log B + L₀) f B - (log log A + L₀) f A
      - ∫_A^B f t / (t log t)`  (`integral_loglog_add_const_mul_deriv`),
  the derivative of `t ↦ log log t + L₀` being `1/(t log t)`;
* the two bounding lemmas `norm_integral_mul_le` and `integral_norm_le_endpoints`.
-/

/-- `primeRecipSum n = Σ_{p ≤ n, p prime} 1/p`. -/
noncomputable def primeRecipSum (n : ℕ) : ℝ := ∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ)

/-- The right-continuous step extension of `primeRecipSum`: `t ↦ Σ_{p ≤ ⌊t⌋} 1/p`. -/
noncomputable def primeRecipStep (t : ℝ) : ℝ := primeRecipSum ⌊t⌋₊

lemma primeRecipStep_apply (t : ℝ) : primeRecipStep t = primeRecipSum ⌊t⌋₊ := rfl

lemma primeRecipStep_natCast (n : ℕ) : primeRecipStep (n : ℝ) = primeRecipSum n := by
  rw [primeRecipStep_apply, Nat.floor_natCast]

lemma primeRecipSum_mono : Monotone primeRecipSum := by
  intro m n hmn
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p hp _ => ?_)
  · rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 hmn, hp.2⟩
  · rw [Nat.mem_primesLE] at hp
    exact div_nonneg zero_le_one (by exact_mod_cast hp.2.pos.le)

lemma primeRecipSum_nonneg (n : ℕ) : 0 ≤ primeRecipSum n := by
  apply Finset.sum_nonneg
  intro p hp
  rw [Nat.mem_primesLE] at hp
  exact div_nonneg zero_le_one (by exact_mod_cast hp.2.pos.le)

lemma primeRecipStep_nonneg (t : ℝ) : 0 ≤ primeRecipStep t := primeRecipSum_nonneg _

lemma primeRecipStep_mono : Monotone primeRecipStep := primeRecipSum_mono.comp Nat.floor_mono

lemma primeRecipStep_measurable : Measurable primeRecipStep := primeRecipStep_mono.measurable

/-! ## The discrete Abel summation identity -/

private noncomputable def primeWeight (n : ℕ) : ℝ := if n.Prime then (1 : ℝ) / (n : ℝ) else 0

private noncomputable def primeWeightSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n+1), primeWeight i

private lemma primeWeightSum_eq (n : ℕ) : primeWeightSum n = primeRecipSum n := by
  rw [primeWeightSum, primeRecipSum, Nat.primesLE_eq_filter_range]
  simp only [primeWeight]
  rw [← Finset.sum_filter]

private lemma primeWeightSum_succ (n : ℕ) : primeWeightSum (n+1) = primeWeightSum n + primeWeight (n+1) := by
  rw [primeWeightSum, primeWeightSum, Finset.sum_range_succ]

private lemma sum_range_primeWeight_mul (f : ℝ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N+1), primeWeight n * f (n:ℝ)
      = primeWeightSum N * f (N:ℝ)
        - ∑ i ∈ Finset.range N, primeWeightSum i * (f ((i:ℝ)+1) - f (i:ℝ)) := by
  induction N with
  | zero => simp [primeWeightSum, primeWeight]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, primeWeightSum_succ, Finset.sum_range_succ]
    push_cast
    ring

/-- **Discrete Abel summation for prime reciprocals.** -/
lemma sum_primesLE_div_eq (f : ℝ → ℝ) (N : ℕ) :
    ∑ p ∈ N.primesLE, f (p:ℝ) / (p:ℝ)
      = primeRecipSum N * f (N:ℝ)
        - ∑ i ∈ Finset.range N, primeRecipSum i * (f ((i:ℝ)+1) - f (i:ℝ)) := by
  have h1 : (∑ p ∈ N.primesLE, f (p:ℝ) / (p:ℝ))
      = ∑ n ∈ Finset.range (N+1), primeWeight n * f (n:ℝ) := by
    rw [Nat.primesLE_eq_filter_range, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.Prime
    · rw [if_pos h, primeWeight, if_pos h, one_div, inv_mul_eq_div]
    · rw [if_neg h, primeWeight, if_neg h, zero_mul]
  have h2 : (∑ i ∈ Finset.range N, primeRecipSum i * (f ((i:ℝ)+1) - f (i:ℝ)))
      = ∑ i ∈ Finset.range N, primeWeightSum i * (f ((i:ℝ)+1) - f (i:ℝ)) :=
    Finset.sum_congr rfl (fun i _ => by rw [primeWeightSum_eq])
  rw [h1, sum_range_primeWeight_mul, h2, primeWeightSum_eq]

/-- The interval version of the discrete Abel identity: the strict lower limit `A < p` is what
removes the endpoint term `f A / A`. -/
lemma sum_Ioc_primes_div_eq (f : ℝ → ℝ) (A B : ℕ) (hAB : A ≤ B) :
    ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, f (p:ℝ)/(p:ℝ)
      = primeRecipSum B * f (B:ℝ) - primeRecipSum A * f (A:ℝ)
        - ∑ i ∈ Finset.Ico A B, primeRecipSum i * (f ((i:ℝ)+1) - f (i:ℝ)) := by
  have hsplit : (Finset.Ioc A B).filter Nat.Prime = B.primesLE \ A.primesLE := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Ioc, Nat.mem_primesLE]
    by_cases hp : p.Prime <;> simp [hp] <;> omega
  have hsub : A.primesLE ⊆ B.primesLE := fun p hp => by
    rw [Nat.mem_primesLE] at hp ⊢; exact ⟨le_trans hp.1 hAB, hp.2⟩
  have hcons := Finset.sum_Ico_consecutive
      (fun i => primeRecipSum i * (f ((i:ℝ)+1) - f (i:ℝ)))
      (m := 0) (n := A) (k := B) (Nat.zero_le A) hAB
  rw [← Finset.range_eq_Ico A, ← Finset.range_eq_Ico B] at hcons
  have hA := sum_primesLE_div_eq f A
  have hB := sum_primesLE_div_eq f B
  have hs := Finset.sum_sdiff (s₁ := A.primesLE) (s₂ := B.primesLE)
    (f := fun p => f (p:ℝ)/(p:ℝ)) hsub
  rw [hsplit]
  linarith only [hcons, hA, hB, hs]

/-! ## Integrability of `primeRecipStep * G` -/

lemma intervalIntegrable_primeRecipStep_mul {a b : ℝ} (hab : a ≤ b) {G : ℝ → ℝ}
    (hG : IntervalIntegrable G volume a b) :
    IntervalIntegrable (fun t => primeRecipStep t * G t) volume a b := by
  have hmeas : MeasurableSet (Set.uIoc a b) := by
    rw [Set.uIoc_of_le hab]; exact measurableSet_Ioc
  refine IntervalIntegrable.mono_fun' ((hG.norm).const_mul (primeRecipSum ⌊b⌋₊)) ?_ ?_
  · rw [Set.uIoc_of_le hab]
    exact (primeRecipStep_measurable.aestronglyMeasurable).mul hG.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem hmeas] with t ht
    have htIoc : t ∈ Set.Ioc a b := by rwa [Set.uIoc_of_le hab] at ht
    have hb : ⌊t⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono htIoc.2
    have h1 : primeRecipStep t ≤ primeRecipSum ⌊b⌋₊ := primeRecipSum_mono hb
    have h2 : 0 ≤ primeRecipStep t := primeRecipStep_nonneg t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg (G t))

lemma ae_ne_add_one (m : ℕ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (m : ℝ) + 1 := by
  rw [MeasureTheory.ae_iff]
  have h : {x : ℝ | ¬ x ≠ (m:ℝ) + 1} = {(m:ℝ)+1} := by ext x; simp
  rw [h]
  exact MeasureTheory.measure_singleton _

/-- **The step-function integral.**  Since `primeRecipStep` is constant equal to
`primeRecipSum i` on the unit interval `[i, i+1)`, its integral against `g = f'` is the
corresponding Riemann sum of increments of `f`. -/
lemma integral_primeRecipStep_mul_deriv {A B : ℕ} {f g : ℝ → ℝ} (hAB : A ≤ B)
    (hderiv : ∀ t ∈ Set.uIcc (A:ℝ) (B:ℝ), HasDerivAt f (g t) t)
    (hfint : IntervalIntegrable g volume (A:ℝ) (B:ℝ)) :
    (∫ t in (A:ℝ)..(B:ℝ), primeRecipStep t * g t)
      = ∑ i ∈ Finset.Ico A B, primeRecipSum i * (f ((i:ℝ)+1) - f (i:ℝ)) := by
  have hAreal : (A:ℝ) ≤ (B:ℝ) := by exact_mod_cast hAB
  have hInt : IntervalIntegrable (fun t => primeRecipStep t * g t) volume (A:ℝ) (B:ℝ) :=
    intervalIntegrable_primeRecipStep_mul hAreal hfint
  have hsub_adj : ∀ k : ℕ, k < B - A →
      Set.uIcc (((A+k : ℕ)) : ℝ) (((A + (k+1) : ℕ)) : ℝ) ⊆ Set.uIcc (A:ℝ) (B:ℝ) := by
    intro k hk
    have hle1 : A ≤ A + k := Nat.le_add_right A k
    have hle2 : A + k + 1 ≤ B := by omega
    rw [Set.uIcc_of_le (by push_cast; linarith), Set.uIcc_of_le hAreal]
    intro x hx
    refine ⟨le_trans (by exact_mod_cast hle1) hx.1, ?_⟩
    calc x ≤ (((A + (k+1) : ℕ)) : ℝ) := hx.2
      _ = (((A+k : ℕ)) : ℝ) + 1 := by rw [Nat.add_succ, Nat.cast_add_one]
      _ ≤ (B:ℝ) := by exact_mod_cast hle2
  have hper : ∀ k ∈ Finset.range (B - A),
      (∫ t in (((A + k : ℕ)) : ℝ)..(((A + (k+1) : ℕ)) : ℝ), primeRecipStep t * g t)
        = primeRecipSum (A + k) * (f (((A + (k+1) : ℕ)) : ℝ) - f (((A + k : ℕ)) : ℝ)) := by
    intro k hk
    have hklt : k < B - A := Finset.mem_range.mp hk
    have hsub := hsub_adj k hklt
    have hcast : (((A+(k+1) : ℕ)) : ℝ) = (((A+k : ℕ)) : ℝ) + 1 := by
      rw [Nat.add_succ, Nat.cast_add_one]
    have hae : ∀ᵐ t ∂(volume : Measure ℝ),
        t ∈ Set.uIoc (((A+k : ℕ)) : ℝ) (((A+(k+1) : ℕ)) : ℝ) →
          primeRecipStep t * g t = primeRecipSum (A + k) * g t := by
      filter_upwards [ae_ne_add_one (A + k)] with t hne ht
      rw [Set.uIoc_of_le (by push_cast; linarith)] at ht
      have h0 : (0:ℝ) ≤ t := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _) ht.1)
      have hfl : ⌊t⌋₊ = A + k := by
        rw [Nat.floor_eq_iff h0]
        exact ⟨le_of_lt ht.1, lt_of_le_of_ne (hcast ▸ ht.2) hne⟩
      rw [primeRecipStep_apply, hfl]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := f) (f' := g) (fun x hx => hderiv x (hsub hx)) (hfint.mono_set hsub)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t => primeRecipStep t * g t)
      (a := fun k : ℕ => (((A + k : ℕ)) : ℝ)) (n := B - A)
      (fun k hk => hInt.mono_set (hsub_adj k hk))
  have h0 : (((A + 0 : ℕ)) : ℝ) = (A:ℝ) := by simp
  have hN : (((A + (B - A) : ℕ)) : ℝ) = (B:ℝ) := by rw [Nat.add_sub_cancel' hAB]
  have hsum'' : (∫ t in (A:ℝ)..(B:ℝ), primeRecipStep t * g t)
      = ∑ k ∈ Finset.range (B - A),
          primeRecipSum (A + k) * (f (((A + (k+1) : ℕ)) : ℝ) - f (((A + k : ℕ)) : ℝ)) := by
    rw [← h0, ← hN, ← hsum]
    exact Finset.sum_congr rfl hper
  rw [hsum'', Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  have hcast : (((A+(k+1) : ℕ)) : ℝ) = (((A+k : ℕ)) : ℝ) + 1 := by
    rw [Nat.add_succ, Nat.cast_add_one]
  rw [hcast]

/-! ## Integration by parts against `log log` -/

lemma continuousOn_loglog_add_const {A B : ℕ} {L₀ : ℝ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    ContinuousOn (fun t : ℝ => Real.log (Real.log t) + L₀) (Set.uIcc (A:ℝ) (B:ℝ)) := by
  have hAreal : (A:ℝ) ≤ (B:ℝ) := by exact_mod_cast hAB
  have hA2 : (2:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
  have ht2 : ∀ t ∈ Set.Icc (A:ℝ) (B:ℝ), 2 ≤ t := by
    intro t ht; linarith [ht.1, hA2]
  rw [Set.uIcc_of_le hAreal]
  refine (ContinuousOn.log (ContinuousOn.log continuousOn_id ?_) ?_).add continuousOn_const
  · intro t ht
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (ht2 t ht))
  · intro t ht
    exact ne_of_gt (Real.log_pos (lt_of_lt_of_le (by norm_num) (ht2 t ht)))

/-- **Integration by parts** for `t ↦ log log t + L₀`, whose derivative is `1/(t log t)`. -/
lemma integral_loglog_add_const_mul_deriv {A B : ℕ} {f g : ℝ → ℝ} {L₀ : ℝ}
    (hA : 2 ≤ A) (hAB : A ≤ B)
    (hderiv : ∀ t ∈ Set.uIcc (A:ℝ) (B:ℝ), HasDerivAt f (g t) t)
    (hfint : IntervalIntegrable g volume (A:ℝ) (B:ℝ)) :
    (∫ t in (A:ℝ)..(B:ℝ), (Real.log (Real.log t) + L₀) * g t)
      = (Real.log (Real.log (B:ℝ)) + L₀) * f (B:ℝ)
        - (Real.log (Real.log (A:ℝ)) + L₀) * f (A:ℝ)
        - ∫ t in (A:ℝ)..(B:ℝ), f t / (t * Real.log t) := by
  have hAreal : (A:ℝ) ≤ (B:ℝ) := by exact_mod_cast hAB
  have hA2 : (2:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
  have ht2 : ∀ t ∈ Set.uIcc (A:ℝ) (B:ℝ), 2 ≤ t := by
    intro t ht
    rw [Set.uIcc_of_le hAreal] at ht
    linarith [ht.1, hA2]
  have ht2' : ∀ t ∈ Set.Icc (A:ℝ) (B:ℝ), 2 ≤ t :=
    fun t ht => ht2 t (by rwa [Set.uIcc_of_le hAreal])
  have hPderiv : ∀ t ∈ Set.uIcc (A:ℝ) (B:ℝ),
      HasDerivAt (fun y : ℝ => Real.log (Real.log y) + L₀) ((t * Real.log t)⁻¹) t := by
    intro t ht
    have h2 := ht2 t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) h2)
    have hl : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (lt_of_lt_of_le (by norm_num) h2))
    have h1 := (Real.hasDerivAt_log ht0).log hl
    have h2' := h1.add_const L₀
    have heq : (t⁻¹) / Real.log t = (t * Real.log t)⁻¹ := by field_simp
    rwa [heq] at h2'
  have hPcont : ContinuousOn (fun y : ℝ => Real.log (Real.log y) + L₀) (Set.uIcc (A:ℝ) (B:ℝ)) :=
    continuousOn_loglog_add_const hA hAB
  have hcont1 : ContinuousOn (fun y : ℝ => (y * Real.log y)⁻¹) (Set.uIcc (A:ℝ) (B:ℝ)) := by
    rw [Set.uIcc_of_le hAreal]
    refine ContinuousOn.inv₀ (continuousOn_id.mul ?_) ?_
    · refine ContinuousOn.log continuousOn_id ?_
      intro t ht
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) (ht2' t ht))
    · intro t ht
      have h2 := ht2' t ht
      exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le (by norm_num) h2))
        (ne_of_gt (Real.log_pos (lt_of_lt_of_le (by norm_num) h2)))
  have hfcont : ContinuousOn f (Set.uIcc (A:ℝ) (B:ℝ)) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hint1 : IntervalIntegrable (fun y : ℝ => (y * Real.log y)⁻¹ * f y) volume (A:ℝ) (B:ℝ) :=
    (hcont1.mul hfcont).intervalIntegrable
  have hint2 : IntervalIntegrable (fun y : ℝ => (Real.log (Real.log y) + L₀) * g y)
      volume (A:ℝ) (B:ℝ) :=
    hfint.continuousOn_mul hPcont
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y => (Real.log (Real.log y) + L₀) * f y)
    (f' := fun y => (y * Real.log y)⁻¹ * f y + (Real.log (Real.log y) + L₀) * g y)
    (fun t ht => (hPderiv t ht).mul (hderiv t ht)) (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2] at hmain
  have hint1' : (∫ y in (A:ℝ)..(B:ℝ), (y * Real.log y)⁻¹ * f y)
      = ∫ y in (A:ℝ)..(B:ℝ), f y / (y * Real.log y) :=
    intervalIntegral.integral_congr (fun y _ => by rw [div_eq_mul_inv, mul_comm])
  rw [hint1'] at hmain
  linarith [hmain]

/-! ## Two bounding lemmas -/

/-- A bounded weight times an integrable function: the norm of the integral is bounded by the
bound times the integral of the norm. -/
lemma norm_integral_mul_le {a b E : ℝ} (hab : a ≤ b) {D G : ℝ → ℝ}
    (hD : ∀ t ∈ Set.Icc a b, |D t| ≤ E) (hG : IntervalIntegrable G volume a b)
    (hDG : IntervalIntegrable (fun t => D t * G t) volume a b) :
    ‖∫ t in a..b, D t * G t‖ ≤ E * ∫ t in a..b, ‖G t‖ := by
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab hDG.norm (hG.norm.const_mul E) ?_
  intro t ht
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hD t ht) (abs_nonneg _)

/-- For `f ≥ 0` monotone with `g = f'` on `[A,B]`, the total variation of `g` is at most
`f A + f B`. -/
lemma integral_norm_le_endpoints {A B : ℕ} {f g : ℝ → ℝ} (hAB : A ≤ B)
    (hderiv : ∀ t ∈ Set.uIcc (A:ℝ) (B:ℝ), HasDerivAt f (g t) t)
    (hfint : IntervalIntegrable g volume (A:ℝ) (B:ℝ))
    (hfnn : ∀ t ∈ Set.Icc (A:ℝ) (B:ℝ), 0 ≤ f t)
    (hmono : (∀ t ∈ Set.Icc (A:ℝ) (B:ℝ), 0 ≤ g t) ∨
      (∀ t ∈ Set.Icc (A:ℝ) (B:ℝ), g t ≤ 0)) :
    ∫ t in (A:ℝ)..(B:ℝ), ‖g t‖ ≤ f (A:ℝ) + f (B:ℝ) := by
  have hAreal : (A:ℝ) ≤ (B:ℝ) := by exact_mod_cast hAB
  have hftc : ∫ t in (A:ℝ)..(B:ℝ), g t = f (B:ℝ) - f (A:ℝ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hfint
  have hA0 : 0 ≤ f (A:ℝ) := hfnn _ ⟨le_rfl, hAreal⟩
  have hB0 : 0 ≤ f (B:ℝ) := hfnn _ ⟨hAreal, le_rfl⟩
  rcases hmono with hg | hg
  · have hcongr : (∫ t in (A:ℝ)..(B:ℝ), ‖g t‖) = ∫ t in (A:ℝ)..(B:ℝ), g t :=
      intervalIntegral.integral_congr (fun t ht => by
        rw [Set.uIcc_of_le hAreal] at ht
        rw [Real.norm_eq_abs, abs_of_nonneg (hg t ht)])
    rw [hcongr, hftc]; linarith
  · have hcongr : (∫ t in (A:ℝ)..(B:ℝ), ‖g t‖) = ∫ t in (A:ℝ)..(B:ℝ), -g t :=
      intervalIntegral.integral_congr (fun t ht => by
        rw [Set.uIcc_of_le hAreal] at ht
        rw [Real.norm_eq_abs, abs_of_nonpos (hg t ht)])
    rw [hcongr, intervalIntegral.integral_neg, hftc]; linarith

end Work.NumberTheory.Chen.BTermCount
