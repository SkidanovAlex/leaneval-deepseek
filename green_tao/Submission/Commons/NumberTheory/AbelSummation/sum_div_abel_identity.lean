import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_div_log_abel_identity

namespace Commons.NumberTheory.AbelSummation

open MeasureTheory intervalIntegral

/-- Fundamental-theorem-of-calculus evaluation of the integral of `1/t²`:
for `0 < a ≤ c`, `∫_a^c dt/t² = 1/a - 1/c`. -/
lemma integral_inv_sq {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    ∫ t in a..c, (t ^ 2)⁻¹ = a⁻¹ - c⁻¹ := by
  have hderiv : ∀ x ∈ Set.uIcc a c, HasDerivAt (fun t : ℝ => -t⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hac] at hx
    have hxpos : x ≠ 0 := by
      have : 0 < x := lt_of_lt_of_le ha hx.1
      exact ne_of_gt this
    have hh : HasDerivAt (fun t : ℝ => -t⁻¹) (- -(x^2)⁻¹) x := (hasDerivAt_inv hxpos).neg
    simpa only [neg_neg] using hh
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a c) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have : 0 < t := lt_of_lt_of_le ha ht.1
      exact pow_ne_zero 2 (ne_of_gt this)
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a c :=
    hcont.intervalIntegrable_of_Icc hac
  have h := integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => -t⁻¹)
    (f' := fun t : ℝ => (t ^ 2)⁻¹) hderiv hint
  rw [h]; ring

theorem sum_div_abel_identity (b : ℕ → ℝ) (h0 : b 0 = 0) (h1 : b 1 = 0) {x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, b n / (n:ℝ)) =
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, b n) / x +
        ∫ t in (2 : ℝ)..x, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, b n) / t ^ 2 := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hfl2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hflx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  set G : ℝ → ℝ := fun t => (t ^ 2)⁻¹ with hG
  have hGval : ∀ t : ℝ, G t = (t ^ 2)⁻¹ := by intro t; rw [hG]
  have hGcont : ContinuousOn G (Set.Icc (2:ℝ) x) := by
    rw [hG]
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have : 0 < t := by linarith [ht.1]
      exact pow_ne_zero 2 (ne_of_gt this)
  have hGint : IntervalIntegrable G volume (2:ℝ) x := hGcont.intervalIntegrable_of_Icc hx
  -- Dropping the terms n = 0 and n = 1
  have drop_sub : Finset.Icc 2 ⌊x⌋₊ ⊆ Finset.Icc 0 ⌊x⌋₊ := by
    intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
  have drop_zero : ∀ n ∈ Finset.Icc 0 ⌊x⌋₊, n ∉ Finset.Icc 2 ⌊x⌋₊ → b n = 0 := by
    intro n hn hnot
    simp only [Finset.mem_Icc] at hn
    have hn2 : n < 2 := by
      by_contra hc
      exact hnot (by simp only [Finset.mem_Icc]; exact ⟨by omega, hn.2⟩)
    interval_cases n
    · exact h0
    · exact h1
  have hL : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, b n / (n:ℝ))
      = ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * ((n:ℝ))⁻¹ := by
    rw [← Finset.sum_subset drop_sub (fun n hn hnot => by rw [drop_zero n hn hnot, zero_div])]
    apply Finset.sum_congr rfl
    intro n hn
    rw [div_eq_mul_inv]
  have hS : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, b n) = ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n :=
    (Finset.sum_subset drop_sub drop_zero).symm
  -- The pointwise FTC identity on the sums
  have hpt : ∀ n ∈ Finset.Icc 2 ⌊x⌋₊,
      ((n:ℝ))⁻¹ = x⁻¹ + ∫ t in (n:ℝ)..x, G t := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
    have hnx : (n:ℝ) ≤ x := by
      have : (n:ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn.2
      linarith
    have h := integral_inv_sq (a := (n:ℝ)) (c := x) (by linarith) hnx
    simp only [← hGval] at h
    linarith
  -- Rewrite each ∫_n^x G as an integral of an indicator over [2,x]
  have hIntg : ∀ n ∈ Finset.Icc 2 ⌊x⌋₊,
      IntervalIntegrable (fun t : ℝ => b n * (Set.Ici (n:ℝ)).indicator G t) volume (2:ℝ) x := by
    intro n hn
    have h1 : IntegrableOn ((Set.Ici (n:ℝ)).indicator G) (Set.uIoc (2:ℝ) x) volume :=
      hGint.def'.indicator measurableSet_Ici
    have h2 : IntegrableOn (fun t : ℝ => b n * (Set.Ici (n:ℝ)).indicator G t)
        (Set.uIoc (2:ℝ) x) volume := h1.const_mul (b n)
    exact intervalIntegrable_iff.mpr h2
  have hInt_eq : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * (∫ t in (n:ℝ)..x, G t)
      = ∫ t in (2:ℝ)..x, ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * (Set.Ici (n:ℝ)).indicator G t := by
    have h1 : ∀ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * (∫ t in (n:ℝ)..x, G t)
        = ∫ t in (2:ℝ)..x, b n * (Set.Ici (n:ℝ)).indicator G t := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
      have hnx : (n:ℝ) ≤ x := by
        have : (n:ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn.2
        linarith
      rw [show (∫ t in (n:ℝ)..x, G t) = ∫ t in (2:ℝ)..x, (Set.Ici (n:ℝ)).indicator G t
          from (Commons.NumberTheory.FriedlanderIwaniec.integral_indicator_Ici (g := G) hn2 hnx).symm]
      rw [intervalIntegral.integral_const_mul]
    rw [Finset.sum_congr rfl h1]
    exact (intervalIntegral.integral_finsetSum (s := Finset.Icc 2 ⌊x⌋₊)
      (f := fun n t => b n * (Set.Ici (n:ℝ)).indicator G t) hIntg).symm
  -- Main algebraic assembly
  have hstep : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * ((n:ℝ))⁻¹
      = (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n) * x⁻¹ +
        ∫ t in (2:ℝ)..x, ∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
          b n * (Set.Ici (n:ℝ)).indicator G t := by
    calc ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * ((n:ℝ))⁻¹
        = ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * (x⁻¹ + ∫ t in (n:ℝ)..x, G t) := by
          apply Finset.sum_congr rfl
          intro n hn; rw [hpt n hn]
      _ = ∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
            (b n * x⁻¹ + b n * ∫ t in (n:ℝ)..x, G t) := by
          apply Finset.sum_congr rfl
          intro n hn; rw [mul_add]
      _ = (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * x⁻¹)
            + ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * ∫ t in (n:ℝ)..x, G t :=
          Finset.sum_add_distrib
      _ = (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n) * x⁻¹
            + ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * ∫ t in (n:ℝ)..x, G t := by
          rw [Finset.sum_mul]
      _ = (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n) * x⁻¹
            + ∫ t in (2:ℝ)..x, ∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
                b n * (Set.Ici (n:ℝ)).indicator G t := by
          rw [hInt_eq]
  -- Pointwise identification of the integrand
  have hcongr : (∫ t in (2:ℝ)..x, ∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
        b n * (Set.Ici (n:ℝ)).indicator G t)
      = ∫ t in (2:ℝ)..x, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, b n) / t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht2 : (2:ℝ) ≤ t := ht.1
    have htx : t ≤ x := ht.2
    dsimp only
    have key : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * (Set.Ici (n:ℝ)).indicator G t
        = (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, if (n:ℝ) ≤ t then b n else 0) * G t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : (n:ℝ) ≤ t
      · rw [Set.indicator_of_mem (by simpa using h), if_pos h]
      · rw [Set.indicator_of_notMem (by simpa using h), if_neg h]
        ring
    rw [key, Commons.NumberTheory.FriedlanderIwaniec.sum_ite_le_eq b h0 h1 hx ht2 htx,
      hGval t, div_eq_mul_inv]
  rw [hL, hstep, hcongr, hS, div_eq_mul_inv]

end Commons.NumberTheory.AbelSummation
