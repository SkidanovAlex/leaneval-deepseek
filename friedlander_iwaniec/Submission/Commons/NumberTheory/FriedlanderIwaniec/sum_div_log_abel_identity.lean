import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.NumberTheory.FriedlanderIwaniec

open MeasureTheory intervalIntegral

/-- Fundamental-theorem-of-calculus evaluation of the integral of `1/(t log²t)`:
for `2 ≤ a ≤ c`,
`∫_a^c dt/(t log²t) = 1/log a - 1/log c`. -/
lemma integral_inv_log_sq {a c : ℝ} (ha : 2 ≤ a) (hac : a ≤ c) :
    ∫ t in a..c, (t * (Real.log t) ^ 2)⁻¹ = (Real.log a)⁻¹ - (Real.log c)⁻¹ := by
  have hderiv : ∀ x ∈ Set.uIcc a c, HasDerivAt (fun t => (Real.log t)⁻¹)
      (-(x * (Real.log x) ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hac] at hx
    have hx2 : (2:ℝ) ≤ x := le_trans ha hx.1
    have hxpos : x ≠ 0 := by linarith
    have hlog : Real.log x ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · linarith
      · intro h; rw [h] at hx2; norm_num at hx2
    have hd : -(x * (Real.log x) ^ 2)⁻¹ = -x⁻¹ / (Real.log x) ^ 2 := by
      rw [div_eq_mul_inv, mul_inv]; ring
    rw [hd]
    exact (Real.hasDerivAt_log hxpos).inv hlog
  have hcont : ContinuousOn (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹)
      (Set.Icc (a:ℝ) c) := by
    apply ContinuousOn.inv₀
    · apply ContinuousOn.mul continuousOn_id
      apply ContinuousOn.pow
      apply Real.continuousOn_log.mono
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have : (2:ℝ) ≤ t := le_trans ha ht.1
      linarith
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := le_trans ha ht.1
      have hlogt : Real.log t ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one
        · linarith
        · intro h; rw [h] at ht2; norm_num at ht2
      exact mul_ne_zero (by linarith) (pow_ne_zero 2 hlogt)
  have hint : IntervalIntegrable (fun t : ℝ => -((t * (Real.log t) ^ 2)⁻¹)) volume a c :=
    hcont.neg.intervalIntegrable_of_Icc hac
  have h := integral_eq_sub_of_hasDerivAt (f := fun t => (Real.log t)⁻¹)
    (f' := fun t => -((t * (Real.log t) ^ 2)⁻¹)) hderiv hint
  simp only [intervalIntegral.integral_neg] at h
  linarith

/-- For `a ≤ b ≤ c`, the interval integral of the indicator of `Ici b` against `g`
equals the integral of `g` over `[b,c]`. -/
lemma integral_indicator_Ici {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∫ t in a..c, (Set.Ici b).indicator g t = ∫ t in b..c, g t := by
  rw [intervalIntegral.integral_of_le (hab.trans hbc), intervalIntegral.integral_of_le hbc]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hae : (Set.Ioc a c ∩ Set.Ici b : Set ℝ) =ᵐ[volume] Set.Ioc b c := by
    rcases lt_or_eq_of_le hab with h | h
    · have hs : Set.Ioc a c ∩ Set.Ici b = Set.Icc b c := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
        constructor
        · rintro ⟨⟨hat, htc⟩, hbt⟩; exact ⟨hbt, htc⟩
        · rintro ⟨hbt, htc⟩; exact ⟨⟨lt_of_lt_of_le h hbt, htc⟩, hbt⟩
      rw [hs]
      exact (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := b) (b := c)).symm
    · rw [← h]
      have hs : Set.Ioc a c ∩ Set.Ici a = Set.Ioc a c := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici]
        constructor
        · rintro ⟨hh, _⟩; exact hh
        · intro hh; exact ⟨hh, le_of_lt hh.1⟩
      rw [hs]
  exact MeasureTheory.setIntegral_congr_set hae

/-- For `2 ≤ t ≤ x`, the partial sum `∑_{2 ≤ n ≤ ⌊x⌋} [n ≤ t] b n` collapses to
`∑_{0 ≤ n ≤ ⌊t⌋} b n` (using `b 0 = b 1 = 0`). -/
lemma sum_ite_le_eq (b : ℕ → ℝ) (h0 : b 0 = 0) (h1 : b 1 = 0) {x t : ℝ}
    (hx : 2 ≤ x) (ht : 2 ≤ t) (htx : t ≤ x) :
    (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, if (n:ℝ) ≤ t then b n else 0) = ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, b n := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have ht0 : (0:ℝ) ≤ t := by linarith
  have hfilter : (Finset.Icc 2 ⌊x⌋₊).filter (fun n : ℕ => (n:ℝ) ≤ t) = Finset.Icc 2 ⌊t⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [Nat.le_floor_iff ht0]
    constructor
    · rintro ⟨⟨h2, _⟩, hnt⟩; exact ⟨h2, hnt⟩
    · rintro ⟨h2, hnt⟩
      exact ⟨⟨h2, (Nat.le_floor_iff hx0).mpr (le_trans hnt htx)⟩, hnt⟩
  rw [← Finset.sum_filter, hfilter]
  apply Finset.sum_subset
  · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn
    have hn2 : n < 2 := by
      by_contra hc
      exact hnot (by simp only [Finset.mem_Icc]; exact ⟨by omega, hn.2⟩)
    interval_cases n
    · exact h0
    · exact h1

/-- **Abel summation / summation by parts** for the weight `1/log n`: writing
`A(t) = ∑_{n ≤ t} b n` (with `b 0 = b 1 = 0`),
`∑_{n ≤ x} b n / log n = A(x)/log x + ∫₂ˣ A(t)/(t log²t) dt`. -/
theorem sum_div_log_abel_identity (b : ℕ → ℝ) (h0 : b 0 = 0) (h1 : b 1 = 0) {x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, b n / Real.log n) =
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, b n) / Real.log x +
        ∫ t in (2 : ℝ)..x, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, b n) / (t * (Real.log t) ^ 2) := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hfl2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hflx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  set G : ℝ → ℝ := fun t => (t * (Real.log t) ^ 2)⁻¹ with hG
  have hGval : ∀ t : ℝ, G t = (t * (Real.log t) ^ 2)⁻¹ := by intro t; rw [hG]
  have hGcont : ContinuousOn G (Set.Icc (2:ℝ) x) := by
    rw [hG]
    apply ContinuousOn.inv₀
    · apply ContinuousOn.mul continuousOn_id
      apply ContinuousOn.pow
      apply Real.continuousOn_log.mono
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have : (2:ℝ) ≤ t := ht.1
      linarith
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := ht.1
      have hlogt : Real.log t ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one
        · linarith
        · intro h; rw [h] at ht2; norm_num at ht2
      exact mul_ne_zero (by linarith) (pow_ne_zero 2 hlogt)
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
  have hL : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, b n / Real.log n)
      = ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * (Real.log n)⁻¹ := by
    rw [← Finset.sum_subset drop_sub (fun n hn hnot => by rw [drop_zero n hn hnot, zero_div])]
    apply Finset.sum_congr rfl
    intro n hn
    rw [div_eq_mul_inv]
  have hS : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, b n) = ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n :=
    (Finset.sum_subset drop_sub drop_zero).symm
  -- The pointwise FTC identity on the sums
  have hpt : ∀ n ∈ Finset.Icc 2 ⌊x⌋₊,
      (Real.log n)⁻¹ = (Real.log x)⁻¹ + ∫ t in (n:ℝ)..x, G t := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
    have hnx : (n:ℝ) ≤ x := by
      have : (n:ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn.2
      linarith
    have h := integral_inv_log_sq hn2 hnx
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
          from (integral_indicator_Ici (g := G) hn2 hnx).symm]
      rw [intervalIntegral.integral_const_mul]
    rw [Finset.sum_congr rfl h1]
    exact (intervalIntegral.integral_finsetSum (s := Finset.Icc 2 ⌊x⌋₊)
      (f := fun n t => b n * (Set.Ici (n:ℝ)).indicator G t) hIntg).symm
  -- Main algebraic assembly
  have hstep : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * (Real.log n)⁻¹
      = (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n) * (Real.log x)⁻¹ +
        ∫ t in (2:ℝ)..x, ∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
          b n * (Set.Ici (n:ℝ)).indicator G t := by
    calc ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * (Real.log n)⁻¹
        = ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * ((Real.log x)⁻¹ + ∫ t in (n:ℝ)..x, G t) := by
          apply Finset.sum_congr rfl
          intro n hn; rw [hpt n hn]
      _ = ∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
            (b n * (Real.log x)⁻¹ + b n * ∫ t in (n:ℝ)..x, G t) := by
          apply Finset.sum_congr rfl
          intro n hn; rw [mul_add]
      _ = (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * (Real.log x)⁻¹)
            + ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * ∫ t in (n:ℝ)..x, G t :=
          Finset.sum_add_distrib
      _ = (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n) * (Real.log x)⁻¹
            + ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n * ∫ t in (n:ℝ)..x, G t := by
          rw [Finset.sum_mul]
      _ = (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, b n) * (Real.log x)⁻¹
            + ∫ t in (2:ℝ)..x, ∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
                b n * (Set.Ici (n:ℝ)).indicator G t := by
          rw [hInt_eq]
  -- Pointwise identification of the integrand
  have hcongr : (∫ t in (2:ℝ)..x, ∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
        b n * (Set.Ici (n:ℝ)).indicator G t)
      = ∫ t in (2:ℝ)..x, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, b n) / (t * (Real.log t) ^ 2) := by
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
    rw [key, sum_ite_le_eq b h0 h1 hx ht2 htx, hGval t, div_eq_mul_inv]
  rw [hL, hstep, hcongr, hS, div_eq_mul_inv]

end Commons.NumberTheory.FriedlanderIwaniec