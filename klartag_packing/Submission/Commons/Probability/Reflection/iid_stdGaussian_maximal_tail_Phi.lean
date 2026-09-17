import Mathlib
import Submission.Commons.Probability.Reflection.measure_exists_sum_le_le_two_mul
import Submission.Commons.Probability.Reflection.pi_fin_maximal_abs_tail
import Submission.Commons.Probability.Gaussian.pi_gaussianReal_sum_law
import Submission.Commons.Probability.Gaussian.stdGaussian_map_neg

namespace Commons.Probability.Reflection

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- `stdGaussian ℝ` is the standard real Gaussian `gaussianReal 0 1`. -/
theorem stdGaussian_real_eq : ProbabilityTheory.stdGaussian ℝ = ProbabilityTheory.gaussianReal 0 1 := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [ProbabilityTheory.charFun_stdGaussian, ProbabilityTheory.charFun_gaussianReal]
  rw [Real.norm_eq_abs]
  have h : (↑|t| : ℂ) ^ 2 = (↑t : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  rw [h]
  congr 1
  simp
  ring

/-- The reflection inequality in the "upward" direction: for a symmetric probability measure
`ν` on `ℝ`, the probability that some partial sum of length `≤ K` of an i.i.d. `ν`-sequence
reaches `a ≥ 0` is at most twice the probability that the partial sum of length `K` does. -/
theorem product_reflection_ge {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν.map (fun x : ℝ => -x) = ν) (K : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (Measure.infinitePi (fun _ : ℕ => ν)).real {x | ∃ k, k ≤ K ∧ a ≤ psum k x}
      ≤ 2 * (Measure.infinitePi (fun _ : ℕ => ν)).real {x | a ≤ psum K x} := by
  classical
  set P : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => ν) with hP
  set negseq : (ℕ → ℝ) → (ℕ → ℝ) := fun x i => -x i with hneg
  have hneg_meas : Measurable negseq := by
    rw [hneg]; exact measurable_pi_iff.mpr (fun i => (measurable_pi_apply i).neg)
  have hmap : P.map negseq = P := by
    rw [hP, hneg]
    have := Measure.infinitePi_map_pi (μ := fun _ : ℕ => ν)
      (f := fun (_ : ℕ) (x : ℝ) => -x) (fun _ => measurable_neg)
    simpa [hν] using this
  have hpsum_neg : ∀ k x, psum k (negseq x) = - psum k x := by
    intro k x
    simp only [psum, hneg]
    rw [Finset.sum_neg_distrib]
  have hsetA : {x : ℕ → ℝ | ∃ k, k ≤ K ∧ a ≤ psum k x} = negseq ⁻¹' badSet K a := by
    ext x
    simp only [Set.mem_preimage, badSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk, hkx⟩
      exact ⟨k, hk, by rw [hpsum_neg k x]; linarith⟩
    · rintro ⟨k, hk, hkx⟩
      exact ⟨k, hk, by have := hkx; rw [hpsum_neg k x] at this; linarith⟩
  have hsetB : {x : ℕ → ℝ | a ≤ psum K x} = negseq ⁻¹' goodSet K a := by
    ext x
    simp only [Set.mem_preimage, goodSet, Set.mem_ofPred_eq]
    constructor
    · intro h
      show psum K (negseq x) ≤ -a
      rw [hpsum_neg K x]; linarith
    · intro h
      have := h; rw [hpsum_neg K x] at this; linarith
  have hENN : P {x | ∃ k, k ≤ K ∧ a ≤ psum k x} ≤ 2 * P {x | a ≤ psum K x} := by
    calc P {x | ∃ k, k ≤ K ∧ a ≤ psum k x}
        = P (negseq ⁻¹' badSet K a) := by rw [hsetA]
      _ = (P.map negseq) (badSet K a) := by
          rw [Measure.map_apply hneg_meas (measurableSet_badSet K a)]
      _ = P (badSet K a) := by rw [hmap]
      _ ≤ 2 * P (goodSet K a) := product_reflection hν K ha
      _ = 2 * (P.map negseq) (goodSet K a) := by rw [hmap]
      _ = 2 * P (negseq ⁻¹' goodSet K a) := by
          rw [Measure.map_apply hneg_meas (measurableSet_goodSet K a)]
      _ = 2 * P {x | a ≤ psum K x} := by rw [hsetB]
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  rw [Measure.real_def, Measure.real_def]
  calc (P {x | ∃ k, k ≤ K ∧ a ≤ psum k x}).toReal
      ≤ (2 * P {x | a ≤ psum K x}).toReal := ENNReal.toReal_mono (by finiteness) hENN
    _ = 2 * (P {x | a ≤ psum K x}).toReal := by rw [ENNReal.toReal_mul]; norm_num

/-- The upper tail of the sum of `n ≥ 1` independent standard Gaussians, expressed through the
tail of a single standard Gaussian. -/
theorem pi_stdGaussian_sum_tail (n : ℕ) (hn : 0 < n) (a : ℝ) :
    (Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ)).real
        {ω : Fin n → ℝ | a ≤ ∑ i, ω i}
      = (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | a / Real.sqrt n ≤ y} := by
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hscale : (ProbabilityTheory.gaussianReal 0 1).map (fun y : ℝ => Real.sqrt n * y)
      = ProbabilityTheory.gaussianReal 0 (n : ℝ≥0) := by
    rw [ProbabilityTheory.gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    rw [ProbabilityTheory.gaussianReal_ext_iff]
    refine ⟨rfl, ?_⟩
    apply NNReal.coe_inj.mp
    rw [NNReal.coe_mk, NNReal.coe_natCast, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hmap : (Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ)).map
        (fun ω : Fin n → ℝ => ∑ i, ω i)
      = (ProbabilityTheory.stdGaussian ℝ).map (fun y : ℝ => Real.sqrt n * y) := by
    rw [stdGaussian_real_eq]
    rw [Commons.Probability.Gaussian.pi_gaussianReal_sum_law n]
    rw [hscale]
  have hf_meas : Measurable (fun ω : Fin n → ℝ => ∑ i, ω i) :=
    Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hset_meas : MeasurableSet {z : ℝ | a ≤ z} := measurableSet_le measurable_const measurable_id
  have hsetpre : (fun y : ℝ => Real.sqrt n * y) ⁻¹' {z : ℝ | a ≤ z}
      = {y : ℝ | a / Real.sqrt n ≤ y} := by
    ext y; simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [div_le_iff₀ hsqrt_pos, mul_comm]
  calc (Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ)).real
          {ω : Fin n → ℝ | a ≤ ∑ i, ω i}
      = (Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ)).real
          ((fun ω : Fin n → ℝ => ∑ i, ω i) ⁻¹' {z : ℝ | a ≤ z}) := rfl
    _ = ((Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ)).map
          (fun ω : Fin n → ℝ => ∑ i, ω i)).real {z : ℝ | a ≤ z} := by
        rw [map_measureReal_apply hf_meas hset_meas]
    _ = ((ProbabilityTheory.stdGaussian ℝ).map (fun y : ℝ => Real.sqrt n * y)).real
          {z : ℝ | a ≤ z} := by rw [hmap]
    _ = (ProbabilityTheory.stdGaussian ℝ).real
          ((fun y : ℝ => Real.sqrt n * y) ⁻¹' {z : ℝ | a ≤ z}) := by
        rw [map_measureReal_apply (by fun_prop) hset_meas]
    _ = (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | a / Real.sqrt n ≤ y} := by rw [hsetpre]

/-- Maximal (one-sided) tail bound for the partial sums of an i.i.d. standard Gaussian
sequence, with the optimal constant `2` and expressed through the standard Gaussian tail. -/
theorem iid_stdGaussian_maximal_tail_Phi {n : ℕ} {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ)).real
        {ω : Fin n → ℝ |
          ∃ k ≤ n, r ≤ σ * ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), ω j}
      ≤ 2 * (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | r / (σ * Real.sqrt n) ≤ y} := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have hset : {ω : Fin 0 → ℝ | ∃ k ≤ 0,
        r ≤ σ * ∑ j ∈ Finset.univ.filter (fun j : Fin 0 => (j : ℕ) < k), ω j} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro k hk
      interval_cases k
      simp [hr]
    rw [hset, measureReal_empty]
    exact mul_nonneg (by norm_num) measureReal_nonneg
  · set a : ℝ := r / σ with hadef
    have ha : 0 ≤ a := by rw [hadef]; exact (div_pos hr hσ).le
    set Efin : Set (Fin n → ℝ) :=
      {ω | ∃ k ≤ n, r ≤ σ * ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), ω j} with hEfin
    have hEfin_meas : MeasurableSet Efin := by
      rw [hEfin]
      have heq : {ω : Fin n → ℝ | ∃ k ≤ n,
          r ≤ σ * ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), ω j}
          = ⋃ k : Fin (n + 1), {ω : Fin n → ℝ |
              r ≤ σ * ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ)), ω j} := by
        ext ω; constructor
        · rintro ⟨k, hk, hk'⟩
          exact Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_of_le hk⟩, hk'⟩
        · intro h; rw [Set.mem_iUnion] at h; obtain ⟨k, hk⟩ := h
          exact ⟨k, Nat.le_of_lt_succ k.2, hk⟩
      rw [heq]
      refine MeasurableSet.iUnion (fun k => ?_)
      exact measurableSet_le measurable_const (measurable_const.mul
        (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)))
    have hrest_meas : Measurable (fun ω : ℕ → ℝ => fun j : Fin n => ω j.val) := by fun_prop
    have hpre : (fun ω : ℕ → ℝ => fun j : Fin n => ω j.val) ⁻¹' Efin
        = {ω : ℕ → ℝ | ∃ k, k ≤ n ∧ a ≤ psum k ω} := by
      rw [hEfin]
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨k, hk, hk'⟩
        refine ⟨k, hk, ?_⟩
        rw [hadef, psum, ← sum_filter_univ_fin (fun i => ω i) hk, div_le_iff₀ hσ, mul_comm]
        exact hk'
      · rintro ⟨k, hk, hk'⟩
        refine ⟨k, hk, ?_⟩
        rw [hadef, psum, ← sum_filter_univ_fin (fun i => ω i) hk, div_le_iff₀ hσ, mul_comm] at hk'
        exact hk'
    have hbridge : (Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ)).real Efin
        = (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.stdGaussian ℝ)).real
            {ω : ℕ → ℝ | ∃ k, k ≤ n ∧ a ≤ psum k ω} := by
      have hLHS : (Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ)).real Efin
          = (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.stdGaussian ℝ)).real
              ((fun ω : ℕ → ℝ => fun j : Fin n => ω j.val) ⁻¹' Efin) := by
        rw [← infinitePi_map_restrict_fin n, map_measureReal_apply hrest_meas hEfin_meas]
      rw [hLHS, hpre]
    rw [hbridge]
    have hνsym : (ProbabilityTheory.stdGaussian ℝ).map (fun x : ℝ => -x) = ProbabilityTheory.stdGaussian ℝ := by
      simpa using (Commons.Probability.Gaussian.stdGaussian_map_neg (E := ℝ))
    have hge := product_reflection_ge (ν := ProbabilityTheory.stdGaussian ℝ) hνsym n ha
    have hsummeas : MeasurableSet {ω : Fin n → ℝ | a ≤ ∑ i, ω i} :=
      measurableSet_le measurable_const (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
    have htail : (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.stdGaussian ℝ)).real
            {ω : ℕ → ℝ | a ≤ psum n ω}
        = (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | a / Real.sqrt n ≤ y} := by
      have hpre2 : {ω : ℕ → ℝ | a ≤ psum n ω}
          = (fun ω : ℕ → ℝ => fun j : Fin n => ω j.val) ⁻¹'
              {ω : Fin n → ℝ | a ≤ ∑ i, ω i} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        rw [psum, ← Fin.sum_univ_eq_sum_range (fun i => ω i) n]
      have hLHS2 : (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.stdGaussian ℝ)).real
              ((fun ω : ℕ → ℝ => fun j : Fin n => ω j.val) ⁻¹' {ω : Fin n → ℝ | a ≤ ∑ i, ω i})
          = (Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ)).real
              {ω : Fin n → ℝ | a ≤ ∑ i, ω i} := by
        rw [← infinitePi_map_restrict_fin n, map_measureReal_apply hrest_meas hsummeas]
      rw [hpre2, hLHS2]
      exact pi_stdGaussian_sum_tail n hn a
    calc (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.stdGaussian ℝ)).real
            {ω : ℕ → ℝ | ∃ k, k ≤ n ∧ a ≤ psum k ω}
        ≤ 2 * (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.stdGaussian ℝ)).real
            {ω : ℕ → ℝ | a ≤ psum n ω} := hge
      _ = 2 * (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | a / Real.sqrt n ≤ y} := by rw [htail]
      _ = 2 * (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | r / (σ * Real.sqrt n) ≤ y} := by
          have heq : a / Real.sqrt n = r / (σ * Real.sqrt n) := by rw [hadef, div_div]
          rw [heq]

end

end Commons.Probability.Reflection
