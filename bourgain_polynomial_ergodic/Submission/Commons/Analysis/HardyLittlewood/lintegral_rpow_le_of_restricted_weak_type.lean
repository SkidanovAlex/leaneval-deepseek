import Mathlib.Analysis.SpecialFunctions.Pow.Integral

namespace Commons.Analysis.HardyLittlewood

open MeasureTheory Set Finset Filter
open scoped ENNReal

/-- Auxiliary `ℝ≥0∞`-inequality: if `X ≤ c * (Y ^ (1/p) * X ^ (1/q))` with
`1/p + 1/q = 1`, `0 < p`, `0 < q` and `X < ⊤`, then `X ≤ c ^ p * Y`.  This is the final
"divide and raise to the power `p`" step of the interpolation argument. -/
private lemma le_mul_rpow_of_le_mul {p q : ℝ} (hpq : 1 / p + 1 / q = 1) (hp : 0 < p)
    (hq : 0 < q) {c X Y : ℝ≥0∞} (hX : X < ⊤)
    (h : X ≤ c * (Y ^ (1 / p) * X ^ (1 / q))) : X ≤ c ^ p * Y := by
  rcases eq_or_ne X 0 with hX0 | hX0
  · rw [hX0]; exact bot_le
  · have hXt : X ≠ ⊤ := hX.ne
    have hsplit : X = X ^ (1 / p) * X ^ (1 / q) := by
      rw [← ENNReal.rpow_add (1 / p) (1 / q) hX0 hXt, hpq, ENNReal.rpow_one]
    have hXq0 : X ^ (1 / q) ≠ 0 := fun hzero =>
      hX0 ((ENNReal.rpow_eq_zero_iff_of_pos (by positivity : (0:ℝ) < 1 / q)).mp hzero)
    have hXqt : X ^ (1 / q) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by positivity : (0:ℝ) ≤ 1 / q) hXt).ne
    have h2 : X ^ (1 / p) ≤ c * Y ^ (1 / p) := by
      have h' : X ^ (1 / p) * X ^ (1 / q) ≤ (c * Y ^ (1 / p)) * X ^ (1 / q) := by
        calc X ^ (1 / p) * X ^ (1 / q) = X := hsplit.symm
          _ ≤ c * (Y ^ (1 / p) * X ^ (1 / q)) := h
          _ = (c * Y ^ (1 / p)) * X ^ (1 / q) := by ring
      exact (ENNReal.mul_le_mul_iff_left hXq0 hXqt).mp h'
    have h3 : (X ^ (1 / p)) ^ p ≤ (c * Y ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow h2 hp.le
    rwa [← ENNReal.rpow_mul X (1 / p) p, div_mul_cancel₀ 1 hp.ne', ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg c (Y ^ (1 / p)) hp.le, ← ENNReal.rpow_mul Y (1 / p) p,
      div_mul_cancel₀ 1 hp.ne', ENNReal.rpow_one] at h3

theorem lintegral_rpow_le_of_restricted_weak_type {p : ℝ} (hp : 1 < p) {f a : ℕ → ℝ}
    (hf_nn : ∀ n, 0 ≤ f n) (ha_nn : ∀ n, 0 ≤ a n) {s : Finset ℕ} (hs : ∀ n, n ∉ s → a n = 0)
    (hweak : ∀ lam : ℝ, 0 < lam → ENNReal.ofReal lam * Measure.count {n : ℕ | lam < f n}
        ≤ ∫⁻ n in {n : ℕ | lam < f n}, ENNReal.ofReal (a n) ∂Measure.count) :
    ∫⁻ n, ENNReal.ofReal ((f n) ^ p) ∂Measure.count
      ≤ ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ n, ENNReal.ofReal ((a n) ^ p) ∂Measure.count := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 ≤ p - 1 := by linarith
  have hp1pos : 0 < p - 1 := by linarith
  have hp1ne : p - 1 ≠ 0 := hp1pos.ne'
  have hc_nn : 0 ≤ p / (p - 1) := div_nonneg hp_pos.le hp1pos.le
  have hq_pos : 0 < p / (p - 1) := div_pos hp_pos hp1pos
  let A : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (a n)
  let F : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (f n)
  have hA_meas : Measurable A := (measurable_of_countable a).ennreal_ofReal
  have hF_meas : Measurable F := (measurable_of_countable f).ennreal_ofReal
  have hFpow_meas : Measurable (fun n => F n ^ (p - 1)) := hF_meas.pow_const (p - 1)
  have hf_meas : Measurable f := measurable_of_countable f
  -- the reference measure and the weighted measure
  set ν : Measure ℕ := Measure.count.withDensity A with hν
  -- C := ∫ A · F^(p-1)
  set C : ℝ≥0∞ := ∫⁻ n, A n * F n ^ (p - 1) ∂Measure.count with hCdef
  -- K := ∫_{t>0} t^(p-2) · ∫_{f>t} A
  set K : ℝ≥0∞ :=
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ n in {n : ℕ | t < f n}, A n ∂Measure.count
    with hKdef
  -- (1) layer cake for ∫ f^p
  have hAlc : ∫⁻ n, ENNReal.ofReal (f n ^ p) ∂Measure.count
      = ENNReal.ofReal p
        * ∫⁻ t in Ioi 0, Measure.count {n : ℕ | t < f n} * ENNReal.ofReal (t ^ (p - 1)) :=
    lintegral_rpow_eq_lintegral_meas_lt_mul Measure.count (Eventually.of_forall hf_nn)
      hf_meas.aemeasurable hp_pos
  -- (2) pointwise use of the restricted weak-type hypothesis
  have hB : (∫⁻ t in Ioi 0, Measure.count {n : ℕ | t < f n} * ENNReal.ofReal (t ^ (p - 1)))
      ≤ K := by
    rw [hKdef]
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hof : ENNReal.ofReal (t ^ (p - 1))
        = ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le (p - 2))]
      congr 1
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
    have hw := hweak t ht0
    calc Measure.count {n : ℕ | t < f n} * ENNReal.ofReal (t ^ (p - 1))
        = Measure.count {n : ℕ | t < f n}
            * (ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal t) := by rw [hof]
      _ = ENNReal.ofReal (t ^ (p - 2))
            * (ENNReal.ofReal t * Measure.count {n : ℕ | t < f n}) := by ring
      _ ≤ ENNReal.ofReal (t ^ (p - 2))
            * (∫⁻ n in {n : ℕ | t < f n}, A n ∂Measure.count) :=
          mul_le_mul_right hw _
  -- (3) weighted layer cake: K is (∫ A·F^(p-1))/(p-1)
  have hCeq : C = ENNReal.ofReal (p - 1) * K := by
    have hνlc := lintegral_rpow_eq_lintegral_meas_lt_mul ν (f := f) (Eventually.of_forall hf_nn)
      hf_meas.aemeasurable hp1pos
    have hνlc_eq : (∫⁻ t in Ioi 0,
          ν {n : ℕ | t < f n} * ENNReal.ofReal (t ^ ((p - 1) - 1))) = K := by
      rw [hKdef]
      apply lintegral_congr
      intro t
      rw [hν, withDensity_apply A (measurableSet_lt measurable_const hf_meas),
        show (p - 1) - 1 = p - 2 by ring, mul_comm]
    have hL : (∫⁻ n, ENNReal.ofReal (f n ^ (p - 1)) ∂ν) = C := by
      rw [hν, lintegral_withDensity_eq_lintegral_mul Measure.count hA_meas
        (((measurable_of_countable f).pow_const (p - 1)).ennreal_ofReal)]
      rw [hCdef]
      apply lintegral_congr
      intro n
      simp only [Pi.mul_apply, A, F]
      rw [ENNReal.ofReal_rpow_of_nonneg (hf_nn n) hp1]
    rw [hνlc_eq, hL] at hνlc
    exact hνlc
  -- (4) Hölder
  have hpq : Real.HolderConjugate p (p / (p - 1)) := by
    rw [Real.holderConjugate_iff]
    exact ⟨hp, by rw [inv_div]; field_simp; ring⟩
  have hA_p : (∫⁻ n, A n ^ p ∂Measure.count)
      = ∫⁻ n, ENNReal.ofReal (a n ^ p) ∂Measure.count := by
    apply lintegral_congr
    intro n
    rw [ENNReal.ofReal_rpow_of_nonneg (ha_nn n) hp_pos.le]
  have hF_p : (∫⁻ n, (F n ^ (p - 1)) ^ (p / (p - 1)) ∂Measure.count)
      = ∫⁻ n, ENNReal.ofReal (f n ^ p) ∂Measure.count := by
    apply lintegral_congr
    intro n
    rw [← ENNReal.rpow_mul (F n) (p - 1) (p / (p - 1)),
      show (p - 1) * (p / (p - 1)) = p by field_simp,
      ENNReal.ofReal_rpow_of_nonneg (hf_nn n) hp_pos.le]
  have hCeq2 : C = ∫⁻ n, (A * fun n => F n ^ (p - 1)) n ∂Measure.count := rfl
  have hH : C ≤ (∫⁻ n, ENNReal.ofReal (a n ^ p) ∂Measure.count) ^ (1 / p)
      * (∫⁻ n, ENNReal.ofReal (f n ^ p) ∂Measure.count) ^ (1 / (p / (p - 1))) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq Measure.count hpq hA_meas.aemeasurable
      hFpow_meas.aemeasurable
    rw [hA_p, hF_p, ← hCeq2] at h
    exact h
  -- (5) put things together
  have hkc : ENNReal.ofReal p * K = ENNReal.ofReal (p / (p - 1)) * C := by
    rw [hCeq, ← mul_assoc, ← ENNReal.ofReal_mul hc_nn]
    rw [show p / (p - 1) * (p - 1) = p by field_simp]
  have hXle : (∫⁻ n, ENNReal.ofReal (f n ^ p) ∂Measure.count)
      ≤ ENNReal.ofReal (p / (p - 1)) * C := by
    rw [hAlc]
    calc ENNReal.ofReal p
          * (∫⁻ t in Ioi 0, Measure.count {n : ℕ | t < f n} * ENNReal.ofReal (t ^ (p - 1)))
        ≤ ENNReal.ofReal p * K := mul_le_mul_right hB _
      _ = ENNReal.ofReal (p / (p - 1)) * C := hkc
  have hCfin : C < ⊤ := by
    rw [hCdef, lintegral_count,
      tsum_eq_sum (s := s) (fun n hn => by simp only [A, hs n hn, ENNReal.ofReal_zero, zero_mul]),
      show (∑ n ∈ s, A n * F n ^ (p - 1)) < ⊤ ↔ ∀ n ∈ s, A n * F n ^ (p - 1) < ⊤ from
        WithTop.sum_lt_top]
    intro n _
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hp1 ENNReal.ofReal_ne_top)
  have hXfin : (∫⁻ n, ENNReal.ofReal (f n ^ p) ∂Measure.count) < ⊤ :=
    lt_of_le_of_lt hXle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCfin)
  have hmain : (∫⁻ n, ENNReal.ofReal (f n ^ p) ∂Measure.count)
      ≤ ENNReal.ofReal (p / (p - 1))
        * ((∫⁻ n, ENNReal.ofReal (a n ^ p) ∂Measure.count) ^ (1 / p)
           * (∫⁻ n, ENNReal.ofReal (f n ^ p) ∂Measure.count) ^ (1 / (p / (p - 1)))) :=
    hXle.trans (mul_le_mul_right hH _)
  have hpqsum : 1 / p + 1 / (p / (p - 1)) = 1 := by
    field_simp
    ring
  have hres := le_mul_rpow_of_le_mul hpqsum hp_pos hq_pos hXfin hmain
  rwa [ENNReal.ofReal_rpow_of_nonneg hc_nn hp_pos.le] at hres

end Commons.Analysis.HardyLittlewood