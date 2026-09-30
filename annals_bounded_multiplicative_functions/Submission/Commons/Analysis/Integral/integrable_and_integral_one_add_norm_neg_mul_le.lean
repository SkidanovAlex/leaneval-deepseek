import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Integral

open MeasureTheory

/-- `(x / 2) ^ (-A) = 2 ^ A * x ^ (-A)` for `0 ≤ x`. -/
private lemma div_two_rpow_neg (x A : ℝ) (hx : 0 ≤ x) :
    (x / 2) ^ (-A) = 2 ^ A * x ^ (-A) := by
  rw [Real.div_rpow hx (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_eq_mul_inv, inv_inv, mul_comm]

/-- The map `u ↦ v - u` preserves Lebesgue measure on a Euclidean space. -/
private lemma measurePreserving_sub_left {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) :
    MeasurePreserving (fun u : EuclideanSpace ℝ (Fin k) => v - u)
      (volume : Measure (EuclideanSpace ℝ (Fin k))) volume := by
  have h1 : MeasurePreserving (fun u : EuclideanSpace ℝ (Fin k) => -u)
      (volume : Measure (EuclideanSpace ℝ (Fin k))) volume :=
    Measure.measurePreserving_neg volume
  have h2 : MeasurePreserving (fun u : EuclideanSpace ℝ (Fin k) => v + u)
      (volume : Measure (EuclideanSpace ℝ (Fin k))) volume :=
    measurePreserving_add_left volume v
  have h3 := h2.comp h1
  have h4 : (fun u : EuclideanSpace ℝ (Fin k) => v - u)
      = (fun u : EuclideanSpace ℝ (Fin k) => v + u) ∘ (fun u : EuclideanSpace ℝ (Fin k) => -u) := by
    funext u
    simp [Function.comp, sub_eq_add_neg]
  rw [h4]
  exact h3

/-- Change of variables `u ↦ v - u`: the integral of `(1 + ‖·‖) ^ (-B)` is invariant. -/
private lemma integral_one_add_norm_sub {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) (B : ℝ) :
    (∫ u : EuclideanSpace ℝ (Fin k), (1 + ‖v - u‖) ^ (-B))
      = ∫ u : EuclideanSpace ℝ (Fin k), (1 + ‖u‖) ^ (-B) := by
  have h1 : (∫ u : EuclideanSpace ℝ (Fin k), (1 + ‖v - u‖) ^ (-B))
      = ∫ u : EuclideanSpace ℝ (Fin k), (1 + ‖v + u‖) ^ (-B) := by
    rw [show (fun u : EuclideanSpace ℝ (Fin k) => (1 + ‖v - u‖) ^ (-B))
        = (fun w : EuclideanSpace ℝ (Fin k) => (1 + ‖v + w‖) ^ (-B)) ∘
            (fun w : EuclideanSpace ℝ (Fin k) => -w) from by
          funext w
          simp [Function.comp, sub_eq_add_neg]]
    exact integral_neg_eq_self
      (fun w : EuclideanSpace ℝ (Fin k) => (1 + ‖v + w‖) ^ (-B)) volume
  rw [h1]
  exact integral_add_left_eq_self
    (fun x : EuclideanSpace ℝ (Fin k) => (1 + ‖x‖) ^ (-B)) v

open MeasureTheory in
/-- **Convolution of two decaying kernels.**  For exponents `A, B > k` (the dimension),
the convolution of `u ↦ (1 + ‖u‖)^{-A}` and `u ↦ (1 + ‖u‖)^{-B}` over
`EuclideanSpace ℝ (Fin k)` is bounded by a constant times `(1 + ‖v‖)^{-min A B}`,
uniformly in `v`; moreover the integrand is integrable.  (Proof: split the integral into
the regions `‖u‖ ≤ ‖v - u‖` and `‖u‖ > ‖v - u‖`, where in each region
`max ‖u‖ ‖v - u‖ ≳ ‖v‖`.) -/
theorem integrable_and_integral_one_add_norm_neg_mul_le {k : ℕ} {A B : ℝ}
    (hA : (k : ℝ) < A) (hB : (k : ℝ) < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : EuclideanSpace ℝ (Fin k),
      Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
        (1 + ‖u‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B)) (volume : Measure (EuclideanSpace ℝ (Fin k))) ∧
      (∫ u : EuclideanSpace ℝ (Fin k),
        (1 + ‖u‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B)) ≤ C * (1 + ‖v‖) ^ (-(min A B)) := by
  have hA0 : 0 < A := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (k : ℝ)) hA
  have hB0 : 0 < B := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (k : ℝ)) hB
  have hfin : (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) : ℝ) = (k : ℝ) := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hIntA : Integrable (fun u : EuclideanSpace ℝ (Fin k) => (1 + ‖u‖) ^ (-A))
      (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
    integrable_one_add_norm (μ := volume) (r := A) (by rw [hfin]; exact hA)
  have hIntB : Integrable (fun u : EuclideanSpace ℝ (Fin k) => (1 + ‖u‖) ^ (-B))
      (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
    integrable_one_add_norm (μ := volume) (r := B) (by rw [hfin]; exact hB)
  set IA : ℝ := ∫ u : EuclideanSpace ℝ (Fin k), (1 + ‖u‖) ^ (-A) with hIA
  set IB : ℝ := ∫ u : EuclideanSpace ℝ (Fin k), (1 + ‖u‖) ^ (-B) with hIB
  have hIA_nonneg : 0 ≤ IA := by
    rw [hIA]
    exact integral_nonneg (fun u => Real.rpow_nonneg (by positivity) _)
  have hIB_nonneg : 0 ≤ IB := by
    rw [hIB]
    exact integral_nonneg (fun u => Real.rpow_nonneg (by positivity) _)
  refine ⟨2 ^ A * IB + 2 ^ B * IA + 1, ?_, ?_⟩
  · have h2A : 0 < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
    have h2B : 0 < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) B
    nlinarith [mul_nonneg (le_of_lt h2A) hIB_nonneg, mul_nonneg (le_of_lt h2B) hIA_nonneg]
  · intro v
    have hkey : ∀ u : EuclideanSpace ℝ (Fin k),
        (1 + ‖u‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B) ≤
          2 ^ A * (1 + ‖v‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B) +
          2 ^ B * (1 + ‖v‖) ^ (-B) * (1 + ‖u‖) ^ (-A) := by
      intro u
      have hv_le : ‖v‖ ≤ ‖u‖ + ‖v - u‖ := by
        calc ‖v‖ = ‖u + (v - u)‖ := by rw [add_sub_cancel]
          _ ≤ ‖u‖ + ‖v - u‖ := norm_add_le _ _
      rcases le_or_gt ‖u‖ ‖v - u‖ with h | h
      · have hvu : ‖v‖ / 2 ≤ ‖v - u‖ := by linarith
        have hbase : (1 + ‖v‖) / 2 ≤ 1 + ‖v - u‖ := by
          linarith [norm_nonneg (v - u)]
        have hstep : (1 + ‖v - u‖) ^ (-B) ≤ 2 ^ B * (1 + ‖v‖) ^ (-B) := by
          calc (1 + ‖v - u‖) ^ (-B) ≤ ((1 + ‖v‖) / 2) ^ (-B) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
            _ = 2 ^ B * (1 + ‖v‖) ^ (-B) := div_two_rpow_neg (1 + ‖v‖) B (by positivity)
        have h1 : 0 ≤ (1 + ‖u‖) ^ (-A) := Real.rpow_nonneg (by positivity) _
        have h2 : 0 ≤ 2 ^ A * (1 + ‖v‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B) :=
          mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) A)
            (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
        calc (1 + ‖u‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B)
            ≤ (1 + ‖u‖) ^ (-A) * (2 ^ B * (1 + ‖v‖) ^ (-B)) :=
              mul_le_mul_of_nonneg_left hstep h1
          _ = 2 ^ B * (1 + ‖v‖) ^ (-B) * (1 + ‖u‖) ^ (-A) := by ring
          _ ≤ 2 ^ A * (1 + ‖v‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B) +
                2 ^ B * (1 + ‖v‖) ^ (-B) * (1 + ‖u‖) ^ (-A) := le_add_of_nonneg_left h2
      · have hu : ‖v‖ / 2 ≤ ‖u‖ := by linarith
        have hbase : (1 + ‖v‖) / 2 ≤ 1 + ‖u‖ := by
          linarith [norm_nonneg u]
        have hstep : (1 + ‖u‖) ^ (-A) ≤ 2 ^ A * (1 + ‖v‖) ^ (-A) := by
          calc (1 + ‖u‖) ^ (-A) ≤ ((1 + ‖v‖) / 2) ^ (-A) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
            _ = 2 ^ A * (1 + ‖v‖) ^ (-A) := div_two_rpow_neg (1 + ‖v‖) A (by positivity)
        have h2 : 0 ≤ (1 + ‖v - u‖) ^ (-B) := Real.rpow_nonneg (by positivity) _
        have h2' : 0 ≤ 2 ^ B * (1 + ‖v‖) ^ (-B) * (1 + ‖u‖) ^ (-A) :=
          mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) B)
            (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
        calc (1 + ‖u‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B)
            ≤ (2 ^ A * (1 + ‖v‖) ^ (-A)) * (1 + ‖v - u‖) ^ (-B) :=
              mul_le_mul_of_nonneg_right hstep h2
          _ = 2 ^ A * (1 + ‖v‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B) := by ring
          _ ≤ 2 ^ A * (1 + ‖v‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B) +
                2 ^ B * (1 + ‖v‖) ^ (-B) * (1 + ‖u‖) ^ (-A) := le_add_of_nonneg_right h2'
    have hsub_int : Integrable (fun u : EuclideanSpace ℝ (Fin k) => (1 + ‖v - u‖) ^ (-B))
        (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
      (measurePreserving_sub_left v).integrable_comp_of_integrable hIntB
    have hterm1_int : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
        2 ^ A * (1 + ‖v‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B))
        (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
      hsub_int.const_mul (2 ^ A * (1 + ‖v‖) ^ (-A))
    have hterm2_int : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
        2 ^ B * (1 + ‖v‖) ^ (-B) * (1 + ‖u‖) ^ (-A))
        (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
      hIntA.const_mul (2 ^ B * (1 + ‖v‖) ^ (-B))
    have hcont : Continuous (fun u : EuclideanSpace ℝ (Fin k) =>
        (1 + ‖u‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B)) := by
      have hf1a : Continuous (fun u : EuclideanSpace ℝ (Fin k) => (1:ℝ) + ‖u‖) :=
        continuous_const.add continuous_norm
      have hf2a : Continuous (fun u : EuclideanSpace ℝ (Fin k) => (1:ℝ) + ‖v - u‖) :=
        continuous_const.add (continuous_const.sub continuous_id).norm
      have hf1 : Continuous (fun u : EuclideanSpace ℝ (Fin k) => (1 + ‖u‖) ^ (-A)) :=
        hf1a.rpow continuous_const (fun u => Or.inl (by positivity))
      have hf2 : Continuous (fun u : EuclideanSpace ℝ (Fin k) => (1 + ‖v - u‖) ^ (-B)) :=
        hf2a.rpow continuous_const (fun u => Or.inl (by positivity))
      exact hf1.mul hf2
    have hf_int : Integrable (fun u : EuclideanSpace ℝ (Fin k) =>
        (1 + ‖u‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B))
        (volume : Measure (EuclideanSpace ℝ (Fin k))) := by
      refine Integrable.mono' (hterm1_int.add hterm2_int) hcont.aestronglyMeasurable ?_
      filter_upwards with u
      have h1 : 0 ≤ (1 + ‖u‖) ^ (-A) := Real.rpow_nonneg (by positivity) _
      have h2 : 0 ≤ (1 + ‖v - u‖) ^ (-B) := Real.rpow_nonneg (by positivity) _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2)]
      exact hkey u
    have hsplit : (∫ u : EuclideanSpace ℝ (Fin k),
          (2 ^ A * (1 + ‖v‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B) +
           2 ^ B * (1 + ‖v‖) ^ (-B) * (1 + ‖u‖) ^ (-A)))
        = 2 ^ A * (1 + ‖v‖) ^ (-A) * IB + 2 ^ B * (1 + ‖v‖) ^ (-B) * IA := by
      rw [integral_add hterm1_int hterm2_int]
      congr 1
      · rw [integral_const_mul, integral_one_add_norm_sub v B, ← hIB]
      · rw [integral_const_mul, ← hIA]
    have hbase1 : 1 ≤ 1 + ‖v‖ := by have := norm_nonneg v; linarith
    have htA : (1 + ‖v‖) ^ (-A) ≤ (1 + ‖v‖) ^ (-(min A B)) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith [min_le_left A B])
    have htB : (1 + ‖v‖) ^ (-B) ≤ (1 + ‖v‖) ^ (-(min A B)) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith [min_le_right A B])
    have ht : 0 ≤ (1 + ‖v‖) ^ (-(min A B)) := Real.rpow_nonneg (by positivity) _
    have h2A' : 0 ≤ (2 : ℝ) ^ A := Real.rpow_nonneg (by norm_num) A
    have h2B' : 0 ≤ (2 : ℝ) ^ B := Real.rpow_nonneg (by norm_num) B
    have step1 : 2 ^ A * (1 + ‖v‖) ^ (-A) * IB ≤ 2 ^ A * IB * (1 + ‖v‖) ^ (-(min A B)) := by
      calc 2 ^ A * (1 + ‖v‖) ^ (-A) * IB
          = 2 ^ A * ((1 + ‖v‖) ^ (-A) * IB) := by ring
        _ ≤ 2 ^ A * ((1 + ‖v‖) ^ (-(min A B)) * IB) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htA hIB_nonneg) h2A'
        _ = 2 ^ A * IB * (1 + ‖v‖) ^ (-(min A B)) := by ring
    have step2 : 2 ^ B * (1 + ‖v‖) ^ (-B) * IA ≤ 2 ^ B * IA * (1 + ‖v‖) ^ (-(min A B)) := by
      calc 2 ^ B * (1 + ‖v‖) ^ (-B) * IA
          = 2 ^ B * ((1 + ‖v‖) ^ (-B) * IA) := by ring
        _ ≤ 2 ^ B * ((1 + ‖v‖) ^ (-(min A B)) * IA) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htB hIA_nonneg) h2B'
        _ = 2 ^ B * IA * (1 + ‖v‖) ^ (-(min A B)) := by ring
    have hsum : 2 ^ A * IB * (1 + ‖v‖) ^ (-(min A B)) +
          2 ^ B * IA * (1 + ‖v‖) ^ (-(min A B))
        ≤ (2 ^ A * IB + 2 ^ B * IA + 1) * (1 + ‖v‖) ^ (-(min A B)) := by
      rw [show 2 ^ A * IB * (1 + ‖v‖) ^ (-(min A B)) +
            2 ^ B * IA * (1 + ‖v‖) ^ (-(min A B))
          = (2 ^ A * IB + 2 ^ B * IA) * (1 + ‖v‖) ^ (-(min A B)) from by ring]
      apply mul_le_mul_of_nonneg_right _ ht
      linarith [mul_nonneg h2A' hIB_nonneg, mul_nonneg h2B' hIA_nonneg]
    refine ⟨hf_int, ?_⟩
    calc (∫ u : EuclideanSpace ℝ (Fin k),
            (1 + ‖u‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B))
        ≤ ∫ u : EuclideanSpace ℝ (Fin k),
            (2 ^ A * (1 + ‖v‖) ^ (-A) * (1 + ‖v - u‖) ^ (-B) +
             2 ^ B * (1 + ‖v‖) ^ (-B) * (1 + ‖u‖) ^ (-A)) :=
          integral_mono hf_int (hterm1_int.add hterm2_int) hkey
      _ = 2 ^ A * (1 + ‖v‖) ^ (-A) * IB + 2 ^ B * (1 + ‖v‖) ^ (-B) * IA := hsplit
      _ ≤ 2 ^ A * IB * (1 + ‖v‖) ^ (-(min A B)) +
            2 ^ B * IA * (1 + ‖v‖) ^ (-(min A B)) := by linarith [step1, step2]
      _ ≤ (2 ^ A * IB + 2 ^ B * IA + 1) * (1 + ‖v‖) ^ (-(min A B)) := hsum

end Commons.Analysis.Integral