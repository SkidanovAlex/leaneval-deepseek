import Mathlib
import Submission.Work.BMF.halasz_plancherel_defs
import Submission.Work.BMF.tendsto_integral_KfN
import Submission.Work.BMF.tendsto_integral_dirSum
import Submission.Work.BMF.integral_dirSum_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Finset MeasureTheory Filter
open scoped Topology

namespace Work.BMF

/-- `KfN f N t` written as a sum over the full range `Icc 1 N` with an explicit cut-off. -/
private lemma KfN_eq (f : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    KfN f N t = ∑ n ∈ Icc 1 N, (if n ≤ ⌊t⌋₊ then f n * (Real.log n : ℂ) else 0) := by
  rw [KfN, ← sum_filter]
  congr 1
  ext x
  simp only [mem_Icc, mem_filter, le_min_iff]
  tauto

/-- Pointwise expansion of `‖KfN f N t‖ ^ 2` as a double sum over the cut-off terms. -/
private lemma KfN_normSq (f : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    ‖KfN f N t‖ ^ 2 = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (if max m n ≤ ⌊t⌋₊ then
        ((f m * (Real.log m : ℂ)) * starRingEnd ℂ (f n * (Real.log n : ℂ))).re else 0) := by
  rw [KfN_eq]
  have hzc : ∀ z : ℂ, (z * starRingEnd ℂ z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [← hzc]
  have hconj : (starRingEnd ℂ) (∑ n ∈ Icc 1 N,
      (if n ≤ ⌊t⌋₊ then f n * (Real.log n : ℂ) else 0))
    = ∑ n ∈ Icc 1 N, (if n ≤ ⌊t⌋₊ then starRingEnd ℂ (f n * (Real.log n : ℂ)) else 0) := by
    rw [map_sum]
    refine sum_congr rfl fun n _ => ?_
    by_cases h : n ≤ ⌊t⌋₊ <;> simp [h]
  rw [hconj, sum_mul_sum, Complex.re_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [Complex.re_sum]
  refine sum_congr rfl fun n _ => ?_
  by_cases hm : m ≤ ⌊t⌋₊
  · by_cases hn : n ≤ ⌊t⌋₊
    · rw [if_pos hm, if_pos hn, if_pos (max_le_iff.mpr ⟨hm, hn⟩)]
    · rw [if_pos hm, if_neg hn, mul_zero, Complex.zero_re,
        if_neg (fun h => hn (le_trans (le_max_right m n) h))]
  · rw [if_neg hm, zero_mul, Complex.zero_re,
      if_neg (fun h => hm (le_trans (le_max_left m n) h))]

/-- The indicator of a half line `Ici M` of `t ↦ c * t ^ (-(3+2α))` is integrable. -/
private lemma integrable_indicator_Ici (M : ℕ) (hM : 1 ≤ M) (c α : ℝ) (hα : 0 < α) :
    Integrable (fun t : ℝ => (Set.Ici (M:ℝ)).indicator (fun t => c * t ^ (-(3 + 2 * α))) t)
      volume := by
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  rw [integrable_indicator_iff measurableSet_Ici]
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-(3 + 2 * α))) (Set.Ioi ((M:ℝ) - 1/2)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)
  have h2 : IntegrableOn (fun t : ℝ => c * t ^ (-(3 + 2 * α))) (Set.Ioi ((M:ℝ) - 1/2)) :=
    h1.integrable.const_mul c
  exact h2.mono_set (fun x hx => by
    simp only [Set.mem_Ici] at hx
    simp only [Set.mem_Ioi]
    linarith)

/-- Integral of the indicator of `Ici M` against `t ↦ c * t ^ (-(3+2α))`. -/
private lemma integral_indicator_Ici (M : ℕ) (hM : 1 ≤ M) (c α : ℝ) (hα : 0 < α) :
    (∫ t in Set.Ioi (0:ℝ), (Set.Ici (M:ℝ)).indicator (fun t => c * t ^ (-(3 + 2 * α))) t)
      = c * ((M : ℝ) ^ (-(2 + 2 * α)) / (2 + 2 * α)) := by
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  rw [setIntegral_indicator measurableSet_Ici]
  have hset : Set.Ioi (0:ℝ) ∩ Set.Ici (M:ℝ) = Set.Ici (M:ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    exact ⟨fun h => h.2, fun h => ⟨by linarith [h, hM1], h⟩⟩
  rw [hset, integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_Ioi_rpow_of_lt (by linarith) (by linarith)]
  congr 1
  rw [show -(3 + 2 * α) + 1 = -(2 + 2 * α) by ring]
  simp only [div_neg, neg_div, neg_neg]

/-- Truncated evaluation of the left hand side of the Mellin–Plancherel identity. -/
theorem integral_KfN_sq (f : ℕ → ℂ) (α : ℝ) (hα : 0 < α) (N : ℕ) :
    (∫ t in Set.Ioi (0 : ℝ), ‖KfN f N t‖ ^ 2 / t ^ (3 + 2 * α)) = (1 / (2 + 2 * α)) * UN f α N := by
  -- pointwise a.e. expansion into a finite double sum of half-line indicators
  have hpt : ∀ᵐ t ∂volume, t ∈ Set.Ioi (0 : ℝ) →
      ‖KfN f N t‖ ^ 2 / t ^ (3 + 2 * α) =
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          (Set.Ici (((max m n : ℕ) : ℝ))).indicator
            (fun t => ((f m * (Real.log m : ℂ)) * starRingEnd ℂ (f n * (Real.log n : ℂ))).re
              * t ^ (-(3 + 2 * α))) t := by
    refine Eventually.of_forall fun t ht => ?_
    have h0 : (0:ℝ) ≤ t := le_of_lt ht
    rw [KfN_normSq f N t, div_eq_mul_inv, ← Real.rpow_neg h0]
    rw [sum_mul]
    refine sum_congr rfl fun m hm => ?_
    rw [sum_mul]
    refine sum_congr rfl fun n hn => ?_
    have hm1 : 1 ≤ max m n :=
      le_trans (mem_Icc.mp hm).1 (le_max_left m n)
    have hiff : max m n ≤ ⌊t⌋₊ ↔ ((max m n : ℕ) : ℝ) ≤ t :=
      ⟨fun h => le_trans (by exact_mod_cast h) (Nat.floor_le h0), fun h => Nat.le_floor h⟩
    rw [ite_mul, zero_mul]
    simp only [Set.indicator_apply, Set.mem_Ici]
    by_cases h : ((max m n : ℕ) : ℝ) ≤ t
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]
  rw [setIntegral_congr_ae measurableSet_Ioi hpt]
  have hInt : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, IntegrableOn
      (fun t : ℝ => (Set.Ici (((max m n : ℕ) : ℝ))).indicator
        (fun t => ((f m * (Real.log m : ℂ)) * starRingEnd ℂ (f n * (Real.log n : ℂ))).re
          * t ^ (-(3 + 2 * α))) t) (Set.Ioi 0) := by
    intro m hm n hn
    exact (integrable_indicator_Ici (max m n)
      (le_trans (mem_Icc.mp hm).1 (le_max_left m n)) _ α hα).integrableOn
  rw [integral_finsetSum (s := Icc 1 N) (fun m hm =>
        integrable_finsetSum (Icc 1 N) (fun n hn => (hInt m hm n hn)))]
  rw [sum_congr rfl (fun m hm => integral_finsetSum (Icc 1 N) (fun n hn => hInt m hm n hn))]
  rw [sum_congr rfl (fun m hm => sum_congr rfl (fun n hn =>
        integral_indicator_Ici (max m n) (le_trans (mem_Icc.mp hm).1 (le_max_left m n)) _ α hα))]
  rw [UN, one_div, Finset.mul_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun n hn => ?_
  simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-!
## Mellin–Plancherel (Parseval) identity

Assembling the truncated computations `integral_KfN_sq` and `integral_dirSum_sq` with the two
limit statements `tendsto_integral_KfN` and `tendsto_integral_dirSum`.
-/

/-- Mellin–Plancherel (Parseval) identity for the summatory function `Kf f t = Σ_{n ≤ t} f n · log n`
of the Dirichlet coefficients `n ↦ f n · log n`. -/
theorem halasz_plancherel (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (α : ℝ) (hα : 0 < α) :
    (∫ t in Set.Ioi (0 : ℝ), ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) =
      (1 / (2 * Real.pi)) *
        ∫ τ : ℝ, ‖Work.BMF.Kser f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
          ‖((((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))‖ ^ 2 := by
  have hD := tendsto_integral_KfN f hb α hα
  have hE := tendsto_integral_dirSum f hb α hα
  have hev : (fun N : ℕ => ∫ t in Set.Ioi (0 : ℝ), ‖KfN f N t‖ ^ 2 / t ^ (3 + 2 * α))
      =ᶠ[atTop] (fun N : ℕ => (1 / (2 * Real.pi)) *
        ∫ τ : ℝ, ‖dirSum f α N τ‖ ^ 2 / ‖((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2) :=
    Eventually.of_forall fun N => by
      dsimp only
      rw [integral_KfN_sq f α hα N, integral_dirSum_sq f α hα N]
  have h2 : Filter.Tendsto
      (fun N : ℕ => ∫ t in Set.Ioi (0 : ℝ), ‖KfN f N t‖ ^ 2 / t ^ (3 + 2 * α)) Filter.atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ τ : ℝ, ‖Kser f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
          ‖((((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))‖ ^ 2)) :=
    (hE.const_mul (1 / (2 * Real.pi))).congr' hev.symm
  exact tendsto_nhds_unique hD h2

end Work.BMF
