import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.defs
import Submission.Work.FIArea7.smallCInner2EpsAux.hyperbolaBilinEps
import Submission.Work.FIArea7.sumAbsDiffPLe

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Smooth bilinear (Type II) bound with power loss `(U + c₀ + 2)^ε`.**

This is the `ε`-loss form of the smooth bilinear estimate: it is obtained from
`hyperbolaBilinEps` by Abel summation in the last variable `m·n`, exactly as the
non-`ε` version `Work.FIArea7.smallCInner2Aux.smoothBilinBound` is obtained from
`Work.FIArea7.hyperbolaBilinBound`.  The smooth weight `P` is monotone-in-`K`-Lipschitz
with support in `(a,b]`, so the discrete total variation of `n ↦ P(c₀n)` is `≤ K(b-a)`. -/
theorem smoothBilinEps (h31 : Work.FIArea7.Prop231) :
    ∀ ε : ℝ, 0 < ε → ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (chi : GaussianInt → ℂ) (k : ℤ) (c0 M N U : ℕ) (α β : ℕ → ℂ)
        (P : ℝ → ℝ) (a b K : ℝ),
        1 ≤ c0 →
        (∀ z', ‖chi z'‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ m ∈ Finset.Icc 1 M, ‖α m‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, ‖β n‖ ≤ 1) →
        ContDiff ℝ 1 P → 0 ≤ a → (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
        (∀ u, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u, |deriv P u| ≤ K) →
        ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ U then α m * β n
              * ((P ((c0 : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * (m * n)) else 0)‖
          ≤ C * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
              * ((U : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((U : ℝ) + 2)) ^ A
              * (((U : ℝ) + (c0 : ℝ) + 2) ^ ε)
              * (K * |b - a| + 1) := by
  intro ε hε
  obtain ⟨C1, A1, hC1, hA1, hprop⟩ := hyperbolaBilinEps h31 ε hε
  refine ⟨C1, A1, hC1, hA1, ?_⟩
  intro chi k c0 M N U α β P a b K hc0 hchi hmul hα hβ hP hPa hP0 hP1 hPsupp hPder
  set X : ℕ → ℕ → ℂ := fun m n => α m * β n
      * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * (m * n)) with hX
  set g : ℕ → ℂ := fun v => ((P ((c0 : ℝ) * (v : ℝ)) : ℝ) : ℂ) with hg
  set TT : ℕ → ℂ := fun V => ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
      (if m * n ≤ V then X m n else 0) with hTT
  have hTbound : ∀ V : ℕ, ‖TT V‖
      ≤ C1 * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
          * ((V : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((V : ℝ) + 2)) ^ A1
          * (((V : ℝ) + (c0 : ℝ) + 2) ^ ε) := by
    intro V
    have h := hprop chi k c0 M N V α β hc0 hchi hmul hα hβ
    rw [hTT, hX]
    exact h
  set B : ℝ := C1 * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
      * ((U : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((U : ℝ) + 2)) ^ A1
      * (((U : ℝ) + (c0 : ℝ) + 2) ^ ε) with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    have hU0 : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
    have h1 : 0 ≤ ((c0.divisors.card : ℕ) : ℝ) := by positivity
    have h2 : 0 ≤ ((M : ℝ) + N) ^ ((1 : ℝ) / 12) :=
      Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (M : ℝ) + N) _
    have h3 : 0 ≤ (U : ℝ) ^ ((11 : ℝ) / 12) := Real.rpow_nonneg hU0 _
    have h4 : 0 ≤ (Real.log ((U : ℝ) + 2)) ^ A1 :=
      Real.rpow_nonneg (Real.log_nonneg (by linarith)) A1
    have h5 : 0 ≤ ((U : ℝ) + (c0 : ℝ) + 2) ^ ε := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC1) h1) h2) h3) h4) h5
  have hTle : ∀ V : ℕ, V ≤ U → ‖TT V‖ ≤ B := by
    intro V hV
    refine le_trans (hTbound V) ?_
    rw [hB]
    have hVU : (V : ℝ) ≤ (U : ℝ) := by exact_mod_cast hV
    have hV0 : (0 : ℝ) ≤ (V : ℝ) := Nat.cast_nonneg V
    have hU0 : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
    have hrpow : (V : ℝ) ^ ((11 : ℝ) / 12) ≤ (U : ℝ) ^ ((11 : ℝ) / 12) :=
      Real.rpow_le_rpow hV0 hVU (by norm_num)
    have hlog1 : (1 : ℝ) ≤ (V : ℝ) + 2 := by linarith
    have hlog2 : (V : ℝ) + 2 ≤ (U : ℝ) + 2 := by linarith
    have hlog : Real.log ((V : ℝ) + 2) ^ A1 ≤ Real.log ((U : ℝ) + 2) ^ A1 :=
      Real.rpow_le_rpow (Real.log_nonneg hlog1)
        (Real.log_le_log (by linarith) hlog2) (le_of_lt hA1)
    have hbasele : ((V : ℝ) + (c0 : ℝ) + 2) ^ ε ≤ ((U : ℝ) + (c0 : ℝ) + 2) ^ ε :=
      Real.rpow_le_rpow (by positivity) (by linarith) (le_of_lt hε)
    have h1 : 0 ≤ ((c0.divisors.card : ℕ) : ℝ) := by positivity
    have hMNN : 0 ≤ C1 * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12)) :=
      mul_nonneg (mul_nonneg (le_of_lt hC1) h1) (Real.rpow_nonneg (by positivity) _)
    have hVnn : 0 ≤ Real.log ((V : ℝ) + 2) ^ A1 :=
      Real.rpow_nonneg (Real.log_nonneg hlog1) _
    have hUnn : 0 ≤ Real.log ((U : ℝ) + 2) ^ A1 :=
      Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    have hdU : 0 ≤ ((U : ℝ) + (c0 : ℝ) + 2) ^ ε := by positivity
    have hdV : 0 ≤ ((V : ℝ) + (c0 : ℝ) + 2) ^ ε := by positivity
    calc C1 * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
          * ((V : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((V : ℝ) + 2)) ^ A1
          * (((V : ℝ) + (c0 : ℝ) + 2) ^ ε)
        ≤ C1 * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
          * ((U : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((V : ℝ) + 2)) ^ A1
          * (((V : ℝ) + (c0 : ℝ) + 2) ^ ε) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrpow hMNN) hVnn) hdV
      _ ≤ C1 * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
          * ((U : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((U : ℝ) + 2)) ^ A1
          * (((V : ℝ) + (c0 : ℝ) + 2) ^ ε) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog
            (mul_nonneg hMNN (Real.rpow_nonneg hU0 _))) hdV
      _ ≤ C1 * ((c0.divisors.card : ℕ) : ℝ) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
          * ((U : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((U : ℝ) + 2)) ^ A1
          * (((U : ℝ) + (c0 : ℝ) + 2) ^ ε) :=
          mul_le_mul_of_nonneg_left hbasele
            (mul_nonneg (mul_nonneg hMNN (Real.rpow_nonneg hU0 _)) hUnn)
  have hmain : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        (if m * n ≤ U then α m * β n
          * ((P ((c0 : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
          * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * (m * n)) else 0))
      = g U * TT U - ∑ w ∈ Finset.Icc 1 (U - 1), (g (w + 1) - g w) * TT w := by
    rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun n hn => ?_))]
    · have hpt : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
          (if m * n ≤ U then g (m * n) else 0)
            = (if m * n ≤ U then g U else 0)
              - ∑ w ∈ Finset.Icc 1 (U - 1), (if m * n ≤ w then (g (w + 1) - g w) else 0) := by
        intro m n hm hn
        have hmn1 : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        by_cases h : m * n ≤ U
        · rw [if_pos h, if_pos h]
          have key : ∑ w ∈ Finset.Icc (m * n) (U - 1), (g (w + 1) - g w)
              = g U - g (m * n) := by
            rcases Nat.lt_or_eq_of_le h with hlt | heq
            · have hle : m * n ≤ U - 1 := by omega
              rw [Finset.sum_Icc_sub (f := g) hle]
              have : U - 1 + 1 = U := Nat.sub_add_cancel (by omega)
              rw [this]
            · rw [heq]
              have hempty : Finset.Icc U (U - 1) = ∅ := Finset.Icc_eq_empty (by omega)
              rw [hempty, Finset.sum_empty]; ring
          have hfil : (Finset.Icc 1 (U - 1)).filter (fun w => m * n ≤ w)
              = Finset.Icc (m * n) (U - 1) := by
            ext w; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
          rw [← Finset.sum_filter, hfil, key]; ring
        · rw [if_neg h, if_neg h, zero_sub]
          have hfil : (Finset.Icc 1 (U - 1)).filter (fun w => m * n ≤ w) = ∅ := by
            rw [Finset.filter_eq_empty_iff]; intro w hw
            simp only [Finset.mem_Icc] at hw; omega
          rw [← Finset.sum_filter, hfil, Finset.sum_empty]; ring
      have h1 : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            X m n * (if m * n ≤ U then g U else 0))
          = g U * (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
              (if m * n ≤ U then X m n else 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m hm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n hn
        by_cases hc : m * n ≤ U
        · rw [if_pos hc, if_pos hc]; ring
        · rw [if_neg hc, if_neg hc]; ring
      have h2 : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, ∑ w ∈ Finset.Icc 1 (U - 1),
            X m n * (if m * n ≤ w then (g (w + 1) - g w) else 0))
          = ∑ w ∈ Finset.Icc 1 (U - 1), (g (w + 1) - g w)
              * (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
                  (if m * n ≤ w then X m n else 0)) := by
        rw [Finset.sum_congr rfl (fun m hm => Finset.sum_comm)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro w hw
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m hm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n hn
        by_cases hc : m * n ≤ w
        · rw [if_pos hc, if_pos hc]; ring
        · rw [if_neg hc, if_neg hc]; ring
      have hstep : ∀ m ∈ Finset.Icc 1 M, ∀ n ∈ Finset.Icc 1 N,
          X m n * (if m * n ≤ U then g (m * n) else 0)
            = X m n * (if m * n ≤ U then g U else 0)
              - ∑ w ∈ Finset.Icc 1 (U - 1),
                  X m n * (if m * n ≤ w then (g (w + 1) - g w) else 0) := by
        intro m hm n hn
        rw [hpt m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1, mul_sub, Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun n hn => hstep m hm n hn))]
      rw [Finset.sum_congr rfl (fun m hm => Finset.sum_sub_distrib _ _), Finset.sum_sub_distrib]
      rw [h1, h2]
    · by_cases hc : m * n ≤ U
      · rw [if_pos hc, if_pos hc]
        simp only [hX, hg]
        ring
      · rw [if_neg hc, if_neg hc]
        simp only [hX, hg]
        ring
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hPder 0)
  have hvar : ∑ w ∈ Finset.Icc 1 (U - 1), ‖g (w + 1) - g w‖ ≤ K * |b - a| := by
    by_cases hab : a ≤ b
    · have h := Work.FIArea7.sumAbsDiffPLe hP hPa hab hPsupp hPder (c0 : ℝ)
          (by exact_mod_cast hc0) (U - 1)
      have heq : (∑ w ∈ Finset.Icc 1 (U - 1), ‖g (w + 1) - g w‖)
          = ∑ w ∈ Finset.Icc 1 (U - 1),
              |P ((c0 : ℝ) * (w : ℝ)) - P ((c0 : ℝ) * ((w : ℝ) + 1))| := by
        apply Finset.sum_congr rfl; intro w hw
        rw [hg]
        simp only []
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        simp only [Nat.cast_add, Nat.cast_one]
      refine le_trans (le_of_eq heq) ?_
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      exact h
    · have hPzero : ∀ u, P u = 0 := by
        intro u
        by_contra hne
        have h1 := (hPsupp u hne).1
        have h2 := (hPsupp u hne).2
        have h3 : b < a := not_le.mp hab
        linarith
      have hz : ∀ w, ‖g (w + 1) - g w‖ = 0 := by
        intro w
        simp only [hg, hPzero]
        simp
      rw [Finset.sum_congr rfl (fun w _ => hz w), Finset.sum_const_zero]
      exact mul_nonneg hK0 (abs_nonneg _)
  have hgU : ‖g U‖ ≤ 1 := by
    rw [hg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP0 _)]
    exact hP1 _
  calc ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          (if m * n ≤ U then α m * β n
            * ((P ((c0 : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * (m * n)) else 0)‖
      = ‖g U * TT U - ∑ w ∈ Finset.Icc 1 (U - 1), (g (w + 1) - g w) * TT w‖ := by rw [hmain]
    _ ≤ ‖g U * TT U‖ + ‖∑ w ∈ Finset.Icc 1 (U - 1), (g (w + 1) - g w) * TT w‖ := norm_sub_le _ _
    _ ≤ ‖g U‖ * ‖TT U‖ + ∑ w ∈ Finset.Icc 1 (U - 1), ‖(g (w + 1) - g w) * TT w‖ := by
        refine add_le_add (le_of_eq (norm_mul _ _)) (norm_sum_le _ _)
    _ ≤ 1 * B + ∑ w ∈ Finset.Icc 1 (U - 1), ‖g (w + 1) - g w‖ * B := by
        refine add_le_add ?_ (Finset.sum_le_sum (fun w hw => ?_))
        · exact mul_le_mul hgU (hTle U le_rfl) (norm_nonneg _) zero_le_one
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hTle w (by
            have := (Finset.mem_Icc.mp hw).2; omega)) (norm_nonneg _)
    _ = B + (∑ w ∈ Finset.Icc 1 (U - 1), ‖g (w + 1) - g w‖) * B := by
        rw [one_mul, Finset.sum_mul]
    _ ≤ B + (K * |b - a|) * B := by
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_right hvar hBnn)
    _ = B * (K * |b - a| + 1) := by ring

end

end Work.FIArea7.smallCInner2EpsAux
