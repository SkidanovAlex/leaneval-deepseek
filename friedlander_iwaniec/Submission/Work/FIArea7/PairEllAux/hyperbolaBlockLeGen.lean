import Mathlib
import Submission.Work.FIArea7.hyperbolaBlockAux

/-!
# `Work.FIArea7.PairEllAux.hyperbolaBlockLeGen`

`Work.FIArea7.hyperbola_block_le` with the summand `quadEigen ψ (c₀ m n)` replaced by an arbitrary
`Q : ℕ → ℕ → ℂ`.  This is what allows the **coprimality restricted** eigenvalue form
`Σ_{m ≤ M} Σ_{n ≤ N, (m,n)=1} α_m β_n λ(c₀mn)` to be handled against the restricted rectangular
bound `LBilinStar` (the `.2` half of `Prop231`), by taking `Q m n = (m,n)=1 · λ(c₀mn)`.
-/

set_option autoImplicit false

namespace Work.FIArea7.PairEllAux

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **One dyadic block of the hyperbola, with a generic summand.**  Given the separating function
`h` for the threshold `u` (`∫ h(t) k^{it} dt = 1` for `k ≤ u`, `0` otherwise) and a uniform bound
`B` on the twisted bilinear forms `Σ_m Σ_n (α_m m^{it}) (β_n n^{it}) Q_{mn}`, the
hyperbola-restricted sum `Σ_{m ≤ Ma} Σ_{n ≤ Ca, mn ≤ u} α_m β_n Q_{mn}` is bounded by
`B · ∫|h|`. -/
lemma hyperbolaBlockLeGen (h : ℝ → ℝ) (u : ℕ) (hu : 1 ≤ u)
    (hint : ∀ k : ℕ, 1 ≤ k →
      (∫ t : ℝ, (h t : ℂ) * (k : ℂ) ^ (t * Complex.I))
        = if (k : ℝ) ≤ (u : ℝ) then 1 else 0)
    (Ma Ca : ℕ) (Q : ℕ → ℕ → ℂ) (α β : ℕ → ℂ) (B : ℝ) (hBnn : 0 ≤ B)
    (hB : ∀ t : ℝ, ‖∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
        (α m * (m : ℂ) ^ (t * Complex.I)) * (β n * (n : ℂ) ^ (t * Complex.I)) * Q m n‖ ≤ B) :
    ‖∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
        (if m * n ≤ u then α m * β n * Q m n else 0)‖ ≤ B * ∫ t : ℝ, |h t| := by
  have hInt : Integrable (fun t : ℝ => (h t : ℂ)) := by
    by_contra hc
    have h0 : (∫ t : ℝ, (h t : ℂ)) = 0 := MeasureTheory.integral_undef hc
    have h1 : (∫ t : ℝ, (h t : ℂ)) = 1 := by
      have h1' := hint 1 le_rfl
      rw [if_pos (by exact_mod_cast hu)] at h1'
      simpa using h1'
    exact one_ne_zero (h1.symm.trans h0)
  have hAbs : Integrable (fun t : ℝ => |h t|) := by
    have := hInt.norm
    simpa only [Work.FIArea7.norm_ofReal_complex] using this
  set F : ℝ → ℂ := fun t => ∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
        (α m * (m : ℂ) ^ (t * Complex.I)) * (β n * (n : ℂ) ^ (t * Complex.I)) * Q m n with hFdef
  have hBF : ∀ t : ℝ, ‖F t‖ ≤ B := fun t => by rw [hFdef]; exact hB t
  have key : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      Integrable (fun t : ℝ => (α m * β n * Q m n)
        * ((h t : ℂ) * ((m * n : ℕ) : ℂ) ^ (t * Complex.I))) := by
    intro m n hm1 hn1
    have hk : 1 ≤ m * n := by have := Nat.mul_le_mul hm1 hn1; simpa using this
    exact (Work.FIArea7.integrable_h_mul_cpowI h hInt (m * n) hk).const_mul _
  have hmain : (∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
        (if m * n ≤ u then α m * β n * Q m n else 0))
      = ∫ t, (h t : ℂ) * F t := by
    have hstep1 : ∀ m ∈ Finset.Icc 1 Ma, ∀ n ∈ Finset.Icc 1 Ca,
        (if m * n ≤ u then α m * β n * Q m n else 0)
        = ∫ t, (α m * β n * Q m n)
            * ((h t : ℂ) * ((m * n : ℕ) : ℂ) ^ (t * Complex.I)) := by
      intro m hm n hn
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hk : 1 ≤ m * n := by have := Nat.mul_le_mul hm1 hn1; simpa using this
      rw [MeasureTheory.integral_const_mul, hint (m * n) hk]
      by_cases hc : m * n ≤ u
      · rw [if_pos hc, if_pos (by exact_mod_cast hc), mul_one]
      · rw [if_neg hc, if_neg (by exact_mod_cast hc), mul_zero]
    rw [show (∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
          (if m * n ≤ u then α m * β n * Q m n else 0))
        = (∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
            ∫ t, (α m * β n * Q m n)
              * ((h t : ℂ) * ((m * n : ℕ) : ℂ) ^ (t * Complex.I))) from
        Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun n hn => hstep1 m hm n hn))]
    rw [Finset.sum_congr rfl (fun m hm => (MeasureTheory.integral_finset_sum _
          (fun n _hn => key m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp _hn).1)).symm)]
    rw [(MeasureTheory.integral_finset_sum _
          (fun m hm => MeasureTheory.integrable_finset_sum _
            (fun n hn => key m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1))).symm]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [hFdef]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n hn
    rw [Work.FIArea7.natCast_mul_cpow_I]
    ring
  rw [hmain]
  calc ‖∫ t, (h t : ℂ) * F t‖ ≤ ∫ t, ‖(h t : ℂ) * F t‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t, |h t| * B := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun t => norm_nonneg _)
        · exact hAbs.mul_const B
        · exact Filter.Eventually.of_forall (fun t => by
            change ‖(h t : ℂ) * F t‖ ≤ |h t| * B
            rw [norm_mul, Work.FIArea7.norm_ofReal_complex]
            exact mul_le_mul_of_nonneg_left (hBF t) (abs_nonneg _))
    _ = B * ∫ t, |h t| := by rw [MeasureTheory.integral_mul_const, mul_comm]

end

end Work.FIArea7.PairEllAux
