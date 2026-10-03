import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Commons.Analysis.ExponentialSums.exp_eval_div_eq_exp_eval_mod
import Submission.Commons.Analysis.ExponentialSums.poly_phase_residue_split
import Submission.Commons.Analysis.Polynomial.abs_eval_sub_eval_le

namespace Commons.Analysis.ExponentialSums

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

/-- Evaluation of a mapped integer polynomial at an integer cast. -/
lemma eval_map_int_cast (P : Polynomial ℤ) (x : ℤ) :
    (P.map (Int.castRingHom ℝ)).eval ((x:ℝ)) = ((P.eval x : ℤ) : ℝ) := by
  rw [Polynomial.eval_map]; simp

/-- Riemann-sum error bound for a Lipschitz function on `[0, M]` with unit mesh. -/
theorem norm_sum_range_sub_integral_le_lipschitz (g : ℝ → ℂ) (M : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) (M : ℝ)))
    (hlip : ∀ x ∈ Set.Icc (0 : ℝ) (M : ℝ), ∀ y ∈ Set.Icc (0 : ℝ) (M : ℝ),
      ‖g x - g y‖ ≤ L * |x - y|) :
    ‖(∑ p ∈ Finset.range M, g (p : ℝ)) - ∫ t in (0 : ℝ)..(M : ℝ), g t‖ ≤ (M : ℝ) * L := by
  have hInt : ∀ p : ℕ, p < M → IntervalIntegrable g volume (p:ℝ) ((p:ℝ)+1) := by
    intro p hp
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply hg.mono
    intro x hx
    refine ⟨le_trans (Nat.cast_nonneg p) hx.1, ?_⟩
    have h1 : ((p:ℝ)+1) ≤ (M:ℝ) := by
      have : p + 1 ≤ M := hp
      exact_mod_cast this
    linarith [hx.2]
  have hsplit : ∫ t in (0:ℝ)..(M:ℝ), g t
      = ∑ p ∈ Finset.range M, ∫ t in (p:ℝ)..((p:ℝ)+1), g t := by
    have := sum_integral_adjacent_intervals (f := g) (μ := volume) (a := fun k : ℕ => (k:ℝ)) (n := M)
      (fun k hk => by simpa using hInt k hk)
    simpa using this.symm
  have hconst : ∀ p : ℕ, (∫ t in (p:ℝ)..((p:ℝ)+1), g ((p:ℝ))) = g (p:ℝ) := by
    intro p
    rw [intervalIntegral.integral_const]
    norm_num
  have hsumeq : (∑ p ∈ Finset.range M, (g (p:ℝ) - ∫ t in (p:ℝ)..((p:ℝ)+1), g t))
      = ∑ p ∈ Finset.range M, (∫ t in (p:ℝ)..((p:ℝ)+1), (g (p:ℝ) - g t)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpM : p < M := Finset.mem_range.mp hp
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hInt p hpM)]
    rw [hconst p]
  rw [hsplit, ← Finset.sum_sub_distrib, hsumeq]
  calc ‖∑ p ∈ Finset.range M, ∫ t in (p:ℝ)..((p:ℝ)+1), (g (p:ℝ) - g t)‖
      ≤ ∑ p ∈ Finset.range M, ‖∫ t in (p:ℝ)..((p:ℝ)+1), (g (p:ℝ) - g t)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.range M, L := by
        apply Finset.sum_le_sum
        intro p hp
        have hpM : p < M := Finset.mem_range.mp hp
        have h1 : ((p:ℝ)+1) ≤ (M:ℝ) := by
          have : p + 1 ≤ M := hpM
          exact_mod_cast this
        have hb : |((p:ℝ)+1) - (p:ℝ)| = 1 := by
          rw [show ((p:ℝ)+1) - (p:ℝ) = 1 by ring]; exact abs_one
        calc ‖∫ t in (p:ℝ)..((p:ℝ)+1), (g (p:ℝ) - g t)‖
            ≤ L * |((p:ℝ)+1) - (p:ℝ)| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro t ht
              rw [Set.uIoc_of_le (by linarith : (p:ℝ) ≤ (p:ℝ)+1)] at ht
              have ht_mem : t ∈ Set.Icc (0:ℝ) (M:ℝ) :=
                ⟨by linarith [ht.1, (by positivity : (0:ℝ) ≤ (p:ℝ))], by linarith [ht.2, h1]⟩
              have hp_mem : (p:ℝ) ∈ Set.Icc (0:ℝ) (M:ℝ) :=
                ⟨(by positivity : (0:ℝ) ≤ (p:ℝ)), by linarith⟩
              have h2 : |(p:ℝ) - t| ≤ 1 := by
                rw [abs_of_nonpos (by linarith [ht.1])]; linarith [ht.2]
              calc ‖g (p:ℝ) - g t‖ ≤ L * |(p:ℝ) - t| := hlip _ hp_mem _ ht_mem
                _ ≤ L * 1 := mul_le_mul_of_nonneg_left h2 hL
                _ = L := mul_one L
          _ = L := by rw [hb, mul_one]
    _ = (M:ℝ) * L := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Block bound for a Lipschitz phase: the residue block `∑_{p<P} φ(pq+r)` is the
integral `∫_0^{N/q} φ(qt)` up to `2 L (N+q) + 1`. -/
lemma phase_block_bound
    (N q r P : ℕ) (φ : ℝ → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hφ : Continuous φ)
    (hlip : ∀ x ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)), ∀ y ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)),
        ‖φ x - φ y‖ ≤ L * |x - y|)
    (hnorm : ∀ x ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)), ‖φ x‖ ≤ 1)
    (hq : 1 ≤ q) (hN : 1 ≤ N) (hr : r < q)
    (hP_le : (P:ℝ) * (q:ℝ) + (r:ℝ) ≤ (N:ℝ) + (q:ℝ))
    (hP_ge : (N:ℝ) ≤ (P:ℝ) * (q:ℝ) + (q:ℝ)) :
    ‖(∑ p ∈ Finset.range P, φ (((p*q+r:ℕ)):ℝ)) - ∫ t in (0:ℝ)..((N:ℝ)/(q:ℝ)), φ ((q:ℝ)*t)‖
      ≤ 2 * L * ((N:ℝ) + (q:ℝ)) + 1 := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hM0 : (0:ℝ) ≤ (N:ℝ) + (q:ℝ) := by positivity
  set M : ℝ := (N:ℝ) + (q:ℝ) with hMdef
  have hPr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
  have hPq_le : (P:ℝ) * (q:ℝ) ≤ M := by rw [hMdef]; linarith [hP_le, hPr0]
  have hP_le_M : (P:ℝ) ≤ M / (q:ℝ) := by
    rw [le_div_iff₀ hq0]; linarith [hPq_le]
  have hPnq_ub : (P:ℝ) - (N:ℝ)/(q:ℝ) ≤ 1 := by
    have hrw : (N:ℝ)/(q:ℝ) + 1 = ((N:ℝ)+(q:ℝ))/(q:ℝ) := by
      rw [add_div, div_self (ne_of_gt hq0)]
    have h : (P:ℝ) ≤ (N:ℝ)/(q:ℝ) + 1 := by
      rw [hrw, le_div_iff₀ hq0]
      linarith [hPq_le, hMdef]
    linarith
  have hPnq_lb : -1 ≤ (P:ℝ) - (N:ℝ)/(q:ℝ) := by
    have h : (N:ℝ) - (q:ℝ) ≤ (P:ℝ)*(q:ℝ) := by linarith [hP_ge]
    have h2 : ((N:ℝ) - (q:ℝ))/(q:ℝ) ≤ (P:ℝ) := by rw [div_le_iff₀ hq0]; linarith
    have h3 : ((N:ℝ) - (q:ℝ))/(q:ℝ) = (N:ℝ)/(q:ℝ) - 1 := by
      rw [sub_div, div_self (ne_of_gt hq0)]
    linarith [h3 ▸ h2]
  have hPabs : |(P:ℝ) - (N:ℝ)/(q:ℝ)| ≤ 1 := abs_le.mpr ⟨hPnq_lb, hPnq_ub⟩
  have hmem : ∀ t : ℝ, 0 ≤ t → t ≤ (P:ℝ) → (q:ℝ)*t + (r:ℝ) ∈ Set.Icc (0:ℝ) M := by
    intro t ht0 htP
    refine ⟨by positivity, ?_⟩
    have : (q:ℝ)*t ≤ (q:ℝ)*(P:ℝ) := by
      apply mul_le_mul_of_nonneg_left htP (le_of_lt hq0)
    rw [hMdef]; nlinarith [this, hP_le]
  have hg : ContinuousOn (fun t : ℝ => φ ((q:ℝ)*t + (r:ℝ))) (Set.Icc (0:ℝ) (P:ℝ)) :=
    (hφ.comp (by continuity)).continuousOn
  have hglip : ∀ x ∈ Set.Icc (0:ℝ) (P:ℝ), ∀ y ∈ Set.Icc (0:ℝ) (P:ℝ),
      ‖φ ((q:ℝ)*x + (r:ℝ)) - φ ((q:ℝ)*y + (r:ℝ))‖ ≤ (L*(q:ℝ)) * |x - y| := by
    intro x hx y hy
    have := hlip _ (hmem x hx.1 hx.2) _ (hmem y hy.1 hy.2)
    have hxy : |(q:ℝ)*x + (r:ℝ) - ((q:ℝ)*y + (r:ℝ))| = (q:ℝ) * |x - y| := by
      rw [show (q:ℝ)*x + (r:ℝ) - ((q:ℝ)*y + (r:ℝ)) = (q:ℝ)*(x-y) by ring, abs_mul,
        abs_of_pos hq0]
    rw [hxy] at this
    calc ‖φ ((q:ℝ)*x + (r:ℝ)) - φ ((q:ℝ)*y + (r:ℝ))‖
        ≤ L * ((q:ℝ) * |x - y|) := this
      _ = (L*(q:ℝ)) * |x - y| := by ring
  have hLq : 0 ≤ L * (q:ℝ) := by positivity
  have hpiece1 : ‖(∑ p ∈ Finset.range P, φ (((p*q+r:ℕ)):ℝ))
      - ∫ t in (0:ℝ)..(P:ℝ), φ ((q:ℝ)*t + (r:ℝ))‖ ≤ L * M := by
    have h := norm_sum_range_sub_integral_le_lipschitz (fun t : ℝ => φ ((q:ℝ)*t + (r:ℝ))) P hLq hg hglip
    have hsum : (∑ p ∈ Finset.range P, φ (((p*q+r:ℕ)):ℝ))
        = ∑ p ∈ Finset.range P, φ ((q:ℝ)*(p:ℝ) + (r:ℝ)) := by
      apply Finset.sum_congr rfl; intro p hp; congr 1; push_cast; ring
    rw [hsum]
    exact le_trans h (by
      calc (P:ℝ) * (L*(q:ℝ)) = L * ((P:ℝ)*(q:ℝ)) := by ring
        _ ≤ L * M := mul_le_mul_of_nonneg_left hPq_le hL)
  have hInt1 : IntervalIntegrable (fun t : ℝ => φ ((q:ℝ)*t + (r:ℝ))) volume (0:ℝ) (P:ℝ) :=
    (hg.intervalIntegrable_of_Icc (by positivity))
  have hInt2 : IntervalIntegrable (fun t : ℝ => φ ((q:ℝ)*t)) volume (0:ℝ) (P:ℝ) :=
    ((hφ.comp (by continuity)).continuousOn.intervalIntegrable_of_Icc (by positivity))
  have hInt3 : IntervalIntegrable (fun t : ℝ => φ ((q:ℝ)*t)) volume (0:ℝ) ((N:ℝ)/(q:ℝ)) :=
    ((hφ.comp (by continuity)).continuousOn.intervalIntegrable_of_Icc (by positivity))
  have hpiece2 : ‖(∫ t in (0:ℝ)..(P:ℝ), φ ((q:ℝ)*t + (r:ℝ)))
      - ∫ t in (0:ℝ)..((N:ℝ)/(q:ℝ)), φ ((q:ℝ)*t)‖ ≤ L * M + 1 := by
    have hsplit : (∫ t in (0:ℝ)..(P:ℝ), φ ((q:ℝ)*t + (r:ℝ)))
        - ∫ t in (0:ℝ)..((N:ℝ)/(q:ℝ)), φ ((q:ℝ)*t)
        = (∫ t in (0:ℝ)..(P:ℝ), (φ ((q:ℝ)*t + (r:ℝ)) - φ ((q:ℝ)*t)))
          + ∫ t in ((N:ℝ)/(q:ℝ))..(P:ℝ), φ ((q:ℝ)*t) := by
      have key1 := intervalIntegral.integral_sub hInt1 hInt2
      have key2 := intervalIntegral.integral_interval_sub_left hInt2 hInt3
      rw [← key2, key1]; ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hA : ‖∫ t in (0:ℝ)..(P:ℝ), (φ ((q:ℝ)*t + (r:ℝ)) - φ ((q:ℝ)*t))‖ ≤ L * M := by
      have hbd : ∀ t ∈ Set.uIoc (0:ℝ) (P:ℝ), ‖φ ((q:ℝ)*t + (r:ℝ)) - φ ((q:ℝ)*t)‖ ≤ L*(q:ℝ) := by
        intro t ht
        rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ (P:ℝ))] at ht
        have ht0 : 0 ≤ t := le_of_lt ht.1
        have htP : t ≤ (P:ℝ) := ht.2
        have h1 := hmem t ht0 htP
        have h2 : (q:ℝ)*t ∈ Set.Icc (0:ℝ) M := by
          refine ⟨by positivity, ?_⟩
          rw [hMdef]; nlinarith [h1.2, hPr0]
        calc ‖φ ((q:ℝ)*t + (r:ℝ)) - φ ((q:ℝ)*t)‖ ≤ L * |((q:ℝ)*t + (r:ℝ)) - (q:ℝ)*t| := hlip _ h1 _ h2
          _ = L * (r:ℝ) := by rw [show ((q:ℝ)*t + (r:ℝ)) - (q:ℝ)*t = (r:ℝ) by ring, abs_of_nonneg hPr0]
          _ ≤ L * (q:ℝ) := by apply mul_le_mul_of_nonneg_left _ hL; exact_mod_cast le_of_lt hr
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t : ℝ => φ ((q:ℝ)*t + (r:ℝ)) - φ ((q:ℝ)*t)) (a := 0) (b := (P:ℝ)) (C := L*(q:ℝ)) hbd
      refine le_trans h ?_
      rw [show |(P:ℝ) - 0| = (P:ℝ) by rw [sub_zero, abs_of_nonneg (by positivity)]]
      calc (L*(q:ℝ)) * (P:ℝ) = L*((P:ℝ)*(q:ℝ)) := by ring
        _ ≤ L * M := mul_le_mul_of_nonneg_left hPq_le hL
    have hB : ‖∫ t in ((N:ℝ)/(q:ℝ))..(P:ℝ), φ ((q:ℝ)*t)‖ ≤ 1 := by
      have hbd : ∀ t ∈ Set.uIoc ((N:ℝ)/(q:ℝ)) (P:ℝ), ‖φ ((q:ℝ)*t)‖ ≤ 1 := by
        intro t ht
        have ht0 : 0 ≤ t := by
          have h1 : 0 ≤ min ((N:ℝ)/(q:ℝ)) (P:ℝ) := le_min (by positivity) (by positivity)
          rcases Set.mem_uIoc.mp ht with ⟨h,_⟩ | ⟨h,_⟩
          · exact le_trans h1 (le_trans (min_le_left _ _) (le_of_lt h))
          · exact le_trans h1 (le_trans (min_le_right _ _) (le_of_lt h))
        have htle : t ≤ max ((N:ℝ)/(q:ℝ)) (P:ℝ) := by
          rcases Set.mem_uIoc.mp ht with ⟨_,h⟩ | ⟨_,h⟩
          · exact le_trans h (le_max_right _ _)
          · exact le_trans h (le_max_left _ _)
        have hqmax : (q:ℝ) * max ((N:ℝ)/(q:ℝ)) (P:ℝ) ≤ M := by
          rw [mul_max_of_nonneg _ _ (le_of_lt hq0)]
          apply max_le
          · have : (q:ℝ)*((N:ℝ)/(q:ℝ)) = (N:ℝ) := by field_simp
            rw [this, hMdef]; linarith
          · calc (q:ℝ)*(P:ℝ) ≤ M - (r:ℝ) := by linarith [hP_le]
            _ ≤ M := by linarith [hPr0]
        have htM : (q:ℝ)*t ≤ M :=
          le_trans (mul_le_mul_of_nonneg_left htle (le_of_lt hq0)) hqmax
        exact hnorm ((q:ℝ)*t) ⟨by positivity, htM⟩
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t : ℝ => φ ((q:ℝ)*t)) (a := (N:ℝ)/(q:ℝ)) (b := (P:ℝ)) (C := 1) hbd
      refine le_trans h ?_
      rw [one_mul]
      exact hPabs
    linarith [hA, hB]
  have hdecomp : (∑ p ∈ Finset.range P, φ (((p*q+r:ℕ)):ℝ)) - ∫ t in (0:ℝ)..((N:ℝ)/(q:ℝ)), φ ((q:ℝ)*t)
      = ((∑ p ∈ Finset.range P, φ (((p*q+r:ℕ)):ℝ)) - ∫ t in (0:ℝ)..(P:ℝ), φ ((q:ℝ)*t + (r:ℝ)))
        + ((∫ t in (0:ℝ)..(P:ℝ), φ ((q:ℝ)*t + (r:ℝ))) - ∫ t in (0:ℝ)..((N:ℝ)/(q:ℝ)), φ ((q:ℝ)*t)) := by
    ring
  rw [hdecomp]
  refine le_trans (norm_add_le _ _) ?_
  linarith [hpiece1, hpiece2]

/-- Change of variables for the major-arc oscillatory integral. -/
lemma inv_q_mul_integral_eq (N q : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N) (φ : ℝ → ℂ) (hφ : Continuous φ) :
    (q:ℂ)⁻¹ * (∫ s in (0:ℝ)..1, φ ((N:ℝ)*s)) = (N:ℂ)⁻¹ * ∫ t in (0:ℝ)..((N:ℝ)/(q:ℝ)), φ ((q:ℝ)*t) := by
  have hNne : (N:ℝ) ≠ 0 := by positivity
  have hqne : (q:ℝ) ≠ 0 := by positivity
  have hcompN := intervalIntegral.integral_comp_mul_left (f := φ) (a := (0:ℝ)) (b := (1:ℝ)) (c := (N:ℝ)) hNne
  simp only [mul_one, mul_zero] at hcompN
  have hcompq := intervalIntegral.integral_comp_mul_left (f := φ) (a := (0:ℝ)) (b := (N:ℝ)/(q:ℝ)) (c := (q:ℝ)) hqne
  simp only [mul_zero] at hcompq
  have hqNq : (q:ℝ) * ((N:ℝ)/(q:ℝ)) = (N:ℝ) := by field_simp
  rw [hqNq] at hcompq
  have hNc : ((N:ℝ)⁻¹ • (∫ u in (0:ℝ)..(N:ℝ), φ u)) = (N:ℂ)⁻¹ * ∫ u in (0:ℝ)..(N:ℝ), φ u := by
    rw [Complex.real_smul]
    congr 1
    simp
  have hqc : ((q:ℝ)⁻¹ • (∫ u in (0:ℝ)..(N:ℝ), φ u)) = (q:ℂ)⁻¹ * ∫ u in (0:ℝ)..(N:ℝ), φ u := by
    rw [Complex.real_smul]
    congr 1
    simp
  rw [hNc] at hcompN
  rw [hqc] at hcompq
  have hqc0 : (q:ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast]; exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hNc0 : (N:ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast]; exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hqI : (∫ u in (0:ℝ)..(N:ℝ), φ u) = (q:ℂ) * ∫ t in (0:ℝ)..((N:ℝ)/(q:ℝ)), φ ((q:ℝ)*t) := by
    rw [hcompq, ← mul_assoc, mul_inv_cancel₀ hqc0, one_mul]
  rw [hcompN, hqI]
  field_simp

/-- Arithmetic of the residue block lengths. -/
lemma card_block_bounds (N q r : ℕ) (hq : 1 ≤ q) (hr : r < q) :
    ((((N + q - 1 - r) / q : ℕ)) : ℝ) * (q:ℝ) + (r:ℝ) ≤ (N:ℝ) + (q:ℝ) ∧
    (N:ℝ) ≤ ((((N + q - 1 - r) / q : ℕ)) : ℝ) * (q:ℝ) + (q:ℝ) := by
  have hq0 : 0 < q := by omega
  set P : ℕ := (N + q - 1 - r) / q with hP
  have hle : P * q ≤ N + q - 1 - r := by rw [hP]; exact Nat.div_mul_le_self _ _
  have hlt : N + q - 1 - r < (P + 1) * q := by
    rw [hP]; exact Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) hq0
  have hrN : r ≤ N + q - 1 := by omega
  constructor
  · have h1 : P * q + r ≤ N + q := by
      have := Nat.add_le_add_right hle r
      rw [Nat.sub_add_cancel hrN] at this
      omega
    have h2 : ((P * q + r : ℕ) : ℝ) ≤ ((N + q : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  · have h2 : N ≤ P * q + q := by
      have hxx : N + q - 1 - r + 1 = N + q - r := by omega
      have h1' : N + q - 1 - r + 1 ≤ (P + 1) * q := hlt
      rw [hxx, Nat.add_mul, one_mul] at h1'
      omega
    have h3 : ((N : ℕ) : ℝ) ≤ ((P * q + q : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith


end Commons.Analysis.ExponentialSums