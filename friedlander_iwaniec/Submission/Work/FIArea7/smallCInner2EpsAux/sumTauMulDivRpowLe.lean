import Mathlib
import Submission.Work.FIArea7.smallCInnerAux.sumTauRpow

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

/-- Pointwise bound: for `1 ≤ d`, the floor-division power `⌊u/d⌋^{11/12}` is at most
`u^{11/12} · d^{-11/12}`.  (No hypothesis `d ≤ u` is needed: when `d > u` the left side is `0`.) -/
private lemma rpowDivFloorLe (u d : ℕ) (hd : 1 ≤ d) :
    (((u / d : ℕ) : ℝ)) ^ ((11 : ℝ) / 12)
      ≤ (u : ℝ) ^ ((11 : ℝ) / 12) * (d : ℝ) ^ (-(11 : ℝ) / 12) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := le_of_lt hdpos
  have hunn : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
  have hfloor : (((u / d : ℕ)) : ℝ) ≤ (u : ℝ) / (d : ℝ) := Nat.cast_div_le
  have h1 : (((u / d : ℕ)) : ℝ) ^ ((11 : ℝ) / 12) ≤ ((u : ℝ) / (d : ℝ)) ^ ((11 : ℝ) / 12) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hfloor (by norm_num)
  have h2 : ((u : ℝ) / (d : ℝ)) ^ ((11 : ℝ) / 12)
      = (u : ℝ) ^ ((11 : ℝ) / 12) * (d : ℝ) ^ (-(11 : ℝ) / 12) := by
    rw [Real.div_rpow hunn hdnn, div_eq_mul_inv]
    rw [show (-(11 : ℝ) / 12) = -((11 : ℝ) / 12) by norm_num, Real.rpow_neg hdnn]
  rw [h2] at h1
  exact h1

theorem sumTauMulDivRpowLe (c u D : ℕ) (hu : 1 ≤ u)
    (hτ : ∀ m n : ℕ, (m * n).divisors.card ≤ m.divisors.card * n.divisors.card) :
    Finset.sum (Finset.Icc 1 D) (fun d => (((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12)))
      ≤ 24 * (((c.divisors.card : ℕ) : ℝ)) * (D : ℝ) ^ ((1 : ℝ) / 12)
          * (u : ℝ) ^ ((11 : ℝ) / 12) * Real.log ((u : ℝ) + 2) := by
  classical
  -- ## Step 0: notation
  set A : ℝ := (((c.divisors.card : ℕ) : ℝ)) with hA
  set U : ℝ := (u : ℝ) ^ ((11 : ℝ) / 12) with hUdef
  set N : ℕ := min D u with hNdef
  have hAnn : 0 ≤ A := by rw [hA]; exact Nat.cast_nonneg _
  have hUnn : 0 ≤ U := by
    rw [hUdef]; exact Real.rpow_nonneg (Nat.cast_nonneg u) _
  -- ## Step 1: terms with `d > u` vanish, so the sum is supported on `d ≤ u`.
  have hvan : ∀ d ∈ Finset.Icc 1 D, d ∉ (Finset.Icc 1 D).filter (fun d => d ≤ u) →
      ((((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12))) = 0 := by
    intro d hd hdnot
    have hdu : ¬ d ≤ u := fun hle => hdnot (Finset.mem_filter.mpr ⟨hd, hle⟩)
    have hlt : u < d := not_le.mp hdu
    have hdiv : u / d = 0 := Nat.div_eq_of_lt hlt
    rw [hdiv, Nat.cast_zero, Real.zero_rpow (by norm_num : ((11 : ℝ) / 12) ≠ 0), mul_zero]
  have hsplit : (Finset.Icc 1 D).filter (fun d => d ≤ u) = Finset.Icc 1 N := by
    rw [hNdef]
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.le_min]
    omega
  have hLHS : Finset.sum (Finset.Icc 1 D)
        (fun d => (((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12)))
      = Finset.sum (Finset.Icc 1 N)
        (fun d => (((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12))) := by
    rw [← Finset.sum_subset (Finset.filter_subset _ _) hvan, hsplit]
  -- ## Step 2: pointwise bound on the retained range.
  have hpt : ∀ d ∈ Finset.Icc 1 N,
      ((((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12)))
        ≤ A * ((((d.divisors.card : ℕ) : ℝ)) * (U * (d : ℝ) ^ (-(11 : ℝ) / 12))) := by
    intro d hd
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
    have hdu : d ≤ u := le_trans hdN (by rw [hNdef]; exact min_le_right D u)
    have htau : (((c * d).divisors.card : ℕ) : ℝ)
        ≤ (((c.divisors.card : ℕ) : ℝ)) * (((d.divisors.card : ℕ) : ℝ)) := by
      exact_mod_cast hτ c d
    have hrpow := rpowDivFloorLe u d hd1
    have hUnn' : (0 : ℝ) ≤ (u : ℝ) ^ ((11 : ℝ) / 12) := Real.rpow_nonneg (Nat.cast_nonneg u) _
    have hprod : (((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12))
        ≤ ((((c.divisors.card : ℕ) : ℝ)) * (((d.divisors.card : ℕ) : ℝ)))
            * ((u : ℝ) ^ ((11 : ℝ) / 12) * (d : ℝ) ^ (-(11 : ℝ) / 12)) :=
      mul_le_mul htau hrpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    calc ((((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12)))
        ≤ ((((c.divisors.card : ℕ) : ℝ)) * (((d.divisors.card : ℕ) : ℝ)))
            * ((u : ℝ) ^ ((11 : ℝ) / 12) * (d : ℝ) ^ (-(11 : ℝ) / 12)) := hprod
      _ = A * ((((d.divisors.card : ℕ) : ℝ)) * (U * (d : ℝ) ^ (-(11 : ℝ) / 12))) := by
          rw [hA, hUdef]; ring
  have hsum_le : Finset.sum (Finset.Icc 1 N)
        (fun d => (((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12)))
      ≤ Finset.sum (Finset.Icc 1 N)
        (fun d => A * ((((d.divisors.card : ℕ) : ℝ)) * (U * (d : ℝ) ^ (-(11 : ℝ) / 12)))) :=
    Finset.sum_le_sum hpt
  -- ## Step 3: factor out `A · U`.
  have hfac : Finset.sum (Finset.Icc 1 N)
        (fun d => A * ((((d.divisors.card : ℕ) : ℝ)) * (U * (d : ℝ) ^ (-(11 : ℝ) / 12))))
      = A * U * Finset.sum (Finset.Icc 1 N)
        (fun d => (((d.divisors.card : ℕ) : ℝ)) * (d : ℝ) ^ (-(11 : ℝ) / 12)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  -- ## Step 4: apply the weighted divisor-sum bound.
  have hbd : Finset.sum (Finset.Icc 1 N)
        (fun d => (((d.divisors.card : ℕ) : ℝ)) * (d : ℝ) ^ (-(11 : ℝ) / 12))
      ≤ 24 * (N : ℝ) ^ ((1 : ℝ) / 12) * Real.log ((N : ℝ) + 2) :=
    Work.FIArea7.smallCInnerAux.sumTauRpow N
  -- ## Step 5: monotonicity in `N ≤ D`, `N ≤ u`.
  have hminle : (N : ℝ) ≤ (D : ℝ) := by rw [hNdef]; exact_mod_cast min_le_left D u
  have hminleu : (N : ℝ) ≤ (u : ℝ) := by rw [hNdef]; exact_mod_cast min_le_right D u
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hrpowmono : (N : ℝ) ^ ((1 : ℝ) / 12) ≤ (D : ℝ) ^ ((1 : ℝ) / 12) :=
    Real.rpow_le_rpow hN0 hminle (by norm_num)
  have hlogmono : Real.log ((N : ℝ) + 2) ≤ Real.log ((u : ℝ) + 2) := by
    refine Real.log_le_log (by positivity) ?_
    linarith
  have hlogN0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith [hN0])
  have hstep : (N : ℝ) ^ ((1 : ℝ) / 12) * Real.log ((N : ℝ) + 2)
      ≤ (D : ℝ) ^ ((1 : ℝ) / 12) * Real.log ((u : ℝ) + 2) :=
    mul_le_mul hrpowmono hlogmono hlogN0 (Real.rpow_nonneg hD0 _)
  -- ## Step 6: assemble.
  calc Finset.sum (Finset.Icc 1 D)
        (fun d => (((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12)))
      = Finset.sum (Finset.Icc 1 N)
        (fun d => (((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12))) := hLHS
    _ ≤ Finset.sum (Finset.Icc 1 N)
        (fun d => A * ((((d.divisors.card : ℕ) : ℝ)) * (U * (d : ℝ) ^ (-(11 : ℝ) / 12)))) := hsum_le
    _ = A * U * Finset.sum (Finset.Icc 1 N)
        (fun d => (((d.divisors.card : ℕ) : ℝ)) * (d : ℝ) ^ (-(11 : ℝ) / 12)) := hfac
    _ ≤ A * U * (24 * (N : ℝ) ^ ((1 : ℝ) / 12) * Real.log ((N : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hbd (mul_nonneg hAnn hUnn)
    _ ≤ 24 * A * (D : ℝ) ^ ((1 : ℝ) / 12) * U * Real.log ((u : ℝ) + 2) := by
        have hrew : A * U * (24 * (N : ℝ) ^ ((1 : ℝ) / 12) * Real.log ((N : ℝ) + 2))
            = 24 * A * U * ((N : ℝ) ^ ((1 : ℝ) / 12) * Real.log ((N : ℝ) + 2)) := by ring
        rw [hrew]
        calc 24 * A * U * ((N : ℝ) ^ ((1 : ℝ) / 12) * Real.log ((N : ℝ) + 2))
            ≤ 24 * A * U * ((D : ℝ) ^ ((1 : ℝ) / 12) * Real.log ((u : ℝ) + 2)) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = 24 * A * (D : ℝ) ^ ((1 : ℝ) / 12) * U * Real.log ((u : ℝ) + 2) := by ring
    _ = 24 * (((c.divisors.card : ℕ) : ℝ)) * (D : ℝ) ^ ((1 : ℝ) / 12)
          * (u : ℝ) ^ ((11 : ℝ) / 12) * Real.log ((u : ℝ) + 2) := by
        rw [hA, hUdef]

end Work.FIArea7.smallCInner2EpsAux
