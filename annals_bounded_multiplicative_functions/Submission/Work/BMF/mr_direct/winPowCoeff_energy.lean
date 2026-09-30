import Mathlib
import Submission.Work.BMF.mr_direct.primePolyWindow_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Energy (mean square) bound for the coefficients of a power of a prime-supported
Dirichlet polynomial, in the *window* version.

Let `c` be a sequence of complex numbers with `‖c p‖ ≤ 1` and let

  `winPowCoeff c A B k n = Σ_{f : Fin k → winSet A B, ∏ j, f j = n} ∏ j, c (f j) / (f j)`

be the coefficient of `n^{-it}` in the `k`-th power of `Σ_{p ∈ winSet A B} c p p^{-1-it}`.
This file proves the "energy" estimate

  `Σ_{n ≤ ⌊B⌋^k} ‖winPowCoeff c A B k n‖² ≤ k^k * (Σ_{p ∈ winSet A B} 1/p²)^k`.

The argument is the same as in the dyadic version (`Work.BMF.mr_direct.powCoeff_energy`):
each fibre of the "product of primes" map has at most `k^k` elements because the entries
of a `k`-tuple of primes lie in the set of prime factors of their product, which has at
most `k` elements.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators

/-- Monotonicity of a finite product of natural numbers, without the hypothesis that the
factors are nonnegative. -/
private lemma prod_le_prod_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) {g h : ι → ℕ}
    (hgh : ∀ i ∈ s, g i ≤ h i) : ∏ i ∈ s, g i ≤ ∏ i ∈ s, h i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Nat.mul_le_mul (hgh a (Finset.mem_insert_self a s))
      (ih (fun i hi => hgh i (Finset.mem_insert_of_mem hi)))

/-- Monotonicity of a finite product of real numbers whose factors are nonnegative. -/
private lemma prod_le_prod_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) {g h : ι → ℝ}
    (hg : ∀ i ∈ s, 0 ≤ g i) (hgh : ∀ i ∈ s, g i ≤ h i) :
    ∏ i ∈ s, g i ≤ ∏ i ∈ s, h i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine mul_le_mul ?_ ?_ ?_ ?_
    · exact hgh a (Finset.mem_insert_self a s)
    · exact ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi => hgh i (Finset.mem_insert_of_mem hi))
    · exact Finset.prod_nonneg (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    · exact le_trans (hg a (Finset.mem_insert_self a s)) (hgh a (Finset.mem_insert_self a s))

/-- A product of `k` primes has at most `k` distinct prime factors. -/
private lemma card_primeFactors_prod_le {k : ℕ} (f : Fin k → ℕ) (hf : ∀ j, Nat.Prime (f j)) :
    (∏ j, f j).primeFactors.card ≤ k := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ]
    have h0 : f 0 ≠ 0 := (hf 0).ne_zero
    have hm : (∏ j : Fin m, f j.succ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => (hf j.succ).ne_zero)
    rw [Nat.primeFactors_mul h0 hm, (hf 0).primeFactors]
    have ih' := ih (fun j => f j.succ) (fun j => hf j.succ)
    have hcard := Finset.card_union_le ({f 0} : Finset ℕ)
      ((∏ j : Fin m, f j.succ).primeFactors)
    simp only [Finset.card_singleton] at hcard
    omega

/-- The number of `k`-tuples of primes of `winSet A B` with a prescribed product is at most
`k ^ k`: the entries all belong to the (at most `k`-element) set of prime factors of the
product. -/
private lemma fiber_card_le (A B : ℝ) (k : ℕ) (n : ℕ) :
    ((Fintype.piFinset (fun _ : Fin k => primePolyWindow.winSet A B)).filter
        (fun f => ∏ j, f j = n)).card ≤ k ^ k := by
  set S : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ : Fin k => primePolyWindow.winSet A B)
    with hS
  set F : Finset (Fin k → ℕ) := S.filter (fun f => ∏ j, f j = n) with hF
  by_cases hne : F.Nonempty
  · obtain ⟨f0, hf0⟩ := hne
    have hf0' : f0 ∈ S ∧ (∏ j, f0 j) = n := Finset.mem_filter.mp hf0
    have hp : ∀ j, Nat.Prime (f0 j) := by
      intro j
      have hmemj : f0 ∈ Fintype.piFinset (fun _ : Fin k => primePolyWindow.winSet A B) := by
        rw [← hS]; exact hf0'.1
      exact (Finset.mem_filter.mp ((Fintype.mem_piFinset.mp hmemj) j)).2
    have hpc : n.primeFactors.card ≤ k := by
      rw [← hf0'.2]
      exact card_primeFactors_prod_le f0 hp
    have hsub : F ⊆ Fintype.piFinset (fun _ : Fin k => n.primeFactors) := by
      intro f hf
      rw [Fintype.mem_piFinset]
      intro j
      have hfm : f ∈ Fintype.piFinset (fun _ : Fin k => primePolyWindow.winSet A B) := by
        rw [← hS]; exact (Finset.mem_filter.mp hf).1
      have hfn : (∏ j, f j) = n := (Finset.mem_filter.mp hf).2
      have hpj : Nat.Prime (f j) :=
        (Finset.mem_filter.mp ((Fintype.mem_piFinset.mp hfm) j)).2
      have hdvd : f j ∣ n := by
        rw [← hfn]
        exact Finset.dvd_prod_of_mem f (Finset.mem_univ j)
      have hn0 : n ≠ 0 := by
        rw [← hf0'.2]
        exact Finset.prod_ne_zero_iff.mpr (fun j _ => (hp j).ne_zero)
      exact Nat.mem_primeFactors.mpr ⟨hpj, hdvd, hn0⟩
    calc F.card ≤ (Fintype.piFinset (fun _ : Fin k => n.primeFactors)).card :=
          Finset.card_le_card hsub
      _ = n.primeFactors.card ^ k := by
          rw [Fintype.card_piFinset]
          simp
      _ ≤ k ^ k := Nat.pow_le_pow_left hpc k
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- **Energy bound for the coefficients of the `k`-th power of the window prime polynomial.** -/
theorem winPowCoeff_energy (A B : ℝ) (c : ℕ → ℂ) (k : ℕ)
    (hA : 2 ≤ A) (hAB : A ≤ B) (hk : 1 ≤ k) (hc : ∀ p, ‖c p‖ ≤ 1) :
    (∑ n ∈ Finset.Icc 1 (⌊B⌋₊ ^ k),
        ‖Work.BMF.mr_direct.primePolyWindow.winPowCoeff c A B k n‖ ^ 2)
      ≤ (k : ℝ) ^ k *
          (∑ p ∈ Work.BMF.mr_direct.primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ) ^ 2) ^ k := by
  set S : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ : Fin k => primePolyWindow.winSet A B)
    with hS
  set T : Finset ℕ := Finset.Icc 1 (⌊B⌋₊ ^ k) with hT
  have hmem : ∀ f ∈ S, ∀ j, f j ∈ primePolyWindow.winSet A B := by
    intro f hf j
    rw [hS] at hf
    exact (Fintype.mem_piFinset.mp hf) j
  have hprodmem : ∀ f ∈ S, (∏ j, f j) ∈ T := by
    intro f hf
    rw [hT, Finset.mem_Icc]
    have hp : ∀ j, Nat.Prime (f j) := by
      intro j
      exact (Finset.mem_filter.mp (hmem f hf j)).2
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr (fun j _ => (hp j).ne_zero))
    · calc (∏ j, f j) ≤ ∏ _j : Fin k, ⌊B⌋₊ := prod_le_prod_nat _ (fun j _ =>
              (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem f hf j)).1).2)
        _ = ⌊B⌋₊ ^ k := by simp
  -- step 1: triangle inequality on each fibre
  have hpoint : ∀ n, ‖primePolyWindow.winPowCoeff c A B k n‖
      ≤ ∑ f ∈ S.filter (fun f => ∏ j, f j = n), ∏ j, ‖c (f j)‖ / (f j : ℝ) := by
    intro n
    rw [primePolyWindow.winPowCoeff, ← hS]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun f hf => ?_)
    rw [norm_prod]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        ‖c (f j) * ((f j : ℂ))⁻¹‖ ≤ ‖c (f j)‖ / (f j : ℝ) := by
      intro j _
      rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv]
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ ‖c (f j) * ((f j : ℂ))⁻¹‖ :=
      fun j _ => norm_nonneg _
    simpa using prod_le_prod_nonneg (Finset.univ : Finset (Fin k)) hnn hterm
  -- step 2: Cauchy--Schwarz on each fibre
  have hcs : ∀ n, ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2
      ≤ ((S.filter (fun f => ∏ j, f j = n)).card : ℝ)
        * ∑ f ∈ S.filter (fun f => ∏ j, f j = n), (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2 := by
    intro n
    set F : Finset (Fin k → ℕ) := S.filter (fun f => ∏ j, f j = n) with hF
    have h4 : ‖primePolyWindow.winPowCoeff c A B k n‖
        ≤ ∑ f ∈ F, ∏ j, ‖c (f j)‖ / (f j : ℝ) := by
      rw [hF]; exact hpoint n
    have h5 : ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2
        ≤ (∑ f ∈ F, ∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h4 2
    have h2' : (∑ f ∈ F, ∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2
        ≤ (∑ f ∈ F, (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2) * (F.card : ℝ) := by
      have h2 := Finset.sum_mul_sq_le_sq_mul_sq F
        (fun f => ∏ j, ‖c (f j)‖ / (f j : ℝ)) (fun _ : Fin k → ℕ => (1:ℝ))
      simpa [Finset.sum_const, nsmul_eq_mul] using h2
    calc ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2
        ≤ (∑ f ∈ F, ∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2 := h5
      _ ≤ (∑ f ∈ F, (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2) * (F.card : ℝ) := h2'
      _ = ((S.filter (fun f => ∏ j, f j = n)).card : ℝ)
            * ∑ f ∈ S.filter (fun f => ∏ j, f j = n), (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2 := by
          rw [hF]; ring
  -- step 3: the fibre cardinalities are at most `k ^ k`
  have hcard : ∀ n, ((S.filter (fun f => ∏ j, f j = n)).card : ℝ) ≤ (k : ℝ) ^ k := by
    intro n
    have h1 := fiber_card_le A B k n
    rw [← hS] at h1
    exact_mod_cast h1
  -- step 4: summing over the fibres recovers the full tuple sum
  have hfiber : ∑ n ∈ T, ∑ f ∈ S.filter (fun f => ∏ j, f j = n),
      (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2
      = ∑ f ∈ S, (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2 := by
    rw [hT]; exact Finset.sum_fiberwise_of_maps_to hprodmem _
  -- step 5: the full tuple sum factors as the `k`-th power of the prime sum
  have hfactor : ∑ f ∈ S, (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2
      ≤ (∑ p ∈ primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ) ^ 2) ^ k := by
    have hL : ∑ f ∈ S, (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2
        = ∑ f ∈ S, ∏ j, (‖c (f j)‖ / (f j : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.prod_pow]
    rw [hL, hS, Finset.sum_pow']
    apply Finset.sum_le_sum
    intro f hf
    have hpj : ∀ j, Nat.Prime (f j) := by
      intro j
      exact (Finset.mem_filter.mp ((Fintype.mem_piFinset.mp hf) j)).2
    apply prod_le_prod_nonneg (Finset.univ : Finset (Fin k))
    · intro j _
      positivity
    · intro j _
      have hfj : (1 : ℝ) ≤ (f j : ℝ) := by
        have := (hpj j).two_le
        exact_mod_cast (by omega : 1 ≤ f j)
      have hc1 : ‖c (f j)‖ ≤ 1 := hc (f j)
      have hd : ‖c (f j)‖ / (f j : ℝ) ≤ 1 / (f j : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hc1 (by positivity)
      calc (‖c (f j)‖ / (f j : ℝ)) ^ 2
          ≤ (1 / (f j : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
        _ = (1 : ℝ) / (f j : ℝ) ^ 2 := by rw [div_pow, one_pow]
  -- assembly
  calc ∑ n ∈ T, ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2
      ≤ ∑ n ∈ T, ((S.filter (fun f => ∏ j, f j = n)).card : ℝ)
          * ∑ f ∈ S.filter (fun f => ∏ j, f j = n), (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2 :=
        Finset.sum_le_sum (fun n _ => hcs n)
    _ ≤ ∑ n ∈ T, (k : ℝ) ^ k
          * ∑ f ∈ S.filter (fun f => ∏ j, f j = n), (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_right (hcard n)
          (Finset.sum_nonneg (fun f _ => by positivity))
    _ = (k : ℝ) ^ k * ∑ n ∈ T, ∑ f ∈ S.filter (fun f => ∏ j, f j = n),
          (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (k : ℝ) ^ k * ∑ f ∈ S, (∏ j, ‖c (f j)‖ / (f j : ℝ)) ^ 2 := by rw [hfiber]
    _ ≤ (k : ℝ) ^ k * (∑ p ∈ primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ) ^ 2) ^ k :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)

end Work.BMF.mr_direct
