import Mathlib
import Submission.Work.A3.Weil.divisors_card_le_rpow
import Submission.Work.A3.Weil.card_fiber_le_pow_divisors

/-!
# Fibres of the product map on a box are small

For every `k` and every `ε > 0` there is `C > 0` such that for all `m ≥ 1` and all `P ≠ 0` the
number of `k`-tuples `l ∈ [-m,m]^k` of integers with `∏ i, l i = P` is at most `C * m ^ ε`.

The proof combines two inputs:

* `Work.A3.Weil.card_fiber_le_pow_divisors`: the fibre is at most `(#(P.natAbs).divisors) ^ k * 2 ^ k`
  (a tuple with product `P ≠ 0` has all entries nonzero, and each `|l i|` divides `P.natAbs`);
* `Work.A3.Weil.divisors_card_le_rpow`: the divisor function is `O(n ^ δ)` for every `δ > 0`.

Since a fibre element satisfies `P.natAbs = ∏ i, (l i).natAbs ≤ m ^ k`, the exponent `δ` can be
taken `ε / k ^ 2`, which turns `(#divisors(P.natAbs)) ^ k ≤ (C n ^ δ) ^ k ≤ C ^ k * m ^ ε`.
-/

set_option autoImplicit false

namespace Work.A3.Weil

open Finset
open scoped BigOperators

/-- If `n ≤ m ^ k` with `k > 0` then `(n ^ (ε / k ^ 2)) ^ k ≤ m ^ ε`.  This is the power
bookkeeping of the reduction: the exponent `δ = ε / k ^ 2` applied `k` times and compounded with
`n ≤ m ^ k` produces exactly the exponent `ε` in the base `m`. -/
private lemma rpow_div_sq_pow_le {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 0 < k) {m n : ℕ}
    (hn : n ≤ m ^ k) : ((n : ℝ) ^ (ε / (k : ℝ) ^ 2)) ^ k ≤ (m : ℝ) ^ ε := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hδnn : 0 ≤ ε / (k : ℝ) ^ 2 := le_of_lt (div_pos hε (pow_pos hk' 2))
  have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm' : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : ((n : ℝ) ^ (ε / (k : ℝ) ^ 2)) ^ k = (n : ℝ) ^ ((ε / (k : ℝ) ^ 2) * (k : ℝ)) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (ε / (k : ℝ) ^ 2)) k,
      ← Real.rpow_mul hn' _ (k : ℝ)]
  have h2 : (n : ℝ) ≤ (m : ℝ) ^ k := by exact_mod_cast hn
  have h3 : (n : ℝ) ^ ((ε / (k : ℝ) ^ 2) * (k : ℝ))
      ≤ ((m : ℝ) ^ k) ^ ((ε / (k : ℝ) ^ 2) * (k : ℝ)) :=
    Real.rpow_le_rpow hn' h2 (mul_nonneg hδnn (Nat.cast_nonneg k))
  have h4 : ((m : ℝ) ^ k) ^ ((ε / (k : ℝ) ^ 2) * (k : ℝ)) = (m : ℝ) ^ ε := by
    rw [← Real.rpow_natCast (m : ℝ) k,
      ← Real.rpow_mul hm' (k : ℝ) ((ε / (k : ℝ) ^ 2) * (k : ℝ))]
    congr 1
    field_simp
  calc ((n : ℝ) ^ (ε / (k : ℝ) ^ 2)) ^ k = (n : ℝ) ^ ((ε / (k : ℝ) ^ 2) * (k : ℝ)) := h1
    _ ≤ ((m : ℝ) ^ k) ^ ((ε / (k : ℝ) ^ 2) * (k : ℝ)) := h3
    _ = (m : ℝ) ^ ε := h4

theorem card_prod_fiber_le (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (P : ℤ), 1 ≤ m → P ≠ 0 →
      ((Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(m : ℤ)) (m : ℤ))).filter
        (fun l => ∏ i, l i = P)).card ≤ C * (m : ℝ) ^ ε := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- the box `[-m,m]^0` is a singleton
    subst hk0
    refine ⟨1, one_pos, ?_⟩
    intro m P hm hP
    have hcard :
        ((Fintype.piFinset (fun _ : Fin 0 => Finset.Icc (-(m : ℤ)) (m : ℤ))).filter
          (fun l => ∏ i, l i = P)).card ≤ 1 := by
      calc ((Fintype.piFinset (fun _ : Fin 0 => Finset.Icc (-(m : ℤ)) (m : ℤ))).filter
            (fun l => ∏ i, l i = P)).card
          ≤ (Fintype.piFinset (fun _ : Fin 0 => Finset.Icc (-(m : ℤ)) (m : ℤ))).card :=
            Finset.card_filter_le _ _
        _ = 1 := by simp
    calc (((Fintype.piFinset (fun _ : Fin 0 => Finset.Icc (-(m : ℤ)) (m : ℤ))).filter
            (fun l => ∏ i, l i = P)).card : ℝ)
        ≤ 1 := by exact_mod_cast hcard
      _ ≤ (m : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hm) hε.le
      _ = 1 * (m : ℝ) ^ ε := (one_mul _).symm
  · -- `k ≥ 1`
    have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    obtain ⟨C₁, hC₁pos, hC₁⟩ := divisors_card_le_rpow (ε / (k : ℝ) ^ 2)
      (div_pos hε (pow_pos hk' 2))
    refine ⟨2 ^ k * C₁ ^ k, mul_pos (pow_pos (by norm_num) k) (pow_pos hC₁pos k), ?_⟩
    intro m P hm hP
    set F : Finset (Fin k → ℤ) :=
      (Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(m : ℤ)) (m : ℤ))).filter
        (fun l => ∏ i, l i = P) with hFdef
    have hfib := card_fiber_le_pow_divisors k m P hP
    have hfibR : (F.card : ℝ) ≤ (((P.natAbs).divisors.card : ℝ)) ^ k * 2 ^ k := by
      have h := hfib
      rw [hFdef]
      exact_mod_cast h
    rcases Finset.eq_empty_or_nonempty F with hE | ⟨l, hl⟩
    · -- empty fibre: nothing to bound
      rw [hE, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (le_of_lt (mul_pos (pow_pos (by norm_num) k) (pow_pos hC₁pos k)))
        (Real.rpow_nonneg (Nat.cast_nonneg m) ε)
    · -- nonempty fibre: `P.natAbs ≤ m ^ k`
      rw [hFdef, Finset.mem_filter] at hl
      obtain ⟨hlmem, hlprod⟩ := hl
      have hbox : ∀ i, l i ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := fun i =>
        Fintype.mem_piFinset.mp hlmem i
      have hle : ∀ i, (l i).natAbs ≤ m := by
        intro i
        rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
        exact abs_le.mpr ⟨(Finset.mem_Icc.mp (hbox i)).1, (Finset.mem_Icc.mp (hbox i)).2⟩
      have hprod : P.natAbs = ∏ i, (l i).natAbs := by
        rw [← hlprod]
        exact map_prod Int.natAbsHom l Finset.univ
      have hn_le : P.natAbs ≤ m ^ k := by
        rw [hprod]
        calc ∏ i, (l i).natAbs ≤ ∏ _i : Fin k, m :=
              Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i _ => hle i)
          _ = m ^ k := by simp [Finset.prod_const, Fintype.card_fin]
      have hn1 : 1 ≤ P.natAbs := by
        have := Int.natAbs_pos.mpr hP
        omega
      have hmain : (((P.natAbs).divisors.card : ℝ)) ^ k * 2 ^ k
          ≤ (2 ^ k * C₁ ^ k) * (m : ℝ) ^ ε := by
        have hd : ((P.natAbs).divisors.card : ℝ)
            ≤ C₁ * (P.natAbs : ℝ) ^ (ε / (k : ℝ) ^ 2) := hC₁ P.natAbs hn1
        have hstep : (((P.natAbs).divisors.card : ℝ)) ^ k
            ≤ (C₁ * (P.natAbs : ℝ) ^ (ε / (k : ℝ) ^ 2)) ^ k :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hd k
        have hstep2 : (C₁ * (P.natAbs : ℝ) ^ (ε / (k : ℝ) ^ 2)) ^ k
            = C₁ ^ k * ((P.natAbs : ℝ) ^ (ε / (k : ℝ) ^ 2)) ^ k := by
          rw [mul_pow]
        have hstep3 : ((P.natAbs : ℝ) ^ (ε / (k : ℝ) ^ 2)) ^ k ≤ (m : ℝ) ^ ε :=
          rpow_div_sq_pow_le hε hkpos hn_le
        calc (((P.natAbs).divisors.card : ℝ)) ^ k * 2 ^ k
            ≤ (C₁ * (P.natAbs : ℝ) ^ (ε / (k : ℝ) ^ 2)) ^ k * 2 ^ k :=
              mul_le_mul_of_nonneg_right hstep (by positivity)
          _ = C₁ ^ k * ((P.natAbs : ℝ) ^ (ε / (k : ℝ) ^ 2)) ^ k * 2 ^ k := by rw [hstep2]
          _ ≤ C₁ ^ k * (m : ℝ) ^ ε * 2 ^ k :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hstep3 (pow_nonneg hC₁pos.le k)) (by positivity)
          _ = (2 ^ k * C₁ ^ k) * (m : ℝ) ^ ε := by ring
      calc (F.card : ℝ) ≤ (((P.natAbs).divisors.card : ℝ)) ^ k * 2 ^ k := hfibR
        _ ≤ (2 ^ k * C₁ ^ k) * (m : ℝ) ^ ε := hmain

end Work.A3.Weil
