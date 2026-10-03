import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Commons.NumberTheory.DirichletCharacter.chi4_primeRecips_sub_const_powLog
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.PrimeCounting
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_eventually_bounded
import Submission.Commons.NumberTheory.Mertens.mertens_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Diophantine

/-- The real-valued Dirichlet character `χ₄` on `ℕ` (values `0, 1, -1`). -/
noncomputable def chi4R (n : ℕ) : ℝ :=
  (Commons.NumberTheory.DirichletCharacter.chi4Fun ((n : ℕ) : ZMod 4)).re

lemma chi4R_eq (n : ℕ) : chi4R n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  unfold chi4R
  rw [Commons.NumberTheory.DirichletCharacter.chi4Fun_eq_zmod]
  rw [show (↑(ZMod.χ₄ ↑n) : ℂ).re = ((ZMod.χ₄ ↑n : ℤ) : ℝ) from by
    exact_mod_cast Complex.ofReal_re ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)]
  exact_mod_cast ZMod.χ₄_nat_eq_if_mod_four n

/-- A prime is congruent to `1`, `2` or `3` modulo `4`. -/
lemma prime_mod_four (p : ℕ) (hp : p.Prime) : p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by
  have hlt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
  have hne0 : p % 4 ≠ 0 := by
    intro h
    have hdvd : 4 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases hp.eq_one_or_self_of_dvd 4 hdvd with h1 | h4
    · norm_num at h1
    · rw [← h4] at hp; norm_num at hp
  omega

lemma chi4R_div_eq (p : ℕ) (hp : p.Prime) :
    chi4R p / (p : ℝ) = (if p % 4 = 1 then 1 / (p : ℝ) else 0)
      - (if p % 4 = 3 then 1 / (p : ℝ) else 0) := by
  rcases prime_mod_four p hp with h | h | h
  · have h2 : p % 2 = 1 := by omega
    rw [chi4R_eq, if_neg (by omega : ¬ p % 2 = 0), if_pos h]
    rw [if_pos h, if_neg (by omega : ¬ p % 4 = 3)]
    ring
  · have h2 : p % 2 = 0 := by omega
    rw [chi4R_eq, if_pos h2]
    rw [if_neg (by omega : ¬ p % 4 = 1), if_neg (by omega : ¬ p % 4 = 3)]
    ring
  · have h2 : p % 2 = 1 := by omega
    rw [chi4R_eq, if_neg (by omega : ¬ p % 2 = 0), if_neg (by omega : ¬ p % 4 = 1)]
    rw [if_neg (by omega : ¬ p % 4 = 1), if_pos h]
    ring

/-- The `χ₄`-weighted prime reciprocal sum is the difference of the two nontrivial
residue class sums. -/
lemma sum_chi4_split (z : ℕ) :
    (∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ))
      = (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 1), 1 / (p : ℝ))
        - (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 3), 1 / (p : ℝ)) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact chi4R_div_eq p (Nat.mem_primesLE.mp hp).2

lemma filter_mod_four_two (z : ℕ) (hz : 2 ≤ z) :
    (Nat.primesLE z).filter (fun p => p % 4 = 2) = {2} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_singleton, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpz, hpprime⟩, hp4⟩
    have h2 : p % 2 = 0 := by omega
    have : p = 2 := by
      rcases Nat.Prime.eq_two_or_odd hpprime with h | h
      · exact h
      · omega
    exact this
  · rintro rfl
    exact ⟨⟨hz, Nat.prime_two⟩, by norm_num⟩

/-- The full prime reciprocal sum splits into the two nontrivial residue classes plus the
single term `1/2` coming from `p = 2`. -/
lemma sum_all_split (z : ℕ) (hz : 2 ≤ z) :
    (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ))
      = 1 / 2 + (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 1), 1 / (p : ℝ))
        + (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 3), 1 / (p : ℝ)) := by
  have hpoint : ∀ p ∈ Nat.primesLE z, (1 : ℝ) / (p : ℝ)
      = (if p % 4 = 1 then 1 / (p : ℝ) else 0) + (if p % 4 = 3 then 1 / (p : ℝ) else 0)
        + (if p % 4 = 2 then 1 / (p : ℝ) else 0) := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesLE.mp hp).2
    rcases prime_mod_four p hpp with h | h | h
    · rw [if_pos h, if_neg (by omega : ¬ p % 4 = 3), if_neg (by omega : ¬ p % 4 = 2)]
      ring
    · rw [if_neg (by omega : ¬ p % 4 = 1), if_neg (by omega : ¬ p % 4 = 3), if_pos h]
      ring
    · rw [if_neg (by omega : ¬ p % 4 = 1), if_pos h, if_neg (by omega : ¬ p % 4 = 2)]
      ring
  calc (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ))
      = ∑ p ∈ Nat.primesLE z, ((if p % 4 = 1 then 1 / (p : ℝ) else 0)
          + (if p % 4 = 3 then 1 / (p : ℝ) else 0) + (if p % 4 = 2 then 1 / (p : ℝ) else 0)) :=
        Finset.sum_congr rfl hpoint
    _ = (∑ p ∈ Nat.primesLE z, if p % 4 = 1 then 1 / (p : ℝ) else 0)
          + (∑ p ∈ Nat.primesLE z, if p % 4 = 3 then 1 / (p : ℝ) else 0)
          + (∑ p ∈ Nat.primesLE z, if p % 4 = 2 then 1 / (p : ℝ) else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 1), 1 / (p : ℝ))
          + (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 3), 1 / (p : ℝ))
          + (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 2), 1 / (p : ℝ)) := by
        rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    _ = 1 / 2 + (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 1), 1 / (p : ℝ))
          + (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 3), 1 / (p : ℝ)) := by
        rw [filter_mod_four_two z hz, Finset.sum_singleton]
        ring

/-- **Asymptotic size of the prime reciprocal sum over the class `3 mod 4`.**  There is a
constant `K` with `|Σ_{p ≤ z, p % 4 = 3} 1/p − (1/2) log log z| ≤ K` for all `z ≥ 11`.
This combines the sharp second Mertens theorem (`primeRecips_sub_loglog_bound`) with the
analytic input that `Σ_p χ₄(p)/p` converges (`chi4_primeRecips_sub_const_powLog`), using
the identities `sum_all_split` and `sum_chi4_split`. -/
theorem sum_three_mod_four_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 11 ≤ z →
      |(∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 3), 1 / (p : ℝ))
          - (1 / 2) * Real.log (Real.log (z : ℝ))| ≤ K := by
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  obtain ⟨C0, C2, hC2pos, hC2⟩ :=
    Commons.NumberTheory.DirichletCharacter.chi4_primeRecips_sub_const_powLog 1 (by norm_num)
  refine ⟨C1 / 2 + (|C0| + C2 / Real.log 11) / 2 + 1 / 4, by positivity, ?_⟩
  intro z hz
  have hzR : (11 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hz2 : 2 ≤ z := by omega
  have hzR2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hlogzpos : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have hlog11pos : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
  -- Bound for the full prime reciprocal sum.
  have hA : |(∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) - Real.log (Real.log (z : ℝ))| ≤ C1 := by
    have h := hC1 (z : ℝ) hzR
    rw [Nat.floor_natCast] at h
    exact h
  -- Bound for the `χ₄`-weighted sum.
  have hX : |(∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) - C0| ≤ C2 / Real.log (z : ℝ) := by
    have h := hC2 (z : ℝ) hzR2
    rw [Nat.floor_natCast, Real.rpow_one] at h
    have hsum : (∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ))
        = ∑ p ∈ Nat.primesLE z,
            (Commons.NumberTheory.DirichletCharacter.chi4Fun ((p : ℕ) : ZMod 4)).re / (p : ℝ) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp [chi4R]
    rwa [hsum]
  have hlog_le : C2 / Real.log (z : ℝ) ≤ C2 / Real.log 11 :=
    div_le_div_of_nonneg_left (le_of_lt hC2pos) hlog11pos
      (Real.log_le_log (by norm_num) hzR)
  have hXabs : |(∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ))| ≤ |C0| + C2 / Real.log 11 := by
    have h1 : |(∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) - C0| ≤ C2 / Real.log 11 :=
      le_trans hX hlog_le
    have h2 : |(∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ))|
        = |((∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) - C0) + C0| := by ring_nf
    rw [h2]
    calc |((∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) - C0) + C0|
        ≤ |(∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) - C0| + |C0| := abs_add_le _ _
      _ ≤ C2 / Real.log 11 + |C0| := by linarith
      _ = |C0| + C2 / Real.log 11 := by ring
  -- The key linear identity.
  have hmain : (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 3), 1 / (p : ℝ))
      = ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ))
          - (∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) - 1 / 2) / 2 := by
    have h1 := sum_all_split z hz2
    have h2 := sum_chi4_split z
    linarith
  have habs (u v : ℝ) : |u - v| ≤ |u| + |v| := by
    have h := abs_add_le u (-v)
    simpa [sub_eq_add_neg] using h
  have habs2 (u v : ℝ) : |u / 2 - v / 2| ≤ |u| / 2 + |v| / 2 := by
    have h := habs (u / 2) (v / 2)
    simp only [abs_div] at h
    norm_num at h
    exact h
  rw [hmain]
  have hEq : ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ))
        - (∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) - 1 / 2) / 2
        - (1 / 2) * Real.log (Real.log (z : ℝ))
      = ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) - Real.log (Real.log (z : ℝ))) / 2
        - (∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) / 2 - 1 / 4 := by ring
  rw [hEq]
  clear hEq hmain
  calc |((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) - Real.log (Real.log (z : ℝ))) / 2
        - (∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) / 2 - 1 / 4|
      = |(((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) - Real.log (Real.log (z : ℝ))) / 2
          - (∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) / 2) - 1 / 4| := by ring_nf
    _ ≤ |((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) - Real.log (Real.log (z : ℝ))) / 2
          - (∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ)) / 2| + |1 / 4| := habs _ _
    _ ≤ (|(∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) - Real.log (Real.log (z : ℝ))| / 2
          + |(∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ))| / 2) + |1 / 4| := by
        linarith [habs2 ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) - Real.log (Real.log (z : ℝ)))
          (∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ))]
    _ = |(∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) - Real.log (Real.log (z : ℝ))| / 2
          + |(∑ p ∈ Nat.primesLE z, chi4R p / (p : ℝ))| / 2 + 1 / 4 := by
        simp only [abs_div]; norm_num
    _ ≤ C1 / 2 + (|C0| + C2 / Real.log 11) / 2 + 1 / 4 := by linarith [hA, hXabs]

/-- For `z ≤ 10` the only primes `≡ 3 (mod 4)` below `z` are `3` and `7`. -/
lemma filter_three_mod_four_le_ten (z : ℕ) (hz : z ≤ 10) :
    (Nat.primesLE z).filter (fun p => p % 4 = 3) ⊆ ({3, 7} : Finset ℕ) := by
  intro p hp
  rw [Finset.mem_filter, Nat.mem_primesLE] at hp
  obtain ⟨⟨hpz, hpprime⟩, hp4⟩ := hp
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hp10 : p ≤ 10 := le_trans hpz hz
  have h2 : 2 ≤ p := hpprime.two_le
  interval_cases p <;> simp_all [Nat.prime_def_lt]

/-- The asymptotic bound of `sum_three_mod_four_bound` holds for **all** `z ≥ 4`. -/
theorem sum_three_mod_four_bound_all :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 4 ≤ z →
      |(∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 3), 1 / (p : ℝ))
          - (1 / 2) * Real.log (Real.log (z : ℝ))| ≤ K := by
  obtain ⟨K0, hK0pos, hK0⟩ := sum_three_mod_four_bound
  refine ⟨max K0 5, lt_of_lt_of_le hK0pos (le_max_left _ _), ?_⟩
  intro z hz4
  by_cases hz11 : 11 ≤ z
  · exact le_trans (hK0 z hz11) (le_max_left _ _)
  · have hz10 : z ≤ 10 := by omega
    have hzR : (4 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz4
    have hzRpos : (0 : ℝ) < (z : ℝ) := by linarith
    have hS3le : (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 3), 1 / (p : ℝ)) ≤ 10 / 21 := by
      have hsub := filter_three_mod_four_le_ten z hz10
      have h1 : (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 3), 1 / (p : ℝ))
          ≤ ∑ p ∈ ({3, 7} : Finset ℕ), 1 / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
      refine le_trans h1 ?_
      norm_num [Finset.sum_insert, Finset.sum_singleton]
    have hS3nn : 0 ≤ (∑ p ∈ (Nat.primesLE z).filter (fun p => p % 4 = 3), 1 / (p : ℝ)) :=
      Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
    have hlogz_ge1 : 1 ≤ Real.log (z : ℝ) := by
      rw [Real.le_log_iff_exp_le hzRpos]
      exact le_trans (le_of_lt Real.exp_one_lt_three) (by exact_mod_cast (by omega : 3 ≤ z))
    have hlogz_le9 : Real.log (z : ℝ) ≤ 9 := by
      have h := Real.log_le_sub_one_of_pos hzRpos
      have hzR10 : (z : ℝ) ≤ 10 := by exact_mod_cast hz10
      linarith
    have hloglog_ge : 0 ≤ Real.log (Real.log (z : ℝ)) := Real.log_nonneg hlogz_ge1
    have hloglog_le : Real.log (Real.log (z : ℝ)) ≤ 8 := by
      have h1 : 0 < Real.log (z : ℝ) := by linarith
      have h2 : Real.log (Real.log (z : ℝ)) ≤ Real.log 9 := Real.log_le_log h1 (by linarith)
      have h3 : Real.log 9 ≤ 8 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
        linarith
      linarith
    have habsL : |(1 / 2) * Real.log (Real.log (z : ℝ))| ≤ 4 := by
      rw [abs_le]; constructor <;> linarith
    rw [abs_le]; constructor
    · have h5 : -(max K0 5) ≤ -5 := by
        have : (5 : ℝ) ≤ max K0 5 := le_max_right _ _
        linarith
      linarith [hS3nn, habsL, h5]
    · have h5 : (5 : ℝ) ≤ max K0 5 := le_max_right _ _
      linarith [hS3le, hloglog_ge, h5]

/-! ### Elementary product-to-exponential bounds -/

private lemma one_sub_inv_le_exp_neg (p : ℕ) :
    (1 : ℝ) - 1 / (p : ℝ) ≤ Real.exp (-(1 / (p : ℝ))) := by
  have h := Real.add_one_le_exp (-(1 / (p : ℝ)))
  linarith

private lemma exp_neg_inv_pred_le_one_sub_inv (p : ℕ) (hp : 2 ≤ p) :
    Real.exp (-(1 / ((p : ℝ) - 1))) ≤ 1 - 1 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1pos : 0 < (p : ℝ) - 1 := by linarith
  have hpos : 0 < (1 : ℝ) - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]
      exact_mod_cast (by omega : 1 < p)
    linarith
  have harg : (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
  have hlog : Real.log ((1 : ℝ) - 1 / (p : ℝ))
      = Real.log ((p : ℝ) - 1) - Real.log (p : ℝ) := by
    rw [harg, Real.log_div (ne_of_gt hpm1pos) (ne_of_gt hp0)]
  have hge : -(1 / ((p : ℝ) - 1)) ≤ Real.log ((1 : ℝ) - 1 / (p : ℝ)) := by
    rw [hlog]
    have h := Real.log_le_sub_one_of_pos (div_pos hp0 hpm1pos)
    have hdiv : Real.log ((p : ℝ) / ((p : ℝ) - 1))
        = Real.log (p : ℝ) - Real.log ((p : ℝ) - 1) :=
      Real.log_div (ne_of_gt hp0) (ne_of_gt hpm1pos)
    have hval : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by
      field_simp
      ring
    rw [hdiv, hval] at h
    linarith
  calc Real.exp (-(1 / ((p : ℝ) - 1)))
      ≤ Real.exp (Real.log ((1 : ℝ) - 1 / (p : ℝ))) := Real.exp_le_exp.mpr hge
    _ = (1 : ℝ) - 1 / (p : ℝ) := Real.exp_log hpos

lemma prod_one_sub_inv_le_exp_neg_sum (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, (1 - 1 / (p : ℝ))) ≤ Real.exp (-(∑ p ∈ S, 1 / (p : ℝ))) := by
  have h1 : (∏ p ∈ S, (1 - 1 / (p : ℝ))) ≤ ∏ p ∈ S, Real.exp (-(1 / (p : ℝ))) := by
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro p hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (by have := (hS p hp).two_le; omega : 1 ≤ p)
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; exact hp1
      linarith
    · intro p _; exact one_sub_inv_le_exp_neg p
  have h2 : (∏ p ∈ S, Real.exp (-(1 / (p : ℝ))))
      = Real.exp (-(∑ p ∈ S, 1 / (p : ℝ))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [h2] at h1; exact h1

private lemma prod_exp_neg_inv_pred_le (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    Real.exp (-(∑ p ∈ S, 1 / ((p : ℝ) - 1))) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  have h1 : (∏ p ∈ S, Real.exp (-(1 / ((p : ℝ) - 1)))) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro p _; exact le_of_lt (Real.exp_pos _)
    · intro p hp; exact exp_neg_inv_pred_le_one_sub_inv p (hS p hp)
  have h2 : (∏ p ∈ S, Real.exp (-(1 / ((p : ℝ) - 1))))
      = Real.exp (-(∑ p ∈ S, 1 / ((p : ℝ) - 1))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [h2] at h1; exact h1

private lemma sum_inv_pred_eq (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∑ p ∈ S, 1 / ((p : ℝ) - 1))
      = (∑ p ∈ S, 1 / (p : ℝ)) + ∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hS p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  field_simp
  ring

/-- `exp (-(1/2) log log x) = 1 / sqrt (log x)` for `x > 1`. -/
lemma exp_neg_half_loglog (x : ℝ) (hx : 1 < x) :
    Real.exp (-(1 / 2) * Real.log (Real.log x)) = 1 / Real.sqrt (Real.log x) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have harg : -(1 / 2) * Real.log (Real.log x) = Real.log (Real.log x) * (-(1 / 2)) := by ring
  rw [harg, ← Real.rpow_def_of_pos hlogx (-(1 / 2)), Real.rpow_neg (le_of_lt hlogx) (1 / 2)]
  rw [← Real.sqrt_eq_rpow, inv_eq_one_div]

end Commons.NumberTheory.Diophantine
