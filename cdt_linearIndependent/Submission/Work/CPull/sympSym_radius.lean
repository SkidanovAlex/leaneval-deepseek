import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.CPull.sympQ

/-!
# Area CPull — `Sym⁺` does not destroy exponential growth of coefficients

If `|coeffₙ P| ≤ C·Rⁿ` then `|coeffₙ (Sym⁺P)| ≤ C'·R'ⁿ`.

The proof is elementary.  Writing `P_m(y)` for the symmetrised powers
(`sympQ m`: `P_0 = 2`, `P_1 = y`, `P_{m+2} = y·P_{m+1} − y·P_m`), one has
`Sym⁺P = Σ_m coeff_m(P) · P_m(y)` (`sympRep P`), a *finite* sum at each coefficient
(`P_m` has `y`-valuation `⌈m/2⌉` where `y = x²/(x−1)`).  Hence

`coeffₙ (Sym⁺P) = Σ_{m ≤ 2n} coeff_m(P)·coeffₙ(P_m)`,

and the coefficients of `P_m` satisfy the crude uniform bound
`|coeff_j (P_m)| ≤ 3·2^j` (an immediate induction on `m`).  Then

`|coeffₙ (Sym⁺P)| ≤ 3·2ⁿ · Σ_{m≤2n} C·R^m ≤ 3C·(8(1+R)²)ⁿ`.
-/

open scoped BigOperators

namespace Work.CPull

open PowerSeries

/-! ## The substitution identity for the symmetrised powers -/

lemma subst_sympY_two : ((2 : PowerSeries ℚ)).subst Submission.CDT.sympY = 2 := by
  have h : (2 : PowerSeries ℚ) = PowerSeries.C 2 := by
    rw [PowerSeries.C_eq_algebraMap]
    exact (map_ofNat (algebraMap ℚ (PowerSeries ℚ)) 2).symm
  rw [h, PowerSeries.subst_C]
  exact (map_ofNat (PowerSeries.C (R := ℚ)) 2).symm

/-- `P_m(y(x)) = x^m + φ(x)^m`. -/
theorem sympQ_subst (m : ℕ) :
    (sympQ m).subst Submission.CDT.sympY = Submission.CDT.sympP m := by
  induction m using Nat.twoStepInduction with
  | zero =>
      rw [show sympQ 0 = (2 : PowerSeries ℚ) from rfl, Submission.CDT.sympP_zero]
      exact subst_sympY_two
  | one =>
      rw [show sympQ 1 = (X : PowerSeries ℚ) from rfl,
        PowerSeries.subst_X Submission.CDT.sympY_hasSubst, Submission.CDT.sympP_one]
  | more n ih1 ih2 =>
      rw [show sympQ (n + 2) = X * sympQ (n + 1) - X * sympQ n from rfl,
        PowerSeries.subst_sub Submission.CDT.sympY_hasSubst,
        PowerSeries.subst_mul Submission.CDT.sympY_hasSubst,
        PowerSeries.subst_mul Submission.CDT.sympY_hasSubst,
        PowerSeries.subst_X Submission.CDT.sympY_hasSubst,
        ih2, ih1]
      exact (Submission.CDT.sympP_succ_succ n).symm

/-- `P_m` has `y`-valuation `⌈m/2⌉`: all coefficients below `m/2` vanish. -/
theorem sympQ_coeff_vanishing (m j : ℕ) (h : 2 * j < m) :
    PowerSeries.coeff j (sympQ m) = 0 := by
  have key : ∀ m : ℕ, ∀ j : ℕ, 2 * j < m → PowerSeries.coeff j (sympQ m) = 0 := by
    intro m
    refine Nat.twoStepInduction
      (motive := fun m => ∀ j : ℕ, 2 * j < m → PowerSeries.coeff j (sympQ m) = 0)
      ?_ ?_ ?_ m
    · intro j h; omega
    · intro j h
      have hj : j = 0 := by omega
      subst hj
      rw [show sympQ 1 = (X : PowerSeries ℚ) from rfl, PowerSeries.coeff_X]
      simp
    · intro n ih1 ih2 j h
      rcases j with _ | k
      · rw [show sympQ (n + 2) = X * sympQ (n + 1) - X * sympQ n from rfl,
            map_sub (PowerSeries.coeff (R := ℚ) 0),
            PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul, sub_zero]
      · rw [show sympQ (n + 2) = X * sympQ (n + 1) - X * sympQ n from rfl,
            map_sub (PowerSeries.coeff (R := ℚ) (k + 1)),
            PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
            ih2 k (by omega), ih1 k (by omega), sub_zero]
  exact key m j h

/-- Uniform crude bound on the coefficients of the symmetrised powers. -/
theorem sympQ_coeff_bound (m j : ℕ) :
    |((PowerSeries.coeff j (sympQ m) : ℚ) : ℝ)| ≤ 3 * (2 : ℝ) ^ j := by
  have key : ∀ m : ℕ, ∀ j : ℕ,
      |((PowerSeries.coeff j (sympQ m) : ℚ) : ℝ)| ≤ 3 * (2 : ℝ) ^ j := by
    intro m
    refine Nat.twoStepInduction
      (motive := fun m => ∀ j : ℕ,
        |((PowerSeries.coeff j (sympQ m) : ℚ) : ℝ)| ≤ 3 * (2 : ℝ) ^ j) ?_ ?_ ?_ m
    · intro j
      have h2 : sympQ 0 = PowerSeries.C (2 : ℚ) := by
        rw [show sympQ 0 = (2 : PowerSeries ℚ) from rfl, PowerSeries.C_eq_algebraMap]
        exact (map_ofNat (algebraMap ℚ (PowerSeries ℚ)) 2).symm
      rw [h2, PowerSeries.coeff_C]
      by_cases hj : j = 0
      · subst hj; norm_num
      · rw [if_neg hj]; simp only [Rat.cast_zero, abs_zero]; positivity
    · intro j
      rw [show sympQ 1 = (X : PowerSeries ℚ) from rfl, PowerSeries.coeff_X]
      by_cases hj : j = 1
      · subst hj; norm_num
      · rw [if_neg hj]; simp only [Rat.cast_zero, abs_zero]; positivity
    · intro n ih1 ih2 j
      rcases j with _ | k
      · rw [show sympQ (n + 2) = X * sympQ (n + 1) - X * sympQ n from rfl,
            map_sub (PowerSeries.coeff (R := ℚ) 0),
            PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul, sub_zero]
        norm_num
      · rw [show sympQ (n + 2) = X * sympQ (n + 1) - X * sympQ n from rfl,
            map_sub (PowerSeries.coeff (R := ℚ) (k + 1)),
            PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
        have hcast : (((PowerSeries.coeff k (sympQ (n + 1))
              - PowerSeries.coeff k (sympQ n) : ℚ) : ℝ))
            = ((PowerSeries.coeff k (sympQ (n + 1)) : ℚ) : ℝ)
              - ((PowerSeries.coeff k (sympQ n) : ℚ) : ℝ) := by push_cast; ring
        rw [hcast]
        calc |((PowerSeries.coeff k (sympQ (n + 1)) : ℚ) : ℝ)
                - ((PowerSeries.coeff k (sympQ n) : ℚ) : ℝ)|
            ≤ |((PowerSeries.coeff k (sympQ (n + 1)) : ℚ) : ℝ)|
                + |((PowerSeries.coeff k (sympQ n) : ℚ) : ℝ)| := abs_sub _ _
          _ ≤ 3 * (2 : ℝ) ^ k + 3 * (2 : ℝ) ^ k := add_le_add (ih2 k) (ih1 k)
          _ = 3 * (2 : ℝ) ^ (k + 1) := by ring
  exact key m j

/-! ## `sympRep` is the descent of `P + P∘φ` -/

/-- `Σ_m coeff_m(P) · P_m(y)` descends to `P + P∘φ`. -/
theorem sympRep_subst (P : PowerSeries ℚ) :
    (sympRep P).subst Submission.CDT.sympY = P + P.subst Submission.CDT.sympPhi := by
  apply PowerSeries.ext
  intro n
  have hL : PowerSeries.coeff n ((sympRep P).subst Submission.CDT.sympY)
      = ∑ j ∈ Finset.range (n / 2 + 1),
          PowerSeries.coeff j (sympRep P) * PowerSeries.coeff n (Submission.CDT.sympY ^ j) :=
    Submission.CDT.coeff_subst_range₂ (sympRep P) Submission.CDT.coeff_sympY_zero
      Submission.CDT.coeff_sympY_one n
  rw [hL]
  have h1 : (∑ j ∈ Finset.range (n / 2 + 1),
        PowerSeries.coeff j (sympRep P) * PowerSeries.coeff n (Submission.CDT.sympY ^ j))
      = ∑ j ∈ Finset.range (n / 2 + 1), ∑ m ∈ Finset.range (2 * n + 1),
          (PowerSeries.coeff m P * PowerSeries.coeff j (sympQ m))
            * PowerSeries.coeff n (Submission.CDT.sympY ^ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj2 : 2 * j ≤ n := by
      have hjn : j ≤ n / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      calc 2 * j = j * 2 := by ring
        _ ≤ (n / 2) * 2 := Nat.mul_le_mul_right 2 hjn
        _ ≤ n := Nat.div_mul_le_self n 2
    rw [sympRep, PowerSeries.coeff_mk, Finset.sum_mul]
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_range] at hm ⊢
      omega
    · intro m hm hmn
      simp only [Finset.mem_range] at hm hmn
      have hm2 : 2 * j < m := by omega
      rw [sympQ_coeff_vanishing m j hm2, mul_zero, zero_mul]
  rw [h1, Finset.sum_comm]
  have h2 : (∑ m ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (n / 2 + 1),
        (PowerSeries.coeff m P * PowerSeries.coeff j (sympQ m))
          * PowerSeries.coeff n (Submission.CDT.sympY ^ j))
      = ∑ m ∈ Finset.range (2 * n + 1), PowerSeries.coeff m P *
          (PowerSeries.coeff n (X ^ m) + PowerSeries.coeff n (Submission.CDT.sympPhi ^ m)) := by
    apply Finset.sum_congr rfl
    intro m _
    have h3 : (∑ j ∈ Finset.range (n / 2 + 1),
          (PowerSeries.coeff m P * PowerSeries.coeff j (sympQ m))
            * PowerSeries.coeff n (Submission.CDT.sympY ^ j))
        = PowerSeries.coeff m P * ∑ j ∈ Finset.range (n / 2 + 1),
            PowerSeries.coeff j (sympQ m) * PowerSeries.coeff n (Submission.CDT.sympY ^ j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [h3]
    have h4 : (∑ j ∈ Finset.range (n / 2 + 1),
          PowerSeries.coeff j (sympQ m) * PowerSeries.coeff n (Submission.CDT.sympY ^ j))
        = PowerSeries.coeff n (X ^ m) + PowerSeries.coeff n (Submission.CDT.sympPhi ^ m) := by
      rw [← Submission.CDT.coeff_subst_range₂ (sympQ m) Submission.CDT.coeff_sympY_zero
        Submission.CDT.coeff_sympY_one n, sympQ_subst m, Submission.CDT.sympP, map_add]
    rw [h4]
  rw [h2]
  have hX : (∑ m ∈ Finset.range (2 * n + 1),
        PowerSeries.coeff m P * PowerSeries.coeff n (X ^ m)) = PowerSeries.coeff n P := by
    rw [Finset.sum_eq_single n]
    · rw [PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
    · intro m _ hmn
      rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm hmn), mul_zero]
    · intro hn
      exact absurd (Finset.mem_range.mpr (by omega)) hn
  have hPhi : (∑ m ∈ Finset.range (2 * n + 1),
        PowerSeries.coeff m P * PowerSeries.coeff n (Submission.CDT.sympPhi ^ m))
      = PowerSeries.coeff n (P.subst Submission.CDT.sympPhi) := by
    rw [Submission.CDT.coeff_subst_range P Submission.CDT.coeff_sympPhi_zero n]
    symm
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_range] at hm ⊢
      omega
    · intro m hm hmn
      simp only [Finset.mem_range] at hm hmn
      have hmn' : n < m := by omega
      rw [Submission.CDT.coeff_pow_lt_one Submission.CDT.coeff_sympPhi_zero hmn', mul_zero]
  have h5 : (∑ m ∈ Finset.range (2 * n + 1), PowerSeries.coeff m P *
        (PowerSeries.coeff n (X ^ m) + PowerSeries.coeff n (Submission.CDT.sympPhi ^ m)))
      = ∑ m ∈ Finset.range (2 * n + 1), (PowerSeries.coeff m P * PowerSeries.coeff n (X ^ m)
          + PowerSeries.coeff m P * PowerSeries.coeff n (Submission.CDT.sympPhi ^ m)) :=
    Finset.sum_congr rfl (fun m _ => mul_add _ _ _)
  rw [h5, Finset.sum_add_distrib, hX, hPhi]
  exact (map_add (PowerSeries.coeff (R := ℚ) n) P (P.subst Submission.CDT.sympPhi)).symm

/-- `sympRep P` is `Sym⁺P`. -/
theorem sympSym_eq_sympRep (P : PowerSeries ℚ) : Submission.CDT.sympSym P = sympRep P := by
  have h : (Submission.CDT.sympSym P - sympRep P).subst Submission.CDT.sympY = 0 := by
    rw [PowerSeries.subst_sub Submission.CDT.sympY_hasSubst, Submission.CDT.sympSym_subst,
      sympRep_subst, sub_self]
  exact sub_eq_zero.mp (Submission.CDT.symp_subst_y_injective _ h)

/-! ## The growth estimate -/

lemma norm_rat_cast_complex (q : ℚ) : ‖((q : ℚ) : ℂ)‖ = |((q : ℚ) : ℝ)| := by
  rw [show ((q : ℚ) : ℂ) = (((q : ℚ) : ℝ) : ℂ) from by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- Geometric estimate for the finite geometric sum. -/
theorem sympRep_geom_bound (R : ℝ) (hR : 0 < R) (n : ℕ) :
    (∑ m ∈ Finset.range (2 * n + 1), R ^ m) ≤ (4 * (1 + R) ^ 2) ^ n := by
  have hpow : ∀ n : ℕ, ((2 * n + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
        have h4 : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
        have hk : (2 * (k : ℝ) + 1) ≤ (4 : ℝ) ^ k := by
          have := ih; push_cast at this; exact this
        push_cast
        rw [h4]
        nlinarith [hk, pow_pos (by norm_num : (0:ℝ) < 4) k]
  have hterm : ∀ m ∈ Finset.range (2 * n + 1), R ^ m ≤ (1 + R) ^ (2 * n) := by
    intro m hm
    simp only [Finset.mem_range] at hm
    by_cases h1 : R < 1
    · have hRm : R ^ m ≤ 1 := pow_le_one₀ (le_of_lt hR) (le_of_lt h1)
      have h1R : (1 : ℝ) ≤ (1 + R) ^ (2 * n) := one_le_pow₀ (by linarith)
      linarith
    · have hR1 : (1 : ℝ) ≤ R := not_lt.mp h1
      have hm2 : m ≤ 2 * n := by omega
      exact le_trans (pow_le_pow_right₀ hR1 hm2) (pow_le_pow_left₀ (le_of_lt hR) (by linarith) _)
  calc (∑ m ∈ Finset.range (2 * n + 1), R ^ m)
      ≤ ∑ _m ∈ Finset.range (2 * n + 1), (1 + R) ^ (2 * n) := Finset.sum_le_sum hterm
    _ = ((2 * n + 1 : ℕ) : ℝ) * (1 + R) ^ (2 * n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 4 ^ n * (1 + R) ^ (2 * n) :=
        mul_le_mul_of_nonneg_right (hpow n) (by positivity)
    _ = (4 * (1 + R) ^ 2) ^ n := by
        rw [mul_pow, pow_mul]

/-- Collecting the powers: `3·2ⁿ · (C·(4(1+R)²)ⁿ) = 3C·(8(1+R)²)ⁿ`. -/
lemma pow_combine_C (C R : ℝ) (n : ℕ) :
    3 * (2 : ℝ) ^ n * (C * (4 * (1 + R) ^ 2) ^ n) = (3 * C) * (8 * (1 + R) ^ 2) ^ n := by
  have hb : (2 : ℝ) * (4 * (1 + R) ^ 2) = 8 * (1 + R) ^ 2 := by ring
  have hL : (3 : ℝ) * 2 ^ n * (C * (4 * (1 + R) ^ 2) ^ n)
      = 3 * C * (2 ^ n * (4 * (1 + R) ^ 2) ^ n) := by ring
  rw [hL, ← mul_pow, ← hb]

/-- The key estimate on the coefficients of `Sym⁺P`. -/
theorem sympSym_coeff_bound (P : PowerSeries ℚ) (C R : ℝ) (hC : 0 < C) (hR : 0 < R)
    (hP : ∀ n, ‖((PowerSeries.coeff n P : ℚ) : ℂ)‖ ≤ C * R ^ n) (n : ℕ) :
    |(((PowerSeries.coeff n (Submission.CDT.sympSym P) : ℚ)) : ℝ)|
      ≤ (3 * C) * (8 * (1 + R) ^ 2) ^ n := by
  have hcoe : PowerSeries.coeff n (Submission.CDT.sympSym P)
      = ∑ m ∈ Finset.range (2 * n + 1),
          PowerSeries.coeff m P * PowerSeries.coeff n (sympQ m) := by
    rw [sympSym_eq_sympRep, sympRep, PowerSeries.coeff_mk]
  have hcast : ((∑ m ∈ Finset.range (2 * n + 1),
        PowerSeries.coeff m P * PowerSeries.coeff n (sympQ m) : ℚ) : ℝ)
      = ∑ m ∈ Finset.range (2 * n + 1),
          ((PowerSeries.coeff m P : ℚ) : ℝ) * ((PowerSeries.coeff n (sympQ m) : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hcoe, hcast]
  calc |∑ m ∈ Finset.range (2 * n + 1),
          ((PowerSeries.coeff m P : ℚ) : ℝ) * ((PowerSeries.coeff n (sympQ m) : ℚ) : ℝ)|
      ≤ ∑ m ∈ Finset.range (2 * n + 1),
          |((PowerSeries.coeff m P : ℚ) : ℝ) * ((PowerSeries.coeff n (sympQ m) : ℚ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ Finset.range (2 * n + 1),
          |((PowerSeries.coeff m P : ℚ) : ℝ)| * |((PowerSeries.coeff n (sympQ m) : ℚ) : ℝ)| :=
        Finset.sum_congr rfl (fun m _ => abs_mul _ _)
    _ ≤ ∑ m ∈ Finset.range (2 * n + 1), (C * R ^ m) * (3 * (2 : ℝ) ^ n) := by
        apply Finset.sum_le_sum
        intro m _
        refine mul_le_mul ?_ (sympQ_coeff_bound m n) (abs_nonneg _) ?_
        · have h := hP m
          rw [norm_rat_cast_complex] at h
          exact h
        · exact mul_nonneg (le_of_lt hC) (pow_nonneg (le_of_lt hR) m)
    _ = (∑ m ∈ Finset.range (2 * n + 1), C * R ^ m) * (3 * (2 : ℝ) ^ n) := by
        rw [Finset.sum_mul]
    _ = 3 * (2 : ℝ) ^ n * (C * ∑ m ∈ Finset.range (2 * n + 1), R ^ m) := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ 3 * (2 : ℝ) ^ n * (C * (4 * (1 + R) ^ 2) ^ n) := by
        have hg := sympRep_geom_bound R hR n
        have h2n : (0 : ℝ) ≤ 3 * (2 : ℝ) ^ n := by positivity
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hg (le_of_lt hC)) h2n
    _ = (3 * C) * (8 * (1 + R) ^ 2) ^ n := pow_combine_C C R n

theorem sympSym_radius (P : PowerSeries ℚ) (C R : ℝ) (hC : 0 < C) (hR : 0 < R)
    (hP : ∀ n, ‖((PowerSeries.coeff n P : ℚ) : ℂ)‖ ≤ C * R ^ n) :
    ∃ C' R' : ℝ, 0 < C' ∧ 0 < R' ∧
      ∀ n, ‖((PowerSeries.coeff n (Submission.CDT.sympSym P) : ℚ) : ℂ)‖ ≤ C' * R' ^ n := by
  refine ⟨3 * C, 8 * (1 + R) ^ 2, by positivity, by positivity, fun n => ?_⟩
  rw [norm_rat_cast_complex]
  exact sympSym_coeff_bound P C R hC hR hP n

end Work.CPull
