import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.JR2.LayerAux
import Submission.Work.ChenPlan.LinearSieve.JR2.abel_sharp
import Submission.Work.ChenPlan.LinearSieve.JR2.layer_sharp_base
import Submission.Work.ChenPlan.LinearSieve.JR2.budget_sharp
import Submission.Work.ChenPlan.LinearSieve.JR2.budget_shift
import Submission.Work.ChenPlan.LinearSieve.JR2.step_small_final
import Submission.Work.JR.abel_change_of_variables

open Finset MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.JR2

noncomputable section

open Work.NumberTheory.Chen.APSwitchUpper


/-! ## The induction step: case (A) (even row, `s ≥ 2`) -/

/-- **The induction step from row `k` to the even row `k+1`** (so `k` is odd and `s ≥ 2`).
The children of the `T`-recursion all have parameter `σ = log (D/p) / log p ≥ s - 1 ≥ 1`, so the
induction hypothesis applies at every prime `p < z`; the Abel step `abel_sharp` with the majorant
`PhiC k D ε` (monotone and nonnegative on `[2,z]`) converts the sum into the logarithmic integral,
the substitution `u = D^{1/t}` identifies `(1/s)∫_s^{T} profC (k-1) (t-1) dt` with `profC k s`, and
`budget_sharp` closes the arithmetic. -/
lemma step_even {A : BoundingSieve} {ε D z : ℝ} {k : ℕ} (hk : 1 ≤ k) (hkodd : Odd k)
    (hB : Budgets) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1/100) (hz : 2 ≤ z) (hD : 1 ≤ D)
    (hSharp : SharpNorm A z ε) (hs2 : 2 ≤ Real.log D / Real.log z)
    (hIH : ∀ D' z' : ℝ, 2 ≤ z' → 1 ≤ D' → SharpNorm A z' ε →
      (Odd k → 1 ≤ Real.log D' / Real.log z') → (Even k → 2 ≤ Real.log D' / Real.log z') →
      T A k D' z' ≤ VfR A z' * (profC (k - 1) (Real.log D' / Real.log z')
        + cCoef k ε * errH (Real.log D' / Real.log z'))) :
    T A (k + 1) D z ≤ VfR A z * (profC k (Real.log D / Real.log z)
      + cCoef (k + 1) ε * errH (Real.log D / Real.log z)) := by
  classical
  rcases eq_or_lt_of_le hz with hzeq | hz2
  · -- the degenerate case `z = 2`: the sum is empty
    have hempty : A.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p:ℝ) < (2:ℝ) ∧ Tcond (k + 1) D p) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun p hp => ?_)
      rintro ⟨hpz, -⟩
      have h2 : (2:ℝ) ≤ (p:ℝ) := by
        exact_mod_cast Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)
      exact absurd hpz (not_lt.mpr h2)
    rw [← hzeq, T.eq_2 A D 2 k, hempty, Finset.sum_empty]
    exact mul_nonneg (VfR_nonneg A 2)
      (add_nonneg (profC_nonneg k _) (mul_nonneg (cCoef_nonneg hε0) (errH_nonneg _)))
  -- the main case `2 < z`
  set s : ℝ := Real.log D / Real.log z with hsdef
  have hz1 : 1 < z := by linarith
  have hzpos : 0 < Real.log z := Real.log_pos hz1
  have hs_pos : 0 < s := by linarith
  have hDz2 : z ^ 2 ≤ D := by
    have h : 2 * Real.log z ≤ Real.log D := by
      have h' := (le_div_iff₀ hzpos).mp hs2
      linarith
    calc z ^ 2 = (Real.exp (Real.log z)) ^ 2 := by rw [Real.exp_log (by positivity)]
      _ = Real.exp (((2:ℕ):ℝ) * Real.log z) := (Real.exp_nat_mul (Real.log z) 2).symm
      _ = Real.exp (2 * Real.log z) := by norm_num
      _ ≤ Real.exp (Real.log D) := Real.exp_le_exp.mpr h
      _ = D := Real.exp_log (by positivity)
  have hD1 : 1 < D := by nlinarith [hz1, hDz2]
  have hDpos : 0 < D := by linarith
  have hlogDpos : 0 < Real.log D := Real.log_pos hD1
  have hEven : Even (k + 1) := Nat.even_add_one.mpr ((Nat.not_even_iff_odd).mpr hkodd)
  have hTcond : ∀ p : ℕ, Tcond (k + 1) D p := by
    refine fun p => ⟨fun h1 => absurd h1 (by omega), fun h2 ho => absurd hEven ((Nat.not_even_iff_odd).mpr ho)⟩
  have hfilter : A.prodPrimes.primeFactors.filter (fun p : ℕ => (p:ℝ) < z ∧ Tcond (k + 1) D p)
      = A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z) := by
    refine Finset.filter_congr (fun p hp => ?_)
    constructor
    · rintro ⟨hpz, -⟩
      exact ⟨by exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)), hpz⟩
    · rintro ⟨-, hpz⟩
      exact ⟨hpz, hTcond p⟩
  have hT : T A (k + 1) D z
      = ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
          A.nu p * T A k (D / (p:ℝ)) (p:ℝ) := by
    rw [T.eq_2 A D z k, hfilter]
  -- the child estimate
  have hchild : ∀ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
      T A k (D / (p:ℝ)) (p:ℝ) ≤ VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := by
    intro p hp
    obtain ⟨hpmem, hp2, hpz⟩ := Finset.mem_filter.mp hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.pos
    have hp2sq : (p:ℝ) ^ 2 ≤ D := by nlinarith [hDz2, hpz, hppos]
    have hDp1 : 1 ≤ D / (p:ℝ) := by
      rw [le_div_iff₀ hppos]; nlinarith
    have hσ1 : 1 ≤ Real.log (D / (p:ℝ)) / Real.log (p:ℝ) := by
      rw [le_div_iff₀ (Real.log_pos (by linarith : 1 < (p:ℝ))),
        Real.log_div (ne_of_gt hDpos) (ne_of_gt hppos)]
      have h := Real.log_le_log (by positivity : (0:ℝ) < (p:ℝ)^2) hp2sq
      rw [Real.log_pow] at h
      push_cast at h
      linarith
    have hres := hIH (D / (p:ℝ)) (p:ℝ) (by linarith) hDp1 (hSharp.sub (le_of_lt hpz))
      (fun _ => hσ1) (fun hE => absurd hE ((Nat.not_even_iff_odd).mpr hkodd))
    have hσeq : Real.log (D / (p:ℝ)) / Real.log (p:ℝ)
        = Real.log D / Real.log (p:ℝ) - 1 := by
      rw [Real.log_div (ne_of_gt hDpos) (ne_of_gt hppos), sub_div,
        div_self (ne_of_gt (Real.log_pos (by linarith : 1 < (p:ℝ))))]
    have hΦ : PhiC k D ε (p:ℝ)
        = profC (k - 1) (Real.log D / Real.log (p:ℝ) - 1)
          + cCoef k ε * errH (Real.log D / Real.log (p:ℝ) - 1) := rfl
    rw [hΦ, ← hσeq]
    exact hres
  have hnu_nonneg : ∀ p ∈ A.prodPrimes.primeFactors, 0 ≤ A.nu p := fun p hp =>
    le_of_lt (A.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp)
      (Nat.mem_primeFactors.mp hp).2.1)
  have hsum : ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
        A.nu p * T A k (D / (p:ℝ)) (p:ℝ)
      ≤ ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
          A.nu p * VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    calc A.nu p * T A k (D / (p:ℝ)) (p:ℝ)
        ≤ A.nu p * (VfR A (p:ℝ) * PhiC k D ε (p:ℝ)) :=
          mul_le_mul_of_nonneg_left (hchild p hp) (hnu_nonneg p (Finset.mem_filter.mp hp).1)
      _ = A.nu p * VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := by ring
  -- the Abel step
  have hV : ∀ u : ℝ, 2 ≤ u → u ≤ z →
      VfR A u ≤ VfR A z * ((1 + ε) * (Real.log z / Real.log u)) :=
    fun u hu huz => VfR_le_of_sharpNorm (A := A) hε0 hSharp hu huz le_rfl
  have hΦnn : ∀ a : ℝ, 2 ≤ a → a ≤ z → 0 ≤ PhiC k D ε a := fun a _ _ => PhiC_nonneg hε0 a
  have hΦmono : ∀ a b : ℝ, 2 ≤ a → a ≤ b → b ≤ z → PhiC k D ε a ≤ PhiC k D ε b := by
    intro a b ha hab hbz
    have hbl : 1 < b := by linarith
    have hσb : 1 ≤ Real.log D / Real.log b - 1 := by
      have h : s ≤ Real.log D / Real.log b := by
        rw [hsdef]
        exact div_le_div_of_nonneg_left hlogDpos.le (Real.log_pos hbl)
          (Real.log_le_log (by linarith) hbz)
      linarith
    exact PhiC_mono hε0 hD1 (Nat.odd_iff.mp hkodd) (by linarith) hab hσb
  have habel := abel_sharp (A := A) (w := 2) (Z := z) (ε := ε) hε0 (le_refl 2)
    hz2 hV (Φ := PhiC k D ε) hΦmono hΦnn
  -- the change of variables
  have hsT : s ≤ Real.log D / Real.log 2 := by
    rw [hsdef]
    exact div_le_div_of_nonneg_left hlogDpos.le (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) hz)
  have hqpos : 0 < Real.log D / Real.log 2 := div_pos hlogDpos (Real.log_pos (by norm_num))
  have hDpow1 : D ^ (1 / (Real.log D / Real.log 2)) = 2 := by
    rw [Real.rpow_def_of_pos hDpos]
    have h : Real.log D * (1 / (Real.log D / Real.log 2)) = Real.log 2 := by
      field_simp
    rw [h, Real.exp_log (by norm_num)]
  have hDpow2 : D ^ (1 / s) = z := by
    rw [Real.rpow_def_of_pos hDpos, hsdef]
    have h : Real.log D * (1 / (Real.log D / Real.log z)) = Real.log z := by
      field_simp
    rw [h, Real.exp_log (by linarith : (0:ℝ) < z)]
  have hcv : (∫ u in (2:ℝ)..z, PhiC k D ε u * (Real.log z / (u * (Real.log u)^2)))
      = (1/s) * ∫ t in s..(Real.log D / Real.log 2), PhiC k D ε (D^(1/t)) := by
    have h := Work.JR.abel_change_of_variables (D := D) hD1 (s := s) (T := Real.log D / Real.log 2)
      hs_pos hsT (intervalIntegrable_PhiC k D ε hDpos s (Real.log D / Real.log 2))
    rw [hDpow1, hDpow2] at h
    exact h
  -- the integral splitting
  have hΦsplit : ∀ t ∈ Set.uIcc s (Real.log D / Real.log 2),
      PhiC k D ε (D^(1/t)) = profC (k - 1) (t - 1) + cCoef k ε * errH (t - 1) := by
    intro t ht
    rw [Set.uIcc_of_le hsT] at ht
    exact PhiC_rpow hD1 (ne_of_gt (lt_of_lt_of_le hs_pos ht.1))
  set L : ℝ := ∫ t in Set.Ioi s, errH (t - 1) with hLdef
  have hint : (∫ t in s..(Real.log D / Real.log 2), PhiC k D ε (D^(1/t)))
      = (∫ t in s..(Real.log D / Real.log 2), profC (k - 1) (t - 1))
        + cCoef k ε * (∫ t in s..(Real.log D / Real.log 2), errH (t - 1)) := by
    have hcongr := intervalIntegral.integral_congr (μ := volume) hΦsplit
    have hadd := intervalIntegral.integral_add (μ := volume) (a := s)
      (b := Real.log D / Real.log 2)
      (f := fun t : ℝ => profC (k - 1) (t - 1))
      (g := fun t : ℝ => cCoef k ε * errH (t - 1))
      (intervalIntegrable_shifted_profC (k - 1) s (Real.log D / Real.log 2))
      ((intervalIntegrable_shifted_errH s (Real.log D / Real.log 2)).const_mul _)
    have hmul := intervalIntegral.integral_const_mul (μ := volume) (a := s)
      (b := Real.log D / Real.log 2) (cCoef k ε) (fun t : ℝ => errH (t - 1))
    rw [hcongr, hadd, hmul]
  have hprof : (∫ t in s..(Real.log D / Real.log 2), profC (k - 1) (t - 1)) ≤ s * profC k s := by
    simpa [Nat.sub_add_cancel hk] using
      profile_integral_le_odd (k - 1) (odd_sub_one_mod hkodd) (by linarith) hsT
  have herrH : (∫ t in s..(Real.log D / Real.log 2), errH (t - 1)) ≤ L := by
    rw [hLdef]; exact errH_interval_le_tail (by linarith) hsT
  have hintle : (∫ t in s..(Real.log D / Real.log 2), PhiC k D ε (D^(1/t)))
      ≤ s * profC k s + cCoef k ε * L := by
    rw [hint]
    exact add_le_add hprof (mul_le_mul_of_nonneg_left herrH (cCoef_nonneg hε0))
  -- the main bound
  have hmain : T A (k + 1) D z ≤ VfR A z * (ε * PhiC k D ε z
      + (1+ε) * ((1/s) * (s * profC k s + cCoef k ε * L))) := by
    calc T A (k + 1) D z
        = ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
            A.nu p * T A k (D / (p:ℝ)) (p:ℝ) := hT
      _ ≤ ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
            A.nu p * VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := hsum
      _ ≤ VfR A z * (ε * PhiC k D ε z
            + (1 + ε) * ∫ u in (2:ℝ)..z, PhiC k D ε u * (Real.log z / (u * (Real.log u)^2))) := habel
      _ = VfR A z * (ε * PhiC k D ε z
            + (1 + ε) * ((1/s) * ∫ t in s..(Real.log D / Real.log 2), PhiC k D ε (D^(1/t)))) := by
          rw [hcv]
      _ ≤ VfR A z * (ε * PhiC k D ε z
            + (1+ε) * ((1/s) * (s * profC k s + cCoef k ε * L))) := by
          refine mul_le_mul_of_nonneg_left ?_ (VfR_nonneg A z)
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity))
          exact mul_le_mul_of_nonneg_left hintle (by positivity)
  -- the final arithmetic
  have hΦz : PhiC k D ε z = profC (k - 1) (s - 1) + cCoef k ε * errH (s - 1) := by
    unfold PhiC
    rw [← hsdef]
  have hbudget_prof : profC k s + profC (k - 1) (s - 1)
      ≤ 990 * (99/100:ℝ)^(k-1) * errH s :=
    hB.2.2.1 (k + 1) s (by omega) (by linarith)
  have hbudget_err : ε * errH (s - 1) + (1 + ε) * L / s ≤ (99/100) * errH s := by
    rw [hLdef]
    exact hB.1 s ε (by linarith) hε0 hε1
  have hexp : ε * PhiC k D ε z + (1+ε) * ((1/s) * (s * profC k s + cCoef k ε * L))
      = profC k s + ε * (profC k s + profC (k - 1) (s - 1))
        + cCoef k ε * (ε * errH (s - 1) + (1 + ε) * L / s) := by
    rw [hΦz]
    field_simp
    ring
  have key : profC k s + ε * (profC k s + profC (k - 1) (s - 1))
      + cCoef k ε * (ε * errH (s - 1) + (1 + ε) * L / s) ≤ profC k s + cCoef (k + 1) ε * errH s := by
    set P : ℝ := ε * (99/100:ℝ)^(k-1) * errH s with hPdef
    have h1 : ε * (profC k s + profC (k - 1) (s - 1)) ≤ 990 * P := by
      have h := mul_le_mul_of_nonneg_left hbudget_prof hε0
      calc ε * (profC k s + profC (k - 1) (s - 1))
          ≤ ε * (990 * (99/100:ℝ)^(k-1) * errH s) := h
        _ = 990 * P := by rw [hPdef]; ring
    have h2 : cCoef k ε * (ε * errH (s - 1) + (1 + ε) * L / s) ≤ 990 * ((k:ℝ) + 1) * P := by
      have h := mul_le_mul_of_nonneg_left hbudget_err (cCoef_nonneg (k := k) hε0)
      calc cCoef k ε * (ε * errH (s - 1) + (1 + ε) * L / s)
          ≤ cCoef k ε * ((99/100) * errH s) := h
        _ = 990 * ((k:ℝ) + 1) * P := by rw [cCoef, hPdef]; ring
    have htarget : cCoef (k + 1) ε * errH s = 990 * ((k:ℝ) + 2) * P := by
      rw [cCoef_succ, hPdef]
      have hpow : (99/100:ℝ)^k = (99/100)^(k-1) * (99/100) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
      rw [hpow]; ring
    have hid : 990 * P + 990 * ((k:ℝ) + 1) * P = 990 * ((k:ℝ) + 2) * P := by ring
    rw [htarget]
    linarith [h1, h2, hid]
  calc T A (k + 1) D z ≤ VfR A z * (ε * PhiC k D ε z
        + (1+ε) * ((1/s) * (s * profC k s + cCoef k ε * L))) := hmain
    _ = VfR A z * (profC k s + ε * (profC k s + profC (k - 1) (s - 1))
        + cCoef k ε * (ε * errH (s - 1) + (1 + ε) * L / s)) := by rw [hexp]
    _ ≤ VfR A z * (profC k s + cCoef (k + 1) ε * errH s) :=
        mul_le_mul_of_nonneg_left key (VfR_nonneg A z)
    _ = VfR A z * (profC k (Real.log D / Real.log z)
        + cCoef (k + 1) ε * errH (Real.log D / Real.log z)) := by rw [hsdef]

/-! ## The induction step: case (B) (odd row, `s ≥ 3`) -/

/-- The unclamped recursion of the clamped parity: for `j` odd and `s ≥ 3`,
`∫_s^{j+4} profC j (t-1) = s·profC (j+1) s`. -/
lemma profile_eq_shifted_even_big (j : ℕ) (hj : j % 2 = 1) {s : ℝ} (hs : 3 ≤ s) :
    (∫ t in s..((j:ℝ) + 4), profC j (t - 1)) = s * profC (j + 1) s := by
  have hs0 : (0:ℝ) < s := by linarith
  have hrec := profC_eq_integral_even j hj s (by linarith : 1 ≤ s)
  rw [hrec, max_eq_left (by linarith : (2:ℝ) ≤ s - 1), mul_comm,
    div_mul_cancel₀ _ (ne_of_gt hs0)]
  have h := intervalIntegral.integral_comp_sub_right (fun u : ℝ => profC j u) 1
    (a := s) (b := (j:ℝ) + 4)
  rw [show ((j:ℝ) + 4) - 1 = (j:ℝ) + 3 by ring] at h
  exact h

/-- The profile integral bound in the clamped parity with `s ≥ 3`. -/
lemma profile_integral_le_even_big (j : ℕ) (hj : j % 2 = 1) {s T : ℝ} (hs : 3 ≤ s) (hsT : s ≤ T) :
    (∫ t in s..T, profC j (t - 1)) ≤ s * profC (j + 1) s := by
  rw [← profile_eq_shifted_even_big j hj hs]
  exact intervalIntegral_le_of_support (f := fun x : ℝ => profC j (x - 1))
    (fun a b => intervalIntegrable_shifted_profC j a b) hsT
    (fun x => profC_nonneg j _) (fun x hx => profC_support j _ (by linarith))

/-- **The induction step from row `k` to the odd row `k+1 ≥ 3` with `s ≥ 3`.**  Here `Tcond` is
automatic (`z³ ≤ D`), every child has parameter `σ ≥ s - 1 ≥ 2`, and the recursion of `profC k`
is the unclamped one (`max (s-1) 2 = s - 1`), so the argument of `step_even` goes through with
`PhiC_mono'` in place of `PhiC_mono` and `profile_integral_le_even_big` in place of
`profile_integral_le_odd`. -/
lemma step_odd_big {A : BoundingSieve} {ε D z : ℝ} {k : ℕ} (hk : 2 ≤ k) (hkeven : Even k)
    (hB : Budgets) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1/100) (hz : 2 ≤ z) (hD : 1 ≤ D)
    (hSharp : SharpNorm A z ε) (hs3 : 3 ≤ Real.log D / Real.log z)
    (hIH : ∀ D' z' : ℝ, 2 ≤ z' → 1 ≤ D' → SharpNorm A z' ε →
      (Odd k → 1 ≤ Real.log D' / Real.log z') → (Even k → 2 ≤ Real.log D' / Real.log z') →
      T A k D' z' ≤ VfR A z' * (profC (k - 1) (Real.log D' / Real.log z')
        + cCoef k ε * errH (Real.log D' / Real.log z'))) :
    T A (k + 1) D z ≤ VfR A z * (profC k (Real.log D / Real.log z)
      + cCoef (k + 1) ε * errH (Real.log D / Real.log z)) := by
  classical
  rcases eq_or_lt_of_le hz with hzeq | hz2
  · -- the degenerate case `z = 2`: no prime is below `z`
    have hempty : A.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p:ℝ) < (2:ℝ) ∧ Tcond (k + 1) D p) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun p hp => ?_)
      rintro ⟨hpz, -⟩
      have h2 : (2:ℝ) ≤ (p:ℝ) := by
        exact_mod_cast Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)
      exact absurd hpz (not_lt.mpr h2)
    rw [← hzeq, T.eq_2 A D 2 k, hempty, Finset.sum_empty]
    exact mul_nonneg (VfR_nonneg A 2)
      (add_nonneg (profC_nonneg k _) (mul_nonneg (cCoef_nonneg hε0) (errH_nonneg _)))
  -- the main case `2 < z`
  set s : ℝ := Real.log D / Real.log z with hsdef
  have hz1 : 1 < z := by linarith
  have hzpos : 0 < Real.log z := Real.log_pos hz1
  have hs_pos : 0 < s := by linarith
  have hDz3 : z ^ 3 ≤ D := by
    have h : 3 * Real.log z ≤ Real.log D := by
      have h' := (le_div_iff₀ hzpos).mp hs3
      linarith
    calc z ^ 3 = (Real.exp (Real.log z)) ^ 3 := by rw [Real.exp_log (by positivity)]
      _ = Real.exp (((3:ℕ):ℝ) * Real.log z) := (Real.exp_nat_mul (Real.log z) 3).symm
      _ = Real.exp (3 * Real.log z) := by norm_num
      _ ≤ Real.exp (Real.log D) := Real.exp_le_exp.mpr h
      _ = D := Real.exp_log (by positivity)
  have hD1 : 1 < D := by
    have h1 : (1:ℝ) < z ^ 3 := one_lt_pow₀ hz1 (by norm_num)
    linarith
  have hDpos : 0 < D := by linarith
  have hlogDpos : 0 < Real.log D := Real.log_pos hD1
  have hkpos : 1 ≤ k := by omega
  have hOdd : Odd (k + 1) := (Nat.not_even_iff_odd).mp
    (fun h => (Nat.even_add_one.mp h) hkeven)
  have hTcond : ∀ p : ℕ, (p:ℝ) < z → Tcond (k + 1) D p := by
    intro p hpz
    refine ⟨fun h1 => absurd h1 (by omega), fun h2 ho => ?_⟩
    have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
    have h1 : (p:ℝ) ^ 3 < z ^ 3 := pow_lt_pow_left₀ hpz hp0 (by norm_num)
    linarith
  have hfilter : A.prodPrimes.primeFactors.filter (fun p : ℕ => (p:ℝ) < z ∧ Tcond (k + 1) D p)
      = A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z) := by
    refine Finset.filter_congr (fun p hp => ?_)
    constructor
    · rintro ⟨hpz, -⟩
      exact ⟨by exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)), hpz⟩
    · rintro ⟨-, hpz⟩
      exact ⟨hpz, hTcond p hpz⟩
  have hT : T A (k + 1) D z
      = ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
          A.nu p * T A k (D / (p:ℝ)) (p:ℝ) := by
    rw [T.eq_2 A D z k, hfilter]
  -- the child estimate
  have hchild : ∀ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
      T A k (D / (p:ℝ)) (p:ℝ) ≤ VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := by
    intro p hp
    obtain ⟨hpmem, hp2, hpz⟩ := Finset.mem_filter.mp hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.pos
    have hp3 : (p:ℝ) ^ 3 ≤ D := (hTcond p hpz).2 (by omega) hOdd
    have hDp1 : 1 ≤ D / (p:ℝ) := by
      rw [le_div_iff₀ hppos]
      have hpp : (p:ℝ) ≤ (p:ℝ)^3 := by
        have h1 : (1:ℝ) ≤ (p:ℝ)^2 := by nlinarith
        calc (p:ℝ) = (p:ℝ) * 1 := by ring
          _ ≤ (p:ℝ) * (p:ℝ)^2 := mul_le_mul_of_nonneg_left h1 hppos.le
          _ = (p:ℝ)^3 := by ring
      linarith
    have hσ2 : 2 ≤ Real.log (D / (p:ℝ)) / Real.log (p:ℝ) := by
      rw [le_div_iff₀ (Real.log_pos (by linarith : 1 < (p:ℝ))),
        Real.log_div (ne_of_gt hDpos) (ne_of_gt hppos)]
      have h := Real.log_le_log (by positivity : (0:ℝ) < (p:ℝ)^3) hp3
      rw [Real.log_pow] at h
      push_cast at h
      linarith
    have hres := hIH (D / (p:ℝ)) (p:ℝ) (by linarith) hDp1 (hSharp.sub (le_of_lt hpz))
      (fun hO => absurd hkeven ((Nat.not_even_iff_odd).mpr hO)) (fun _ => hσ2)
    have hσeq : Real.log (D / (p:ℝ)) / Real.log (p:ℝ)
        = Real.log D / Real.log (p:ℝ) - 1 := by
      rw [Real.log_div (ne_of_gt hDpos) (ne_of_gt hppos), sub_div,
        div_self (ne_of_gt (Real.log_pos (by linarith : 1 < (p:ℝ))))]
    have hΦ : PhiC k D ε (p:ℝ)
        = profC (k - 1) (Real.log D / Real.log (p:ℝ) - 1)
          + cCoef k ε * errH (Real.log D / Real.log (p:ℝ) - 1) := rfl
    rw [hΦ, ← hσeq]
    exact hres
  have hnu_nonneg : ∀ p ∈ A.prodPrimes.primeFactors, 0 ≤ A.nu p := fun p hp =>
    le_of_lt (A.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp)
      (Nat.mem_primeFactors.mp hp).2.1)
  have hsum : ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
        A.nu p * T A k (D / (p:ℝ)) (p:ℝ)
      ≤ ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
          A.nu p * VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    calc A.nu p * T A k (D / (p:ℝ)) (p:ℝ)
        ≤ A.nu p * (VfR A (p:ℝ) * PhiC k D ε (p:ℝ)) :=
          mul_le_mul_of_nonneg_left (hchild p hp) (hnu_nonneg p (Finset.mem_filter.mp hp).1)
      _ = A.nu p * VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := by ring
  -- the Abel step
  have hV : ∀ u : ℝ, 2 ≤ u → u ≤ z →
      VfR A u ≤ VfR A z * ((1 + ε) * (Real.log z / Real.log u)) :=
    fun u hu huz => VfR_le_of_sharpNorm (A := A) hε0 hSharp hu huz le_rfl
  have hΦnn : ∀ a : ℝ, 2 ≤ a → a ≤ z → 0 ≤ PhiC k D ε a := fun a _ _ => PhiC_nonneg hε0 a
  have hΦmono : ∀ a b : ℝ, 2 ≤ a → a ≤ b → b ≤ z → PhiC k D ε a ≤ PhiC k D ε b := by
    intro a b ha hab hbz
    have hbl : 1 < b := by linarith
    have hσb : 2 ≤ Real.log D / Real.log b - 1 := by
      have h : s ≤ Real.log D / Real.log b := by
        rw [hsdef]
        exact div_le_div_of_nonneg_left hlogDpos.le (Real.log_pos hbl)
          (Real.log_le_log (by linarith) hbz)
      linarith
    exact PhiC_mono' hε0 hD1 (Nat.even_iff.mp hkeven) (by linarith) hab hσb
  have habel := abel_sharp (A := A) (w := 2) (Z := z) (ε := ε) hε0 (le_refl 2)
    hz2 hV (Φ := PhiC k D ε) hΦmono hΦnn
  -- the change of variables
  have hsT : s ≤ Real.log D / Real.log 2 := by
    rw [hsdef]
    exact div_le_div_of_nonneg_left hlogDpos.le (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) hz)
  have hDpow1 : D ^ (1 / (Real.log D / Real.log 2)) = 2 := by
    rw [Real.rpow_def_of_pos hDpos]
    have h : Real.log D * (1 / (Real.log D / Real.log 2)) = Real.log 2 := by
      field_simp
    rw [h, Real.exp_log (by norm_num)]
  have hDpow2 : D ^ (1 / s) = z := by
    rw [Real.rpow_def_of_pos hDpos, hsdef]
    have h : Real.log D * (1 / (Real.log D / Real.log z)) = Real.log z := by
      field_simp
    rw [h, Real.exp_log (by linarith : (0:ℝ) < z)]
  have hcv : (∫ u in (2:ℝ)..z, PhiC k D ε u * (Real.log z / (u * (Real.log u)^2)))
      = (1/s) * ∫ t in s..(Real.log D / Real.log 2), PhiC k D ε (D^(1/t)) := by
    have h := Work.JR.abel_change_of_variables (D := D) hD1 (s := s) (T := Real.log D / Real.log 2)
      hs_pos hsT (intervalIntegrable_PhiC k D ε hDpos s (Real.log D / Real.log 2))
    rw [hDpow1, hDpow2] at h
    exact h
  -- the integral splitting
  have hΦsplit : ∀ t ∈ Set.uIcc s (Real.log D / Real.log 2),
      PhiC k D ε (D^(1/t)) = profC (k - 1) (t - 1) + cCoef k ε * errH (t - 1) := by
    intro t ht
    rw [Set.uIcc_of_le hsT] at ht
    exact PhiC_rpow hD1 (ne_of_gt (lt_of_lt_of_le hs_pos ht.1))
  set L : ℝ := ∫ t in Set.Ioi s, errH (t - 1) with hLdef
  have hint : (∫ t in s..(Real.log D / Real.log 2), PhiC k D ε (D^(1/t)))
      = (∫ t in s..(Real.log D / Real.log 2), profC (k - 1) (t - 1))
        + cCoef k ε * (∫ t in s..(Real.log D / Real.log 2), errH (t - 1)) := by
    have hcongr := intervalIntegral.integral_congr (μ := volume) hΦsplit
    have hadd := intervalIntegral.integral_add (μ := volume) (a := s)
      (b := Real.log D / Real.log 2)
      (f := fun t : ℝ => profC (k - 1) (t - 1))
      (g := fun t : ℝ => cCoef k ε * errH (t - 1))
      (intervalIntegrable_shifted_profC (k - 1) s (Real.log D / Real.log 2))
      ((intervalIntegrable_shifted_errH s (Real.log D / Real.log 2)).const_mul _)
    have hmul := intervalIntegral.integral_const_mul (μ := volume) (a := s)
      (b := Real.log D / Real.log 2) (cCoef k ε) (fun t : ℝ => errH (t - 1))
    rw [hcongr, hadd, hmul]
  have hprof : (∫ t in s..(Real.log D / Real.log 2), profC (k - 1) (t - 1)) ≤ s * profC k s := by
    simpa [Nat.sub_add_cancel hkpos] using
      profile_integral_le_even_big (k - 1) (even_sub_one_mod hkpos hkeven) (by linarith : 3 ≤ s) hsT
  have herrH : (∫ t in s..(Real.log D / Real.log 2), errH (t - 1)) ≤ L := by
    rw [hLdef]; exact errH_interval_le_tail (by linarith) hsT
  have hintle : (∫ t in s..(Real.log D / Real.log 2), PhiC k D ε (D^(1/t)))
      ≤ s * profC k s + cCoef k ε * L := by
    rw [hint]
    exact add_le_add hprof (mul_le_mul_of_nonneg_left herrH (cCoef_nonneg hε0))
  -- the main bound
  have hmain : T A (k + 1) D z ≤ VfR A z * (ε * PhiC k D ε z
      + (1+ε) * ((1/s) * (s * profC k s + cCoef k ε * L))) := by
    calc T A (k + 1) D z
        = ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
            A.nu p * T A k (D / (p:ℝ)) (p:ℝ) := hT
      _ ≤ ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => 2 ≤ (p:ℝ) ∧ (p:ℝ) < z),
            A.nu p * VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := hsum
      _ ≤ VfR A z * (ε * PhiC k D ε z
            + (1 + ε) * ∫ u in (2:ℝ)..z, PhiC k D ε u * (Real.log z / (u * (Real.log u)^2))) := habel
      _ = VfR A z * (ε * PhiC k D ε z
            + (1 + ε) * ((1/s) * ∫ t in s..(Real.log D / Real.log 2), PhiC k D ε (D^(1/t)))) := by
          rw [hcv]
      _ ≤ VfR A z * (ε * PhiC k D ε z
            + (1+ε) * ((1/s) * (s * profC k s + cCoef k ε * L))) := by
          refine mul_le_mul_of_nonneg_left ?_ (VfR_nonneg A z)
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity))
          exact mul_le_mul_of_nonneg_left hintle (by positivity)
  -- the final arithmetic
  have hΦz : PhiC k D ε z = profC (k - 1) (s - 1) + cCoef k ε * errH (s - 1) := by
    unfold PhiC
    rw [← hsdef]
  have hbudget_prof : profC k s + profC (k - 1) (s - 1)
      ≤ 990 * (99/100:ℝ)^(k-1) * errH s :=
    hB.2.2.1 (k + 1) s (by omega) (by linarith)
  have hbudget_err : ε * errH (s - 1) + (1 + ε) * L / s ≤ (99/100) * errH s := by
    rw [hLdef]
    exact hB.1 s ε (by linarith) hε0 hε1
  have hexp : ε * PhiC k D ε z + (1+ε) * ((1/s) * (s * profC k s + cCoef k ε * L))
      = profC k s + ε * (profC k s + profC (k - 1) (s - 1))
        + cCoef k ε * (ε * errH (s - 1) + (1 + ε) * L / s) := by
    rw [hΦz]
    field_simp
    ring
  have key : profC k s + ε * (profC k s + profC (k - 1) (s - 1))
      + cCoef k ε * (ε * errH (s - 1) + (1 + ε) * L / s) ≤ profC k s + cCoef (k + 1) ε * errH s := by
    set P : ℝ := ε * (99/100:ℝ)^(k-1) * errH s with hPdef
    have h1 : ε * (profC k s + profC (k - 1) (s - 1)) ≤ 990 * P := by
      have h := mul_le_mul_of_nonneg_left hbudget_prof hε0
      calc ε * (profC k s + profC (k - 1) (s - 1))
          ≤ ε * (990 * (99/100:ℝ)^(k-1) * errH s) := h
        _ = 990 * P := by rw [hPdef]; ring
    have h2 : cCoef k ε * (ε * errH (s - 1) + (1 + ε) * L / s) ≤ 990 * ((k:ℝ) + 1) * P := by
      have h := mul_le_mul_of_nonneg_left hbudget_err (cCoef_nonneg (k := k) hε0)
      calc cCoef k ε * (ε * errH (s - 1) + (1 + ε) * L / s)
          ≤ cCoef k ε * ((99/100) * errH s) := h
        _ = 990 * ((k:ℝ) + 1) * P := by rw [cCoef, hPdef]; ring
    have htarget : cCoef (k + 1) ε * errH s = 990 * ((k:ℝ) + 2) * P := by
      rw [cCoef_succ, hPdef]
      have hpow : (99/100:ℝ)^k = (99/100)^(k-1) * (99/100) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
      rw [hpow]; ring
    have hid : 990 * P + 990 * ((k:ℝ) + 1) * P = 990 * ((k:ℝ) + 2) * P := by ring
    rw [htarget]
    linarith [h1, h2, hid]
  calc T A (k + 1) D z ≤ VfR A z * (ε * PhiC k D ε z
        + (1+ε) * ((1/s) * (s * profC k s + cCoef k ε * L))) := hmain
    _ = VfR A z * (profC k s + ε * (profC k s + profC (k - 1) (s - 1))
        + cCoef k ε * (ε * errH (s - 1) + (1 + ε) * L / s)) := by rw [hexp]
    _ ≤ VfR A z * (profC k s + cCoef (k + 1) ε * errH s) :=
        mul_le_mul_of_nonneg_left key (VfR_nonneg A z)
    _ = VfR A z * (profC k (Real.log D / Real.log z)
        + cCoef (k + 1) ε * errH (Real.log D / Real.log z)) := by rw [hsdef]

/-! ## The assembly: `LayerSharpBound 1000 (99/100)` -/

/-- `¬ Even (k+1)` forces `k` to be even. -/
lemma even_of_not_even_succ {k : ℕ} (h : ¬ Even (k + 1)) : Even k := by
  refine Nat.even_iff.mpr ?_
  have h1 : (k + 1) % 2 ≠ 0 := fun hc => h (Nat.even_iff.mpr hc)
  omega

/-- `Even (k+1)` forces `k` to be odd. -/
lemma odd_of_even_succ {k : ℕ} (h : Even (k + 1)) : Odd k :=
  (Nat.not_even_iff_odd).mp (Nat.even_add_one.mp h)

/-- **The sharp layer bound, given the arithmetic budgets.** -/
theorem layer_sharp_of_budgets (hB : Budgets) :
    LayerSharpBound 1000 (99/100) := by
  intro A ε D z hε0 hε1 hz hD hSharp n hn hodd heven
  have main : ∀ n : ℕ, (1 ≤ n → ∀ D z : ℝ, 2 ≤ z → 1 ≤ D → SharpNorm A z ε →
      (Odd n → 1 ≤ Real.log D / Real.log z) → (Even n → 2 ≤ Real.log D / Real.log z) →
      T A n D z ≤ VfR A z * (profC (n - 1) (Real.log D / Real.log z)
        + cCoef n ε * errH (Real.log D / Real.log z))) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · -- index `1`: the base case
        subst hk0
        intro D z hz hD hSharp hodd heven
        have hs1 : 1 ≤ Real.log D / Real.log z := hodd (by norm_num)
        have hbase := layer_sharp_base (A := A) hε0 hε1 hz hD hSharp hs1
        have hc1 : cCoef 1 ε = ε * 2000 := by
          rw [cCoef, show (1:ℕ) - 1 = 0 from rfl, pow_zero, mul_one, Nat.cast_one]
          ring
        have heq : ε * 2000 * errH (Real.log D / Real.log z)
            = cCoef 1 ε * errH (Real.log D / Real.log z) := by rw [hc1]
        rw [heq] at hbase
        simpa using hbase
      · -- index `k+1`, `k ≥ 1`
        intro D z hz hD hSharp hodd heven
        by_cases hEven : Even (k + 1)
        · -- case (A): even row, `s ≥ 2`
          have hkodd : Odd k := odd_of_even_succ hEven
          have hs2 : 2 ≤ Real.log D / Real.log z := heven hEven
          exact step_even (A := A) hkpos hkodd hB hε0 hε1 hz hD hSharp hs2
            (fun D' z' hz' hD' hS' ho he => ih hkpos D' z' hz' hD' hS' ho he)
        · -- case (B)/(B'): odd row
          have hOdd : Odd (k + 1) := (Nat.not_even_iff_odd).mp hEven
          have hkeven : Even k := even_of_not_even_succ hEven
          have hs1 : 1 ≤ Real.log D / Real.log z := hodd hOdd
          have hk2 : 2 ≤ k := by
            obtain ⟨m, hm⟩ := hkeven
            omega
          by_cases hs3 : 3 ≤ Real.log D / Real.log z
          · -- case (B): `s ≥ 3`
            exact step_odd_big (A := A) hk2 hkeven hB hε0 hε1 hz hD hSharp hs3
              (fun D' z' hz' hD' hS' ho he => ih hkpos D' z' hz' hD' hS' ho he)
          · -- case (B'): `1 ≤ s < 3`
            exact step_small_final (A := A) hk2 hkeven hB hε0 hε1 hz hD hSharp hs1
              (not_le.mp hs3) (budget_shift ε hε0 hε1)
              (fun D' z' hz' hD' hS' ho he => ih hkpos D' z' hz' hD' hS' ho he)
  exact main n hn D z hz hD hSharp hodd heven

/-- **The crux: the per-layer Rosser–Iwaniec bound under the sharp normalisation**
(BJS arXiv:2207.09452 `lemma:expf_n` / Nathanson Thm 9.5, in the simplified *geometric* allowance
shape `ε·C·(n+1)·ρ^{n-1}·errH s`, which is all the glue needs since `Σ_n ρ^n < ∞`). -/
theorem layer_sharp : Work.ChenPlan.LinearSieve.JR2.LayerSharpBound 1000 (99/100) :=
  layer_sharp_of_budgets budget_sharp

end

end Work.ChenPlan.LinearSieve.JR2
