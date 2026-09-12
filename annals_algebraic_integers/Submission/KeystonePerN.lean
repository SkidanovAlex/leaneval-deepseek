import Submission.ConverseAssembly
import Submission.Asymptotics
import Submission.MeanAsymptotics
import Submission.SqfVieta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Per-n construction of the Eisenstein irreducible polynomial

Smith, adjust.tex §4.1: given the early-ints polynomial `P` (high coefficients
even integers), the squarefree `Q` of degree `d = n − m`, and the adjusted
integer polynomial `R0` with `‖R0 − (¼·P_low + ½)‖_d ≤ n^{C0+C0√n}`, define

    R_n := T_high + 4·R0 − 2          (T_high = P's integer high part)

and prove: monic, degree `n`, irreducible (Eisenstein at 2), all complex roots
in the open Serre interval (sign changes in the brackets), and the weighted
`n`-norm bound `‖R_n‖_n ≤ M^m·(n^{C1}·κ^m + 4·n^{C0+C0√n})`.
-/

noncomputable section

open MeasureTheory
open ComplexOrder
open Filter
open Polynomial
open scoped Real BigOperators Topology

namespace Submission.KeystonePerN

open Submission.Contracts
open Submission.ConverseAssembly
open Submission.WnormToolkit
open Submission.IvtRoots
open Submission.Notions
open Submission.Serre
open Submission.SerreExample
open Submission.WeightedNorm

/-- Eisenstein shape: `T + S` with `T` monic degree `n` (even non-constant
coefficients, zero constant term) and `S` low-degree with even coefficients and
constant term not divisible by 4, is monic, of degree `n`, and irreducible. -/
lemma eisenstein_shape {n : ℕ} (T S : Polynomial ℤ)
    (hTmon : T.Monic) (hTn : T.natDegree = n)
    (hT0 : T.coeff 0 = 0)
    (hTeven : ∀ k : ℕ, 0 < k → k < n → Even (T.coeff k))
    (hSdeg : S.natDegree < n) (hScoeff : ∀ k : ℕ, k < n → Even (S.coeff k))
    (hS0 : ¬ (4 : ℤ) ∣ S.coeff 0) (hn : 0 < n) :
    (T + S).Monic ∧ (T + S).natDegree = n ∧ Irreducible (T + S) := by
  let R := T + S
  have hSlt : S.natDegree < T.natDegree := by rwa [hTn]
  have hRn : R.natDegree = n := by
    dsimp [R]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (p := T) (q := S) hSlt, hTn]
  have hmon : R.Monic := by
    unfold Polynomial.Monic
    rw [Polynomial.leadingCoeff, hRn]
    dsimp [R]
    rw [Polynomial.coeff_add]
    have hSn : S.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hSdeg
    rw [hSn, add_zero]
    have hTcn : T.coeff n = 1 := by
      rw [← hTn]
      change Polynomial.leadingCoeff T = 1
      exact hTmon.leadingCoeff
    exact hTcn
  have hcoeffR : ∀ k : ℕ, k < R.natDegree → Even (R.coeff k) := by
    intro k hk
    have hkn : k < n := by simpa [hRn] using hk
    dsimp [R]
    rw [Polynomial.coeff_add]
    by_cases hk0 : k = 0
    · subst k
      rw [hT0, zero_add]
      exact hScoeff 0 hkn
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      exact Even.add (hTeven k hkpos hkn) (hScoeff k hkn)
  have hnd4 : ¬ (4 : ℤ) ∣ R.coeff 0 := by
    dsimp [R]
    rw [Polynomial.coeff_add, hT0, zero_add]
    exact hS0
  have hIrred : Irreducible R := by
    exact EisensteinInt.irreducible_of_eisenstein_two (F := R) (by rwa [hRn]) hmon hcoeffR hnd4
  exact ⟨hmon, hRn, hIrred⟩

/-- The low perturbation `4·R0 − 2` has degree `< n` when `natDegree R0 ≤ d−1`
and `d ≤ n`. -/
lemma low_part_deg {n d : ℕ} (R0 : Polynomial ℤ) (hRdeg : R0.natDegree ≤ d - 1)
    (hd : 1 ≤ d) (hdn : d ≤ n) : (Polynomial.C (4 : ℤ) * R0 - Polynomial.C 2).natDegree < n := by
  have h1 : (Polynomial.C (4 : ℤ) * R0).natDegree ≤ d - 1 := by
    exact le_trans (Polynomial.natDegree_C_mul_le (4 : ℤ) R0) hRdeg
  have h2 : (Polynomial.C (2 : ℤ) : Polynomial ℤ).natDegree ≤ d - 1 := by simp
  have hle : (Polynomial.C (4 : ℤ) * R0 - Polynomial.C 2).natDegree ≤ d - 1 := by
    exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le h1 h2)
  have hlt : d - 1 < n := by omega
  exact lt_of_le_of_lt hle hlt

/-- Coefficient parities of the low perturbation `4·R0 − 2`. -/
lemma low_part_coeff_even {n d : ℕ} (R0 : Polynomial ℤ) (hRdeg : R0.natDegree ≤ d - 1)
    (k : ℕ) (hk : k < n) : Even ((Polynomial.C (4 : ℤ) * R0 - Polynomial.C 2).coeff k) := by
  by_cases hk0 : k = 0
  · subst k
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C]
    simp only [eq_self_iff_true, if_true]
    exact even_four_mul_sub_two (R0.coeff 0)
  · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C]
    simp only [if_neg hk0, sub_zero]
    exact even_four_mul (R0.coeff k)

/-- Constant coefficient of the low perturbation is `4·c − 2`, not divisible by 4. -/
lemma low_part_const_not_four {R0 : Polynomial ℤ} :
    ¬ (4 : ℤ) ∣ (Polynomial.C (4 : ℤ) * R0 - Polynomial.C 2).coeff 0 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C]
  simp only [eq_self_iff_true, if_true]
  exact not_four_dvd_four_mul_sub_two (R0.coeff 0)


/-! ## The integer high part `T_high` of the early-ints polynomial

The early-ints `P` has even *integer* coefficients in degrees `[d, n−1]`
(`z k`); `highPoly n d z = X^n + Σ_{k=d}^{n−1} z(k)·X^k` packages that integer
part.  `highPoly_spec` records monicity, degree, zero low coefficients, and the
high coefficients `z k`.
-/

lemma sumDegree_le {n d : ℕ} (z : ℕ → ℤ) :
    ((Finset.Icc d (n - 1)).sum (fun k => Polynomial.monomial k (z k))).natDegree ≤ n - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.Icc d (n - 1) : Finset ℕ))
    (n := n - 1) (f := fun k : ℕ => (Polynomial.monomial k (z k) : Polynomial ℤ)) ?_
  intro k hk
  have hk1 : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
  exact (Polynomial.natDegree_monomial_le (a := z k) (m := k)).trans hk1

noncomputable def highPoly (n d : ℕ) (z : ℕ → ℤ) : Polynomial ℤ :=
  X ^ n + (Finset.Icc d (n - 1)).sum (fun k => Polynomial.monomial k (z k))

lemma highPoly_spec {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (hn : 0 < n) (z : ℕ → ℤ) :
    (highPoly n d z).Monic ∧ (highPoly n d z).natDegree = n ∧ (highPoly n d z).coeff 0 = 0 ∧
    (∀ k : ℕ, k < d → (highPoly n d z).coeff k = 0) ∧
    (∀ k : ℕ, d ≤ k → k < n → (highPoly n d z).coeff k = z k) := by
  classical
  let S : Polynomial ℤ := (Finset.Icc d (n - 1)).sum (fun k => Polynomial.monomial k (z k))
  have hSdeg : S.natDegree ≤ n - 1 := by
    change ((Finset.Icc d (n - 1)).sum (fun k => Polynomial.monomial k (z k))).natDegree ≤ n - 1
    exact sumDegree_le z
  have hXdeg : (X ^ n : Polynomial ℤ).natDegree = n := by
    rw [Polynomial.natDegree_X_pow]
  have hSlt : S.natDegree < (X ^ n : Polynomial ℤ).natDegree := by
    rw [hXdeg]
    exact lt_of_le_of_lt hSdeg (Nat.sub_lt hn (by norm_num))
  have hTn : (X ^ n + S : Polynomial ℤ).natDegree = n := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (p := (X ^ n : Polynomial ℤ))
      (q := S) hSlt, hXdeg]
  have hScoeff : ∀ j : ℕ, S.coeff j =
      (Finset.Icc d (n - 1)).sum (fun k => if k = j then z k else 0) := by
    intro j
    dsimp [S]
    simp [Polynomial.coeff_monomial]
  have hSn : S.coeff n = 0 := by
    rw [hScoeff n]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k ≠ n := by
      have hk1 : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
      omega
    simp [hkn]
  have hmon : (X ^ n + S : Polynomial ℤ).Monic := by
    unfold Polynomial.Monic
    rw [Polynomial.leadingCoeff, hTn]
    rw [Polynomial.coeff_add, hSn, add_zero]
    rw [Polynomial.coeff_X_pow]
    simp
  have hXcoeff0 : (X ^ n : Polynomial ℤ).coeff 0 = 0 := by
    rw [Polynomial.coeff_X_pow]
    simp [show 0 ≠ n by omega]
  have hT0 : (X ^ n + S : Polynomial ℤ).coeff 0 = 0 := by
    rw [Polynomial.coeff_add, hXcoeff0, zero_add, hScoeff 0]
    apply Finset.sum_eq_zero
    intro k hk
    have hk0 : k ≠ 0 := by
      have hkd : d ≤ k := (Finset.mem_Icc.mp hk).1
      omega
    simp [hk0]
  have hXcoeff : ∀ k : ℕ, (X ^ n : Polynomial ℤ).coeff k = if k = n then 1 else 0 := by
    intro k
    rw [Polynomial.coeff_X_pow]
  have hTlow : ∀ k : ℕ, k < d → (X ^ n + S : Polynomial ℤ).coeff k = 0 := by
    intro k hkd
    rw [Polynomial.coeff_add]
    have hkX : (X ^ n : Polynomial ℤ).coeff k = 0 := by
      rw [hXcoeff k]
      simp [show k ≠ n by omega]
    rw [hkX, zero_add, hScoeff k]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j ≠ k := by
      have hjd : d ≤ j := (Finset.mem_Icc.mp hj).1
      omega
    simp [hjk]
  have hThigh : ∀ k : ℕ, d ≤ k → k < n → (X ^ n + S : Polynomial ℤ).coeff k = z k := by
    intro k hkd hkn
    rw [Polynomial.coeff_add]
    have hkX : (X ^ n : Polynomial ℤ).coeff k = 0 := by
      rw [hXcoeff k]
      simp [show k ≠ n by omega]
    rw [hkX, zero_add, hScoeff k]
    have hkm : k ∈ Finset.Icc d (n - 1) := by
      rw [Finset.mem_Icc]
      exact ⟨hkd, Nat.le_pred_of_lt hkn⟩
    rw [Finset.sum_eq_single k]
    · simp
    · intro j hj hjk
      simp [hjk]
    · intro hknot
      exact False.elim (hknot hkm)
  rw [show highPoly n d z = (X ^ n + S : Polynomial ℤ) by rfl]
  exact ⟨hmon, hTn, hT0, hTlow, hThigh⟩


/-! ## The per-n construction (`per_n_exists`) -/

/-- Real-power bound for the adjustment step:
`d^Ca · d^{Cs√d} ≤ n^{C0 + C0√n}` (d ≤ n, Cs,Ca ≤ C0). -/
lemma power_bound_adjust {n d : ℕ} {Cs Ca C0 : ℝ}
    (hdn : d ≤ n) (hn1 : 1 ≤ (n : ℝ))
    (hCs0 : 0 ≤ Cs) (hCa0 : 0 ≤ Ca)
    (hCsC0 : Cs ≤ C0) (hCaC0 : Ca ≤ C0) (hC0 : 0 ≤ C0) :
    (d : ℝ) ^ Ca * (d : ℝ) ^ (Cs * Real.sqrt (d : ℝ)) ≤
      (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) := by
  have hd0 : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hCsd0 : 0 ≤ Cs * Real.sqrt (d : ℝ) :=
    mul_nonneg hCs0 (Real.sqrt_nonneg _)
  have h1a : (d : ℝ) ^ Ca ≤ (n : ℝ) ^ Ca := Real.rpow_le_rpow hd0 (by exact_mod_cast hdn) hCa0
  have h1b : (n : ℝ) ^ Ca ≤ (n : ℝ) ^ C0 :=
    Real.rpow_le_rpow_of_exponent_le hn1 hCaC0
  have h1 : (d : ℝ) ^ Ca ≤ (n : ℝ) ^ C0 := le_trans h1a h1b
  have h2a : (d : ℝ) ^ (Cs * Real.sqrt (d : ℝ)) ≤ (n : ℝ) ^ (Cs * Real.sqrt (d : ℝ)) :=
    Real.rpow_le_rpow hd0 (by exact_mod_cast hdn) hCsd0
  have hsq : Real.sqrt (d : ℝ) ≤ Real.sqrt (n : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hdn)
  have h2b : (n : ℝ) ^ (Cs * Real.sqrt (d : ℝ)) ≤ (n : ℝ) ^ (Cs * Real.sqrt (n : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    exact mul_le_mul_of_nonneg_left hsq hCs0
  have h2c : (n : ℝ) ^ (Cs * Real.sqrt (n : ℝ)) ≤ (n : ℝ) ^ (C0 * Real.sqrt (n : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    exact mul_le_mul_of_nonneg_right hCsC0 (Real.sqrt_nonneg _)
  have h2 : (d : ℝ) ^ (Cs * Real.sqrt (d : ℝ)) ≤ (n : ℝ) ^ (C0 * Real.sqrt (n : ℝ)) :=
    le_trans (le_trans h2a h2b) h2c
  have hprod : (d : ℝ) ^ Ca * (d : ℝ) ^ (Cs * Real.sqrt (d : ℝ)) ≤
      (n : ℝ) ^ C0 * (n : ℝ) ^ (C0 * Real.sqrt (n : ℝ)) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hn1
  have hcomb : (n : ℝ) ^ C0 * (n : ℝ) ^ (C0 * Real.sqrt (n : ℝ)) =
      (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) := by
    rw [Real.rpow_add hnpos]
  rw [← hcomb]
  exact hprod

/-- From the four contracts (unpacked to this index `n`), construct the
Eisenstein polynomial `R_n`. -/
theorem per_n_exists {Cs Ca C0 C1 Cm B M : ℝ}
    (hCs : 0 < Cs) (hCa : 0 < Ca) (hC0 : 0 < C0)
    (hCsC0 : Cs ≤ C0) (hCaC0 : Ca ≤ C0)
    (sqf : ∀ n : ℕ, 2 ≤ n → ∃ Q : Polynomial ℤ, Squarefree Q ∧ Q.natDegree = n ∧
        wnorm n (zmap Q) ≤ npow n Cs)
    (adj : ∀ n : ℕ, 2 ≤ n → ∀ Q : Polynomial ℤ, Squarefree Q → Q.natDegree = n →
        ∀ P : Polynomial ℝ, P.natDegree ≤ n - 1 →
          ∃ R : Polynomial ℤ, R.natDegree ≤ n - 1 ∧
            wnorm n (P - zmap R) ≤ (n : ℝ) ^ Ca * wnorm n (zmap Q))
    (early : ∀ n : ℕ, (C1 : ℝ) < n → 2 ≤ n - mFloor B n → EarlyPolynomialData B C1 Cm n)
    (hM1 : 1 ≤ M)
    (hM : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → weight muSerre x ≤ M)
    {n : ℕ}
    (hineq : let m := mFloor B n
      2 ≤ n - m ∧ m ≤ n ∧ (C1 : ℝ) < (n : ℝ) ∧
        4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) < (n : ℝ) ^ (-C1) * kappa ^ m ∧
        1 ≤ mFloor B n) :
    ∃ Rn : Polynomial ℤ,
      Rn.Monic ∧ Rn.natDegree = n ∧ Irreducible Rn ∧
      (∀ z : ℂ, Polynomial.aeval z Rn = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) ∧
      wnorm n (zmap Rn) ≤
        M ^ mFloor B n * ((n : ℝ) ^ C1 * kappa ^ mFloor B n +
          4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ))) ∧
      |rootMeanReal Rn - (∫ x : ℝ, x ∂muSerre)| ≤
        Cm * ((mFloor B n : ℝ) + 1) / (n : ℝ) := by
  classical
  let m : ℕ := mFloor B n
  let d : ℕ := n - m
  have hineq' : 2 ≤ n - mFloor B n ∧ mFloor B n ≤ n ∧ (C1 : ℝ) < (n : ℝ) ∧
      4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) < (n : ℝ) ^ (-C1) * kappa ^ mFloor B n ∧
      1 ≤ mFloor B n := by
    simpa [m] using hineq
  have hd2 : 2 ≤ d := by
    simpa [d, m] using hineq'.1
  have hmle : m ≤ n := by
    simpa [m] using hineq'.2.1
  have hC1n : (C1 : ℝ) < (n : ℝ) := hineq'.2.2.1
  have hmain : 4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) <
      (n : ℝ) ^ (-C1) * kappa ^ m := by
    simpa [m] using hineq'.2.2.2.1
  have hm1 : 1 ≤ mFloor B n := hineq'.2.2.2.2
  have hdn : d ≤ n := by
    exact Nat.sub_le n m
  have hd_pos : 0 < d := by omega
  have hn_pos : 0 < n := by omega
  have hn_natC1 : (C1 : ℝ) < n := by simpa using hC1n
  -- early-ints polynomial P with its bracket data
  have hPearly : EarlyPolynomialData B C1 Cm n :=
    early n hn_natC1 (by simpa [d, m] using hd2)
  rcases hPearly with ⟨P, hPmon, hPdeg, hPbig⟩
  rcases hPbig with ⟨hPαxy, hzeven, hPnorm⟩
  rcases hPαxy with ⟨α, x, y, hPfac, hαab, hαmono, hxyIcc, hxy, hxαy, hsep, hwv, hαmean⟩
  -- weighted endpoint values (rewritten with d)
  have hwv' : ∀ i : Fin n,
      (weight muSerre (x i)) ^ d * |P.eval (x i)| ≥ (n : ℝ) ^ (-C1) * kappa ^ m ∧
      (weight muSerre (y i)) ^ d * |P.eval (y i)| ≥ (n : ℝ) ^ (-C1) * kappa ^ m ∧
      P.eval (x i) ≠ 0 ∧ P.eval (y i) ≠ 0 := by
    intro i
    simpa [d, m] using (hwv i)
  -- high coefficients z k (even integers matching P)
  let z : ℕ → ℤ := fun k => if h : d ≤ k ∧ k < n then
      Classical.choose (hzeven k (by simpa [d, m] using h.1) (by omega)) else 0
  have hzP : ∀ k : ℕ, d ≤ k → k < n → P.coeff k = (z k : ℝ) := by
    intro k hkd hkn
    dsimp [z]
    rw [dif_pos]
    · exact (Classical.choose_spec (hzeven k (by simpa [d, m] using hkd) (by omega))).1
    · exact ⟨hkd, hkn⟩
  have hzEven : ∀ k : ℕ, d ≤ k → k < n → Even (z k) := by
    intro k hkd hkn
    dsimp [z]
    rw [dif_pos]
    · exact (Classical.choose_spec (hzeven k (by simpa [d, m] using hkd) (by omega))).2
    · exact ⟨hkd, hkn⟩
  -- the integer high part and its properties
  let T : Polynomial ℤ := highPoly n d z
  have hTs : T.Monic ∧ T.natDegree = n ∧ T.coeff 0 = 0 ∧
      (∀ k : ℕ, k < d → T.coeff k = 0) ∧
      (∀ k : ℕ, d ≤ k → k < n → T.coeff k = z k) := highPoly_spec hd_pos hdn hn_pos z
  -- the real low part
  let Plow : Polynomial ℝ := P - zmap T
  have hPlow_deg : Plow.natDegree ≤ d - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    have hkd : d ≤ k := by omega
    dsimp [Plow]
    rw [Polynomial.coeff_sub]
    by_cases hkn : k < n
    · have hz : P.coeff k = (z k : ℝ) := hzP k hkd hkn
      have ht : (zmap T).coeff k = (z k : ℝ) := by
        dsimp [zmap]
        rw [Polynomial.coeff_map, hTs.2.2.2.2 k hkd hkn]
        norm_num
      rw [hz, ht]
      ring
    · by_cases hkeq : k = n
      · subst k
        have hp1 : P.coeff n = 1 := by
          rw [← hPdeg]
          change Polynomial.leadingCoeff P = 1
          exact hPmon.leadingCoeff
        have ht1' : T.coeff n = 1 := by
          rw [← hTs.2.1]
          change Polynomial.leadingCoeff T = 1
          exact hTs.1.leadingCoeff
        have ht1 : (zmap T).coeff n = 1 := by
          dsimp [zmap]
          rw [Polynomial.coeff_map, ht1']
          norm_num
        rw [hp1, ht1]
        norm_num
      · have hkg : n < k := by omega
        have hp : P.coeff k = 0 := by
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hPdeg]; exact hkg)
        have ht : (zmap T).coeff k = 0 := by
          dsimp [zmap]
          rw [Polynomial.coeff_map]
          have ht' : T.coeff k = 0 := by
            exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hTs.2.1]; exact hkg)
          rw [ht']
          norm_num
        rw [hp, ht]
        ring
  have hP_eq : P = zmap T + Plow := by
    dsimp [Plow]
    abel
  -- choose z high coefficients -- (z k are the same)
  have hz_high : ∀ k : ℕ, d ≤ k → k < n → (zmap T).coeff k = (z k : ℝ) := by
    intro k hkd hkn
    dsimp [zmap]
    rw [Polynomial.coeff_map]
    rw [hTs.2.2.2.2 k hkd hkn]
    norm_num
  -- squarefree Q of degree d
  obtain ⟨Q, hQsq, hQd, hQn⟩ := sqf d (by simpa [d, m] using hd2)
  -- adjusted R0 for (1/4)Plow + 1/2
  let P' : Polynomial ℝ := (1 / 4 : ℝ) • Plow + Polynomial.C (1 / 2)
  have hP'deg : P'.natDegree ≤ d - 1 := by
    dsimp [P']
    have h1 : ((1 / 4 : ℝ) • Plow).natDegree ≤ d - 1 := by
      exact le_trans (Polynomial.natDegree_smul_le (1 / 4 : ℝ) Plow) hPlow_deg
    have h2 : (Polynomial.C (1 / 2) : Polynomial ℝ).natDegree ≤ d - 1 := by
      rw [Polynomial.natDegree_C]
      exact Nat.zero_le _
    exact le_trans (Polynomial.natDegree_add_le _ _) (max_le h1 h2)
  rcases adj d (by simpa [d, m] using hd2) Q hQsq hQd P' hP'deg with ⟨R0, hR0deg, hR0n⟩
  -- combined weighted-norm bound for the adjustment
  have hQb : wnorm d (zmap Q) ≤ (d : ℝ) ^ (Cs * Real.sqrt (d : ℝ)) := by
    simpa [npow] using hQn
  have hR0n'' : wnorm d (P' - zmap R0) ≤ (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) := by
    calc
      wnorm d (P' - zmap R0) ≤ (d : ℝ) ^ Ca * wnorm d (zmap Q) := hR0n
      _ ≤ (d : ℝ) ^ Ca * (d : ℝ) ^ (Cs * Real.sqrt (d : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hQb (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le d) _)
      _ ≤ (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) := by
        refine power_bound_adjust (n := n) (d := d) hdn ?_ hCs.le hCa.le hCsC0 hCaC0 hC0.le
        exact_mod_cast (by omega : (1 : ℕ) ≤ n)
  have hR0n' : wnorm d (zmap R0 - P') ≤ (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) := by
    rw [show zmap R0 - P' = -(P' - zmap R0) by abel]
    rw [wnorm_neg]
    exact hR0n''
  -- the constructed Eisenstein polynomial
  let S0 : Polynomial ℤ := Polynomial.C (4 : ℤ) * R0 - Polynomial.C 2
  let Rn : Polynomial ℤ := T + S0
  have hSdeg : S0.natDegree < n := by
    exact low_part_deg R0 hR0deg (by omega) hdn
  have hScoeff : ∀ k : ℕ, k < n → Even (S0.coeff k) := by
    intro k hk
    exact low_part_coeff_even R0 hR0deg k hk
  have hS0n4 : ¬ (4 : ℤ) ∣ S0.coeff 0 := low_part_const_not_four (R0 := R0)
  have hTeven : ∀ k : ℕ, 0 < k → k < n → Even (T.coeff k) := by
    intro k hkpos hkn
    by_cases hkd : k < d
    · have ht : T.coeff k = 0 := hTs.2.2.2.1 k hkd
      rw [ht]
      exact ⟨0, by simp⟩
    · have hdk : d ≤ k := le_of_not_gt hkd
      have ht : T.coeff k = z k := hTs.2.2.2.2 k hdk hkn
      rw [ht]
      exact hzEven k hdk hkn
  have hEis := eisenstein_shape (n := n) T S0 hTs.1 hTs.2.1 hTs.2.2.1 hTeven hSdeg hScoeff hS0n4 hn_pos
  have hRn_mon : Rn.Monic := by simpa [Rn] using hEis.1
  have hRn_deg : Rn.natDegree = n := by simpa [Rn] using hEis.2.1
  have hRn_irr : Irreducible Rn := by simpa [Rn] using hEis.2.2
  -- the norm identity:  zmap Rn − P = 4 • (zmap R0 − P')
  have hnorm_id : zmap Rn - P = (4 : ℝ) • (zmap R0 - P') := by
    dsimp [Rn, S0, P', Plow]
    have hL : zmap (T + (Polynomial.C (4 : ℤ) * R0 - Polynomial.C 2)) - P
        = (4 : ℝ) • zmap R0 - Polynomial.C (2 : ℝ) - (P - zmap T) := by
      have h1 : zmap (T + (Polynomial.C (4 : ℤ) * R0 - Polynomial.C 2))
          = zmap T + zmap (Polynomial.C (4 : ℤ) * R0) - zmap (Polynomial.C (2 : ℤ)) := by
        simp [zmap]
        abel
      rw [h1, zmap_four_mul, zmap_two]
      rw [← Polynomial.smul_eq_C_mul]
      abel
    have hR : (4 : ℝ) • (zmap R0 - ((1 / 4 : ℝ) • (P - zmap T) + Polynomial.C (1 / 2)))
        = (4 : ℝ) • zmap R0 - (P - zmap T) - Polynomial.C (2 : ℝ) := by
      rw [smul_sub, smul_add]
      rw [show (4 : ℝ) • ((1 / 4 : ℝ) • (P - zmap T)) = (P - zmap T) by
        rw [smul_smul]
        norm_num]
      rw [show (4 : ℝ) • Polynomial.C (1 / 2 : ℝ) = Polynomial.C (2 : ℝ) by
        rw [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
        norm_num]
      abel
    rw [hL, hR]
    abel
  -- weighted-d norm bound for Rn − P and for Rn
  have hdiff : wnorm d (zmap Rn - P) ≤ 4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) := by
    rw [hnorm_id]
    rw [wnorm_four_smul]
    exact mul_le_mul_of_nonneg_left hR0n' (by norm_num : (0 : ℝ) ≤ 4)
  have hPnorm' : wnorm d P ≤ (n : ℝ) ^ C1 * kappa ^ m := by
    simpa [d, m] using hPnorm
  have hRn_lownorm : wnorm d (zmap Rn) ≤ (n : ℝ) ^ C1 * kappa ^ m +
      4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) := by
    have hz : P + (zmap Rn - P) = zmap Rn := by abel
    calc
      wnorm d (zmap Rn) = wnorm d (P + (zmap Rn - P)) := by rw [hz]
      _ ≤ wnorm d P + wnorm d (zmap Rn - P) := wnorm_add_le d P (zmap Rn - P)
      _ ≤ (n : ℝ) ^ C1 * kappa ^ m + 4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) := by
        exact add_le_add hPnorm' hdiff
  -- exponent shift to the n-norm
  have hRn_norm : wnorm n (zmap Rn) ≤ M ^ m * ((n : ℝ) ^ C1 * kappa ^ m +
      4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ))) := by
    have hsh := wnorm_exp_shift (n := n) (m := m) (M := M) (P := zmap Rn) hmle
      (fun x hx => hM x hx) (by linarith)
    have hshift : wnorm n (zmap Rn) ≤ M ^ m * wnorm d (zmap Rn) := by
      simpa [d] using hsh
    exact le_trans hshift (mul_le_mul_of_nonneg_left hRn_lownorm (pow_nonneg (by linarith) m))
  -- roots of Rn lie in the open interval: sign changes in each bracket
  have hclose : ∀ i : Fin n,
      |P.eval (x i) - (zmap Rn).eval (x i)| < |P.eval (x i)| ∧
      |P.eval (y i) - (zmap Rn).eval (y i)| < |P.eval (y i)| := by
    intro i
    have hxI : x i ∈ Set.Icc aSerre bSerre :=
      ⟨(hxyIcc i).1, le_trans (le_of_lt (hxy i)) (hxyIcc i).2⟩
    have hyI : y i ∈ Set.Icc aSerre bSerre :=
      ⟨le_trans (hxyIcc i).1 (le_of_lt (hxy i)), (hxyIcc i).2⟩
    have hwvx : (weight muSerre (x i)) ^ d * |P.eval (x i)| ≥ (n : ℝ) ^ (-C1) * kappa ^ m := (hwv' i).1
    have hwvy : (weight muSerre (y i)) ^ d * |P.eval (y i)| ≥ (n : ℝ) ^ (-C1) * kappa ^ m := (hwv' i).2.1
    have hb1x : (weight muSerre (x i)) ^ d * |(zmap Rn).eval (x i) - P.eval (x i)|
        ≤ wnorm d (zmap Rn - P) := by
      have hg := wnorm_ge_pointwise d (zmap Rn - P) hxI
      simpa [Polynomial.eval_sub] using hg
    have hx_lt : (weight muSerre (x i)) ^ d * |(zmap Rn).eval (x i) - P.eval (x i)|
        < (weight muSerre (x i)) ^ d * |P.eval (x i)| := by
      exact lt_of_lt_of_le (lt_of_le_of_lt (le_trans hb1x hdiff) hmain) hwvx
    have hrel : |(zmap Rn).eval (x i) - P.eval (x i)| < |P.eval (x i)| := by
      have hwp : 0 ≤ (weight muSerre (x i)) ^ d := pow_nonneg (le_of_lt (weight_pos muSerre (x i))) d
      exact lt_of_mul_lt_mul_left hx_lt hwp
    have hrel' : |P.eval (x i) - (zmap Rn).eval (x i)| < |P.eval (x i)| := by
      simpa [abs_sub_comm] using hrel
    have hb1y : (weight muSerre (y i)) ^ d * |(zmap Rn).eval (y i) - P.eval (y i)|
        ≤ wnorm d (zmap Rn - P) := by
      have hg := wnorm_ge_pointwise d (zmap Rn - P) hyI
      simpa [Polynomial.eval_sub] using hg
    have hy_lt : (weight muSerre (y i)) ^ d * |(zmap Rn).eval (y i) - P.eval (y i)|
        < (weight muSerre (y i)) ^ d * |P.eval (y i)| := by
      exact lt_of_lt_of_le (lt_of_le_of_lt (le_trans hb1y hdiff) hmain) hwvy
    have hrely : |(zmap Rn).eval (y i) - P.eval (y i)| < |P.eval (y i)| := by
      have hwp : 0 ≤ (weight muSerre (y i)) ^ d := pow_nonneg (le_of_lt (weight_pos muSerre (y i))) d
      exact lt_of_mul_lt_mul_left hy_lt hwp
    have hrely' : |P.eval (y i) - (zmap Rn).eval (y i)| < |P.eval (y i)| := by
      simpa [abs_sub_comm] using hrely
    exact ⟨hrel', hrely'⟩
  have hrootloc := roots_of_close (n := n) α x y P (zmap Rn) hPmon (zmap_monic hRn_mon) hPdeg
    (by rw [zmap_natDegree hRn_mon, hRn_deg]) hPfac hαmono hxαy hsep (fun i => hxyIcc i) hclose
  -- aeval over ℤ matches aeval over ℝ (zmap)
  have hrootsRn : ∀ z : ℂ, Polynomial.aeval z Rn = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ) := by
    intro z hz
    have hz' : Polynomial.aeval z (zmap Rn) = 0 := by
      rw [aeval_zmap]
      exact hz
    exact hrootloc.2 z hz'
  -- the top coefficient identity: P.coeff(n−1) = Rn.coeff(n−1) (only degrees
  -- < d ≤ n−1 are altered by the 4R0−2 perturbation, and m ≥ 1 forces d ≤ n−1)
  have hS0degd : S0.natDegree ≤ d - 1 := by
    dsimp [S0]
    have h1 : (Polynomial.C (4 : ℤ) * R0).natDegree ≤ d - 1 :=
      le_trans (Polynomial.natDegree_C_mul_le (4 : ℤ) R0) hR0deg
    have h2 : (Polynomial.C (2 : ℤ) : Polynomial ℤ).natDegree ≤ d - 1 := by simp
    exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le h1 h2)
  have hd1 : d ≤ n - 1 := by omega
  have hnm1 : n - 1 < n := by omega
  have hS0c : S0.coeff (n - 1) = 0 := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hTc : T.coeff (n - 1) = z (n - 1) := hTs.2.2.2.2 (n - 1) hd1 hnm1
  have hRn_c : Rn.coeff (n - 1) = T.coeff (n - 1) := by
    dsimp [Rn]
    rw [Polynomial.coeff_add, hS0c, add_zero]
  have hcoeff_id : P.coeff (n - 1) = (Rn.coeff (n - 1) : ℝ) := by
    rw [hRn_c, hTc]
    exact hzP (n - 1) hd1 hnm1
  have hrm : rootMeanReal Rn = (∑ i : Fin n, α i) / (n : ℝ) :=
    SqfVieta.rootMeanReal_eq_sum_div hRn_mon (hdegRn := hRn_deg)
      (hn := (by omega : 1 ≤ n)) (hcoeff := hcoeff_id) (hPfac := hPfac)
  have hmean : |rootMeanReal Rn - (∫ x : ℝ, x ∂muSerre)| ≤
      Cm * ((mFloor B n : ℝ) + 1) / (n : ℝ) := by
    rw [hrm]
    exact hαmean
  -- assemble
  exact ⟨Rn, hRn_mon, hRn_deg, hRn_irr, hrootsRn, by simpa [m] using hRn_norm, hmean⟩


/-! ## The keystone: four contracts imply the converse output -/

/-- The four deep contracts produce the converse output at Serre's data. -/
theorem converse_output_of_contracts (hsqf : SquarefreeContract) (hadj : AdjustContract)
    (hearly : EarlyIntsContract) : ConverseOutputSerre := by
  classical
  rcases hsqf with ⟨Cs, hCs, sqf⟩
  rcases hadj with ⟨Ca, hCa, adj⟩
  let C0 : ℝ := max Cs Ca
  have hC0 : 0 < C0 := by
    dsimp [C0]
    exact lt_of_lt_of_le hCs (le_max_left Cs Ca)
  have hCsC0 : Cs ≤ C0 := by dsimp [C0]; exact le_max_left Cs Ca
  have hCaC0 : Ca ≤ C0 := by dsimp [C0]; exact le_max_right Cs Ca
  let B : ℝ := (2 * C0) / Real.log kappa
  have hB : 0 < B := B_pos hC0
  rcases hearly B hB with ⟨C1, Cm, hC1gt3, hCm0, early⟩
  rcases weight_bdd_on_Icc with ⟨Mw, hMw0, hMw⟩
  let M : ℝ := max Mw 1
  have hM1 : 1 ≤ M := by dsimp [M]; exact le_max_right Mw 1
  have hM : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → weight muSerre x ≤ M := by
    intro x hx
    exact le_trans (hMw x hx) (by dsimp [M]; exact le_max_left Mw 1)
  rcases Asymptotics.exists_good_n (C0 := C0) (C1 := C1) hC0 hC1gt3 with ⟨N0, hN01, hN0⟩
  have hgood : ∀ n : ℕ, N0 ≤ n → ∃ Rn : Polynomial ℤ,
      Rn.Monic ∧ Rn.natDegree = n ∧ Irreducible Rn ∧
      (∀ z : ℂ, Polynomial.aeval z Rn = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) ∧
      wnorm n (zmap Rn) ≤ M ^ mFloor B n * ((n : ℝ) ^ C1 * kappa ^ mFloor B n +
        4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ))) ∧
      |rootMeanReal Rn - (∫ x : ℝ, x ∂muSerre)| ≤
        Cm * ((mFloor B n : ℝ) + 1) / (n : ℝ) := by
    intro n hn
    exact per_n_exists (Cs := Cs) (Ca := Ca) (C0 := C0) (C1 := C1) (Cm := Cm) (B := B) (M := M)
      hCs hCa hC0 hCsC0 hCaC0 sqf adj early hM1 hM (n := n) (by simpa [B] using hN0 n hn)
  let R : ℕ → Polynomial ℤ := fun n => if h : N0 ≤ n then Classical.choose (hgood n h)
      else Polynomial.X - Polynomial.C (1 : ℤ)
  -- per-index facts
  have hspec : ∀ n : ℕ, (R n).Monic ∧ Irreducible (R n) ∧ 1 ≤ (R n).natDegree ∧
      (∀ z : ℂ, Polynomial.aeval z (R n) = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) ∧
      (N0 ≤ n → (R n).natDegree = n) := by
    intro n
    by_cases hn : N0 ≤ n
    · have hs := Classical.choose_spec (hgood n hn)
      have hRn : R n = Classical.choose (hgood n hn) := by
        dsimp [R]
        rw [dif_pos hn]
      rw [hRn]
      constructor
      · exact hs.1
      · constructor
        · exact hs.2.2.1
        · constructor
          · rw [hs.2.1]
            omega
          · constructor
            · exact hs.2.2.2.1
            · intro h
              exact hs.2.1
    · have hRn : R n = Polynomial.X - Polynomial.C (1 : ℤ) := by
        dsimp [R]
        rw [dif_neg hn]
      rw [hRn]
      have hmon1 : (Polynomial.X - Polynomial.C (1 : ℤ) : Polynomial ℤ).Monic := by
        simpa using Polynomial.monic_X_sub_C (1 : ℤ)
      have hirr1 : Irreducible (Polynomial.X - Polynomial.C (1 : ℤ) : Polynomial ℤ) := by
        simpa using Polynomial.irreducible_X_sub_C (1 : ℤ)
      have hnd1 : 1 ≤ (Polynomial.X - Polynomial.C (1 : ℤ) : Polynomial ℤ).natDegree := by
        rw [show (Polynomial.X - Polynomial.C (1 : ℤ) : Polynomial ℤ).natDegree = 1 by
          simpa using Polynomial.natDegree_X_sub_C (1 : ℤ)]
      have hroot1 : ∀ z : ℂ, Polynomial.aeval z (Polynomial.X - Polynomial.C (1 : ℤ)) = 0 →
          (aSerre : ℂ) < z ∧ z < (bSerre : ℂ) := by
        intro z hz
        have hz1 : z = 1 := by
          have hz1' : z - 1 = 0 := by
            simpa using hz
          exact sub_eq_zero.mp hz1'
        subst z
        constructor
        · exact Complex.real_lt_real.mpr (by norm_num [aSerre])
        · exact Complex.real_lt_real.mpr (by norm_num [aSerre, bSerre])
      constructor
      · exact hmon1
      · constructor
        · exact hirr1
        · constructor
          · exact hnd1
          · constructor
            · exact hroot1
            · intro h
              exfalso
              exact hn h
  -- Clause 1: monic, irreducible, positive degree
  have h1 : ∀ n : ℕ, (R n).Monic ∧ Irreducible (R n) ∧ 1 ≤ (R n).natDegree := by
    intro n
    exact ⟨(hspec n).1, (hspec n).2.1, (hspec n).2.2.1⟩
  -- Clause 2: roots in the open Serre interval
  have h2 : ∀ n : ℕ, ∀ z : ℂ, Polynomial.aeval z (R n) = 0 →
      (aSerre : ℂ) < z ∧ z < (bSerre : ℂ) := by
    intro n
    exact (hspec n).2.2.2.1
  -- Clause 3: degrees tend to infinity
  have h3 : Tendsto (fun n : ℕ => (R n).natDegree) atTop atTop := by
    rw [tendsto_atTop]
    intro K
    refine eventually_atTop.2 ⟨max N0 K, ?_⟩
    intro n hn
    have hnN : N0 ≤ n := le_trans (le_max_left N0 K) hn
    rw [(hspec n).2.2.2.2 hnN]
    exact le_trans (le_max_right N0 K) hn
  -- Clause 4: root means → first moment (the per-n mean clause replaces RSphere)
  have hmeanN : ∀ n : ℕ, N0 ≤ n → |rootMeanReal (R n) - (∫ x : ℝ, x ∂muSerre)| ≤
      Cm * ((mFloor B n : ℝ) + 1) / (n : ℝ) := by
    intro n hn
    have hs := Classical.choose_spec (hgood n hn)
    have hRn : R n = Classical.choose (hgood n hn) := by
      dsimp [R]
      rw [dif_pos hn]
    rw [hRn]
    exact hs.2.2.2.2.2
  have hcloseN : ∀ᶠ n : ℕ in atTop, |rootMeanReal (R n) - (∫ x : ℝ, x ∂muSerre)| ≤
      Cm * ((mFloor B n : ℝ) + 1) / (n : ℝ) := by
    exact eventually_atTop.2 ⟨N0, hmeanN⟩
  have hmean : Tendsto (fun n : ℕ => rootMeanReal (R n)) atTop (𝓝 (∫ x : ℝ, x ∂muSerre)) := by
    exact MeanAsymptotics.tendsto_of_abs_sub_le (a := fun n : ℕ => rootMeanReal (R n))
      (L := (∫ x : ℝ, x ∂muSerre))
      (b := fun n : ℕ => Cm * ((mFloor B n : ℝ) + 1) / (n : ℝ))
      (MeanAsymptotics.tendsto_mFloor_mean_zero B Cm hB hCm0) hcloseN
  exact ⟨R, h1, h2, h3, hmean⟩

end Submission.KeystonePerN
