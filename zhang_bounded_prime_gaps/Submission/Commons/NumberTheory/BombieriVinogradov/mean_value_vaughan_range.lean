import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.maximal_bilinear_char_large_sieve_sSup
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_mean_value_param
import Submission.Commons.NumberTheory.ArithmeticFunction.vonMangoldt_eq_lambda_decomp_pos
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap_gt
import Submission.Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov
import Submission.Commons.NumberTheory.DirichletCharacter.charSum_logWeighted_range_le_polyaVinogradov
import Submission.Commons.NumberTheory.Moebius.sum_moebius_small_divisors_sq_le
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_sq_le
import Submission.Commons.Data.Finset.sum_Icc_eq_sum_log2_blocks
import Submission.Commons.NumberTheory.DivisorSum.sum_Icc_mul_fiber_regroup
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_type1_lambda2_estimate
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_type1_lambda3_estimate
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_type2_lambda4_estimate_sqrt

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators
open Finset

noncomputable section

/-- The primitive characters modulo `q`, as a finset. -/
abbrev primChars (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  @Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive) (Classical.decPred _) Finset.univ

/-- The left hand side of Vaughan's mean value theorem. -/
abbrev meanValueLHS (x Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ ∈ primChars q,
      sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x)

/-! ## The absolute constants extracted from the shared commons -/

/-- Pólya–Vinogradov constant. -/
noncomputable def cPV : ℝ :=
  Classical.choose Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov

lemma cPV_pos : 0 < cPV :=
  (Classical.choose_spec Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov).1

lemma cPV_spec (q : ℕ) (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (a b : ℕ)
    (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b, χ (n : ZMod q)‖
      ≤ cPV * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) :=
  (Classical.choose_spec Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov).2
    q hq χ hχ a b hab

/-- Pólya–Vinogradov constant for logarithmically weighted sums. -/
noncomputable def cPVlog : ℝ :=
  Classical.choose Commons.NumberTheory.DirichletCharacter.charSum_logWeighted_range_le_polyaVinogradov

lemma cPVlog_pos : 0 < cPVlog :=
  (Classical.choose_spec
    Commons.NumberTheory.DirichletCharacter.charSum_logWeighted_range_le_polyaVinogradov).1

lemma cPVlog_spec (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (a b : ℕ)
    (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b, ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q)‖
      ≤ cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (b : ℝ) + 2) :=
  (Classical.choose_spec
    Commons.NumberTheory.DirichletCharacter.charSum_logWeighted_range_le_polyaVinogradov).2
    q χ hχ a b hab

/-- Bilinear large sieve constant (maximal version). -/
noncomputable def cBil : ℝ :=
  Classical.choose Commons.NumberTheory.BombieriVinogradov.maximal_bilinear_char_large_sieve_sSup

lemma cBil_pos : 0 < cBil :=
  (Classical.choose_spec
    Commons.NumberTheory.BombieriVinogradov.maximal_bilinear_char_large_sieve_sSup).1

lemma cBil_spec (Q M N : ℕ) (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hN : 1 ≤ N) (a b : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q,
          sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
              (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
                '' Set.Icc 1 (M * N)))
      ≤ cBil * Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)
          * Real.log (2 * (M : ℝ) * (N : ℝ) + 2) :=
  (Classical.choose_spec
    Commons.NumberTheory.BombieriVinogradov.maximal_bilinear_char_large_sieve_sSup).2 Q M N hQ hM hN a b

/-- Constant for the square mean of the von Mangoldt function. -/
noncomputable def cVM : ℝ :=
  Classical.choose Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_sq_le

lemma cVM_pos : 0 < cVM :=
  (Classical.choose_spec Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_sq_le).1

lemma cVM_spec (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.vonMangoldt n) ^ 2
      ≤ cVM * (x : ℝ) * Real.log (2 * (x : ℝ) + 2) :=
  (Classical.choose_spec Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_sq_le).2 x

/-- Constant for the square mean of the truncated Möbius divisor sum. -/
noncomputable def cMoeb : ℝ :=
  Classical.choose Commons.NumberTheory.Moebius.sum_moebius_small_divisors_sq_le

lemma cMoeb_pos : 0 < cMoeb :=
  (Classical.choose_spec Commons.NumberTheory.Moebius.sum_moebius_small_divisors_sq_le).1

lemma cMoeb_spec (x V : ℕ) (hV : 1 ≤ V) :
    ∑ k ∈ Finset.Icc 1 x,
        (∑ d ∈ k.divisors.filter (fun d => d ≤ V), (ArithmeticFunction.moebius d : ℝ)) ^ 2
      ≤ cMoeb * (x : ℝ) * (Real.log (Real.exp 3 * (V : ℝ))) ^ 2 :=
  (Classical.choose_spec Commons.NumberTheory.Moebius.sum_moebius_small_divisors_sq_le).2 x V hV

/-- Chebyshev constant. -/
noncomputable def cCh : ℝ := Real.log 4 + 4

lemma cCh_pos : 0 < cCh := by rw [cCh]; positivity



/-! ## The four Vaughan pieces -/

/-- First Vaughan piece: `Λ(n)·1_{n ≤ T}`. -/
def lam1 (T n : ℕ) : ℝ := if n ≤ T then ArithmeticFunction.vonMangoldt n else 0

/-- Second Vaughan piece (type I sum). -/
def lam2 (T n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ))

/-- Third Vaughan piece. -/
def lam3 (T n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e

/-- Fourth Vaughan piece. -/
def lam4 (T n : ℕ) : ℝ :=
  ∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
    ArithmeticFunction.vonMangoldt m *
      (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ))

lemma vonMangoldt_eq_lam1234 (n T : ℕ) (hT : 1 ≤ T) :
    ArithmeticFunction.vonMangoldt n = lam1 T n + lam2 T n - lam3 T n - lam4 T n :=
  Commons.NumberTheory.ArithmeticFunction.vonMangoldt_eq_lambda_decomp_pos n T hT

/-- The character sums of the four Vaughan pieces. -/
def S1 (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y, ((lam1 T n : ℝ) : ℂ) * χ (n : ZMod q)

def S2 (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y, ((lam2 T n : ℝ) : ℂ) * χ (n : ZMod q)

def S3 (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y, ((lam3 T n : ℝ) : ℂ) * χ (n : ZMod q)

def S4 (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y, ((lam4 T n : ℝ) : ℂ) * χ (n : ZMod q)

/-- The von Mangoldt character sum splits into the four Vaughan pieces. -/
lemma psi_eq_sum_S (T q : ℕ) (hT : 1 ≤ T) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    (∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q))
      = S1 T q χ y + S2 T q χ y - S3 T q χ y - S4 T q χ y := by
  rw [S1, S2, S3, S4, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [vonMangoldt_eq_lam1234 n T hT]
  push_cast
  ring

/-- `ψ(t) ≤ (log 4 + 4) t` transported to our setting. -/
lemma psi_bound (t : ℕ) :
    (∑ n ∈ Finset.Icc 1 t, ArithmeticFunction.vonMangoldt n) ≤ (Real.log 4 + 4) * (t : ℝ) := by
  have hsub : Finset.Icc 1 t ⊆ Finset.Icc 0 t := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    omega
  calc (∑ n ∈ Finset.Icc 1 t, ArithmeticFunction.vonMangoldt n)
      ≤ ∑ n ∈ Finset.Icc 0 t, ArithmeticFunction.vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Chebyshev.psi (t : ℝ) := by
        rw [Chebyshev.psi_eq_sum_Icc]
        simp
    _ ≤ (Real.log 4 + 4) * (t : ℝ) := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg t)

/-- Pointwise bound for the first Vaughan piece. -/
lemma S1_norm_le (T q : ℕ) (hT : 1 ≤ T) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    ‖S1 T q χ y‖ ≤ (Real.log 4 + 4) * (T : ℝ) := by
  rw [S1]
  calc ‖∑ n ∈ Finset.Icc 1 y, ((lam1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖
      ≤ ∑ n ∈ Finset.Icc 1 y, ‖((lam1 T n : ℝ) : ℂ) * χ (n : ZMod q)‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 y, lam1 T n * ‖χ (n : ZMod q)‖ := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        have hnn : 0 ≤ lam1 T n := by
          rw [lam1]; split_ifs
          · exact ArithmeticFunction.vonMangoldt_nonneg
          · norm_num
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    _ ≤ ∑ n ∈ Finset.Icc 1 y, lam1 T n := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        rw [lam1]
        split_ifs with h
        · exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
            (DirichletCharacter.norm_le_one χ (n : ZMod q))
        · simp
    _ = ∑ n ∈ (Finset.Icc 1 y).filter (fun n => n ≤ T), ArithmeticFunction.vonMangoldt n := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun n _ => rfl)
    _ ≤ ∑ n ∈ Finset.Icc 1 T, ArithmeticFunction.vonMangoldt n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          rw [Finset.mem_Icc]
          exact ⟨hn.1.1, hn.2⟩
        · intro n _ _
          exact ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ (Real.log 4 + 4) * (T : ℝ) := psi_bound T

/-! ## Elementary facts about primitive characters -/

lemma primChars_card_le_totient (q : ℕ) [NeZero q] :
    (((primChars q).card : ℕ) : ℝ) ≤ (q.totient : ℝ) := by
  classical
  have hle := Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ q))
      (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  have hc : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h2 : (primChars q).card ≤ q.totient := le_trans hle (le_of_eq hc)
  exact_mod_cast h2

lemma isPrimitive_ne_one_of_two_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hq : 2 ≤ q) : χ ≠ 1 := by
  intro h
  have h1 : χ.conductor = q := (DirichletCharacter.isPrimitive_def χ).mp hprim
  have h2 : q = 1 := by rw [← h1, h, DirichletCharacter.conductor_one]
  omega

lemma totient_cast_pos (q : ℕ) (hq : 1 ≤ q) : (0 : ℝ) < (q.totient : ℝ) := by
  have h : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  exact_mod_cast h

lemma log2nn (a : ℕ) : (0 : ℝ) ≤ Real.log (2 * (a : ℝ) + 2) :=
  Real.log_nonneg (by have h : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a; linarith)

lemma sqrtnn (a : ℕ) : (0 : ℝ) ≤ Real.sqrt (a : ℝ) := Real.sqrt_nonneg _

lemma mem_primChars {q : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ primChars q ↔ χ.IsPrimitive := by
  classical
  simp [primChars]

/-! ## Piece 2: the type-I sum -/

lemma S2_eq_pair (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    S2 T q χ y =
      ∑ d ∈ Finset.Icc 1 T, ∑ h ∈ Finset.Icc 1 (y / d),
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (h : ℝ) : ℝ) : ℂ)
          * χ ((d * h : ℕ) : ZMod q) := by
  rw [S2]
  have h1 : (∑ n ∈ Finset.Icc 1 y, ((lam2 T n : ℝ) : ℂ) * χ (n : ZMod q))
      = ∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)) : ℝ) : ℂ)
            * χ ((d * (n / d) : ℕ) : ZMod q) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hcoe : (((∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)) : ℝ)) : ℂ)
        = ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)) : ℝ) : ℂ) :=
      Complex.ofReal_sum _ _
    rw [lam2, hcoe, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdvd : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    rw [Nat.mul_div_cancel' hdvd]
  rw [h1]
  exact Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap y T
    (fun d h => ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (h : ℝ) : ℝ) : ℂ)
      * χ ((d * h : ℕ) : ZMod q))

lemma S2_pair_norm_le (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    ‖∑ d ∈ Finset.Icc 1 T, ∑ h ∈ Finset.Icc 1 (y / d),
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (h : ℝ) : ℝ) : ℂ)
          * χ ((d * h : ℕ) : ZMod q)‖
      ≤ ∑ d ∈ Finset.Icc 1 T,
          ‖∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * χ (h : ZMod q)‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum (fun d hd => ?_)
  have hfac : (∑ h ∈ Finset.Icc 1 (y / d),
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (h : ℝ) : ℝ) : ℂ)
          * χ ((d * h : ℕ) : ZMod q))
      = (((ArithmeticFunction.moebius d : ℤ) : ℝ) : ℂ) * χ (d : ZMod q)
        * (∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * χ (h : ZMod q)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Nat.cast_mul, map_mul]
    push_cast
    ring
  rw [hfac, norm_mul]
  have hmu : ‖(((ArithmeticFunction.moebius d : ℤ) : ℝ) : ℂ) * χ (d : ZMod q)‖ ≤ 1 := by
    rw [norm_mul]
    have h1 : ‖(((ArithmeticFunction.moebius d : ℤ) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast this
    have h2 : ‖χ (d : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    calc ‖(((ArithmeticFunction.moebius d : ℤ) : ℝ) : ℂ)‖ * ‖χ (d : ZMod q)‖
        ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  calc ‖(((ArithmeticFunction.moebius d : ℤ) : ℝ) : ℂ) * χ (d : ZMod q)‖
        * ‖∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * χ (h : ZMod q)‖
      ≤ 1 * ‖∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * χ (h : ZMod q)‖ :=
        mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
    _ = ‖∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * χ (h : ZMod q)‖ := one_mul _

lemma S2_inner_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (y d : ℕ) :
    ‖∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * χ (h : ZMod q)‖
      ≤ cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (y : ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos (y / d) with h | h
  · have hempty : Finset.Icc 1 (y / d) = ∅ := by
      rw [h]; ext n; simp [Finset.mem_Icc]
    rw [hempty, Finset.sum_empty, norm_zero]
    have h0 : (0 : ℝ) < cPVlog := cPVlog_pos
    have h1 : (0 : ℝ) ≤ Real.sqrt q := sqrtnn q
    have h2 : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := log2nn q
    have h3 : (0 : ℝ) ≤ Real.log (2 * (y : ℝ) + 2) := log2nn y
    positivity
  · have hlog : Real.log (2 * ((y / d : ℕ) : ℝ) + 2) ≤ Real.log (2 * (y : ℝ) + 2) := by
      apply Real.log_le_log (by positivity)
      have hle : ((y / d : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast Nat.div_le_self y d
      linarith
    have hcoef : (0 : ℝ) ≤ cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) := by
      have h0 : (0 : ℝ) < cPVlog := cPVlog_pos
      have h1 : (0 : ℝ) ≤ Real.sqrt q := sqrtnn q
      have h2 : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := log2nn q
      positivity
    calc ‖∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * χ (h : ZMod q)‖
        ≤ cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
            * Real.log (2 * ((y / d : ℕ) : ℝ) + 2) :=
          cPVlog_spec q χ hχ 1 (y / d) h
      _ ≤ cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (y : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlog hcoef

lemma S2_pointwise_le (T q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (y : ℕ) :
    ‖S2 T q χ y‖
      ≤ (T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
          * Real.log (2 * (y : ℝ) + 2) := by
  rw [S2_eq_pair]
  refine le_trans (S2_pair_norm_le T q χ y) ?_
  calc ∑ d ∈ Finset.Icc 1 T,
        ‖∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * χ (h : ZMod q)‖
      ≤ ∑ _d ∈ Finset.Icc 1 T,
          cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (y : ℝ) + 2) :=
        Finset.sum_le_sum (fun d _ => S2_inner_le q χ hχ y d)
    _ = (T : ℝ) * (cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
          * Real.log (2 * (y : ℝ) + 2)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num
    _ = (T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
          * Real.log (2 * (y : ℝ) + 2) := by
        ring

lemma S2_sum_le (T Q x : ℕ) (hQ : 2 ≤ Q) (hx : 1 ≤ x) :
    (∑ q ∈ Finset.Icc 2 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S2 T q χ y‖) '' Set.Icc 1 x))
      ≤ (T : ℝ) * cPVlog * (Q : ℝ) ^ (5 / 2 : ℝ)
          * Real.log (2 * (Q : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) := by
  have hcl : (0 : ℝ) < cPVlog := cPVlog_pos
  have hterm : ∀ q ∈ Finset.Icc 2 Q,
      ((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ primChars q,
          sSup ((fun y : ℕ => ‖S2 T q χ y‖) '' Set.Icc 1 x)
        ≤ (q : ℝ) * ((T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
            * Real.log (2 * (x : ℝ) + 2)) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    haveI : NeZero q := ⟨by omega⟩
    have hφpos : (0 : ℝ) < (q.totient : ℝ) := totient_cast_pos q (by omega)
    have hmain : ∀ χ ∈ primChars q,
        sSup ((fun y : ℕ => ‖S2 T q χ y‖) '' Set.Icc 1 x)
          ≤ (T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
              * Real.log (2 * (x : ℝ) + 2) := by
      intro χ hχ
      have hχne : χ ≠ 1 := isPrimitive_ne_one_of_two_le q χ (mem_primChars.mp hχ) hq.1
      have hb : (0 : ℝ) ≤ (T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
              * Real.log (2 * (x : ℝ) + 2) := by
        have h1 : (0 : ℝ) ≤ Real.sqrt q := sqrtnn q
        have h2 : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := log2nn q
        have h3 : (0 : ℝ) ≤ Real.log (2 * (x : ℝ) + 2) := log2nn x
        positivity
      refine Real.sSup_le ?_ hb
      rintro b ⟨y, hy, rfl⟩
      have hyx : y ≤ x := hy.2
      calc ‖S2 T q χ y‖
          ≤ (T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
              * Real.log (2 * (y : ℝ) + 2) := S2_pointwise_le T q χ hχne y
        _ ≤ (T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
              * Real.log (2 * (x : ℝ) + 2) := by
            have hlog : Real.log (2 * (y : ℝ) + 2) ≤ Real.log (2 * (x : ℝ) + 2) := by
              apply Real.log_le_log (by positivity)
              have : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hyx
              linarith
            have hcoef : (0 : ℝ) ≤ (T : ℝ) * cPVlog * Real.sqrt q
                * Real.log (2 * (q : ℝ) + 2) := by
              have h1 : (0 : ℝ) ≤ Real.sqrt q := sqrtnn q
              have h2 : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := log2nn q
              positivity
            exact mul_le_mul_of_nonneg_left hlog hcoef
    have hsum_le : (∑ χ ∈ primChars q,
          sSup ((fun y : ℕ => ‖S2 T q χ y‖) '' Set.Icc 1 x))
        ≤ (((primChars q).card : ℕ) : ℝ) * ((T : ℝ) * cPVlog * Real.sqrt q
            * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2)) := by
      calc (∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S2 T q χ y‖) '' Set.Icc 1 x))
          ≤ ∑ _χ ∈ primChars q, ((T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
              * Real.log (2 * (x : ℝ) + 2)) := Finset.sum_le_sum hmain
        _ = ((primChars q).card : ℝ) * ((T : ℝ) * cPVlog * Real.sqrt q
              * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard := primChars_card_le_totient q
    have hb : (0 : ℝ) ≤ (T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
              * Real.log (2 * (x : ℝ) + 2) := by
      have h1 : (0 : ℝ) ≤ Real.sqrt q := sqrtnn q
      have h2 : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := log2nn q
      have h3 : (0 : ℝ) ≤ Real.log (2 * (x : ℝ) + 2) := log2nn x
      positivity
    calc ((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ primChars q,
          sSup ((fun y : ℕ => ‖S2 T q χ y‖) '' Set.Icc 1 x)
        ≤ ((q : ℝ) / (q.totient : ℝ)) *
            ((((primChars q).card : ℕ) : ℝ) * ((T : ℝ) * cPVlog * Real.sqrt q
              * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ ≤ ((q : ℝ) / (q.totient : ℝ)) *
            ((q.totient : ℝ) * ((T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
              * Real.log (2 * (x : ℝ) + 2))) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hcard hb
          · positivity
      _ = (q : ℝ) * ((T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
              * Real.log (2 * (x : ℝ) + 2)) := by
          rw [← mul_assoc, div_mul_cancel₀ (q : ℝ) (ne_of_gt hφpos)]
  have hsum := Finset.sum_le_sum hterm
  have hqbound : (∑ q ∈ Finset.Icc 2 Q, (q : ℝ) * ((T : ℝ) * cPVlog * Real.sqrt q
        * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2)))
      ≤ (T : ℝ) * cPVlog * (Q : ℝ) ^ (5 / 2 : ℝ) * Real.log (2 * (Q : ℝ) + 2)
        * Real.log (2 * (x : ℝ) + 2) := by
    have hlogx : (0 : ℝ) ≤ Real.log (2 * (x : ℝ) + 2) := log2nn x
    have hpt : ∀ q ∈ Finset.Icc 2 Q,
        (q : ℝ) * ((T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
          * Real.log (2 * (x : ℝ) + 2))
        ≤ ((T : ℝ) * cPVlog * Real.log (2 * (x : ℝ) + 2))
          * ((Q : ℝ) * Real.sqrt Q * Real.log (2 * (Q : ℝ) + 2)) := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      have hqQ : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq.2
      have hsq : Real.sqrt (q : ℝ) ≤ Real.sqrt (Q : ℝ) := Real.sqrt_le_sqrt hqQ
      have hlogle : Real.log (2 * (q : ℝ) + 2) ≤ Real.log (2 * (Q : ℝ) + 2) := by
        apply Real.log_le_log (by positivity); linarith [hqQ]
      have h1 : (q : ℝ) * Real.sqrt q ≤ (Q : ℝ) * Real.sqrt Q := by
        have ha := mul_le_mul_of_nonneg_right hqQ (Real.sqrt_nonneg (q : ℝ))
        have hb := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg Q)
        linarith
      have h3 : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := log2nn q
      have h4 : (0 : ℝ) ≤ (Q : ℝ) * Real.sqrt Q := by
        have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
        positivity
      calc (q : ℝ) * ((T : ℝ) * cPVlog * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
            * Real.log (2 * (x : ℝ) + 2))
          = ((T : ℝ) * cPVlog * Real.log (2 * (x : ℝ) + 2))
            * (((q : ℝ) * Real.sqrt q) * Real.log (2 * (q : ℝ) + 2)) := by ring
        _ ≤ ((T : ℝ) * cPVlog * Real.log (2 * (x : ℝ) + 2))
            * (((Q : ℝ) * Real.sqrt Q) * Real.log (2 * (Q : ℝ) + 2)) := by
            apply mul_le_mul_of_nonneg_left (mul_le_mul h1 hlogle h3 h4)
            exact mul_nonneg (mul_nonneg (Nat.cast_nonneg T) (le_of_lt cPVlog_pos)) (log2nn x)
        _ = ((T : ℝ) * cPVlog * Real.log (2 * (x : ℝ) + 2))
          * ((Q : ℝ) * Real.sqrt Q * Real.log (2 * (Q : ℝ) + 2)) := by ring
    calc (∑ q ∈ Finset.Icc 2 Q, (q : ℝ) * ((T : ℝ) * cPVlog * Real.sqrt q
          * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2)))
        ≤ ∑ _q ∈ Finset.Icc 2 Q, ((T : ℝ) * cPVlog * Real.log (2 * (x : ℝ) + 2))
          * ((Q : ℝ) * Real.sqrt Q * Real.log (2 * (Q : ℝ) + 2)) := Finset.sum_le_sum hpt
      _ = ((Finset.Icc 2 Q).card : ℝ) * (((T : ℝ) * cPVlog * Real.log (2 * (x : ℝ) + 2))
          * ((Q : ℝ) * Real.sqrt Q * Real.log (2 * (Q : ℝ) + 2))) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Q : ℝ) * (((T : ℝ) * cPVlog * Real.log (2 * (x : ℝ) + 2))
          * ((Q : ℝ) * Real.sqrt Q * Real.log (2 * (Q : ℝ) + 2))) := by
          apply mul_le_mul_of_nonneg_right _
            (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg T) (le_of_lt cPVlog_pos))
              (log2nn x)) (mul_nonneg (mul_nonneg (Nat.cast_nonneg Q) (sqrtnn Q)) (log2nn Q)))
          rw [Nat.card_Icc]
          have : (Q + 1 - 2 : ℕ) ≤ Q := by omega
          exact_mod_cast this
      _ = (T : ℝ) * cPVlog * (Q : ℝ) ^ (5 / 2 : ℝ) * Real.log (2 * (Q : ℝ) + 2)
            * Real.log (2 * (x : ℝ) + 2) := by
          have hQ2 : (Q : ℝ) * Real.sqrt Q * (Q : ℝ) = (Q : ℝ) ^ (5 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
            rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add (by positivity)]
            rw [Real.rpow_two]
            ring
          rw [show (Q : ℝ) * (((T : ℝ) * cPVlog * Real.log (2 * (x : ℝ) + 2))
                * ((Q : ℝ) * Real.sqrt Q * Real.log (2 * (Q : ℝ) + 2)))
              = (T : ℝ) * cPVlog * Real.log (2 * (x : ℝ) + 2)
                * ((Q : ℝ) * Real.sqrt Q * (Q : ℝ)) * Real.log (2 * (Q : ℝ) + 2) by ring]
          rw [hQ2]
          ring
  exact le_trans hsum hqbound

/-! ## Piece 3: the double truncated divisor sum -/

/-- The fiber sums of the third Vaughan piece. -/
def aT (T : ℕ) (t : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
    if d * e = t then
      ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
    else 0

/-- The third Vaughan piece written as a triple sum over `(d,e,r)` with `d*e*r ≤ y`. -/
lemma S3_eq_pair (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    S3 T q χ y
      = ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T, ∑ r ∈ Finset.Icc 1 (y / (d * e)),
          ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
            * χ ((d * e * r : ℕ) : ZMod q) := by
  rw [S3]
  have hstep1 : (∑ n ∈ Finset.Icc 1 y, ((lam3 T n : ℝ) : ℂ) * χ (n : ZMod q))
      = ∑ d ∈ Finset.Icc 1 T, ∑ h ∈ Finset.Icc 1 (y / d),
          ∑ e ∈ h.divisors.filter (fun e => e ≤ T),
            ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
              * χ ((d * h : ℕ) : ZMod q) := by
    have h1 : (∑ n ∈ Finset.Icc 1 y, ((lam3 T n : ℝ) : ℂ) * χ (n : ZMod q))
        = ∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
            ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T),
              ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
                * χ ((d * (n / d) : ℕ) : ZMod q) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hcoe : ((lam3 T n : ℝ) : ℂ)
          = ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
              ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T),
                ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ) := by
        rw [lam3, Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        exact Complex.ofReal_sum _ _
      rw [hcoe, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun d hd => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun e he => ?_)
      have hdvd : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      rw [Nat.mul_div_cancel' hdvd]
    rw [h1]
    exact Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap y T
      (fun d h => ∑ e ∈ h.divisors.filter (fun e => e ≤ T),
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
          * χ ((d * h : ℕ) : ZMod q))
  rw [hstep1]
  have hstep2 : ∀ d ∈ Finset.Icc 1 T,
      (∑ h ∈ Finset.Icc 1 (y / d), ∑ e ∈ h.divisors.filter (fun e => e ≤ T),
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
          * χ ((d * h : ℕ) : ZMod q))
      = ∑ e ∈ Finset.Icc 1 T, ∑ r ∈ Finset.Icc 1 (y / (d * e)),
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
          * χ ((d * e * r : ℕ) : ZMod q) := by
    intro d hd
    have h1 : (∑ h ∈ Finset.Icc 1 (y / d), ∑ e ∈ h.divisors.filter (fun e => e ≤ T),
          ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
            * χ ((d * h : ℕ) : ZMod q))
        = ∑ h ∈ Finset.Icc 1 (y / d), ∑ e ∈ h.divisors.filter (fun e => e ≤ T),
            ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
              * χ ((d * (e * (h / e)) : ℕ) : ZMod q) := by
      refine Finset.sum_congr rfl (fun h _ => ?_)
      refine Finset.sum_congr rfl (fun e he => ?_)
      have hedvd : e ∣ h := (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
      rw [Nat.mul_div_cancel' hedvd]
    rw [h1]
    rw [Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap (y / d) T
      (fun e r => ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
          * χ ((d * (e * r) : ℕ) : ZMod q))]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [Nat.div_div_eq_div_mul]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [show (d * (e * r) : ℕ) = d * e * r by ring]
  exact Finset.sum_congr rfl hstep2

/-- The third Vaughan piece regrouped by the value of the product `d * e`. -/
lemma S3_regroup (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    S3 T q χ y = ∑ t ∈ Finset.Icc 1 (T * T),
      aT T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)) := by
  rw [S3_eq_pair]
  have h1 : (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T, ∑ r ∈ Finset.Icc 1 (y / (d * e)),
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
          * χ ((d * e * r : ℕ) : ZMod q))
      = ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
          ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
            * χ ((d * e : ℕ) : ZMod q)
            * (∑ r ∈ Finset.Icc 1 (y / (d * e)), χ (r : ZMod q)) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [show (∑ r ∈ Finset.Icc 1 (y / (d * e)),
          ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
            * χ ((d * e * r : ℕ) : ZMod q))
        = ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
            * χ ((d * e : ℕ) : ZMod q)
            * (∑ r ∈ Finset.Icc 1 (y / (d * e)), χ (r : ZMod q)) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Nat.cast_mul, map_mul]
      ring]
  rw [h1]
  rw [show (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
          * χ ((d * e : ℕ) : ZMod q)
          * (∑ r ∈ Finset.Icc 1 (y / (d * e)), χ (r : ZMod q)))
      = ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
          * (χ ((d * e : ℕ) : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / (d * e)), χ (r : ZMod q)))
      from by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring]
  rw [Commons.NumberTheory.DivisorSum.sum_Icc_mul_fiber_regroup T
    (fun d e => ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ))
    (fun t => χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)))]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [aT]
  ring

/-- The first part of the third Vaughan piece: `d * e ≤ T`. -/
def S3' (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ t ∈ Finset.Icc 1 T,
    aT T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))

/-- The second part of the third Vaughan piece: `T < d * e ≤ T * T`. -/
def S3'' (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ t ∈ Finset.Icc (T + 1) (T * T),
    aT T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))

lemma sum_Icc_split (f : ℕ → ℂ) (T N : ℕ) (hT : 1 ≤ T) (hTN : T ≤ N) :
    (∑ t ∈ Finset.Icc 1 N, f t)
      = (∑ t ∈ Finset.Icc 1 T, f t) + ∑ t ∈ Finset.Icc (T + 1) N, f t := by
  have hunion : Finset.Icc 1 N = Finset.Icc 1 T ∪ Finset.Icc (T + 1) N := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 T) (Finset.Icc (T + 1) N) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    rw [Finset.mem_Icc] at ht ht'
    omega
  rw [hunion, Finset.sum_union hdisj]

lemma S3_eq_S3'_add_S3'' (T q : ℕ) (hT : 1 ≤ T) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    S3 T q χ y = S3' T q χ y + S3'' T q χ y := by
  rw [S3_regroup, S3', S3'']
  exact sum_Icc_split _ T (T * T) hT (by nlinarith)

/-- Bound for the fiber sums. -/
lemma norm_ite_mul_le (d e t : ℕ) :
    ‖(if d * e = t then
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
      else 0)‖ ≤ if d * e = t then ArithmeticFunction.vonMangoldt e else 0 := by
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hμ : |(((ArithmeticFunction.moebius d : ℤ) : ℝ))| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast this
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt e := ArithmeticFunction.vonMangoldt_nonneg
    rw [abs_of_nonneg hΛ]
    calc |(((ArithmeticFunction.moebius d : ℤ) : ℝ))| * ArithmeticFunction.vonMangoldt e
        ≤ 1 * ArithmeticFunction.vonMangoldt e := mul_le_mul_of_nonneg_right hμ hΛ
      _ = ArithmeticFunction.vonMangoldt e := one_mul _
  · simp

lemma sum_pair_ite_le_divisors (T t : ℕ) (ht : 1 ≤ t) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T, if d * e = t then f e else 0)
      ≤ ∑ e ∈ t.divisors, f e := by
  rw [Finset.sum_comm]
  calc (∑ e ∈ Finset.Icc 1 T, ∑ d ∈ Finset.Icc 1 T, if d * e = t then f e else 0)
      ≤ ∑ e ∈ Finset.Icc 1 T, (if e ∣ t then f e else 0) := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        by_cases he : e ∣ t
        · rw [if_pos he, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hcard : ((Finset.Icc 1 T).filter (fun d => d * e = t)).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro a ha b hb
            rw [Finset.mem_filter] at ha hb
            have hpos : 0 < e := Nat.pos_of_dvd_of_pos he (by omega)
            exact Nat.mul_right_cancel hpos (by rw [ha.2, hb.2])
          calc ((((Finset.Icc 1 T).filter (fun d => d * e = t)).card : ℕ) : ℝ) * f e
              ≤ 1 * f e := by
                apply mul_le_mul_of_nonneg_right _ (hf e)
                exact_mod_cast hcard
            _ = f e := one_mul _
        · rw [if_neg he]
          have hz : (∑ d ∈ Finset.Icc 1 T, (if d * e = t then f e else 0)) = 0 := by
            refine Finset.sum_eq_zero (fun d _ => ?_)
            rw [if_neg]
            intro h
            exact he ⟨d, by rw [← h, mul_comm]⟩
          rw [hz]
    _ ≤ ∑ e ∈ t.divisors, f e := by
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          rw [Finset.mem_filter] at he
          exact Nat.mem_divisors.mpr ⟨he.2, by omega⟩
        · intro e _ _
          exact hf e

lemma norm_aT_le (T t : ℕ) (ht : 1 ≤ t) : ‖aT T t‖ ≤ Real.log (2 * (t : ℝ) + 2) := by
  have h1 : ‖aT T t‖ ≤ ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
      if d * e = t then ArithmeticFunction.vonMangoldt e else 0 := by
    rw [aT]
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ d ∈ Finset.Icc 1 T,
          ‖∑ e ∈ Finset.Icc 1 T, (if d * e = t then
            ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
            else 0)‖
        ≤ ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
            ‖(if d * e = t then
              ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e : ℝ) : ℂ)
              else 0)‖ :=
          Finset.sum_le_sum (fun d _ => norm_sum_le _ _)
      _ ≤ ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
            (if d * e = t then ArithmeticFunction.vonMangoldt e else 0) :=
          Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun e _ => norm_ite_mul_le d e t))
  calc ‖aT T t‖ ≤ ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
        (if d * e = t then ArithmeticFunction.vonMangoldt e else 0) := h1
    _ ≤ ∑ e ∈ t.divisors, ArithmeticFunction.vonMangoldt e :=
        sum_pair_ite_le_divisors T t ht _ (fun n => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log t := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log (2 * (t : ℝ) + 2) := by
        apply Real.log_le_log
        · exact_mod_cast ht
        · have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
          linarith

lemma sum_norm_aT_le (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, ‖aT T t‖) ≤ (T : ℝ) * Real.log (2 * (T : ℝ) + 2) := by
  calc (∑ t ∈ Finset.Icc 1 T, ‖aT T t‖)
      ≤ ∑ _t ∈ Finset.Icc 1 T, Real.log (2 * (T : ℝ) + 2) := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        rw [Finset.mem_Icc] at ht
        calc ‖aT T t‖ ≤ Real.log (2 * (t : ℝ) + 2) := norm_aT_le T t ht.1
          _ ≤ Real.log (2 * (T : ℝ) + 2) := by
              apply Real.log_le_log (by positivity)
              have : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht.2
              linarith
    _ = (T : ℝ) * Real.log (2 * (T : ℝ) + 2) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num


/-! ## The maximal bilinear large sieve with a restricted range of `y` -/

lemma cBil_spec_lower (Q M N x : ℕ) (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hx1 : 1 ≤ x) (hx : x ≤ M * N) (a b : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q,
          sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
              (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
                '' Set.Icc 1 x))
      ≤ cBil * Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)
          * Real.log (2 * (M : ℝ) * (N : ℝ) + 2) := by
  refine le_trans ?_ (cBil_spec Q M N hQ hM hN a b)
  refine Finset.sum_le_sum (fun q hq => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum (fun χ hχ => ?_)
  refine csSup_le_csSup ?_ ⟨_, ⟨1, ⟨le_rfl, hx1⟩, rfl⟩⟩ ?_
  · exact ((Set.finite_Icc 1 (M * N)).image _).bddAbove
  · intro b hb
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨y, ⟨hy.1, le_trans hy.2 hx⟩, rfl⟩

/-! ## A helper for sums over `q` -/

lemma sum_Icc_two_q_sqrt_q_log_le (Q : ℕ) (hQ : 2 ≤ Q) (K : ℝ) (hK : 0 ≤ K) :
    (∑ q ∈ Finset.Icc 2 Q, (q : ℝ) * (K * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)))
      ≤ K * (Q : ℝ) ^ (5 / 2 : ℝ) * Real.log (2 * (Q : ℝ) + 2) := by
  have hpt : ∀ q ∈ Finset.Icc 2 Q,
      (q : ℝ) * (K * Real.sqrt q * Real.log (2 * (q : ℝ) + 2))
        ≤ (K * Real.log (2 * (Q : ℝ) + 2)) * ((Q : ℝ) * Real.sqrt Q) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hqQ : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq.2
    have hsq : Real.sqrt (q : ℝ) ≤ Real.sqrt (Q : ℝ) := Real.sqrt_le_sqrt hqQ
    have hlogle : Real.log (2 * (q : ℝ) + 2) ≤ Real.log (2 * (Q : ℝ) + 2) := by
      apply Real.log_le_log (by positivity); linarith [hqQ]
    have h1 : (q : ℝ) * Real.sqrt q ≤ (Q : ℝ) * Real.sqrt Q := by
      have ha := mul_le_mul_of_nonneg_right hqQ (Real.sqrt_nonneg (q : ℝ))
      have hb := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg Q)
      linarith
    have h3 : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := log2nn q
    have h4 : (0 : ℝ) ≤ (q : ℝ) * Real.sqrt q := by
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      positivity
    calc (q : ℝ) * (K * Real.sqrt q * Real.log (2 * (q : ℝ) + 2))
        = (K * Real.log (2 * (q : ℝ) + 2)) * ((q : ℝ) * Real.sqrt q) := by ring
      _ ≤ (K * Real.log (2 * (Q : ℝ) + 2)) * ((Q : ℝ) * Real.sqrt Q) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hlogle hK
          · exact h1
          · exact h4
          · exact mul_nonneg hK (log2nn Q)
      _ = (K * Real.log (2 * (Q : ℝ) + 2)) * ((Q : ℝ) * Real.sqrt Q) := rfl
  calc (∑ q ∈ Finset.Icc 2 Q, (q : ℝ) * (K * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)))
      ≤ ∑ _q ∈ Finset.Icc 2 Q, (K * Real.log (2 * (Q : ℝ) + 2)) * ((Q : ℝ) * Real.sqrt Q) :=
        Finset.sum_le_sum hpt
    _ = ((Finset.Icc 2 Q).card : ℝ) * ((K * Real.log (2 * (Q : ℝ) + 2)) * ((Q : ℝ) * Real.sqrt Q)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * ((K * Real.log (2 * (Q : ℝ) + 2)) * ((Q : ℝ) * Real.sqrt Q)) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (mul_nonneg hK (log2nn Q)) (by
            have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
            positivity))
        rw [Nat.card_Icc]
        have : (Q + 1 - 2 : ℕ) ≤ Q := by omega
        exact_mod_cast this
    _ = K * (Q : ℝ) ^ (5 / 2 : ℝ) * Real.log (2 * (Q : ℝ) + 2) := by
        have hQ2 : (Q : ℝ) * Real.sqrt Q * (Q : ℝ) = (Q : ℝ) ^ (5 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
          rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add (by positivity)]
          rw [Real.rpow_two]
          ring
        rw [show (Q : ℝ) * ((K * Real.log (2 * (Q : ℝ) + 2)) * ((Q : ℝ) * Real.sqrt Q))
            = K * Real.log (2 * (Q : ℝ) + 2) * ((Q : ℝ) * Real.sqrt Q * (Q : ℝ)) by ring,
          hQ2]
        ring

/-! ## Piece 3, first part: the pointwise bound -/

lemma S3'_pointwise_le (T q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hq : 2 ≤ q) (y : ℕ) :
    ‖S3' T q χ y‖
      ≤ (T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) := by
  have hcv : (0 : ℝ) < cPV := cPV_pos
  calc ‖S3' T q χ y‖
      ≤ ∑ t ∈ Finset.Icc 1 T,
          ‖aT T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖ := by
        rw [S3']
        exact norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.Icc 1 T, (Real.log (2 * (T : ℝ) + 2) *
          (cPV * Real.sqrt q * Real.log (2 * (q : ℝ) + 2))) := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        rw [Finset.mem_Icc] at ht
        have h1 : ‖aT T t‖ ≤ Real.log (2 * (T : ℝ) + 2) :=
          le_trans (norm_aT_le T t ht.1) (by
            apply Real.log_le_log (by positivity)
            have : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht.2
            linarith)
        have h2 : ‖χ (t : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have h3 : ‖∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)‖
            ≤ cPV * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) := by
          rcases Nat.eq_zero_or_pos (y / t) with h | h
          · have hempty : Finset.Icc 1 (y / t) = ∅ := by
              rw [h]; ext n; simp [Finset.mem_Icc]
            rw [hempty, Finset.sum_empty, norm_zero]
            have : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := log2nn q
            have : (0 : ℝ) ≤ Real.sqrt q := sqrtnn q
            have hc : (0 : ℝ) < cPV := cPV_pos
            positivity
          · exact cPV_spec q hq χ hχ 1 (y / t) h
        calc ‖aT T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖
            = ‖aT T t‖ * ‖χ (t : ZMod q)‖
              * ‖∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)‖ := by
              rw [norm_mul, norm_mul]
          _ ≤ Real.log (2 * (T : ℝ) + 2) * 1
              * (cPV * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by
              apply mul_le_mul
              · exact mul_le_mul h1 h2 (norm_nonneg _) (by
                  have hc : (0 : ℝ) < cPV := cPV_pos
                  have : (0 : ℝ) ≤ Real.log (2 * (T : ℝ) + 2) := log2nn T
                  have : (0 : ℝ) ≤ Real.sqrt q := sqrtnn q
                  have : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := log2nn q
                  positivity)
              · exact h3
              · exact norm_nonneg _
              · have hc : (0 : ℝ) < cPV := cPV_pos
                have : (0 : ℝ) ≤ Real.log (2 * (T : ℝ) + 2) := log2nn T
                positivity
          _ = Real.log (2 * (T : ℝ) + 2) * (cPV * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by
              ring
    _ = (T : ℝ) * (Real.log (2 * (T : ℝ) + 2) *
          (cPV * Real.sqrt q * Real.log (2 * (q : ℝ) + 2))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num
    _ = (T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV * Real.sqrt q
          * Real.log (2 * (q : ℝ) + 2) := by ring

lemma S3'_sum_le (T Q x : ℕ) (hT : 1 ≤ T) (hQ : 2 ≤ Q) (hx : 1 ≤ x) :
    (∑ q ∈ Finset.Icc 2 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S3' T q χ y‖) '' Set.Icc 1 x))
      ≤ (T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV * (Q : ℝ) ^ (5 / 2 : ℝ)
          * Real.log (2 * (Q : ℝ) + 2) := by
  have hterm : ∀ q ∈ Finset.Icc 2 Q,
      ((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ primChars q,
          sSup ((fun y : ℕ => ‖S3' T q χ y‖) '' Set.Icc 1 x)
        ≤ (q : ℝ) * ((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV * Real.sqrt q
            * Real.log (2 * (q : ℝ) + 2)) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    haveI : NeZero q := ⟨by omega⟩
    have hφpos : (0 : ℝ) < (q.totient : ℝ) := totient_cast_pos q (by omega)
    have hb : (0 : ℝ) ≤ (T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV * Real.sqrt q
            * Real.log (2 * (q : ℝ) + 2) := by
      have h1 : (0 : ℝ) ≤ Real.sqrt q := sqrtnn q
      have h2 : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := log2nn q
      have h3 : (0 : ℝ) ≤ Real.log (2 * (T : ℝ) + 2) := log2nn T
      have h4 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
      have hcv : (0 : ℝ) < cPV := cPV_pos
      positivity
    have hmain : ∀ χ ∈ primChars q,
        sSup ((fun y : ℕ => ‖S3' T q χ y‖) '' Set.Icc 1 x)
          ≤ (T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV * Real.sqrt q
            * Real.log (2 * (q : ℝ) + 2) := by
      intro χ hχ
      have hχne : χ ≠ 1 := isPrimitive_ne_one_of_two_le q χ (mem_primChars.mp hχ) hq.1
      refine Real.sSup_le ?_ hb
      rintro b ⟨y, hy, rfl⟩
      exact S3'_pointwise_le T q χ hχne hq.1 y
    have hsum_le : (∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S3' T q χ y‖) '' Set.Icc 1 x))
        ≤ (((primChars q).card : ℕ) : ℝ) * ((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV
            * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by
      calc (∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S3' T q χ y‖) '' Set.Icc 1 x))
          ≤ ∑ _χ ∈ primChars q, ((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV
              * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := Finset.sum_le_sum hmain
        _ = ((primChars q).card : ℝ) * ((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV
              * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard := primChars_card_le_totient q
    calc ((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ primChars q,
          sSup ((fun y : ℕ => ‖S3' T q χ y‖) '' Set.Icc 1 x)
        ≤ ((q : ℝ) / (q.totient : ℝ)) *
            ((((primChars q).card : ℕ) : ℝ) * ((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV
              * Real.sqrt q * Real.log (2 * (q : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ ≤ ((q : ℝ) / (q.totient : ℝ)) *
            ((q.totient : ℝ) * ((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV
              * Real.sqrt q * Real.log (2 * (q : ℝ) + 2))) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hcard hb
          · positivity
      _ = (q : ℝ) * ((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV * Real.sqrt q
            * Real.log (2 * (q : ℝ) + 2)) := by
          rw [← mul_assoc, div_mul_cancel₀ (q : ℝ) (ne_of_gt hφpos)]
  have hK : (0 : ℝ) ≤ (T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV := by
    have h3 : (0 : ℝ) ≤ Real.log (2 * (T : ℝ) + 2) := log2nn T
    have h4 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    have hcv : (0 : ℝ) < cPV := cPV_pos
    positivity
  calc (∑ q ∈ Finset.Icc 2 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S3' T q χ y‖) '' Set.Icc 1 x))
      ≤ ∑ q ∈ Finset.Icc 2 Q, (q : ℝ) * ((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV
            * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := Finset.sum_le_sum hterm
    _ = ∑ q ∈ Finset.Icc 2 Q, (q : ℝ) * (((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV)
            * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by
        refine Finset.sum_congr rfl (fun q _ => ?_); ring
    _ ≤ ((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV) * (Q : ℝ) ^ (5 / 2 : ℝ)
          * Real.log (2 * (Q : ℝ) + 2) :=
        sum_Icc_two_q_sqrt_q_log_le Q hQ ((T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV) hK
    _ = (T : ℝ) * Real.log (2 * (T : ℝ) + 2) * cPV * (Q : ℝ) ^ (5 / 2 : ℝ)
          * Real.log (2 * (Q : ℝ) + 2) := by ring


/-! ## The main bracket and its domination properties -/

/-- The bracket appearing on the right-hand side of Vaughan's mean value theorem. -/
abbrev mainBracket (x Q : ℕ) : ℝ :=
  (x : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2
    + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ)

/-- The logarithm appearing on the right-hand side. -/
abbrev mainLog (x Q : ℕ) : ℝ := Real.log ((x : ℝ) * (Q : ℝ) + 2)

lemma mainLog_ge_one {x Q : ℕ} (hx : 2 ≤ x) (hQ : 2 ≤ Q) : 1 ≤ mainLog x Q := by
  have h6 : (6 : ℝ) ≤ (x : ℝ) * (Q : ℝ) + 2 := by
    have h1 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have h2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    nlinarith
  have hlog6 : (1 : ℝ) ≤ Real.log 6 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    nlinarith [Real.exp_one_lt_d9]
  exact le_trans hlog6 (Real.log_le_log (by norm_num) h6)

lemma mainBracket_nonneg (x Q : ℕ) : 0 ≤ mainBracket x Q := by
  have h1 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have h2 : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg h1 _
  have h3 : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg h1 _
  have h4 : (0 : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) := Real.rpow_nonneg h1 _
  have h5 : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have h6 : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := by positivity
  have h7 : (0 : ℝ) ≤ (Q : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg h5 _
  have h8 : (0 : ℝ) ≤ (Q : ℝ) ^ (3 / 2 : ℝ) := h7
  simp only [mainBracket]
  positivity

/-- Dominating terms by the main bracket. -/
lemma le_mainBracket_self (x Q : ℕ) : (x : ℝ) ≤ mainBracket x Q := by
  have h1 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have h5 : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have h2 : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have h4 : (0 : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) := by positivity
  simp only [mainBracket]
  linarith

lemma rpow_third_sq (x : ℝ) (hx : 0 ≤ x) :
    ((x) ^ (1 / 3 : ℝ)) ^ (2 : ℝ) = x ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_mul hx (1 / 3) 2]
  norm_num

lemma rpow_sixth_sq (x : ℝ) (hx : 0 ≤ x) :
    ((x) ^ (1 / 6 : ℝ)) ^ (2 : ℝ) = x ^ (1 / 3 : ℝ) := by
  rw [← Real.rpow_mul hx (1 / 6) 2]
  norm_num

lemma domino_T2 {x Q T : ℕ} (hx : 2 ≤ x) (hTx : (T : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ)) :
    (T : ℝ) ^ 2 ≤ mainBracket x Q := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have : (1 : ℕ) ≤ x := by omega
    exact_mod_cast this
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith
  have h0T : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hT2 : (T : ℝ) ^ 2 ≤ ((x : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ h0T hTx 2
  have h23 : ((x : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = (x : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast ((x : ℝ) ^ (1 / 3 : ℝ)) 2]
    exact rpow_third_sq (x : ℝ) hx0
  have hx23 : (x : ℝ) ^ (2 / 3 : ℝ) ≤ (x : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (2 : ℝ) / 3 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  calc (T : ℝ) ^ 2 ≤ ((x : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := hT2
    _ = (x : ℝ) ^ (2 / 3 : ℝ) := h23
    _ ≤ (x : ℝ) := hx23
    _ ≤ mainBracket x Q := le_mainBracket_self x Q

lemma domino_Q_sqrtx_T {x Q T : ℕ} (hx : 2 ≤ x) (hQ : 2 ≤ Q)
    (hTx : (T : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ)) :
    (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ) ≤ mainBracket x Q := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have : (1 : ℕ) ≤ x := by omega
    exact_mod_cast this
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith
  have h0T : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have h0Q : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have h0s : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0 _
  have hstep : (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) := by
    calc (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (x : ℝ) ^ (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hTx h0s
      _ = (x : ℝ) ^ (5 / 6 : ℝ) := by
          rw [← Real.rpow_add (by linarith)]; norm_num
  have h2 : (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
      = (Q : ℝ) * ((x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)) := by ring
  have h56 : (0 : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) := Real.rpow_nonneg hx0 _
  have hmain : (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) ≤ mainBracket x Q := by
    have h0s2 : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2 := by positivity
    have h0t : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) := by positivity
    simp only [mainBracket]
    linarith
  rw [h2]
  calc (Q : ℝ) * ((x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)) ≤ (Q : ℝ) * (x : ℝ) ^ (5 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_left hstep h0Q
    _ = (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) := by ring
    _ ≤ mainBracket x Q := hmain

lemma domino_Q_T2 {x Q T : ℕ} (hx : 2 ≤ x) (hQ : 2 ≤ Q)
    (hTx : (T : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ)) (hTQ : (T : ℝ) * (Q : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ)) :
    (Q : ℝ) * (T : ℝ) ^ 2 ≤ mainBracket x Q := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have : (1 : ℕ) ≤ x := by omega
    exact_mod_cast this
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith
  have h0T : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have h0Q : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have h1 : (Q : ℝ) * (T : ℝ) ^ 2 = ((T : ℝ) * (Q : ℝ)) * (T : ℝ) := by ring
  have h2 : ((T : ℝ) * (Q : ℝ)) * (T : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (x : ℝ) ^ (1 / 3 : ℝ) :=
    mul_le_mul hTQ hTx h0T (Real.rpow_nonneg hx0 _)
  have h3 : (x : ℝ) ^ (2 / 3 : ℝ) * (x : ℝ) ^ (1 / 3 : ℝ) = (x : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  rw [h1]
  linarith [h2, h3.le, le_mainBracket_self x Q]

lemma domino_Q_sqrtx {x Q : ℕ} (hx : 2 ≤ x) :
    (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) ≤ mainBracket x Q := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have : (1 : ℕ) ≤ x := by omega
    exact_mod_cast this
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith
  have h0Q : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hstep : (x : ℝ) ^ (1 / 2 : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h1 : (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) ≤ (Q : ℝ) * (x : ℝ) ^ (5 / 6 : ℝ) :=
    mul_le_mul_of_nonneg_left hstep h0Q
  have h2 : (Q : ℝ) * (x : ℝ) ^ (5 / 6 : ℝ) = (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) := by ring
  have h0t : (0 : ℝ) ≤ (Q : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg h0Q _
  have h0s : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0 _
  have h0u : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hx0 _
  have h0q : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := by positivity
  have hmain : (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) ≤ mainBracket x Q := by
    have h0s2 : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2 := by positivity
    have h0t : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) := by positivity
    simp only [mainBracket]; linarith
  calc (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) ≤ (Q : ℝ) * (x : ℝ) ^ (5 / 6 : ℝ) := h1
    _ = (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) := h2
    _ ≤ mainBracket x Q := hmain

lemma domino_Q_T {x Q T : ℕ} (hx : 2 ≤ x) (hQ : 2 ≤ Q)
    (hTQ : (T : ℝ) * (Q : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ)) :
    (Q : ℝ) * (T : ℝ) ≤ mainBracket x Q := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have : (1 : ℕ) ≤ x := by omega
    exact_mod_cast this
  have h3 : (Q : ℝ) * (T : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) := by
    rw [mul_comm]; exact hTQ
  have h4 : (x : ℝ) ^ (2 / 3 : ℝ) ≤ (x : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (2 : ℝ) / 3 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  calc (Q : ℝ) * (T : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) := h3
    _ ≤ (x : ℝ) := h4
    _ ≤ mainBracket x Q := le_mainBracket_self x Q

lemma domino_Q2_T {x Q T : ℕ} (hx : 2 ≤ x) (hQ : 2 ≤ Q)
    (hTx : (T : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ)) (hTQ : (T : ℝ) * (Q : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ)) :
    (Q : ℝ) ^ 2 * (T : ℝ) ≤ mainBracket x Q := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have : (1 : ℕ) ≤ x := by omega
    exact_mod_cast this
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith
  have h0Q : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have h0T : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hQT : (Q : ℝ) ^ 2 * (T : ℝ) = (Q : ℝ) * ((Q : ℝ) * (T : ℝ)) := by ring
  have h1 : (Q : ℝ) * (T : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) := by rw [mul_comm]; exact hTQ
  have h2 : (Q : ℝ) ^ 2 * (T : ℝ) ≤ (Q : ℝ) * (x : ℝ) ^ (2 / 3 : ℝ) := by
    rw [hQT]; exact mul_le_mul_of_nonneg_left h1 h0Q
  have h3 : (x : ℝ) ^ (2 / 3 : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h4 : (Q : ℝ) * (x : ℝ) ^ (2 / 3 : ℝ) ≤ (Q : ℝ) * (x : ℝ) ^ (5 / 6 : ℝ) :=
    mul_le_mul_of_nonneg_left h3 h0Q
  have h5 : (Q : ℝ) * (x : ℝ) ^ (5 / 6 : ℝ) = (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) := by ring
  have h0t : (0 : ℝ) ≤ (Q : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg h0Q _
  have h0s : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0 _
  have h0u : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hx0 _
  have h0q : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := by positivity
  have hmain : (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) ≤ mainBracket x Q := by
    have h0s2 : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2 := by positivity
    have h0t : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) := by positivity
    simp only [mainBracket]; linarith
  linarith [h2, h4, h5.le, hmain]


/-! ## Elementary dyadic sums -/

lemma sum_range_two_pow_le (J : ℕ) :
    (∑ j ∈ Finset.range J, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc (∑ j ∈ Finset.range n, (2 : ℝ) ^ j) + (2 : ℝ) ^ n ≤ (2 : ℝ) ^ n + (2 : ℝ) ^ n := by
          linarith
      _ = (2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

lemma sqrt_two_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

lemma sqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

lemma five_le_four_sqrt_two : (5 : ℝ) ≤ 4 * Real.sqrt 2 := by
  have h : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  linarith

lemma four_le_three_sqrt_two : (4 : ℝ) ≤ 3 * Real.sqrt 2 := by
  have h : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  linarith

lemma sum_range_sqrt_two_pow_le (J : ℕ) :
    (∑ j ∈ Finset.range J, (Real.sqrt 2) ^ j) ≤ 4 * (Real.sqrt 2) ^ J := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp : (0 : ℝ) ≤ (Real.sqrt 2) ^ n := by positivity
    nlinarith [ih, hp, five_le_four_sqrt_two, mul_nonneg hp (Real.sqrt_nonneg 2)]

lemma inv_sqrt_two_le_three_quarters : ((Real.sqrt 2))⁻¹ ≤ (3 : ℝ) / 4 := by
  have hp : (0 : ℝ) < Real.sqrt 2 := by
    have := sqrt_two_ge_one; linarith
  rw [inv_le_comm₀ hp (by norm_num)]
  have h := four_le_three_sqrt_two
  linarith

lemma sum_range_inv_sqrt_two_pow_le (J : ℕ) :
    (∑ j ∈ Finset.range J, ((Real.sqrt 2) ^ j)⁻¹) ≤ 4 := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have hsplit : (∑ k ∈ Finset.range n, ((Real.sqrt 2) ^ (k + 1))⁻¹)
        = ((Real.sqrt 2))⁻¹ * (∑ k ∈ Finset.range n, ((Real.sqrt 2) ^ k)⁻¹) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [pow_succ, mul_inv_rev]
    rw [hsplit, pow_zero, inv_one]
    have h0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range n, ((Real.sqrt 2) ^ k)⁻¹ :=
      Finset.sum_nonneg (fun k _ => by positivity)
    have h1 := inv_sqrt_two_le_three_quarters
    have h2 : ((Real.sqrt 2))⁻¹ * (∑ k ∈ Finset.range n, ((Real.sqrt 2) ^ k)⁻¹) ≤ (3/4) * 4 :=
      mul_le_mul h1 ih h0 (by norm_num)
    linarith

/-- The recursive form of the `M_j * N_j` sum. -/
lemma dyadic_MN_le (x J : ℕ) :
    (∑ j ∈ Finset.range J, (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
      ≤ 2 * (x : ℝ) * J + 2 * (2 : ℝ) ^ J := by
  have hpt : ∀ j ∈ Finset.range J, (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
      ≤ 2 * (x : ℝ) + (2 : ℝ) ^ (j + 1) := by
    intro j _
    have h1 : (((x / 2 ^ j : ℕ)) : ℝ) ≤ (x : ℝ) / (2 : ℝ) ^ j := by
      have h : (((x / 2 ^ j : ℕ)) : ℝ) ≤ (x : ℝ) / (((2 ^ j : ℕ)) : ℝ) :=
        Nat.cast_div_le
      rw [Nat.cast_pow] at h
      exact h
    have h3 : (2 : ℝ) ^ (j + 1) * ((x : ℝ) / (2 : ℝ) ^ j + 1)
        = 2 * (x : ℝ) + (2 : ℝ) ^ (j + 1) := by
      have hp : (2 : ℝ) ^ j ≠ 0 := by positivity
      rw [pow_succ]
      have hdiv : (2 : ℝ) ^ j * 2 * ((x : ℝ) / (2 : ℝ) ^ j) = 2 * (x : ℝ) := by
        field_simp
      rw [mul_add, mul_one, hdiv]
    calc (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
        ≤ (2 : ℝ) ^ (j + 1) * ((x : ℝ) / (2 : ℝ) ^ j + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 2 * (x : ℝ) + (2 : ℝ) ^ (j + 1) := h3
  calc (∑ j ∈ Finset.range J, (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
      ≤ ∑ j ∈ Finset.range J, (2 * (x : ℝ) + (2 : ℝ) ^ (j + 1)) := Finset.sum_le_sum hpt
    _ = (J : ℝ) * (2 * (x : ℝ)) + 2 * ∑ j ∈ Finset.range J, (2 : ℝ) ^ j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [pow_succ]; ring
    _ ≤ 2 * (x : ℝ) * J + 2 * (2 : ℝ) ^ J := by
        have h := sum_range_two_pow_le J
        have hx : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
        have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
        have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ J := by positivity
        nlinarith [h, mul_nonneg hx hJ]


/-! ## Piece 3, second part: the dyadic split -/

lemma two_pow_log2_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ n.log2 ≤ n :=
  ((Nat.log2_eq_iff (by omega)).mp rfl).1

lemma log2_le_log_div_log_two (n : ℕ) (hn : 1 ≤ n) :
    (n.log2 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ (n.log2 : ℕ) ≤ (n : ℝ) := by
    have := two_pow_log2_le n hn
    exact_mod_cast this
  have h1 : (0 : ℝ) < (2 : ℝ) ^ n.log2 := by positivity
  have hlog := Real.log_le_log h1 hpow
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ h2]
  linarith [hlog]

/-- The dyadic blocks in the range `(T, T * T]`. -/
def blk (T j : ℕ) : Finset ℕ := (Finset.Icc (T + 1) (T * T)).filter (fun t => t.log2 = j)

/-- The coefficient of the second part of the third Vaughan piece, cut to the block `j`. -/
def aBlk (T j : ℕ) (t : ℕ) : ℂ := if t ∈ blk T j then aT T t else 0

lemma mem_blk {T j t : ℕ} : t ∈ blk T j ↔ T + 1 ≤ t ∧ t ≤ T * T ∧ t.log2 = j := by
  rw [blk, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro h; exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h; exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

lemma blk_subset (T j : ℕ) (hT : 1 ≤ T) : blk T j ⊆ Finset.Icc 1 (2 ^ (j + 1)) := by
  intro t ht
  rw [mem_blk] at ht
  rw [Finset.mem_Icc]
  have hlt : t < 2 ^ (j + 1) := ((Nat.log2_eq_iff (by omega : t ≠ 0)).mp ht.2.2).2
  omega

lemma S3''_as_blockSum (T q : ℕ) (hT : 1 ≤ T) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    S3'' T q χ y
      = ∑ j ∈ Finset.range ((T * T).log2 + 1),
          ∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)),
            aBlk T j t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)) := by
  rw [S3'', Commons.Data.Finset.sum_Icc_eq_sum_log2_blocks]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hset : (Finset.Icc 1 (2 ^ (j + 1))).filter (fun t => t ∈ blk T j)
      = (Finset.Icc (T + 1) (T * T)).filter (fun t => t.log2 = j) := by
    ext t
    constructor
    · intro h
      have h2 : t ∈ blk T j := (Finset.mem_filter.mp h).2
      have h3 : T + 1 ≤ t ∧ t ≤ T * T ∧ t.log2 = j := mem_blk.mp h2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3.1, h3.2.1⟩, h3.2.2⟩
    · intro h
      have h1 : t ∈ Finset.Icc (T + 1) (T * T) := (Finset.mem_filter.mp h).1
      have h2 : t.log2 = j := (Finset.mem_filter.mp h).2
      have h3 : T + 1 ≤ t ∧ t ≤ T * T := Finset.mem_Icc.mp h1
      have hlt : t < 2 ^ (j + 1) := ((Nat.log2_eq_iff (by omega : t ≠ 0)).mp h2).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        mem_blk.mpr ⟨h3.1, h3.2, h2⟩⟩
  have hrw : (∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)), aBlk T j t * χ (t : ZMod q)
        * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)))
      = ∑ t ∈ (Finset.Icc 1 (2 ^ (j + 1))).filter (fun t => t ∈ blk T j),
          aT T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [aBlk]
    by_cases h : t ∈ blk T j <;> simp [h]
  rw [hrw, hset]

lemma S3''_blk_term (T j q : ℕ) (hT : 1 ≤ T) (χ : DirichletCharacter ℂ q) (x y t : ℕ)
    (hyx : y ≤ x) (ht : t ∈ Finset.Icc 1 (2 ^ (j + 1))) :
    aBlk T j t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))
      = ∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
          (if t * r ≤ y then (1 : ℂ) else 0) * aBlk T j t * (1 : ℂ) * χ ((t * r : ℕ) : ZMod q) := by
  by_cases hb : t ∈ blk T j
  · rw [aBlk, if_pos hb]
    have hpos : 0 < t := by
      rw [mem_blk] at hb
      omega
    have ht2 : 2 ^ j ≤ t := ((Nat.log2_eq_iff (by omega : t ≠ 0)).mp (mem_blk.mp hb).2.2).1
    have hyt : y / t ≤ x / 2 ^ j + 1 := by
      calc y / t ≤ x / t := Nat.div_le_div_right hyx
        _ ≤ x / 2 ^ j := Nat.div_le_div_left ht2 (by positivity)
        _ ≤ x / 2 ^ j + 1 := Nat.le_succ _
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hyt)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have hrle : r ≤ y / t := (Finset.mem_Icc.mp hr).2
      have hind : t * r ≤ y := by
        have h := (Nat.le_div_iff_mul_le hpos).mp hrle
        rwa [mul_comm] at h
      rw [if_pos hind, Nat.cast_mul, map_mul]
      ring
    · intro r hr hrn
      have hnr : ¬ (t * r ≤ y) := by
        intro hc
        have hrt : r * t ≤ y := by rw [mul_comm]; exact hc
        have hrd : r ≤ y / t := (Nat.le_div_iff_mul_le hpos).mpr hrt
        exact hrn (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, hrd⟩)
      rw [if_neg hnr]
      ring
  · rw [aBlk, if_neg hb]
    have hz : (∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
        (if t * r ≤ y then (1 : ℂ) else 0) * (0 : ℂ) * (1 : ℂ)
          * χ ((t * r : ℕ) : ZMod q)) = 0 := by
      refine Finset.sum_eq_zero (fun r _ => ?_)
      ring
    rw [hz]
    ring


/-! ## Piece 3, second part: the blockwise bound -/

lemma blk_l1_le (T x Q : ℕ) (hT : 1 ≤ T) (hQ : 2 ≤ Q) (hx : 2 ≤ x)
    (hTx : (T : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ)) (j : ℕ) (hj : j ∈ Finset.range ((T * T).log2 + 1)) :
    Real.log (2 * (2 : ℝ) ^ (j + 1) + 2) ≤ 2 * mainLog x Q := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have : (1 : ℕ) ≤ x := by omega
    exact_mod_cast this
  have h23 : ((x : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = (x : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast ((x : ℝ) ^ (1 / 3 : ℝ)) 2]
    exact rpow_third_sq (x : ℝ) (by positivity)
  have hT2 : (T : ℝ) ^ 2 ≤ (x : ℝ) ^ (2 / 3 : ℝ) := by
    have h' : (T : ℝ) ^ 2 ≤ ((x : ℝ) ^ (1 / 3 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg T) hTx 2
    rwa [h23] at h'
  have h23x : (x : ℝ) ^ (2 / 3 : ℝ) ≤ (x : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (2 : ℝ) / 3 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hT2x : (T : ℝ) ^ 2 ≤ (x : ℝ) := le_trans hT2 h23x
  have hj' : j ≤ (T * T).log2 := by
    have := Finset.mem_range.mp hj
    omega
  have h2J : (2 : ℝ) ^ (j + 1) ≤ 4 * (T : ℝ) ^ 2 := by
    have h2p : (2 : ℝ) ^ (j + 1) ≤ 2 * (2 : ℝ) ^ ((T * T).log2) := by
      calc (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
        _ ≤ 2 * (2 : ℝ) ^ ((T * T).log2) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hj') (by norm_num)
    have hlog2 : (2 : ℝ) ^ ((T * T).log2) ≤ ((T : ℝ) * (T : ℝ)) := by
      have h := two_pow_log2_le (T * T) (by nlinarith)
      have h' : ((2 : ℝ)) ^ ((T * T).log2) ≤ ((T * T : ℕ) : ℝ) := by exact_mod_cast h
      rwa [Nat.cast_mul] at h'
    nlinarith [h2p, hlog2]
  have harg : 2 * (2 : ℝ) ^ (j + 1) + 2 ≤ ((x : ℝ) * (Q : ℝ) + 2) ^ 2 := by
    have h2x : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hA : 2 * (2 : ℝ) ^ (j + 1) + 2 ≤ 8 * (x : ℝ) + 2 := by nlinarith [h2J, hT2x]
    have hB : 8 * (x : ℝ) + 2 ≤ (2 * (x : ℝ) + 2) ^ 2 := by nlinarith [h2x]
    have hC : (2 * (x : ℝ) + 2) ^ 2 ≤ ((x : ℝ) * (Q : ℝ) + 2) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) (by nlinarith) 2
    linarith
  calc Real.log (2 * (2 : ℝ) ^ (j + 1) + 2)
      ≤ Real.log (((x : ℝ) * (Q : ℝ) + 2) ^ 2) := by
        apply Real.log_le_log (by positivity) harg
    _ = 2 * Real.log ((x : ℝ) * (Q : ℝ) + 2) := by
        rw [Real.log_pow]; norm_num

lemma blk_l2_le (T x Q : ℕ) (hT : 1 ≤ T) (hQ : 2 ≤ Q) (hx : 2 ≤ x)
    (hTx : (T : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ)) (j : ℕ) (hj : j ∈ Finset.range ((T * T).log2 + 1)) :
    Real.log (2 * (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) + 2)
      ≤ 4 * mainLog x Q := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have : (1 : ℕ) ≤ x := by omega
    exact_mod_cast this
  have h23 : ((x : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = (x : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast ((x : ℝ) ^ (1 / 3 : ℝ)) 2]
    exact rpow_third_sq (x : ℝ) (by positivity)
  have hT2 : (T : ℝ) ^ 2 ≤ (x : ℝ) ^ (2 / 3 : ℝ) := by
    have h' : (T : ℝ) ^ 2 ≤ ((x : ℝ) ^ (1 / 3 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg T) hTx 2
    rwa [h23] at h'
  have h23x : (x : ℝ) ^ (2 / 3 : ℝ) ≤ (x : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (2 : ℝ) / 3 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hT2x : (T : ℝ) ^ 2 ≤ (x : ℝ) := le_trans hT2 h23x
  have hj' : j ≤ (T * T).log2 := by
    have := Finset.mem_range.mp hj
    omega
  have h2J : (2 : ℝ) ^ (j + 1) ≤ 4 * (T : ℝ) ^ 2 := by
    have h2p : (2 : ℝ) ^ (j + 1) ≤ 2 * (2 : ℝ) ^ ((T * T).log2) := by
      calc (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
        _ ≤ 2 * (2 : ℝ) ^ ((T * T).log2) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hj') (by norm_num)
    have hlog2 : (2 : ℝ) ^ ((T * T).log2) ≤ ((T : ℝ) * (T : ℝ)) := by
      have h := two_pow_log2_le (T * T) (by nlinarith)
      have h' : ((2 : ℝ)) ^ ((T * T).log2) ≤ ((T * T : ℕ) : ℝ) := by exact_mod_cast h
      rwa [Nat.cast_mul] at h'
    nlinarith [h2p, hlog2]
  have hNle : ((((x / 2 ^ j : ℕ)) : ℝ) + 1) ≤ (x : ℝ) + 1 := by
    have h := Nat.div_le_self x (2 ^ j)
    have h' : ((x / 2 ^ j : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
    linarith
  have harg : 2 * (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) + 2
      ≤ ((x : ℝ) * (Q : ℝ) + 2) ^ 4 := by
    have h2x : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hA : 2 * (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) + 2
        ≤ 8 * (x : ℝ) * ((x : ℝ) + 1) + 2 := by
      have hpos : (0 : ℝ) ≤ ((((x / 2 ^ j : ℕ)) : ℝ) + 1) := by positivity
      have hpos2 : (0 : ℝ) ≤ 4 * (T : ℝ) ^ 2 := by positivity
      have h1 : 2 * (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
          ≤ 8 * (T : ℝ) ^ 2 * ((x : ℝ) + 1) := by
        have h := mul_le_mul h2J hNle hpos hpos2
        nlinarith [h]
      have h2 : 8 * (T : ℝ) ^ 2 * ((x : ℝ) + 1) ≤ 8 * (x : ℝ) * ((x : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
      linarith
    have hB : 8 * (x : ℝ) * ((x : ℝ) + 1) + 2 ≤ (2 * (x : ℝ) + 2) ^ 4 := by
      have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith
      have h9 : (9 : ℝ) ≤ ((x : ℝ) + 1) ^ 2 := by nlinarith
      have hq : (81 : ℝ) ≤ ((x : ℝ) + 1) ^ 4 := by nlinarith
      have hxx : 8 * (x : ℝ) * ((x : ℝ) + 1) ≤ 8 * ((x : ℝ) + 1) ^ 2 := by nlinarith
      nlinarith [h9, hq, hxx]
    have hC : (2 * (x : ℝ) + 2) ^ 4 ≤ ((x : ℝ) * (Q : ℝ) + 2) ^ 4 := by
      apply pow_le_pow_left₀ (by positivity) (by nlinarith) 4
    linarith
  calc Real.log (2 * (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) + 2)
      ≤ Real.log (((x : ℝ) * (Q : ℝ) + 2) ^ 4) := by
        apply Real.log_le_log (by positivity) harg
    _ = 4 * Real.log ((x : ℝ) * (Q : ℝ) + 2) := by
        rw [Real.log_pow]; norm_num


/-- `sqrt` of the main bracket expansion. -/
lemma sqrt_mul_add_sq_le {M N Q : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hQ : 0 ≤ Q) :
    Real.sqrt ((M + Q ^ 2) * (N + Q ^ 2))
      ≤ Real.sqrt (M * N) + Q * Real.sqrt M + Q * Real.sqrt N + Q ^ 2 := by
  have h1 : Real.sqrt (M + Q ^ 2) ≤ Real.sqrt M + Q := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hM, Real.sqrt_nonneg M, hQ]
  have h2 : Real.sqrt (N + Q ^ 2) ≤ Real.sqrt N + Q := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hN, Real.sqrt_nonneg N, hQ]
  calc Real.sqrt ((M + Q ^ 2) * (N + Q ^ 2))
      = Real.sqrt (M + Q ^ 2) * Real.sqrt (N + Q ^ 2) := Real.sqrt_mul (by positivity) _
    _ ≤ (Real.sqrt M + Q) * (Real.sqrt N + Q) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.sqrt (M * N) + Q * Real.sqrt M + Q * Real.sqrt N + Q ^ 2 := by
        rw [Real.sqrt_mul hM]
        ring

lemma blk_M_le (T J j : ℕ) (hT : 1 ≤ T) (hj : j < J) (hJ : J ≤ (T * T).log2 + 1) :
    (2 : ℝ) ^ (j + 1) ≤ 2 * ((T : ℝ) * (T : ℝ)) := by
  have hlog2 : (2 : ℝ) ^ ((T * T).log2) ≤ ((T : ℝ) * (T : ℝ)) := by
    have h := two_pow_log2_le (T * T) (by nlinarith)
    have h' : ((2 : ℝ)) ^ ((T * T).log2) ≤ ((T * T : ℕ) : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_mul] at h'
  have h2J : (2 : ℝ) ^ J ≤ 2 * ((T : ℝ) * (T : ℝ)) := by
    have h1 : J - 1 ≤ (T * T).log2 := by omega
    have h2 := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) h1
    have hJeq : J = (J - 1) + 1 := by omega
    have hstep : (2 : ℝ) ^ J = 2 * (2 : ℝ) ^ (J - 1) := by
      conv_lhs => rw [hJeq]
      rw [pow_succ]; ring
    rw [hstep]
    exact mul_le_mul_of_nonneg_left (le_trans h2 hlog2) (by norm_num)
  calc (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J :=
        pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (by omega)
    _ ≤ 2 * ((T : ℝ) * (T : ℝ)) := h2J

lemma blk_M_two_le (T J j : ℕ) (hT : 1 ≤ T) (hj : j < J) (hJ : J ≤ (T * T).log2 + 1) :
    (2 : ℝ) ^ (j + 1) ≤ 2 * (T : ℝ) ^ 2 := by
  have h := blk_M_le T J j hT hj hJ
  have : (T : ℝ) * (T : ℝ) = (T : ℝ) ^ 2 := by ring
  rw [this] at h; exact h

lemma blk_M_two_le' (T J j : ℕ) (hj : j < J) (h2J : (2 : ℝ) ^ J ≤ 2 * (T : ℝ) ^ 2) :
    (2 : ℝ) ^ (j + 1) ≤ 2 * (T : ℝ) ^ 2 :=
  le_trans (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (by omega)) h2J

lemma sqrt_two_pow_sq (j : ℕ) : ((Real.sqrt 2) ^ j) ^ 2 = (2 : ℝ) ^ j := by
  have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  rw [pow_two, ← pow_add, show j + j = 2 * j by ring, pow_mul, h]

lemma sqrt_two_pow_eq (j : ℕ) : Real.sqrt ((2 : ℝ) ^ j) = (Real.sqrt 2) ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^n), ih, pow_succ]

lemma sqrt_two_pow_eq_sqrt (j : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (j + 1)) = Real.sqrt 2 * (Real.sqrt 2) ^ j := by
  rw [show (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j by rw [pow_succ]; ring,
    Real.sqrt_mul (by norm_num), sqrt_two_pow_eq]

lemma blk_sqrt_M_le (T J j : ℕ) (h2J : (2 : ℝ) ^ J ≤ 2 * (T : ℝ) ^ 2) (hj : j < J) :
    Real.sqrt ((2 : ℝ) ^ (j + 1)) ≤ Real.sqrt 2 * (Real.sqrt 2) ^ j :=
  le_of_eq (sqrt_two_pow_eq_sqrt j)

lemma sqrt_two_pow_J_le (T J : ℕ) (h2J : (2 : ℝ) ^ J ≤ 2 * (T : ℝ) ^ 2) :
    (Real.sqrt 2) ^ J ≤ Real.sqrt 2 * (T : ℝ) := by
  have hJT : (Real.sqrt 2) ^ J = Real.sqrt ((2 : ℝ) ^ J) := (sqrt_two_pow_eq J).symm
  rw [hJT]
  calc Real.sqrt ((2 : ℝ) ^ J) ≤ Real.sqrt (2 * (T : ℝ) ^ 2) := Real.sqrt_le_sqrt h2J
    _ = Real.sqrt 2 * (T : ℝ) := by
        rw [show (2 * (T : ℝ) ^ 2) = 2 * (T * T) by ring, Real.sqrt_mul (by norm_num)]
        rw [Real.sqrt_mul_self (Nat.cast_nonneg T)]

lemma blk_Nj_le (x j : ℕ) : ((((x / 2 ^ j : ℕ)) : ℝ) + 1) ≤ (x : ℝ) + 1 := by
  have h := Nat.div_le_self x (2 ^ j)
  have h' : ((x / 2 ^ j : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
  linarith

lemma blk_sqrt_Nj_le (x j : ℕ) :
    Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1) ≤ Real.sqrt x + 1 := by
  have h := blk_Nj_le x j
  calc Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1) ≤ Real.sqrt ((x : ℝ) + 1) := Real.sqrt_le_sqrt h
    _ ≤ Real.sqrt x + 1 := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (x:ℝ) by positivity),
          Real.sqrt_nonneg (x:ℝ)]

lemma two_pow_log2_lt_succ (n : ℕ) (hn : 1 ≤ n) : n < 2 * 2 ^ (n.log2) := by
  have h := ((Nat.log2_eq_iff (by omega : n ≠ 0)).mp rfl).2
  rw [pow_succ] at h
  omega

lemma inv_sqrt_two_pow_log2_le (T : ℕ) (hT : 1 ≤ T) :
    ((Real.sqrt 2) ^ ((T + 1).log2))⁻¹ ≤ Real.sqrt 2 / Real.sqrt ((T : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (Real.sqrt 2) ^ ((T + 1).log2) := by positivity
  have hposT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hlt : (T : ℝ) + 1 < 2 * ((Real.sqrt 2) ^ ((T+1).log2)) ^ 2 := by
    have h := two_pow_log2_lt_succ (T+1) (by omega)
    have h' : ((T + 1 : ℕ) : ℝ) < 2 * ((2:ℝ) ^ ((T+1).log2)) := by exact_mod_cast h
    rw [sqrt_two_pow_sq]
    push_cast at h' ⊢
    linarith
  have key : Real.sqrt ((T : ℝ) + 1) ≤ Real.sqrt 2 * (Real.sqrt 2) ^ ((T + 1).log2) := by
    rw [Real.sqrt_le_left (by positivity)]
    have hsq : (Real.sqrt 2 * (Real.sqrt 2) ^ ((T + 1).log2)) ^ 2
        = 2 * ((Real.sqrt 2) ^ ((T + 1).log2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    rw [hsq]
    exact le_of_lt hlt
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hposT)]
  calc ((Real.sqrt 2) ^ ((T + 1).log2))⁻¹ * Real.sqrt ((T : ℝ) + 1)
      ≤ ((Real.sqrt 2) ^ ((T + 1).log2))⁻¹
          * (Real.sqrt 2 * (Real.sqrt 2) ^ ((T + 1).log2)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = Real.sqrt 2 := by field_simp


lemma blk_sqrt_Nj_le' (x j : ℕ) :
    Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1) ≤ Real.sqrt x / (Real.sqrt 2) ^ j + 1 := by
  have h1 : ((((x / 2 ^ j : ℕ)) : ℝ)) ≤ (x : ℝ) / (2 : ℝ) ^ j := by
    have h : (((x / 2 ^ j : ℕ)) : ℝ) ≤ (x : ℝ) / (((2 ^ j : ℕ)) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_pow] at h
    exact h
  have h2 : Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
      ≤ Real.sqrt ((x : ℝ) / (2 : ℝ) ^ j + 1) := by
    apply Real.sqrt_le_sqrt; linarith
  have h3 : Real.sqrt ((x : ℝ) / (2 : ℝ) ^ j + 1)
      ≤ Real.sqrt ((x : ℝ) / (2 : ℝ) ^ j) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (x:ℝ)/(2:ℝ)^j),
      Real.sqrt_nonneg ((x:ℝ)/(2:ℝ)^j)]
  have h4 : Real.sqrt ((x : ℝ) / (2 : ℝ) ^ j) = Real.sqrt x / (Real.sqrt 2) ^ j := by
    rw [Real.sqrt_div (Nat.cast_nonneg x), sqrt_two_pow_eq]
  linarith [h2, h3, h4.le, h4.ge]

/-- `M_j N_j ≤ 2x + 4T²`. -/
lemma blk_MN_le' (x T J j : ℕ) (hj : j < J) (h2J : (2 : ℝ) ^ J ≤ 2 * (T : ℝ) ^ 2) :
    (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) ≤ 2 * (x : ℝ) + 4 * (T : ℝ) ^ 2 := by
  have h1 : ((((x / 2 ^ j : ℕ)) : ℝ)) ≤ (x : ℝ) / (2 : ℝ) ^ j := by
    have h : (((x / 2 ^ j : ℕ)) : ℝ) ≤ (x : ℝ) / (((2 ^ j : ℕ)) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_pow] at h
    exact h
  have h2 : (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
      ≤ (2 : ℝ) ^ (j + 1) * ((x : ℝ) / (2 : ℝ) ^ j + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : (2 : ℝ) ^ (j + 1) * ((x : ℝ) / (2 : ℝ) ^ j + 1)
      = 2 * (x : ℝ) + (2 : ℝ) ^ (j + 1) := by
    have hp : (2 : ℝ) ^ j ≠ 0 := by positivity
    rw [pow_succ]
    have hdiv : (2 : ℝ) ^ j * 2 * ((x : ℝ) / (2 : ℝ) ^ j) = 2 * (x : ℝ) := by
      field_simp
    rw [mul_add, mul_one, hdiv]
  have h4 : (2 : ℝ) ^ (j + 1) ≤ 4 * (T : ℝ) ^ 2 := by
    have h := blk_M_two_le' T J j hj h2J
    nlinarith [h, sq_nonneg (T : ℝ)]
  linarith [h2, h3.le, h4]

/-- Sum of `A + B r^j` over the filtered range. -/
lemma filtered_card_le (J j₀ : ℕ) :
    ((((Finset.range J).filter (fun j => j₀ ≤ j)).card : ℕ) : ℝ) ≤ (J : ℝ) := by
  have h : ((Finset.range J).filter (fun j => j₀ ≤ j)).card ≤ J :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
  exact_mod_cast h

lemma filtered_sum_le (J j₀ : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (r : ℝ) (hr0 : 0 ≤ r)
    (hgeo : (∑ j ∈ Finset.range J, r ^ j) ≤ 4 * r ^ J) :
    (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), (A + B * r ^ j))
      ≤ A * (J : ℝ) + B * (4 * r ^ J) := by
  have hsum : (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), r ^ j) ≤ 4 * r ^ J := by
    calc (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), r ^ j)
        ≤ ∑ j ∈ Finset.range J, r ^ j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro i _ _; exact pow_nonneg hr0 i
      _ ≤ 4 * r ^ J := hgeo
  have hcard := filtered_card_le J j₀
  calc (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), (A + B * r ^ j))
      = (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), A)
          + B * (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), r ^ j) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = A * ((((Finset.range J).filter (fun j => j₀ ≤ j)).card : ℕ) : ℝ)
          + B * (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), r ^ j) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ A * (J : ℝ) + B * (4 * r ^ J) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hcard hA
        · exact mul_le_mul_of_nonneg_left hsum hB

lemma filtered_sum_inv_le (J j₀ : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (r : ℝ) (hr : 1 ≤ r)
    (hgeo : (∑ j ∈ Finset.range J, r ^ j) ≤ 4 * r ^ J) :
    (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), (A * (r ^ j)⁻¹ + B * r ^ j))
      ≤ A * ((J : ℝ) * (r ^ j₀)⁻¹) + B * (4 * r ^ J) := by
  have hcard := filtered_card_le J j₀
  have hinv : (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), (r ^ j)⁻¹)
      ≤ (J : ℝ) * (r ^ j₀)⁻¹ := by
    calc (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), (r ^ j)⁻¹)
        ≤ ∑ _j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), (r ^ j₀)⁻¹ := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [Finset.mem_filter] at hj
          exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (pow_le_pow_right₀ hr hj.2)
      _ = (((Finset.range J).filter (fun j => j₀ ≤ j)).card : ℝ) * (r ^ j₀)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (J : ℝ) * (r ^ j₀)⁻¹ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hsum : (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), r ^ j) ≤ 4 * r ^ J := by
    calc (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), r ^ j)
        ≤ ∑ j ∈ Finset.range J, r ^ j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro i _ _; exact pow_nonneg (by linarith : (0:ℝ) ≤ r) i
      _ ≤ 4 * r ^ J := hgeo
  calc (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), (A * (r ^ j)⁻¹ + B * r ^ j))
      = A * (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), (r ^ j)⁻¹)
          + B * (∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j), r ^ j) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ A * ((J : ℝ) * (r ^ j₀)⁻¹) + B * (4 * r ^ J) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hinv hA
        · exact mul_le_mul_of_nonneg_left hsum hB


lemma blk_MN_le_sharp (x T J j : ℕ) (hj : j < J) (h2J : (2 : ℝ) ^ J ≤ 2 * (T : ℝ) ^ 2) :
    (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) ≤ 2 * (x : ℝ) + (2 : ℝ) ^ (j + 1) := by
  have h1 : ((((x / 2 ^ j : ℕ)) : ℝ)) ≤ (x : ℝ) / (2 : ℝ) ^ j := by
    have h : (((x / 2 ^ j : ℕ)) : ℝ) ≤ (x : ℝ) / (((2 ^ j : ℕ)) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_pow] at h
    exact h
  have h2 : (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
      ≤ (2 : ℝ) ^ (j + 1) * ((x : ℝ) / (2 : ℝ) ^ j + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : (2 : ℝ) ^ (j + 1) * ((x : ℝ) / (2 : ℝ) ^ j + 1)
      = 2 * (x : ℝ) + (2 : ℝ) ^ (j + 1) := by
    have hp : (2 : ℝ) ^ j ≠ 0 := by positivity
    rw [pow_succ]
    have hdiv : (2 : ℝ) ^ j * 2 * ((x : ℝ) / (2 : ℝ) ^ j) = 2 * (x : ℝ) := by
      field_simp
    rw [mul_add, mul_one, hdiv]
  linarith [h2, h3.le]

lemma blk_MN_filtered_le (x T J : ℕ) (hT : 1 ≤ T) (h2J : (2 : ℝ) ^ J ≤ 2 * (T : ℝ) ^ 2) :
    (∑ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
        (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
      ≤ 2 * (x : ℝ) * (J : ℝ) + 4 * (T : ℝ) ^ 2 := by
  have h := dyadic_MN_le x J
  have h' : (∑ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
        (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
      ≤ ∑ j ∈ Finset.range J, (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _; positivity
  have h2 : (2 : ℝ) ^ J ≤ 2 * (T : ℝ) ^ 2 := h2J
  linarith

lemma blk_M_sqrtN_filtered_le (x T J : ℕ) (hT : 1 ≤ T) (h2J : (2 : ℝ) ^ J ≤ 2 * (T : ℝ) ^ 2) :
    (∑ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
        (2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
      ≤ (2 * (T : ℝ) * Real.sqrt x + 4 * Real.sqrt 2 * (T : ℝ) ^ 2) * (J : ℝ) := by
  have hpt : ∀ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
      (2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
        ≤ 2 * (T : ℝ) * Real.sqrt x + 4 * Real.sqrt 2 * (T : ℝ) ^ 2 := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hjlt : j < J := Finset.mem_range.mp hj.1
    have h5 : (2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
        = Real.sqrt ((2 : ℝ) ^ (j + 1))
            * Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)) := by
      have hsq : Real.sqrt ((2 : ℝ) ^ (j + 1)) * Real.sqrt ((2 : ℝ) ^ (j + 1))
          = (2 : ℝ) ^ (j + 1) := Real.mul_self_sqrt (by positivity)
      calc (2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
          = (Real.sqrt ((2 : ℝ) ^ (j + 1)) * Real.sqrt ((2 : ℝ) ^ (j + 1)))
              * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1) := by rw [hsq]
        _ = Real.sqrt ((2 : ℝ) ^ (j + 1))
              * (Real.sqrt ((2 : ℝ) ^ (j + 1)) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1)) := by
            ring
        _ = Real.sqrt ((2 : ℝ) ^ (j + 1))
              * Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^(j+1))]
    have hM : Real.sqrt ((2 : ℝ) ^ (j + 1)) ≤ Real.sqrt 2 * (T : ℝ) := by
      have h := blk_M_two_le' T J j hjlt h2J
      calc Real.sqrt ((2 : ℝ) ^ (j + 1)) ≤ Real.sqrt (2 * (T : ℝ) ^ 2) := Real.sqrt_le_sqrt h
        _ = Real.sqrt 2 * (T : ℝ) := by
            rw [show (2 * (T : ℝ) ^ 2) = 2 * (T * T) by ring, Real.sqrt_mul (by norm_num)]
            rw [Real.sqrt_mul_self (Nat.cast_nonneg T)]
    have hMN := blk_MN_le' x T J j hjlt h2J
    have h1 : Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
        ≤ Real.sqrt (2 * (x : ℝ) + 4 * (T : ℝ) ^ 2) := Real.sqrt_le_sqrt hMN
    have h2 : Real.sqrt (2 * (x : ℝ) + 4 * (T : ℝ) ^ 2)
        ≤ Real.sqrt (2 * (x : ℝ)) + Real.sqrt (4 * (T : ℝ) ^ 2) := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * (x:ℝ)),
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ 4 * (T:ℝ)^2),
        Real.sqrt_nonneg (2 * (x:ℝ)), Real.sqrt_nonneg (4 * (T:ℝ)^2)]
    have h3 : Real.sqrt (4 * (T : ℝ) ^ 2) = 2 * (T : ℝ) := by
      rw [show (4 : ℝ) * (T : ℝ) ^ 2 = (2 * (T:ℝ))^2 by ring, Real.sqrt_sq (by positivity)]
    have h4 : Real.sqrt (2 * (x : ℝ)) = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
    rw [h4, h3] at h2
    rw [h5]
    have h6 : Real.sqrt ((2 : ℝ) ^ (j + 1))
          * Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
        ≤ (Real.sqrt 2 * (T : ℝ)) * (Real.sqrt 2 * Real.sqrt x + 2 * (T : ℝ)) :=
      mul_le_mul hM (le_trans h1 h2) (by positivity) (by positivity)
    have h7 : (Real.sqrt 2 * (T : ℝ)) * (Real.sqrt 2 * Real.sqrt x + 2 * (T : ℝ))
        ≤ 2 * (T : ℝ) * Real.sqrt x + 4 * Real.sqrt 2 * (T : ℝ) ^ 2 := by
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      have h1 : (Real.sqrt 2 * (T : ℝ)) * (Real.sqrt 2 * Real.sqrt x + 2 * (T : ℝ))
          = (Real.sqrt 2 * Real.sqrt 2) * (T : ℝ) * Real.sqrt x
            + 2 * Real.sqrt 2 * (T : ℝ) ^ 2 := by ring
      rw [h1, hsq2]
      nlinarith [Real.sqrt_nonneg (2:ℝ), (show (0:ℝ) ≤ (T:ℝ) by positivity), sq_nonneg (T:ℝ),
        mul_nonneg (Real.sqrt_nonneg (2:ℝ)) (sq_nonneg (T:ℝ))]
    linarith [h6, h7]
  calc (∑ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
        (2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
      ≤ ∑ _j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
          (2 * (T : ℝ) * Real.sqrt x + 4 * Real.sqrt 2 * (T : ℝ) ^ 2) := Finset.sum_le_sum hpt
    _ = (((Finset.range J).filter (fun j => (T + 1).log2 ≤ j)).card : ℝ)
          * (2 * (T : ℝ) * Real.sqrt x + 4 * Real.sqrt 2 * (T : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (J : ℝ) * (2 * (T : ℝ) * Real.sqrt x + 4 * Real.sqrt 2 * (T : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_right (filtered_card_le J _)
        have : (0:ℝ) ≤ 2 * (T : ℝ) * Real.sqrt x := by positivity
        have hsq : (0:ℝ) ≤ 4 * Real.sqrt 2 * (T:ℝ)^2 := by positivity
        linarith
    _ = (2 * (T : ℝ) * Real.sqrt x + 4 * Real.sqrt 2 * (T : ℝ) ^ 2) * (J : ℝ) := by ring

lemma blk_N_sqrtM_filtered_le (x T J : ℕ) (hT : 1 ≤ T) (h2J : (2 : ℝ) ^ J ≤ 2 * (T : ℝ) ^ 2) :
    (∑ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
        ((((x / 2 ^ j : ℕ)) : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1)))
      ≤ 2 * (x : ℝ) * (J : ℝ) / Real.sqrt ((T : ℝ) + 1) + 8 * (T : ℝ) := by
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpt : ∀ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
      ((((x / 2 ^ j : ℕ)) : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1))
        ≤ Real.sqrt 2 * x * ((Real.sqrt 2) ^ j)⁻¹ + Real.sqrt 2 * (Real.sqrt 2) ^ j := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have h1 : ((((x / 2 ^ j : ℕ)) : ℝ) + 1) ≤ (x : ℝ) / (2 : ℝ) ^ j + 1 := by
      have h : (((x / 2 ^ j : ℕ)) : ℝ) ≤ (x : ℝ) / (((2 ^ j : ℕ)) : ℝ) := Nat.cast_div_le
      rw [Nat.cast_pow] at h
      linarith
    have h2 := sqrt_two_pow_eq_sqrt j
    have h3 : ((((x / 2 ^ j : ℕ)) : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1))
        ≤ ((x : ℝ) / (2 : ℝ) ^ j + 1) * (Real.sqrt 2 * (Real.sqrt 2) ^ j) := by
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have h4 : ((x : ℝ) / (2 : ℝ) ^ j + 1) * (Real.sqrt 2 * (Real.sqrt 2) ^ j)
        = Real.sqrt 2 * x * ((Real.sqrt 2) ^ j)⁻¹ + Real.sqrt 2 * (Real.sqrt 2) ^ j := by
      have hA : ((Real.sqrt 2) ^ j) ≠ 0 := by positivity
      rw [show (2 : ℝ) ^ j = ((Real.sqrt 2) ^ j)^2 by rw [sqrt_two_pow_sq]]
      field_simp
    linarith [h3, h4.le]
  have hfinal := filtered_sum_inv_le J ((T+1).log2) (Real.sqrt 2 * x) (Real.sqrt 2)
    (by positivity) (by positivity) (Real.sqrt 2) hs2 (sum_range_sqrt_two_pow_le J)
  calc (∑ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
        ((((x / 2 ^ j : ℕ)) : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1)))
      ≤ ∑ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
          (Real.sqrt 2 * x * ((Real.sqrt 2) ^ j)⁻¹ + Real.sqrt 2 * (Real.sqrt 2) ^ j) :=
        Finset.sum_le_sum hpt
    _ ≤ Real.sqrt 2 * x * ((J : ℝ) * (((Real.sqrt 2) ^ ((T + 1).log2))⁻¹))
          + Real.sqrt 2 * (4 * (Real.sqrt 2) ^ J) := hfinal
    _ ≤ 2 * (x : ℝ) * (J : ℝ) / Real.sqrt ((T : ℝ) + 1) + 8 * (T : ℝ) := by
        have hinv : ((Real.sqrt 2) ^ ((T + 1).log2))⁻¹ ≤ Real.sqrt 2 / Real.sqrt ((T : ℝ) + 1) :=
          inv_sqrt_two_pow_log2_le T hT
        have hsJ := sqrt_two_pow_J_le T J h2J
        have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
        have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
        have hposT : (0 : ℝ) < Real.sqrt ((T:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
        have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        have h1 : Real.sqrt 2 * x * ((J : ℝ) * (((Real.sqrt 2) ^ ((T + 1).log2))⁻¹))
            ≤ Real.sqrt 2 * x * ((J : ℝ) * (Real.sqrt 2 / Real.sqrt ((T:ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left _
          · positivity
          · exact mul_le_mul_of_nonneg_left hinv hJ0
        have h2 : Real.sqrt 2 * x * ((J : ℝ) * (Real.sqrt 2 / Real.sqrt ((T:ℝ) + 1)))
            = 2 * x * (J : ℝ) / Real.sqrt ((T:ℝ) + 1) := by
          have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
          have h1 : Real.sqrt 2 * x * ((J : ℝ) * (Real.sqrt 2 / Real.sqrt ((T:ℝ) + 1)))
              = (Real.sqrt 2 * Real.sqrt 2) * x * (J : ℝ) / Real.sqrt ((T:ℝ) + 1) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
          rw [h1, hsq2]
        have h3 : Real.sqrt 2 * (4 * (Real.sqrt 2) ^ J) ≤ 8 * (T : ℝ) := by
          have h4 : (0:ℝ) ≤ 4 := by norm_num
          have hlt := mul_le_mul_of_nonneg_left hsJ h4
          have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
          nlinarith [hlt]
        linarith [h1, h2.le, h2.ge, h3]

lemma blk_sqrtMN_filtered_le (x T J : ℕ) (hT : 1 ≤ T) (h2J : (2 : ℝ) ^ J ≤ 2 * (T : ℝ) ^ 2) :
    (∑ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
        Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)))
      ≤ Real.sqrt 2 * Real.sqrt x * (J : ℝ) + 8 * (T : ℝ) := by
  have hpt : ∀ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
      Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
        ≤ Real.sqrt 2 * Real.sqrt x + Real.sqrt 2 * (Real.sqrt 2) ^ j := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hjlt : j < J := Finset.mem_range.mp hj.1
    have hMN := blk_MN_le_sharp x T J j hjlt h2J
    have h1 : Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
        ≤ Real.sqrt (2 * (x : ℝ) + (2 : ℝ) ^ (j + 1)) := Real.sqrt_le_sqrt hMN
    have h2 : Real.sqrt (2 * (x : ℝ) + (2 : ℝ) ^ (j + 1))
        ≤ Real.sqrt (2 * (x : ℝ)) + Real.sqrt ((2 : ℝ) ^ (j + 1)) := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * (x:ℝ)),
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ (2:ℝ)^(j+1)),
        Real.sqrt_nonneg (2 * (x:ℝ)), Real.sqrt_nonneg ((2:ℝ)^(j+1))]
    have h3 : Real.sqrt (2 * (x : ℝ)) = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
    have h4 := sqrt_two_pow_eq_sqrt j
    rw [h3, h4] at h2
    linarith [h1, h2]
  have hfinal := filtered_sum_le J ((T+1).log2) (Real.sqrt 2 * Real.sqrt x) (Real.sqrt 2)
    (by positivity) (by positivity) (Real.sqrt 2) (Real.sqrt_nonneg 2) (sum_range_sqrt_two_pow_le J)
  calc (∑ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
        Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)))
      ≤ ∑ j ∈ (Finset.range J).filter (fun j => (T + 1).log2 ≤ j),
          (Real.sqrt 2 * Real.sqrt x + Real.sqrt 2 * (Real.sqrt 2) ^ j) :=
        Finset.sum_le_sum hpt
    _ ≤ Real.sqrt 2 * Real.sqrt x * (J : ℝ) + Real.sqrt 2 * (4 * (Real.sqrt 2) ^ J) := hfinal
    _ ≤ Real.sqrt 2 * Real.sqrt x * (J : ℝ) + 8 * (T : ℝ) := by
        have hsJ := sqrt_two_pow_J_le T J h2J
        have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        nlinarith [hsJ, hs2, hsq2, Real.sqrt_nonneg x, (show (0:ℝ) ≤ (T:ℝ) by positivity)]


lemma blk_one_le (j : ℕ) : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow

lemma blk_N_one_le (x j : ℕ) : 1 ≤ x / 2 ^ j + 1 := Nat.le_add_left 1 _

lemma blk_x_le_MN (x j : ℕ) : x ≤ 2 ^ (j + 1) * (x / 2 ^ j + 1) := by
  have hmod : x % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
  have hdec : x = 2 ^ j * (x / 2 ^ j) + x % 2 ^ j := by
    have h := Nat.div_add_mod x (2 ^ j)
    exact h.symm.trans (by ring)
  have h1 : x < 2 ^ j * (x / 2 ^ j + 1) := by
    calc x = 2 ^ j * (x / 2 ^ j) + x % 2 ^ j := hdec
      _ < 2 ^ j * (x / 2 ^ j) + 2 ^ j := Nat.add_lt_add_left hmod _
      _ = 2 ^ j * (x / 2 ^ j + 1) := by rw [mul_add, mul_one]
  have h2 : 2 ^ j * (x / 2 ^ j + 1) ≤ 2 ^ (j + 1) * (x / 2 ^ j + 1) :=
    Nat.mul_le_mul_right _ (by rw [pow_succ]; omega)
  omega

/-- The bilinear large sieve applied to a dyadic block of the third Vaughan piece. -/
lemma S3''_blk_le (T Q x j : ℕ) (hQ : 1 ≤ Q) (hx : 1 ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ ∈ primChars q,
        sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)),
            ∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
              (if t * r ≤ y then (1 : ℂ) else 0) * aBlk T j t * (1 : ℂ)
                * χ ((t * r : ℕ) : ZMod q)‖) '' Set.Icc 1 x))
      ≤ cBil
          * Real.sqrt (((2 : ℝ) ^ (j + 1) + (Q : ℝ) ^ 2)
              * ((2 : ℝ) ^ (j + 1) * (Real.log (2 * (2 : ℝ) ^ (j + 1) + 2)) ^ 2))
          * Real.sqrt (((((x / 2 ^ j + 1 : ℕ)) : ℝ) + (Q : ℝ) ^ 2)
              * (((x / 2 ^ j + 1 : ℕ)) : ℝ))
          * Real.log (2 * (2 : ℝ) ^ (j + 1) * (((x / 2 ^ j + 1 : ℕ)) : ℝ) + 2) := by
  have hM : 1 ≤ 2 ^ (j + 1) := blk_one_le j
  have hN : 1 ≤ x / 2 ^ j + 1 := blk_N_one_le x j
  have hxMN : x ≤ 2 ^ (j + 1) * (x / 2 ^ j + 1) := blk_x_le_MN x j
  have h := cBil_spec_lower Q (2 ^ (j + 1)) (x / 2 ^ j + 1) x hQ hM hN hx hxMN
    (aBlk T j) (fun _ => (1 : ℂ))
  refine le_trans h ?_
  have hA : (∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)), ‖aBlk T j t‖ ^ 2)
      ≤ ((2 : ℝ) ^ (j + 1)) * (Real.log (2 * (2 : ℝ) ^ (j + 1) + 2)) ^ 2 := by
    calc (∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)), ‖aBlk T j t‖ ^ 2)
        ≤ ∑ _t ∈ Finset.Icc 1 (2 ^ (j + 1)),
            (Real.log (2 * (2 : ℝ) ^ (j + 1) + 2)) ^ 2 := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          rw [Finset.mem_Icc] at ht
          by_cases hb : t ∈ blk T j
          · rw [aBlk, if_pos hb]
            have h1 : ‖aT T t‖ ≤ Real.log (2 * (t : ℝ) + 2) := norm_aT_le T t ht.1
            have h2 : Real.log (2 * (t : ℝ) + 2) ≤ Real.log (2 * (2 : ℝ) ^ (j + 1) + 2) := by
              apply Real.log_le_log (by positivity)
              have : (t : ℝ) ≤ ((2 : ℝ) ^ (j + 1)) := by
                have := ht.2
                exact_mod_cast this
              linarith
            exact pow_le_pow_left₀ (norm_nonneg _) (le_trans h1 h2) 2
          · rw [aBlk, if_neg hb]
            simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              zero_pow]
            positivity
      _ = ((2 : ℝ) ^ (j + 1)) * (Real.log (2 * (2 : ℝ) ^ (j + 1) + 2)) ^ 2 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          norm_num
  have hB : (∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1), ‖(1 : ℂ)‖ ^ 2)
      = (((x / 2 ^ j + 1 : ℕ)) : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    norm_num
  have hsq1 : Real.sqrt (((2 : ℝ) ^ (j + 1) + (Q : ℝ) ^ 2)
        * (∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)), ‖aBlk T j t‖ ^ 2))
      ≤ Real.sqrt (((2 : ℝ) ^ (j + 1) + (Q : ℝ) ^ 2)
        * ((2 : ℝ) ^ (j + 1) * (Real.log (2 * (2 : ℝ) ^ (j + 1) + 2)) ^ 2)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have hsq2 : Real.sqrt (((((x / 2 ^ j + 1 : ℕ)) : ℝ) + (Q : ℝ) ^ 2)
        * (∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1), ‖(1 : ℂ)‖ ^ 2))
      ≤ Real.sqrt (((((x / 2 ^ j + 1 : ℕ)) : ℝ) + (Q : ℝ) ^ 2)
        * (((x / 2 ^ j + 1 : ℕ)) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    rw [hB]
  have hlog : Real.log (2 * ((2 : ℝ) ^ (j + 1)) * (((x / 2 ^ j + 1 : ℕ)) : ℝ) + 2)
      = Real.log (2 * (2 : ℝ) ^ (j + 1) * (((x / 2 ^ j + 1 : ℕ)) : ℝ) + 2) := by
    ring_nf
  rw [Nat.cast_pow, hlog]
  have hcB : (0 : ℝ) ≤ cBil := cBil_pos.le
  have hs1 : (0 : ℝ) ≤ Real.sqrt (((2 : ℝ) ^ (j + 1) + (Q : ℝ) ^ 2)
        * (∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)), ‖aBlk T j t‖ ^ 2)) := Real.sqrt_nonneg _
  have hs2 : (0 : ℝ) ≤ Real.sqrt (((((x / 2 ^ j + 1 : ℕ)) : ℝ) + (Q : ℝ) ^ 2)
        * (∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1), ‖(1 : ℂ)‖ ^ 2)) := Real.sqrt_nonneg _
  have hlg : (0 : ℝ) ≤ Real.log (2 * (2 : ℝ) ^ (j + 1)
        * (((x / 2 ^ j + 1 : ℕ)) : ℝ) + 2) := by
    apply Real.log_nonneg
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by positivity
    have h2 : (0 : ℝ) ≤ (((x / 2 ^ j + 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h1 h2]
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hsq1 hcB) hsq2 hs2
      (mul_nonneg hcB (Real.sqrt_nonneg _))) le_rfl hlg (by positivity)


/-- The pointwise rearrangement of `S3''` into a sum of dyadic block bilinear forms. -/
lemma S3''_pointwise (T q : ℕ) (hT : 1 ≤ T) (χ : DirichletCharacter ℂ q) (x y : ℕ)
    (hy : y ∈ Set.Icc 1 x) :
    ‖S3'' T q χ y‖
      ≤ ∑ j ∈ Finset.range ((T * T).log2 + 1),
          ‖∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)),
              ∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
                (if t * r ≤ y then (1 : ℂ) else 0) * aBlk T j t * (1 : ℂ)
                  * χ ((t * r : ℕ) : ZMod q)‖ := by
  rw [S3''_as_blockSum T q hT χ y]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  have heq : (∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)),
        aBlk T j t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)))
      = ∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)), ∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
          (if t * r ≤ y then (1 : ℂ) else 0) * aBlk T j t * (1 : ℂ)
            * χ ((t * r : ℕ) : ZMod q) :=
    Finset.sum_congr rfl (fun t ht => S3''_blk_term T j q hT χ x y t hy.2 ht)
  rw [heq]

/-- For `j < (T+1).log2` the block is empty, hence every term vanishes. -/
lemma S3''_blk_zero_of_lt (T q : ℕ) (hT : 1 ≤ T) (χ : DirichletCharacter ℂ q) (x y j : ℕ)
    (hj : j < (T + 1).log2) :
    (∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)),
        ∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
          (if t * r ≤ y then (1 : ℂ) else 0) * aBlk T j t * (1 : ℂ)
            * χ ((t * r : ℕ) : ZMod q)) = 0 := by
  refine Finset.sum_eq_zero (fun t _ => ?_)
  refine Finset.sum_eq_zero (fun r _ => ?_)
  have hz : aBlk T j t = 0 := by
    rw [aBlk, if_neg]
    intro hb
    rw [mem_blk] at hb
    have hlt : t < 2 ^ (j + 1) := ((Nat.log2_eq_iff (by omega : t ≠ 0)).mp hb.2.2).2
    have h2 : 2 ^ (j + 1) ≤ 2 ^ ((T + 1).log2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : 2 ^ ((T + 1).log2) ≤ T + 1 := two_pow_log2_le (T + 1) (by omega)
    omega
  rw [hz]
  ring

/-- `√(M + Q²) ≤ √M + Q` for `M, Q ≥ 0`. -/
lemma sqrt_add_sq_le {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 ≤ Q) :
    Real.sqrt (M + Q ^ 2) ≤ Real.sqrt M + Q := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hM, Real.sqrt_nonneg M, hQ]

/-- The algebraic core of the blockwise bound: after expanding the two square roots and
using `√(M + Q²) ≤ √M + Q`, `√(N + Q²) ≤ √N + Q`, `L1 ≤ 2L`, `L2 ≤ 4L`, the expression
is bounded by `8L²(MN + Q·M√N + Q·N√M + Q²√(MN))`. -/
lemma blk_algebra {M N Q L L1 L2 : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hQ : 0 ≤ Q)
    (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) (hL : 0 ≤ L)
    (h2L : L1 ≤ 2 * L) (h4L : L2 ≤ 4 * L) :
    Real.sqrt (M + Q ^ 2) * Real.sqrt (M * L1 ^ 2) * Real.sqrt (N + Q ^ 2)
        * Real.sqrt N * L2
      ≤ 8 * L ^ 2 * (M * N + Q * (M * Real.sqrt N) + Q * (N * Real.sqrt M)
          + Q ^ 2 * Real.sqrt (M * N)) := by
  have hsM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hMQ : Real.sqrt (M + Q ^ 2) ≤ Real.sqrt M + Q := sqrt_add_sq_le hM hQ
  have hNQ : Real.sqrt (N + Q ^ 2) ≤ Real.sqrt N + Q := sqrt_add_sq_le hN hQ
  have hsqL1 : Real.sqrt (M * L1 ^ 2) = Real.sqrt M * L1 := by
    rw [Real.sqrt_mul hM (L1 ^ 2), Real.sqrt_sq hL1]
  have hMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
  have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN
  have hMNsq : Real.sqrt (M * N) = Real.sqrt M * Real.sqrt N := Real.sqrt_mul hM N
  have hA : Real.sqrt (M + Q ^ 2) * Real.sqrt M * L1
      ≤ (Real.sqrt M + Q) * Real.sqrt M * (2 * L) := by
    calc Real.sqrt (M + Q ^ 2) * Real.sqrt M * L1
        = (Real.sqrt (M + Q ^ 2) * Real.sqrt M) * L1 := by ring
      _ ≤ ((Real.sqrt M + Q) * Real.sqrt M) * (2 * L) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hMQ hsM) h2L hL1 (by positivity)
  have hB : Real.sqrt (N + Q ^ 2) * Real.sqrt N ≤ (Real.sqrt N + Q) * Real.sqrt N :=
    mul_le_mul_of_nonneg_right hNQ hsN
  have hAB : Real.sqrt (M + Q ^ 2) * Real.sqrt M * L1
        * (Real.sqrt (N + Q ^ 2) * Real.sqrt N)
      ≤ ((Real.sqrt M + Q) * Real.sqrt M * (2 * L)) * ((Real.sqrt N + Q) * Real.sqrt N) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have hAB2 : Real.sqrt (M + Q ^ 2) * Real.sqrt M * L1
        * (Real.sqrt (N + Q ^ 2) * Real.sqrt N) * L2
      ≤ ((Real.sqrt M + Q) * Real.sqrt M * (2 * L))
        * ((Real.sqrt N + Q) * Real.sqrt N) * (4 * L) :=
    mul_le_mul hAB h4L hL2 (by positivity)
  have e3 : ((Real.sqrt M + Q) * Real.sqrt M) * ((Real.sqrt N + Q) * Real.sqrt N)
      = M * N + Q * (M * Real.sqrt N) + Q * (N * Real.sqrt M)
        + Q ^ 2 * (Real.sqrt M * Real.sqrt N) := by
    rw [show ((Real.sqrt M + Q) * Real.sqrt M) * ((Real.sqrt N + Q) * Real.sqrt N)
        = (Real.sqrt M * Real.sqrt M) * (Real.sqrt N * Real.sqrt N)
          + Q * ((Real.sqrt M * Real.sqrt M) * Real.sqrt N)
          + Q * ((Real.sqrt N * Real.sqrt N) * Real.sqrt M)
          + Q * Q * (Real.sqrt M * Real.sqrt N) by ring,
      hMM, hNN]
    ring
  calc Real.sqrt (M + Q ^ 2) * Real.sqrt (M * L1 ^ 2) * Real.sqrt (N + Q ^ 2)
        * Real.sqrt N * L2
      = Real.sqrt (M + Q ^ 2) * Real.sqrt M * L1
        * (Real.sqrt (N + Q ^ 2) * Real.sqrt N) * L2 := by rw [hsqL1]; ring
    _ ≤ ((Real.sqrt M + Q) * Real.sqrt M * (2 * L))
        * ((Real.sqrt N + Q) * Real.sqrt N) * (4 * L) := hAB2
    _ = 8 * L ^ 2 * (((Real.sqrt M + Q) * Real.sqrt M)
        * ((Real.sqrt N + Q) * Real.sqrt N)) := by ring
    _ = 8 * L ^ 2 * (M * N + Q * (M * Real.sqrt N) + Q * (N * Real.sqrt M)
          + Q ^ 2 * (Real.sqrt M * Real.sqrt N)) := by rw [e3]
    _ = 8 * L ^ 2 * (M * N + Q * (M * Real.sqrt N) + Q * (N * Real.sqrt M)
          + Q ^ 2 * Real.sqrt (M * N)) := by rw [hMNsq]

/-- The blockwise bound with the logarithmic factors evaluated. -/
lemma S3''_blk_le2 (T Q x j : ℕ) (hT : 1 ≤ T) (hQ : 2 ≤ Q) (hx : 2 ≤ x)
    (hTx : (T : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ)) (hj : j ∈ Finset.range ((T * T).log2 + 1)) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ ∈ primChars q,
        sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)),
            ∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
              (if t * r ≤ y then (1 : ℂ) else 0) * aBlk T j t * (1 : ℂ)
                * χ ((t * r : ℕ) : ZMod q)‖) '' Set.Icc 1 x))
      ≤ 8 * (mainLog x Q) ^ 2 * cBil *
          ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
            + (Q : ℝ) * ((2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
            + (Q : ℝ) * (((((x / 2 ^ j : ℕ)) : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1)))
            + (Q : ℝ) ^ 2 * Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))) := by
  have hx1 : (1 : ℕ) ≤ x := by omega
  have hsb := S3''_blk_le T Q x j (by omega) hx1
  have hL1 := blk_l1_le T x Q hT hQ hx hTx j hj
  have hL2 := blk_l2_le T x Q hT hQ hx hTx j hj
  have hNcast : (((x / 2 ^ j + 1 : ℕ)) : ℝ) = ((((x / 2 ^ j : ℕ)) : ℝ) + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hNcast] at hsb
  have hMnn : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by positivity
  have hNnn : (0 : ℝ) ≤ ((((x / 2 ^ j : ℕ)) : ℝ) + 1) := by positivity
  have hQnn : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hL1nn : (0 : ℝ) ≤ Real.log (2 * (2 : ℝ) ^ (j + 1) + 2) := by
    apply Real.log_nonneg; nlinarith [hMnn]
  have hL2nn : (0 : ℝ) ≤ Real.log (2 * (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) + 2) := by
    apply Real.log_nonneg
    have h0 : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) := by positivity
    linarith
  have hML : (0 : ℝ) ≤ mainLog x Q := le_trans (by norm_num) (mainLog_ge_one hx (by omega))
  have hcore := blk_algebra (M := (2 : ℝ) ^ (j + 1)) (N := ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
    (Q := (Q : ℝ)) (L := mainLog x Q) (L1 := Real.log (2 * (2 : ℝ) ^ (j + 1) + 2))
    (L2 := Real.log (2 * (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) + 2))
    hMnn hNnn hQnn hL1nn hL2nn hML hL1 hL2
  have hX : Real.sqrt (((2 : ℝ) ^ (j + 1) + (Q : ℝ) ^ 2)
        * ((2 : ℝ) ^ (j + 1) * (Real.log (2 * (2 : ℝ) ^ (j + 1) + 2)) ^ 2))
      = Real.sqrt ((2 : ℝ) ^ (j + 1) + (Q : ℝ) ^ 2)
        * Real.sqrt ((2 : ℝ) ^ (j + 1) * (Real.log (2 * (2 : ℝ) ^ (j + 1) + 2)) ^ 2) :=
    Real.sqrt_mul (by positivity) _
  have hY : Real.sqrt ((((((x / 2 ^ j : ℕ)) : ℝ) + 1) + (Q : ℝ) ^ 2)
        * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
      = Real.sqrt (((((x / 2 ^ j : ℕ)) : ℝ) + 1) + (Q : ℝ) ^ 2)
        * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1) :=
    Real.sqrt_mul (by positivity) _
  refine le_trans hsb ?_
  calc cBil * Real.sqrt (((2 : ℝ) ^ (j + 1) + (Q : ℝ) ^ 2)
          * ((2 : ℝ) ^ (j + 1) * (Real.log (2 * (2 : ℝ) ^ (j + 1) + 2)) ^ 2))
        * Real.sqrt (((((x / 2 ^ j : ℕ)) : ℝ) + 1 + (Q : ℝ) ^ 2)
            * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
        * Real.log (2 * (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) + 2)
      = cBil * (Real.sqrt ((2 : ℝ) ^ (j + 1) + (Q : ℝ) ^ 2)
          * Real.sqrt ((2 : ℝ) ^ (j + 1) * (Real.log (2 * (2 : ℝ) ^ (j + 1) + 2)) ^ 2)
          * Real.sqrt (((((x / 2 ^ j : ℕ)) : ℝ) + 1) + (Q : ℝ) ^ 2)
          * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
          * Real.log (2 * (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1) + 2)) := by
        rw [hX, hY]; ring
    _ ≤ cBil * (8 * (mainLog x Q) ^ 2
          * ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
            + (Q : ℝ) * ((2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
            + (Q : ℝ) * (((((x / 2 ^ j : ℕ)) : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1)))
            + (Q : ℝ) ^ 2 * Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left hcore cBil_pos.le
    _ = 8 * (mainLog x Q) ^ 2 * cBil *
          ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
            + (Q : ℝ) * ((2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
            + (Q : ℝ) * (((((x / 2 ^ j : ℕ)) : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1)))
            + (Q : ℝ) ^ 2 * Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))) := by
        ring


/-! ## Auxiliary estimates for the dyadic blocks of `S₃''` -/

lemma mem_filter_range {J : ℕ} {p : ℕ → Prop} [DecidablePred p] {j : ℕ}
    (hj : j ∈ (Finset.range J).filter p) : j ∈ Finset.range J :=
  (Finset.mem_filter.mp hj).1

lemma mem_filter_range' {J : ℕ} {p : ℕ → Prop} [DecidablePred p] {j : ℕ}
    (hj : j ∈ (Finset.range J).filter p) : j < J :=
  Finset.mem_range.mp (Finset.mem_filter.mp hj).1

/-- The number of dyadic blocks below `T * T` is at most `8 log(xQ+2)`. -/
lemma blk_J_le (T x Q : ℕ) (hT : 1 ≤ T) (hx : 1 ≤ x) (hQ : 1 ≤ Q)
    (hTx : (T : ℝ) ≤ (x : ℝ)) :
    (((T * T).log2 + 1 : ℕ) : ℝ) ≤ 8 * mainLog x Q := by
  have hL1 : (1 : ℝ) ≤ mainLog x Q := by
    show (1 : ℝ) ≤ Real.log ((x : ℝ) * (Q : ℝ) + 2)
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h3 : (3 : ℝ) ≤ (x : ℝ) * (Q : ℝ) + 2 := by
      have h1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
      have h2 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      nlinarith
    linarith [Real.exp_one_lt_three]
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ge : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT0 : (0 : ℝ) ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT)
  have hLT : Real.log (T : ℝ) ≤ mainLog x Q := by
    show Real.log (T : ℝ) ≤ Real.log ((x : ℝ) * (Q : ℝ) + 2)
    apply Real.log_le_log hT0
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have h2 : (0 : ℝ) ≤ (x : ℝ) := by positivity
    have h3 : (x : ℝ) ≤ (x : ℝ) * (Q : ℝ) + 2 := by nlinarith
    linarith [hTx, h3]
  have hmain := log2_le_log_div_log_two (T * T) (by have := Nat.mul_le_mul hT hT; simpa using this)
  have hlogmul : Real.log (((T * T : ℕ)) : ℝ) = 2 * Real.log (T : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (ne_of_gt hT0) (ne_of_gt hT0)]
    ring
  rw [hlogmul] at hmain
  have hstep : 2 * Real.log (T : ℝ) / Real.log 2 ≤ 3 * Real.log (T : ℝ) := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [hlog2ge, hlogT0, mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * Real.log 2 - 2) hlogT0]
  have hcast : (((T * T).log2 + 1 : ℕ) : ℝ) = ((T * T).log2 : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hcast]
  linarith [hmain, hstep, hLT, hL1]

/-- A `S₃''`-type bound on `xQ/√(T+1)` when `T` is comparable to `min(x^{1/3}, x^{2/3}/Q)`. -/
lemma domino_x_Q_invsqrtT {x Q T : ℕ} (hx : 2 ≤ x) (hQ : 2 ≤ Q)
    (hmin : min ((x : ℝ) ^ (1 / 3 : ℝ)) ((x : ℝ) ^ (2 / 3 : ℝ) / (Q : ℝ)) ≤ 2 * (T : ℝ)) :
    (x : ℝ) * (Q : ℝ) / Real.sqrt ((T : ℝ) + 1) ≤ 2 * mainBracket x Q := by
  have hx0 : (0 : ℝ) < (x : ℝ) := by positivity
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by positivity
  have hx1r : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  set a : ℝ := (x : ℝ) ^ (1 / 3 : ℝ) with hadef
  set b : ℝ := (x : ℝ) ^ (2 / 3 : ℝ) / (Q : ℝ) with hbdef
  have ha0 : 0 < a := by rw [hadef]; exact Real.rpow_pos_of_pos hx0 _
  have hb0 : 0 < b := by rw [hbdef]; positivity
  have hminpos : 0 < min a b := lt_min ha0 hb0
  have hTmin : min a b / 2 ≤ (T : ℝ) := by linarith [hmin]
  have hstep1 : (x : ℝ) * (Q : ℝ) / Real.sqrt ((T : ℝ) + 1)
      ≤ (x : ℝ) * (Q : ℝ) / Real.sqrt (min a b / 2) := by
    refine div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr (by linarith))
      (Real.sqrt_le_sqrt (by linarith))
  have hsqrtdiv : Real.sqrt (min a b / 2) = Real.sqrt (min a b) / Real.sqrt 2 :=
    Real.sqrt_div (le_of_lt hminpos) 2
  have hstep2 : (x : ℝ) * (Q : ℝ) / Real.sqrt (min a b / 2)
      = Real.sqrt 2 * ((x : ℝ) * (Q : ℝ) / Real.sqrt (min a b)) := by
    rw [hsqrtdiv]
    have hm : (Real.sqrt (min a b)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hminpos)
    have h2 : (Real.sqrt 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  have hstep3 : 1 / Real.sqrt (min a b) ≤ 1 / Real.sqrt a + 1 / Real.sqrt b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h]
      have : 0 < 1 / Real.sqrt b := one_div_pos.mpr (Real.sqrt_pos.mpr hb0)
      linarith
    · rw [min_eq_right h]
      have : 0 < 1 / Real.sqrt a := one_div_pos.mpr (Real.sqrt_pos.mpr ha0)
      linarith
  have hstep4 : Real.sqrt 2 * ((x : ℝ) * (Q : ℝ) / Real.sqrt (min a b))
      ≤ Real.sqrt 2 * ((x : ℝ) * (Q : ℝ) * (1 / Real.sqrt a + 1 / Real.sqrt b)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2)
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hstep3 (by positivity)
  have hsqrt_a : Real.sqrt a = (x : ℝ) ^ (1 / 6 : ℝ) := by
    rw [hadef, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hx0)]
    norm_num
  have hsqrt_b : Real.sqrt b = (x : ℝ) ^ (1 / 3 : ℝ) / Real.sqrt (Q : ℝ) := by
    rw [hbdef, Real.sqrt_div (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hx0)]
    norm_num
  have hx56 : (x : ℝ) / (x : ℝ) ^ (1 / 6 : ℝ) = (x : ℝ) ^ (5 / 6 : ℝ) := by
    rw [div_eq_iff (ne_of_gt (by positivity : (0 : ℝ) < (x : ℝ) ^ (1 / 6 : ℝ)))]
    rw [← Real.rpow_add hx0, show (5 : ℝ) / 6 + 1 / 6 = 1 by norm_num, Real.rpow_one]
  have hx23 : (x : ℝ) / (x : ℝ) ^ (1 / 3 : ℝ) = (x : ℝ) ^ (2 / 3 : ℝ) := by
    rw [div_eq_iff (ne_of_gt (by positivity : (0 : ℝ) < (x : ℝ) ^ (1 / 3 : ℝ)))]
    rw [← Real.rpow_add hx0, show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num, Real.rpow_one]
  have hQ32 : (Q : ℝ) * Real.sqrt (Q : ℝ) = (Q : ℝ) ^ (3 / 2 : ℝ) := by
    have h := Real.rpow_add hQ0 (1 : ℝ) (1 / 2 : ℝ)
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, Real.rpow_one, ← Real.sqrt_eq_rpow] at h
    exact h.symm
  have hQne : Real.sqrt (Q : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ0)
  have hxne : (x : ℝ) ^ (1 / 3 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx0 _)
  have e1 : (x : ℝ) * (Q : ℝ) / Real.sqrt a = (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) := by
    rw [hsqrt_a]
    rw [show (x : ℝ) * (Q : ℝ) / (x : ℝ) ^ (1 / 6 : ℝ)
        = ((x : ℝ) / (x : ℝ) ^ (1 / 6 : ℝ)) * (Q : ℝ) by ring, hx56]
  have e2 : (x : ℝ) * (Q : ℝ) / Real.sqrt b
      = (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) := by
    rw [hsqrt_b]
    rw [show (x : ℝ) * (Q : ℝ) / ((x : ℝ) ^ (1 / 3 : ℝ) / Real.sqrt (Q : ℝ))
        = ((x : ℝ) / (x : ℝ) ^ (1 / 3 : ℝ)) * ((Q : ℝ) * Real.sqrt (Q : ℝ)) by
      field_simp]
    rw [hx23, hQ32]
  have hstep5 : Real.sqrt 2 * ((x : ℝ) * (Q : ℝ) * (1 / Real.sqrt a + 1 / Real.sqrt b))
      ≤ 2 * ((x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ)
        + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)) := by
    rw [mul_add, mul_one_div, mul_one_div, e1, e2]
    have h1 : (0 : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (le_of_lt hQ0)
    have h2 : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (Real.rpow_nonneg (le_of_lt hQ0) _)
    have h3 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [h1, h2, h3]
  have hbr : (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)
      ≤ mainBracket x Q := by
    have h0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hx0
    have h1 : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2 := by positivity
    simp only [mainBracket]
    linarith
  linarith [hstep1, hstep2.le, hstep4, hstep5, hbr]

/-- The supremum over `y ≤ x` of a dyadic block of `S₃''`. -/
def blkSup (T q x j : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)),
      ∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
        (if t * r ≤ y then (1 : ℂ) else 0) * aBlk T j t * (1 : ℂ)
          * χ ((t * r : ℕ) : ZMod q)‖) '' Set.Icc 1 x)

/-- The explicit bound for the `j`-th dyadic block. -/
def blkTerm (x Q j : ℕ) : ℝ :=
  (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
    + (Q : ℝ) * ((2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
    + (Q : ℝ) * (((((x / 2 ^ j : ℕ)) : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1)))
    + (Q : ℝ) ^ 2 * Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))

set_option maxHeartbeats 1000000 in
/-- The total of the four dyadic block sums for `S₃''`. -/
lemma S3''_blkSum_le (T Q x : ℕ) (hT : 1 ≤ T) (hQ : 2 ≤ Q) (hx : 2 ≤ x)
    (hTx : (T : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ))
    (hTQ : (T : ℝ) * (Q : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ))
    (hmin : min ((x : ℝ) ^ (1 / 3 : ℝ)) ((x : ℝ) ^ (2 / 3 : ℝ) / (Q : ℝ)) ≤ 2 * (T : ℝ)) :
    (∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j), blkTerm x Q j)
      ≤ 200 * mainLog x Q * mainBracket x Q := by
  have hx1 : (1 : ℕ) ≤ x := by omega
  have hbr : (0 : ℝ) ≤ mainBracket x Q := mainBracket_nonneg x Q
  have hL1 : (1 : ℝ) ≤ mainLog x Q := mainLog_ge_one hx hQ
  have hLpos : (0 : ℝ) ≤ mainLog x Q := le_trans (by norm_num) hL1
  have hXL : (x : ℝ) ≤ mainBracket x Q := le_mainBracket_self x Q
  have hJ : (((T * T).log2 + 1 : ℕ) : ℝ) ≤ 8 * mainLog x Q := by
    refine blk_J_le T x Q hT hx1 (by omega) ?_
    have hx1r : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have h13x : (x : ℝ) ^ (1 / 3 : ℝ) ≤ (x : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hx1r (show (1 : ℝ) / 3 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    linarith [hTx, h13x]
  have h2J : (2 : ℝ) ^ ((T * T).log2 + 1) ≤ 2 * (T : ℝ) ^ 2 := by
    have h := blk_M_le T ((T * T).log2 + 1) ((T * T).log2) hT (by omega) le_rfl
    have h' : (T : ℝ) * (T : ℝ) = (T : ℝ) ^ 2 := by ring
    rwa [h'] at h
  have hT2b : (T : ℝ) ^ 2 ≤ mainBracket x Q := domino_T2 hx hTx
  have hQTx : (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ) ≤ mainBracket x Q :=
    domino_Q_sqrtx_T hx hQ hTx
  have hQTx' : (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ) ≤ mainBracket x Q := by
    have h := hQTx
    rwa [← Real.sqrt_eq_rpow] at h
  have hQT2 : (Q : ℝ) * (T : ℝ) ^ 2 ≤ mainBracket x Q := domino_Q_T2 hx hQ hTx hTQ
  have hQT : (Q : ℝ) * (T : ℝ) ≤ mainBracket x Q := domino_Q_T hx hQ hTQ
  have hQ2T : (Q : ℝ) ^ 2 * (T : ℝ) ≤ mainBracket x Q := domino_Q2_T hx hQ hTx hTQ
  have hxQ : (x : ℝ) * (Q : ℝ) / Real.sqrt ((T : ℝ) + 1) ≤ 2 * mainBracket x Q :=
    domino_x_Q_invsqrtT hx hQ hmin
  have hsqrtxQ2 : Real.sqrt (x : ℝ) * (Q : ℝ) ^ 2 ≤ mainBracket x Q := by
    rw [Real.sqrt_eq_rpow]
    have h0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) :=
      mul_nonneg (Real.rpow_nonneg h0 _) (Real.rpow_nonneg (by positivity) _)
    have h3 : (0 : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) :=
      mul_nonneg (Real.rpow_nonneg h0 _) (by positivity)
    simp only [mainBracket]
    linarith
  have hExp : (∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
        blkTerm x Q j)
      = ∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
          ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)
            + (Q : ℝ) * ((2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
            + (Q : ℝ) * (((((x / 2 ^ j : ℕ)) : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1)))
            + (Q : ℝ) ^ 2 * Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold blkTerm
    ring
  rw [hExp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hb1 : (∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
        (2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
      ≤ 20 * mainLog x Q * mainBracket x Q := by
    refine le_trans (blk_MN_filtered_le x T ((T * T).log2 + 1) hT h2J) ?_
    have hbL : (0 : ℝ) ≤ mainBracket x Q * mainLog x Q := mul_nonneg hbr hLpos
    have e1 : 2 * (x : ℝ) * ((((T * T).log2 + 1 : ℕ)) : ℝ)
        ≤ 16 * (mainBracket x Q * mainLog x Q) := by
      have h1 : 2 * (x : ℝ) * ((((T * T).log2 + 1 : ℕ)) : ℝ) ≤ 2 * (x : ℝ) * (8 * mainLog x Q) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
      have h2 : 2 * (x : ℝ) * (8 * mainLog x Q) = 16 * ((x : ℝ) * mainLog x Q) := by ring
      have h3 : 16 * ((x : ℝ) * mainLog x Q) ≤ 16 * (mainBracket x Q * mainLog x Q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXL hLpos) (by norm_num)
      linarith [h1, h2, h3]
    have e4 : 4 * (T : ℝ) ^ 2 ≤ 4 * (mainBracket x Q * mainLog x Q) := by nlinarith [hT2b, hbL, hL1]
    have hfin : 20 * mainLog x Q * mainBracket x Q = 16 * (mainBracket x Q * mainLog x Q)
        + 4 * (mainBracket x Q * mainLog x Q) := by ring
    linarith [e1, e4, hfin]
  have hb2 : (Q : ℝ) * (∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
        (2 : ℝ) ^ (j + 1) * Real.sqrt ((((x / 2 ^ j : ℕ)) : ℝ) + 1))
      ≤ 80 * mainLog x Q * mainBracket x Q := by
    have h := blk_M_sqrtN_filtered_le x T ((T * T).log2 + 1) hT h2J
    have hQ1 := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ (Q : ℝ) by positivity)
    have hJb : (2 * (T : ℝ) * Real.sqrt (x : ℝ) + 4 * Real.sqrt 2 * (T : ℝ) ^ 2)
          * ((((T * T).log2 + 1 : ℕ)) : ℝ)
        ≤ (2 * (T : ℝ) * Real.sqrt (x : ℝ) + 4 * Real.sqrt 2 * (T : ℝ) ^ 2)
          * (8 * mainLog x Q) := mul_le_mul_of_nonneg_left hJ (by positivity)
    have hQ2 := mul_le_mul_of_nonneg_left hJb (show (0 : ℝ) ≤ (Q : ℝ) by positivity)
    have hdecomp : (Q : ℝ) * ((2 * (T : ℝ) * Real.sqrt (x : ℝ) + 4 * Real.sqrt 2 * (T : ℝ) ^ 2)
          * (8 * mainLog x Q))
        = 16 * ((Q : ℝ) * (T : ℝ) * Real.sqrt (x : ℝ)) * mainLog x Q
          + 32 * Real.sqrt 2 * ((Q : ℝ) * (T : ℝ) ^ 2) * mainLog x Q := by ring
    have hQTsqrtx : (Q : ℝ) * (T : ℝ) * Real.sqrt (x : ℝ) ≤ mainBracket x Q := by
      rw [show (Q : ℝ) * (T : ℝ) * Real.sqrt (x : ℝ)
          = (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ) by ring]
      exact hQTx'
    have hs1 : 16 * ((Q : ℝ) * (T : ℝ) * Real.sqrt (x : ℝ)) * mainLog x Q
        ≤ 16 * (mainBracket x Q * mainLog x Q) := by
      have hh : (Q : ℝ) * (T : ℝ) * Real.sqrt (x : ℝ) * mainLog x Q
          ≤ mainBracket x Q * mainLog x Q := mul_le_mul hQTsqrtx le_rfl hLpos hbr
      nlinarith [hh]
    have hs2 : 32 * Real.sqrt 2 * ((Q : ℝ) * (T : ℝ) ^ 2) * mainLog x Q
        ≤ 32 * Real.sqrt 2 * (mainBracket x Q * mainLog x Q) := by
      have hh : (Q : ℝ) * (T : ℝ) ^ 2 * mainLog x Q ≤ mainBracket x Q * mainLog x Q :=
        mul_le_mul hQT2 le_rfl hLpos hbr
      have h2 : 32 * Real.sqrt 2 * ((Q : ℝ) * (T : ℝ) ^ 2 * mainLog x Q)
          ≤ 32 * Real.sqrt 2 * (mainBracket x Q * mainLog x Q) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      rw [show 32 * Real.sqrt 2 * ((Q : ℝ) * (T : ℝ) ^ 2) * mainLog x Q
          = 32 * Real.sqrt 2 * ((Q : ℝ) * (T : ℝ) ^ 2 * mainLog x Q) by ring]
      exact h2
    have hs2b : 32 * Real.sqrt 2 * (mainBracket x Q * mainLog x Q)
        ≤ 64 * (mainBracket x Q * mainLog x Q) := by
      have hsq2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have hbL : (0 : ℝ) ≤ mainBracket x Q * mainLog x Q := mul_nonneg hbr hLpos
      nlinarith [hsq2, hbL]
    have hfin : 80 * mainLog x Q * mainBracket x Q = 16 * (mainBracket x Q * mainLog x Q)
        + 64 * (mainBracket x Q * mainLog x Q) := by ring
    linarith [hQ1, hQ2, hdecomp, hs1, hs2, hs2b, hfin]
  have hb3 : (Q : ℝ) * (∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
        ((((x / 2 ^ j : ℕ)) : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1)))
      ≤ 40 * mainLog x Q * mainBracket x Q := by
    have h := blk_N_sqrtM_filtered_le x T ((T * T).log2 + 1) hT h2J
    have hQ1 := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ (Q : ℝ) by positivity)
    have hpos : (0 : ℝ) < Real.sqrt ((T : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hJb : 2 * (x : ℝ) * ((((T * T).log2 + 1 : ℕ)) : ℝ) / Real.sqrt ((T : ℝ) + 1)
        ≤ 2 * (x : ℝ) * (8 * mainLog x Q) / Real.sqrt ((T : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJ (by positivity)) (le_of_lt hpos)
    have hQ2 : (Q : ℝ) * (2 * (x : ℝ) * ((((T * T).log2 + 1 : ℕ)) : ℝ) / Real.sqrt ((T : ℝ) + 1)
          + 8 * (T : ℝ))
        ≤ (Q : ℝ) * (2 * (x : ℝ) * (8 * mainLog x Q) / Real.sqrt ((T : ℝ) + 1) + 8 * (T : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith [hJb]
    have hdecomp : (Q : ℝ) * (2 * (x : ℝ) * (8 * mainLog x Q) / Real.sqrt ((T : ℝ) + 1)
          + 8 * (T : ℝ))
        = 16 * ((x : ℝ) * (Q : ℝ) / Real.sqrt ((T : ℝ) + 1)) * mainLog x Q
          + 8 * ((Q : ℝ) * (T : ℝ)) := by ring
    have hs1 : 16 * ((x : ℝ) * (Q : ℝ) / Real.sqrt ((T : ℝ) + 1)) * mainLog x Q
        ≤ 32 * (mainBracket x Q * mainLog x Q) := by
      have hh : (x : ℝ) * (Q : ℝ) / Real.sqrt ((T : ℝ) + 1) * mainLog x Q
          ≤ 2 * mainBracket x Q * mainLog x Q :=
        mul_le_mul hxQ le_rfl hLpos (by positivity : (0 : ℝ) ≤ 2 * mainBracket x Q)
      nlinarith [hh]
    have hs2 : 8 * ((Q : ℝ) * (T : ℝ)) ≤ 8 * (mainBracket x Q * mainLog x Q) := by
      have hQTnn : (0 : ℝ) ≤ (Q : ℝ) * (T : ℝ) := by positivity
      have h1 : 8 * ((Q : ℝ) * (T : ℝ)) ≤ 8 * ((Q : ℝ) * (T : ℝ)) * mainLog x Q := by
        nlinarith [hQTnn, hL1]
      have h2 : 8 * ((Q : ℝ) * (T : ℝ)) * mainLog x Q ≤ 8 * (mainBracket x Q * mainLog x Q) := by
        have hh : (Q : ℝ) * (T : ℝ) * mainLog x Q ≤ mainBracket x Q * mainLog x Q :=
          mul_le_mul hQT le_rfl hLpos hbr
        nlinarith [hh]
      linarith [h1, h2]
    have hfin : 40 * mainLog x Q * mainBracket x Q = 32 * (mainBracket x Q * mainLog x Q)
        + 8 * (mainBracket x Q * mainLog x Q) := by ring
    linarith [hQ1, hQ2, hdecomp, hs1, hs2, hfin]
  have hb4 : (Q : ℝ) ^ 2 * (∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
        Real.sqrt ((2 : ℝ) ^ (j + 1) * ((((x / 2 ^ j : ℕ)) : ℝ) + 1)))
      ≤ 30 * mainLog x Q * mainBracket x Q := by
    have h := blk_sqrtMN_filtered_le x T ((T * T).log2 + 1) hT h2J
    have hQ1 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (Q : ℝ) ^ 2)
    have hJb : Real.sqrt 2 * Real.sqrt (x : ℝ) * ((((T * T).log2 + 1 : ℕ)) : ℝ)
        ≤ Real.sqrt 2 * Real.sqrt (x : ℝ) * (8 * mainLog x Q) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    have hQ2 : (Q : ℝ) ^ 2 * (Real.sqrt 2 * Real.sqrt (x : ℝ)
          * ((((T * T).log2 + 1 : ℕ)) : ℝ) + 8 * (T : ℝ))
        ≤ (Q : ℝ) ^ 2 * (Real.sqrt 2 * Real.sqrt (x : ℝ) * (8 * mainLog x Q) + 8 * (T : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith [hJb]
    have hdecomp : (Q : ℝ) ^ 2 * (Real.sqrt 2 * Real.sqrt (x : ℝ) * (8 * mainLog x Q) + 8 * (T : ℝ))
        = 8 * Real.sqrt 2 * (Real.sqrt (x : ℝ) * (Q : ℝ) ^ 2) * mainLog x Q
          + 8 * ((Q : ℝ) ^ 2 * (T : ℝ)) := by ring
    have hs1 : 8 * Real.sqrt 2 * (Real.sqrt (x : ℝ) * (Q : ℝ) ^ 2) * mainLog x Q
        ≤ 16 * (mainBracket x Q * mainLog x Q) := by
      have hsq2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have hh : Real.sqrt (x : ℝ) * (Q : ℝ) ^ 2 * mainLog x Q ≤ mainBracket x Q * mainLog x Q :=
        mul_le_mul hsqrtxQ2 le_rfl hLpos hbr
      have h2 : 8 * Real.sqrt 2 * (Real.sqrt (x : ℝ) * (Q : ℝ) ^ 2 * mainLog x Q)
          ≤ 8 * Real.sqrt 2 * (mainBracket x Q * mainLog x Q) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      have h3 : 8 * Real.sqrt 2 * (mainBracket x Q * mainLog x Q)
          ≤ 16 * (mainBracket x Q * mainLog x Q) := by
        have hbL : (0 : ℝ) ≤ mainBracket x Q * mainLog x Q := mul_nonneg hbr hLpos
        nlinarith [hsq2, hbL]
      rw [show 8 * Real.sqrt 2 * (Real.sqrt (x : ℝ) * (Q : ℝ) ^ 2) * mainLog x Q
          = 8 * Real.sqrt 2 * (Real.sqrt (x : ℝ) * (Q : ℝ) ^ 2 * mainLog x Q) by ring]
      linarith [h2, h3]
    have hs2 : 8 * ((Q : ℝ) ^ 2 * (T : ℝ)) ≤ 8 * (mainBracket x Q * mainLog x Q) := by
      have hnn : (0 : ℝ) ≤ (Q : ℝ) ^ 2 * (T : ℝ) := by positivity
      have h1 : 8 * ((Q : ℝ) ^ 2 * (T : ℝ)) ≤ 8 * ((Q : ℝ) ^ 2 * (T : ℝ)) * mainLog x Q := by
        nlinarith [hnn, hL1]
      have h2 : 8 * ((Q : ℝ) ^ 2 * (T : ℝ)) * mainLog x Q ≤ 8 * (mainBracket x Q * mainLog x Q) := by
        have hh : (Q : ℝ) ^ 2 * (T : ℝ) * mainLog x Q ≤ mainBracket x Q * mainLog x Q :=
          mul_le_mul hQ2T le_rfl hLpos hbr
        nlinarith [hh]
      linarith [h1, h2]
    have hfin : 30 * mainLog x Q * mainBracket x Q = 16 * (mainBracket x Q * mainLog x Q)
        + 14 * (mainBracket x Q * mainLog x Q) := by ring
    linarith [hQ1, hQ2, hdecomp, hs1, hs2, hfin, mul_nonneg hbr hLpos]
  linarith [hb1, hb2, hb3, hb4, mul_nonneg hbr hLpos]

set_option maxHeartbeats 1000000 in
/-- The contribution of the second half of the third Vaughan piece. -/
lemma S3''_sum_le (T Q x : ℕ) (hT : 1 ≤ T) (hQ : 2 ≤ Q) (hx : 2 ≤ x)
    (hTx : (T : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ))
    (hTQ : (T : ℝ) * (Q : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ))
    (hmin : min ((x : ℝ) ^ (1 / 3 : ℝ)) ((x : ℝ) ^ (2 / 3 : ℝ) / (Q : ℝ)) ≤ 2 * (T : ℝ)) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S3'' T q χ y‖) '' Set.Icc 1 x))
      ≤ cBil * (100000 * (mainLog x Q) ^ 3) * mainBracket x Q := by
  have hx1 : (1 : ℕ) ≤ x := by omega
  have hL1 : (1 : ℝ) ≤ mainLog x Q := mainLog_ge_one hx hQ
  have hLpos : (0 : ℝ) ≤ mainLog x Q := le_trans (by norm_num) hL1
  have hbr : (0 : ℝ) ≤ mainBracket x Q := mainBracket_nonneg x Q
  have hcB : (0 : ℝ) ≤ cBil := cBil_pos.le
  have hper : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      sSup ((fun y : ℕ => ‖S3'' T q χ y‖) '' Set.Icc 1 x)
        ≤ ∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
            blkSup T q x j χ := by
    intro q χ
    refine Real.sSup_le ?_ ?_
    · intro b hb
      rcases hb with ⟨y, hy, rfl⟩
      have h1 : ‖S3'' T q χ y‖ ≤ ∑ j ∈ Finset.range ((T * T).log2 + 1),
          ‖∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)), ∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
              (if t * r ≤ y then (1 : ℂ) else 0) * aBlk T j t * (1 : ℂ)
                * χ ((t * r : ℕ) : ZMod q)‖ := S3''_pointwise T q hT χ x y hy
      have hsub : (∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
            ‖∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)), ∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
              (if t * r ≤ y then (1 : ℂ) else 0) * aBlk T j t * (1 : ℂ)
                * χ ((t * r : ℕ) : ZMod q)‖)
          = ∑ j ∈ Finset.range ((T * T).log2 + 1),
              ‖∑ t ∈ Finset.Icc 1 (2 ^ (j + 1)), ∑ r ∈ Finset.Icc 1 (x / 2 ^ j + 1),
                (if t * r ≤ y then (1 : ℂ) else 0) * aBlk T j t * (1 : ℂ)
                  * χ ((t * r : ℕ) : ZMod q)‖ := by
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro j hj hjnot
        have hjlt : j < (T + 1).log2 := by
          by_contra hc
          exact hjnot (Finset.mem_filter.mpr ⟨hj, le_of_not_gt hc⟩)
        have hz := S3''_blk_zero_of_lt T q hT χ x y j hjlt
        rw [hz, norm_zero]
      rw [← hsub] at h1
      refine le_trans h1 ?_
      refine Finset.sum_le_sum (fun j hj => ?_)
      refine le_csSup ((Set.finite_Icc 1 x).image _).bddAbove ⟨y, hy, rfl⟩
    · refine Finset.sum_nonneg (fun j _ => Real.sSup_nonneg (fun b hb => ?_))
      rcases hb with ⟨y, hy, rfl⟩
      exact norm_nonneg _
  calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S3'' T q χ y‖) '' Set.Icc 1 x))
      ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ primChars q,
            ∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
              blkSup T q x j χ := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ hχ => hper q χ)) (by positivity)
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primChars q,
          ∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
            ((q : ℝ) / (q.totient : ℝ)) * blkSup T q x j χ := by
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun χ hχ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ q ∈ Finset.Icc 1 Q,
          ∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
            ∑ χ ∈ primChars q, ((q : ℝ) / (q.totient : ℝ)) * blkSup T q x j χ := by
        refine Finset.sum_congr rfl (fun q hq => Finset.sum_comm)
    _ = ∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
          ∑ q ∈ Finset.Icc 1 Q,
            ∑ χ ∈ primChars q, ((q : ℝ) / (q.totient : ℝ)) * blkSup T q x j χ :=
        Finset.sum_comm
    _ = ∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
          ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ primChars q, blkSup T q x j χ := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
          8 * (mainLog x Q) ^ 2 * cBil * blkTerm x Q j :=
        Finset.sum_le_sum (fun j hj => S3''_blk_le2 T Q x j hT hQ hx hTx (mem_filter_range hj))
    _ = 8 * (mainLog x Q) ^ 2 * cBil *
          ∑ j ∈ (Finset.range ((T * T).log2 + 1)).filter (fun j => (T + 1).log2 ≤ j),
            blkTerm x Q j := by rw [Finset.mul_sum]
    _ ≤ 8 * (mainLog x Q) ^ 2 * cBil * (200 * mainLog x Q * mainBracket x Q) :=
        mul_le_mul_of_nonneg_left (S3''_blkSum_le T Q x hT hQ hx hTx hTQ hmin) (by positivity)
    _ ≤ cBil * (100000 * (mainLog x Q) ^ 3) * mainBracket x Q := by
        have h1 : (0 : ℝ) ≤ (mainLog x Q) ^ 3 * mainBracket x Q :=
          mul_nonneg (pow_nonneg hLpos 3) hbr
        have h2 : (0 : ℝ) ≤ cBil * ((mainLog x Q) ^ 3 * mainBracket x Q) := mul_nonneg hcB h1
        nlinarith [h2]

/-! ## Assembly of Vaughan's mean value theorem -/

/-- `sSup` of the norm of a signed four-term sum is bounded by the sum of the four `sSup`s. -/
lemma sSup_norm_four_le (f1 f2 f3 f4 : ℕ → ℂ) (x : ℕ) :
    sSup ((fun y : ℕ => ‖f1 y + f2 y - f3 y - f4 y‖) '' Set.Icc 1 x)
      ≤ sSup ((fun y : ℕ => ‖f1 y‖) '' Set.Icc 1 x)
        + sSup ((fun y : ℕ => ‖f2 y‖) '' Set.Icc 1 x)
        + sSup ((fun y : ℕ => ‖f3 y‖) '' Set.Icc 1 x)
        + sSup ((fun y : ℕ => ‖f4 y‖) '' Set.Icc 1 x) := by
  have hn1 : (0 : ℝ) ≤ sSup ((fun y : ℕ => ‖f1 y‖) '' Set.Icc 1 x) :=
    Real.sSup_nonneg (fun b hb => by rcases hb with ⟨y, hy, rfl⟩; exact norm_nonneg _)
  have hn2 : (0 : ℝ) ≤ sSup ((fun y : ℕ => ‖f2 y‖) '' Set.Icc 1 x) :=
    Real.sSup_nonneg (fun b hb => by rcases hb with ⟨y, hy, rfl⟩; exact norm_nonneg _)
  have hn3 : (0 : ℝ) ≤ sSup ((fun y : ℕ => ‖f3 y‖) '' Set.Icc 1 x) :=
    Real.sSup_nonneg (fun b hb => by rcases hb with ⟨y, hy, rfl⟩; exact norm_nonneg _)
  have hn4 : (0 : ℝ) ≤ sSup ((fun y : ℕ => ‖f4 y‖) '' Set.Icc 1 x) :=
    Real.sSup_nonneg (fun b hb => by rcases hb with ⟨y, hy, rfl⟩; exact norm_nonneg _)
  refine Real.sSup_le ?_ (by linarith)
  rintro b ⟨y, hy, rfl⟩
  have e1 : ‖f1 y‖ ≤ sSup ((fun y : ℕ => ‖f1 y‖) '' Set.Icc 1 x) :=
    le_csSup ((Set.finite_Icc 1 x).image _).bddAbove ⟨y, hy, rfl⟩
  have e2 : ‖f2 y‖ ≤ sSup ((fun y : ℕ => ‖f2 y‖) '' Set.Icc 1 x) :=
    le_csSup ((Set.finite_Icc 1 x).image _).bddAbove ⟨y, hy, rfl⟩
  have e3 : ‖f3 y‖ ≤ sSup ((fun y : ℕ => ‖f3 y‖) '' Set.Icc 1 x) :=
    le_csSup ((Set.finite_Icc 1 x).image _).bddAbove ⟨y, hy, rfl⟩
  have e4 : ‖f4 y‖ ≤ sSup ((fun y : ℕ => ‖f4 y‖) '' Set.Icc 1 x) :=
    le_csSup ((Set.finite_Icc 1 x).image _).bddAbove ⟨y, hy, rfl⟩
  have h1 := norm_sub_le (f1 y + f2 y - f3 y) (f4 y)
  have h2 := norm_sub_le (f1 y + f2 y) (f3 y)
  have h3 := norm_add_le (f1 y) (f2 y)
  linarith

lemma sSup_norm_add_le (f g : ℕ → ℂ) (x : ℕ) :
    sSup ((fun y : ℕ => ‖f y + g y‖) '' Set.Icc 1 x)
      ≤ sSup ((fun y : ℕ => ‖f y‖) '' Set.Icc 1 x)
        + sSup ((fun y : ℕ => ‖g y‖) '' Set.Icc 1 x) := by
  have hn1 : (0 : ℝ) ≤ sSup ((fun y : ℕ => ‖f y‖) '' Set.Icc 1 x) :=
    Real.sSup_nonneg (fun b hb => by rcases hb with ⟨y, hy, rfl⟩; exact norm_nonneg _)
  have hn2 : (0 : ℝ) ≤ sSup ((fun y : ℕ => ‖g y‖) '' Set.Icc 1 x) :=
    Real.sSup_nonneg (fun b hb => by rcases hb with ⟨y, hy, rfl⟩; exact norm_nonneg _)
  refine Real.sSup_le ?_ (by linarith)
  rintro b ⟨y, hy, rfl⟩
  have e1 : ‖f y‖ ≤ sSup ((fun y : ℕ => ‖f y‖) '' Set.Icc 1 x) :=
    le_csSup ((Set.finite_Icc 1 x).image _).bddAbove ⟨y, hy, rfl⟩
  have e2 : ‖g y‖ ≤ sSup ((fun y : ℕ => ‖g y‖) '' Set.Icc 1 x) :=
    le_csSup ((Set.finite_Icc 1 x).image _).bddAbove ⟨y, hy, rfl⟩
  linarith [norm_add_le (f y) (g y), e1, e2]

/-- The `λ₂`-piece in the form used by the shared type-I estimate. -/
def lam2A (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)))
      * (χ (n : ZMod q) : ℂ)

/-- The first half of the `λ₃`-piece in the form used by the shared estimates. -/
def lam3A (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ t ∈ Finset.Icc 1 T,
    (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
        ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ)
          * ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
      * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))

/-- The second half of the `λ₃`-piece in the form used by the shared estimates. -/
def lam3B (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ t ∈ Finset.Icc (T + 1) (T ^ 2),
    (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
        ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ)
          * ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
      * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))

/-- The `λ₄`-piece in the form used by the shared type-II estimate. -/
def lam4Form (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    (∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
        ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)
          * (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)))
      * χ (n : ZMod q)

lemma S3'_eq_form (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    S3' T q χ y = lam3A T q χ y := by
  rw [S3', lam3A]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have h1 : (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
        ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ)
          * ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
      = aT T t := by
    rw [aT, Finset.sum_comm, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun e he => Finset.sum_congr rfl (fun d hd => ?_))
    by_cases h : d * e = t
    · rw [if_pos h, if_pos (by rw [mul_comm]; exact h)]
      push_cast
      ring
    · rw [if_neg h, if_neg (fun hh => h (by rw [mul_comm] at hh; exact hh))]
  rw [h1]

lemma S3''_eq_form (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    S3'' T q χ y = lam3B T q χ y := by
  rw [S3'', lam3B, ← pow_two T]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have h1 : (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
        ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ)
          * ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
      = aT T t := by
    rw [aT, Finset.sum_comm, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun e he => Finset.sum_congr rfl (fun d hd => ?_))
    by_cases h : d * e = t
    · rw [if_pos h, if_pos (by rw [mul_comm]; exact h)]
      push_cast
      ring
    · rw [if_neg h, if_neg (fun hh => h (by rw [mul_comm] at hh; exact hh))]
  rw [h1]

lemma S4_eq_form (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    S4 T q χ y = lam4Form T q χ y := by
  rw [S4, lam4Form]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  congr 1
  rw [lam4]
  push_cast
  ring

/-- Crude bound for the partial sums of `Λχ` by `(log 4 + 4) x`. -/
lemma psiSup_le {x q : ℕ} (χ : DirichletCharacter ℂ q) :
    sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x)
      ≤ cCh * (x : ℝ) := by
  refine Real.sSup_le ?_ (mul_nonneg (le_of_lt cCh_pos) (Nat.cast_nonneg x))
  rintro b ⟨y, hy, rfl⟩
  rw [Set.mem_Icc] at hy
  have h1 : ‖∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖
      ≤ ∑ n ∈ Finset.Icc 1 y, ArithmeticFunction.vonMangoldt n := by
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
    exact mul_le_of_le_one_right (ArithmeticFunction.vonMangoldt_nonneg)
      (DirichletCharacter.norm_le_one χ (n : ZMod q))
  have h2 : (∑ n ∈ Finset.Icc 1 y, ArithmeticFunction.vonMangoldt n) ≤ cCh * (y : ℝ) := by
    rw [cCh]; exact psi_bound y
  have h3 : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hy.2
  calc ‖∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖
      ≤ ∑ n ∈ Finset.Icc 1 y, ArithmeticFunction.vonMangoldt n := h1
    _ ≤ cCh * (y : ℝ) := h2
    _ ≤ cCh * (x : ℝ) := mul_le_mul_of_nonneg_left h3 (le_of_lt cCh_pos)

/-- Bound for the first Vaughan piece. -/
lemma S1_sum_le (T Q x : ℕ) (hT : 1 ≤ T) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x))
      ≤ cCh * (T : ℝ) * (Q : ℝ) ^ 2 := by
  have hterm : ∀ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x)
        ≤ (q : ℝ) * (cCh * (T : ℝ)) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    haveI : NeZero q := ⟨by omega⟩
    have hφpos : (0 : ℝ) < (q.totient : ℝ) := totient_cast_pos q (by omega)
    have hφnn : (0 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) :=
      div_nonneg (Nat.cast_nonneg q) (le_of_lt hφpos)
    have hcT : (0 : ℝ) ≤ cCh * (T : ℝ) := mul_nonneg (le_of_lt cCh_pos) (Nat.cast_nonneg T)
    have hmain : ∀ χ ∈ primChars q,
        sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x) ≤ cCh * (T : ℝ) := by
      intro χ hχ
      refine Real.sSup_le ?_ (mul_nonneg (le_of_lt cCh_pos) (Nat.cast_nonneg T))
      rintro b ⟨y, hy, rfl⟩
      exact S1_norm_le T q hT χ y
    have hsum : (∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x))
        ≤ ((primChars q).card : ℝ) * (cCh * (T : ℝ)) := by
      calc (∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x))
          ≤ ∑ _χ ∈ primChars q, (cCh * (T : ℝ)) := Finset.sum_le_sum hmain
        _ = ((primChars q).card : ℝ) * (cCh * (T : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard := primChars_card_le_totient q
    calc ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x)
        ≤ ((q : ℝ) / (q.totient : ℝ)) * (((primChars q).card : ℝ) * (cCh * (T : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum hφnn
      _ ≤ ((q : ℝ) / (q.totient : ℝ)) * ((q.totient : ℝ) * (cCh * (T : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hφnn
          exact mul_le_mul_of_nonneg_right hcard hcT
      _ = (q : ℝ) * (cCh * (T : ℝ)) := by
          rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hφpos)]
  have hQ2 : (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) ≤ (Q : ℝ) ^ 2 := by
    calc (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) :=
          Finset.sum_le_sum (fun q hq => by
            rw [Finset.mem_Icc] at hq; exact_mod_cast hq.2)
      _ = (Q : ℝ) ^ 2 := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          ring
  calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x))
      ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * (cCh * (T : ℝ)) := Finset.sum_le_sum hterm
    _ = (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) * (cCh * (T : ℝ)) := by rw [Finset.sum_mul]
    _ ≤ (Q : ℝ) ^ 2 * (cCh * (T : ℝ)) :=
        mul_le_mul_of_nonneg_right hQ2 (mul_nonneg (le_of_lt cCh_pos) (Nat.cast_nonneg T))
    _ = cCh * (T : ℝ) * (Q : ℝ) ^ 2 := by ring

/-- The log factor `L³ √L` is `L^{7/2}`. -/
lemma log_pow_three_mul_sqrt (L : ℝ) (hL : 0 < L) : L ^ 3 * Real.sqrt L = L ^ (7 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast L 3, ← Real.rpow_add hL]
  norm_num

lemma S2_eq_form (T q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    S2 T q χ y = lam2A T q χ y := rfl

lemma sqrtx_Q2_le_bracket (x Q : ℕ) :
    Real.sqrt (x : ℝ) * (Q : ℝ) ^ 2 ≤ mainBracket x Q := by
  rw [Real.sqrt_eq_rpow]
  have h0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg h0 _) (Real.rpow_nonneg (by positivity) _)
  have h3 : (0 : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) :=
    mul_nonneg (Real.rpow_nonneg h0 _) (by positivity)
  simp only [mainBracket]
  linarith

lemma sum_Icc_cast_le_sq (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) ≤ (Q : ℝ) ^ 2 := by
  calc (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) :=
        Finset.sum_le_sum (fun q hq => by
          rw [Finset.mem_Icc] at hq; exact_mod_cast hq.2)
    _ = (Q : ℝ) ^ 2 := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

set_option maxHeartbeats 3000000 in
theorem mean_value_vaughan_range :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q : ℕ, 2 ≤ x → 2 ≤ Q → Q ^ 2 ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2
              + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)
              + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ (7 / 2 : ℝ) := by
  obtain ⟨C2, hC2pos, hC2⟩ :=
    Commons.NumberTheory.BombieriVinogradov.vaughan_type1_lambda2_estimate
  obtain ⟨C3, hC3pos, hC3⟩ :=
    Commons.NumberTheory.BombieriVinogradov.vaughan_type1_lambda3_estimate
  obtain ⟨C5, hC5pos, hC5⟩ := Commons.NumberTheory.BombieriVinogradov.vaughan_type2_lambda4_estimate_sqrt
  refine ⟨63 * cCh + cCh + 2 * C2 + 2 * C3 + 100000 * cBil + 8 * C5 + 1, by
    have h1 : (0 : ℝ) < cCh := cCh_pos
    have h2 : (0 : ℝ) < C2 := hC2pos
    have h3 : (0 : ℝ) < C3 := hC3pos
    have h4 : (0 : ℝ) < cBil := cBil_pos
    have h5 : (0 : ℝ) < C5 := hC5pos
    linarith, ?_⟩
  intro x Q hx hQ hQx
  have hx1 : (1 : ℕ) ≤ x := by omega
  have hQ1 : (1 : ℕ) ≤ Q := by omega
  have hcCh : (0 : ℝ) < cCh := cCh_pos
  have hL1 : (1 : ℝ) ≤ mainLog x Q := mainLog_ge_one hx hQ
  have hLpos : (0 : ℝ) < mainLog x Q := lt_of_lt_of_le one_pos hL1
  have hL7 : (1 : ℝ) ≤ (mainLog x Q) ^ (7 / 2 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hBnn : (0 : ℝ) ≤ mainBracket x Q := mainBracket_nonneg x Q
  rcases lt_or_ge x 64 with hxs | hxb
  · -- small case
    have hterm : ∀ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x)
          ≤ (q : ℝ) * (cCh * (x : ℝ)) := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      haveI : NeZero q := ⟨by omega⟩
      have hφpos : (0 : ℝ) < (q.totient : ℝ) := totient_cast_pos q (by omega)
      have hφnn : (0 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) :=
        div_nonneg (Nat.cast_nonneg q) (le_of_lt hφpos)
      have hcx : (0 : ℝ) ≤ cCh * (x : ℝ) := mul_nonneg (le_of_lt hcCh) (Nat.cast_nonneg x)
      have hmain : ∀ χ ∈ primChars q,
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x)
            ≤ cCh * (x : ℝ) := by
        intro χ hχ
        exact psiSup_le χ
      have hsum : (∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
          ≤ ((primChars q).card : ℝ) * (cCh * (x : ℝ)) := by
        calc _ ≤ ∑ _χ ∈ primChars q, (cCh * (x : ℝ)) := Finset.sum_le_sum hmain
          _ = ((primChars q).card : ℝ) * (cCh * (x : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hcard := primChars_card_le_totient q
      calc ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x)
          ≤ ((q : ℝ) / (q.totient : ℝ)) * (((primChars q).card : ℝ) * (cCh * (x : ℝ))) :=
            mul_le_mul_of_nonneg_left hsum hφnn
        _ ≤ ((q : ℝ) / (q.totient : ℝ)) * ((q.totient : ℝ) * (cCh * (x : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hφnn
            exact mul_le_mul_of_nonneg_right hcard hcx
        _ = (q : ℝ) * (cCh * (x : ℝ)) := by
            rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hφpos)]
    have hLHS : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
        ≤ cCh * (x : ℝ) * (Q : ℝ) ^ 2 := by
      calc _ ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * (cCh * (x : ℝ)) := Finset.sum_le_sum hterm
        _ = (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) * (cCh * (x : ℝ)) := by rw [Finset.sum_mul]
        _ ≤ (Q : ℝ) ^ 2 * (cCh * (x : ℝ)) :=
            mul_le_mul_of_nonneg_right (sum_Icc_cast_le_sq Q)
              (mul_nonneg (le_of_lt hcCh) (Nat.cast_nonneg x))
        _ = cCh * (x : ℝ) * (Q : ℝ) ^ 2 := by ring
    have hx63 : (x : ℝ) ≤ 63 := by
      have h : x ≤ 63 := by omega
      exact_mod_cast h
    have hQ2x : (Q : ℝ) ^ 2 ≤ (x : ℝ) := by
      have h : ((Q ^ 2 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hQx
      simpa [Nat.cast_pow] using h
    have h63 : (0 : ℝ) ≤ 63 := by norm_num
    have h63cCh : (0 : ℝ) ≤ 63 * cCh := by positivity
    have hCtot : 63 * cCh + 1 ≤ 63 * cCh + cCh + 2 * C2 + 2 * C3 + 100000 * cBil + 8 * C5 + 1 := by
      nlinarith [le_of_lt hcCh, le_of_lt hC2pos, le_of_lt hC3pos, le_of_lt cBil_pos,
        le_of_lt hC5pos]
    calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
        ≤ cCh * (x : ℝ) * (Q : ℝ) ^ 2 := hLHS
      _ ≤ cCh * (x : ℝ) * (x : ℝ) := by
          exact mul_le_mul_of_nonneg_left hQ2x
            (mul_nonneg (le_of_lt hcCh) (Nat.cast_nonneg x))
      _ ≤ 63 * cCh * (x : ℝ) := by
          have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
          nlinarith [hx63, le_of_lt hcCh, hx0,
            mul_nonneg (mul_nonneg (le_of_lt hcCh) hx0) (by linarith : (0 : ℝ) ≤ 63 - (x : ℝ))]
      _ ≤ 63 * cCh * mainBracket x Q :=
          mul_le_mul_of_nonneg_left (le_mainBracket_self x Q) h63cCh
      _ ≤ (63 * cCh + 1) * mainBracket x Q := by nlinarith [hBnn]
      _ ≤ (63 * cCh + 1) * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
          have h := mul_le_mul_of_nonneg_left hL7
            (mul_nonneg (by linarith [h63cCh] : (0 : ℝ) ≤ 63 * cCh + 1) hBnn)
          rwa [mul_one] at h
      _ ≤ (63 * cCh + cCh + 2 * C2 + 2 * C3 + 100000 * cBil + 8 * C5 + 1)
            * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
          have hmul1 : (63 * cCh + 1) * mainBracket x Q
              ≤ (63 * cCh + cCh + 2 * C2 + 2 * C3 + 100000 * cBil + 8 * C5 + 1)
                * mainBracket x Q := mul_le_mul_of_nonneg_right hCtot hBnn
          have h1 : (63 * cCh + 1) * mainBracket x Q
              ≤ (63 * cCh + 1) * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
            have h := mul_le_mul_of_nonneg_left hL7
              (mul_nonneg (by linarith [h63cCh] : (0 : ℝ) ≤ 63 * cCh + 1) hBnn)
            rwa [mul_one] at h
          have h2 : (63 * cCh + 1) * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ)
              ≤ (63 * cCh + cCh + 2 * C2 + 2 * C3 + 100000 * cBil + 8 * C5 + 1)
                * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hmul1 (le_of_lt (Real.rpow_pos_of_pos hLpos _))
          linarith [h1, h2]
  · -- main case
    obtain ⟨T, hT1, hTx13, hTQ, hTmin, hTle⟩ := vaughan_mean_value_param x Q hxb hQ hQx
    have hTlex : T ≤ x := by exact_mod_cast hTle
    have hT1r : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT1
    have hpoint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x)
          ≤ sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x)
            + sSup ((fun y : ℕ => ‖lam2A T q χ y‖) '' Set.Icc 1 x)
            + sSup ((fun y : ℕ => ‖lam3A T q χ y‖) '' Set.Icc 1 x)
            + sSup ((fun y : ℕ => ‖lam3B T q χ y‖) '' Set.Icc 1 x)
            + sSup ((fun y : ℕ => ‖lam4Form T q χ y‖) '' Set.Icc 1 x) := by
      intro q χ
      have hfun : (fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖)
          = (fun y : ℕ => ‖S1 T q χ y + lam2A T q χ y - (lam3A T q χ y + lam3B T q χ y)
              - lam4Form T q χ y‖) := by
        funext y
        rw [psi_eq_sum_S T q hT1 χ y, S2_eq_form, S3_eq_S3'_add_S3'' T q hT1 χ y,
          S3'_eq_form, S3''_eq_form, S4_eq_form]
      rw [hfun]
      have h4 := sSup_norm_four_le (S1 T q χ) (lam2A T q χ)
        (fun y : ℕ => lam3A T q χ y + lam3B T q χ y) (lam4Form T q χ) x
      have h2 := sSup_norm_add_le (lam3A T q χ) (lam3B T q χ) x
      linarith
    have hdec : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
        ≤ (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x))
          + (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam2A T q χ y‖) '' Set.Icc 1 x))
          + (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam3A T q χ y‖) '' Set.Icc 1 x))
          + (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam3B T q χ y‖) '' Set.Icc 1 x))
          + (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam4Form T q χ y‖) '' Set.Icc 1 x)) := by
      have hA : ∀ q ∈ Finset.Icc 1 Q, (0 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := fun q hq =>
        div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg _)
      calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
          ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ primChars q,
              (sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x)
                + sSup ((fun y : ℕ => ‖lam2A T q χ y‖) '' Set.Icc 1 x)
                + sSup ((fun y : ℕ => ‖lam3A T q χ y‖) '' Set.Icc 1 x)
                + sSup ((fun y : ℕ => ‖lam3B T q χ y‖) '' Set.Icc 1 x)
                + sSup ((fun y : ℕ => ‖lam4Form T q χ y‖) '' Set.Icc 1 x)) :=
            Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum (fun χ hχ => hpoint q χ)) (hA q hq))
        _ = ∑ q ∈ Finset.Icc 1 Q, ((((q : ℝ) / (q.totient : ℝ)) *
                ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S1 T q χ y‖) '' Set.Icc 1 x)
              + ((q : ℝ) / (q.totient : ℝ)) *
                ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam2A T q χ y‖) '' Set.Icc 1 x))
              + ((q : ℝ) / (q.totient : ℝ)) *
                ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam3A T q χ y‖) '' Set.Icc 1 x)
              + ((q : ℝ) / (q.totient : ℝ)) *
                ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam3B T q χ y‖) '' Set.Icc 1 x)
              + ((q : ℝ) / (q.totient : ℝ)) *
                ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam4Form T q χ y‖) '' Set.Icc 1 x)) := by
            refine Finset.sum_congr rfl (fun q hq => ?_)
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.sum_add_distrib]
            ring
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.sum_add_distrib]
    have b1 := S1_sum_le T Q x hT1 hQ1
    have b2 : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam2A T q χ y‖) '' Set.Icc 1 x))
        ≤ C2 * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ)) * (mainLog x Q) ^ 3 :=
      hC2 x Q T hx hQ hT1 hTlex
    have b3 : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam3A T q χ y‖) '' Set.Icc 1 x))
        ≤ C3 * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ)) * (mainLog x Q) ^ 3 :=
      hC3 x Q T hx hQ hT1 hTlex
    have b4 : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam3B T q χ y‖) '' Set.Icc 1 x))
        ≤ cBil * (100000 * (mainLog x Q) ^ 3) * mainBracket x Q := by
      have h := S3''_sum_le T Q x hT1 hQ hx hTx13 hTQ hTmin
      have heq : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam3B T q χ y‖) '' Set.Icc 1 x))
          = (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖S3'' T q χ y‖) '' Set.Icc 1 x)) := by
        refine Finset.sum_congr rfl (fun q hq => congrArg
          (fun z => ((q : ℝ) / (q.totient : ℝ)) * z) ?_)
        refine Finset.sum_congr rfl (fun χ hχ => congrArg
          (fun z => sSup (z '' Set.Icc 1 x)) ?_)
        funext y
        rw [S3''_eq_form T q χ y]
      rw [heq]; exact h
    have b5 : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖lam4Form T q χ y‖) '' Set.Icc 1 x))
        ≤ C5 * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
              + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ))
          * (mainLog x Q) ^ 3 * Real.sqrt (mainLog x Q) :=
      hC5 x Q T hx hQ hT1 hTlex
    -- bracket comparisons
    have hTQ2B : (T : ℝ) * (Q : ℝ) ^ 2 ≤ mainBracket x Q := by
      have hQ2le : (Q : ℝ) ^ 2 ≤ (Q : ℝ) ^ (5 / 2 : ℝ) := by
        have h1 : (1 : ℝ) ≤ (Q : ℝ) ^ (1 / 2 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast hQ1) (by norm_num)
        rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add (by positivity),
          Real.rpow_two]
        nlinarith [h1, (show (0 : ℝ) ≤ (Q : ℝ) by positivity)]
      have h2 : (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ) = ((T : ℝ) * (Q : ℝ)) * (Q : ℝ) ^ (3 / 2 : ℝ) := by
        rw [show (5 : ℝ) / 2 = 1 + 3 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
        ring
      have h3 : ((T : ℝ) * (Q : ℝ)) * (Q : ℝ) ^ (3 / 2 : ℝ)
          ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hTQ (Real.rpow_nonneg (by positivity) _)
      have h4 : (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) ≤ mainBracket x Q := by
        have h5 : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2 := by positivity
        have h6 : (0 : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) := by positivity
        simp only [mainBracket]; linarith
      calc (T : ℝ) * (Q : ℝ) ^ 2 ≤ (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hQ2le (Nat.cast_nonneg T)
        _ = ((T : ℝ) * (Q : ℝ)) * (Q : ℝ) ^ (3 / 2 : ℝ) := h2
        _ ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) := h3
        _ ≤ mainBracket x Q := h4
    have hSA : (x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ) ≤ 2 * mainBracket x Q := by
      have h1 : (x : ℝ) ≤ mainBracket x Q := le_mainBracket_self x Q
      have h2 : (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ) ≤ mainBracket x Q := by
        rw [show (5 : ℝ) / 2 = 1 + 3 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
        rw [show (T : ℝ) * ((Q : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ))
            = ((T : ℝ) * (Q : ℝ)) * (Q : ℝ) ^ (3 / 2 : ℝ) by ring]
        have h3 : ((T : ℝ) * (Q : ℝ)) * (Q : ℝ) ^ (3 / 2 : ℝ)
            ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hTQ (Real.rpow_nonneg (by positivity) _)
        have h4 : (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) ≤ mainBracket x Q := by
          have h5 : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2 := by positivity
          have h6 : (0 : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) := by positivity
          simp only [mainBracket]; linarith
        linarith [h3, h4]
      linarith [h1, h2]
    have hsqrtxQ2' : (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ) ≤ mainBracket x Q := by
      have h := sqrtx_Q2_le_bracket x Q
      rw [Real.sqrt_eq_rpow, mul_comm] at h
      exact h
    have hQB1 : (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
        ≤ Real.sqrt 2 * (2 * mainBracket x Q) := by
      have hT0 : (0 : ℝ) < (T : ℝ) := by positivity
      have hsp : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hT0
      have hsp1 : 0 < Real.sqrt ((T : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
      have hsqrt : Real.sqrt ((T : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt (T : ℝ) := by
        calc Real.sqrt ((T : ℝ) + 1) ≤ Real.sqrt (2 * (T : ℝ)) :=
              Real.sqrt_le_sqrt (by linarith [hT1r])
          _ = Real.sqrt 2 * Real.sqrt (T : ℝ) := Real.sqrt_mul (by norm_num) _
      have heq : (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
          = (x : ℝ) * (Q : ℝ) / Real.sqrt (T : ℝ) := by
        rw [← Real.sqrt_eq_rpow, div_eq_mul_inv]; ring
      rw [heq]
      have hle1 : (x : ℝ) * (Q : ℝ) / Real.sqrt (T : ℝ)
          ≤ Real.sqrt 2 * ((x : ℝ) * (Q : ℝ) / Real.sqrt ((T : ℝ) + 1)) := by
        rw [div_le_iff₀ hsp]
        have e : (Real.sqrt 2 * ((x : ℝ) * (Q : ℝ) / Real.sqrt ((T : ℝ) + 1))) * Real.sqrt (T : ℝ)
            = Real.sqrt 2 * (x : ℝ) * (Q : ℝ) * Real.sqrt (T : ℝ) / Real.sqrt ((T : ℝ) + 1) := by
          ring
        rw [e, le_div_iff₀ hsp1]
        nlinarith [hsqrt, (show (0 : ℝ) ≤ (x : ℝ) * (Q : ℝ) by positivity),
          Real.sqrt_nonneg (T : ℝ), Real.sqrt_nonneg ((T : ℝ) + 1)]
      calc (x : ℝ) * (Q : ℝ) / Real.sqrt (T : ℝ)
          ≤ Real.sqrt 2 * ((x : ℝ) * (Q : ℝ) / Real.sqrt ((T : ℝ) + 1)) := hle1
        _ ≤ Real.sqrt 2 * (2 * mainBracket x Q) :=
            mul_le_mul_of_nonneg_left (domino_x_Q_invsqrtT hx hQ hTmin) (Real.sqrt_nonneg 2)
        _ = Real.sqrt 2 * (2 * mainBracket x Q) := rfl
    have hSB : (x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
        + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
        + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ) ≤ 8 * mainBracket x Q := by
      have h1 : (x : ℝ) ≤ mainBracket x Q := le_mainBracket_self x Q
      have h2 : (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ) ≤ mainBracket x Q :=
        domino_Q_sqrtx_T hx hQ hTx13
      have h3 : (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
          ≤ Real.sqrt 2 * (2 * mainBracket x Q) := hQB1
      have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      nlinarith [h1, h2, h3, hs2, hBnn, hsqrtxQ2']
    have hQ2sqrtxT : (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ) ≤ mainBracket x Q :=
      domino_Q_sqrtx_T hx hQ hTx13
    have hL3 : (mainLog x Q) ^ 3 ≤ (mainLog x Q) ^ (7 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (mainLog x Q) 3]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hL35 : (mainLog x Q) ^ 3 * Real.sqrt (mainLog x Q)
        = (mainLog x Q) ^ (7 / 2 : ℝ) := log_pow_three_mul_sqrt _ hLpos
    have hC2nn : (0 : ℝ) ≤ C2 := le_of_lt hC2pos
    have hC3nn : (0 : ℝ) ≤ C3 := le_of_lt hC3pos
    have hC5nn : (0 : ℝ) ≤ C5 := le_of_lt hC5pos
    have hcBilnn : (0 : ℝ) ≤ cBil := le_of_lt cBil_pos
    have hcChnn : (0 : ℝ) ≤ cCh := le_of_lt hcCh
    have e1 : cCh * (T : ℝ) * (Q : ℝ) ^ 2
        ≤ cCh * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
      have a : cCh * (T : ℝ) * (Q : ℝ) ^ 2 ≤ cCh * mainBracket x Q := by
        have h := mul_le_mul_of_nonneg_left hTQ2B hcChnn
        nlinarith [h]
      have b : cCh * mainBracket x Q ≤ cCh * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hL7 (mul_nonneg hcChnn hBnn)
        rwa [mul_one] at h
      linarith [a, b]
    have e2 : C2 * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ)) * (mainLog x Q) ^ 3
        ≤ 2 * C2 * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hSA hC2nn
      have h' : C2 * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ))
          ≤ C2 * (2 * mainBracket x Q) := by
        have := mul_le_mul_of_nonneg_left hSA hC2nn
        linarith [this]
      have h2 := mul_le_mul h' hL3 (pow_nonneg (le_of_lt hLpos) 3) (by positivity)
      nlinarith [h2, hBnn, hC2nn, hL7]
    have e3 : C3 * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ)) * (mainLog x Q) ^ 3
        ≤ 2 * C3 * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
      have h' : C3 * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ))
          ≤ C3 * (2 * mainBracket x Q) := by
        have := mul_le_mul_of_nonneg_left hSA hC3nn
        linarith [this]
      have h2 := mul_le_mul h' hL3 (pow_nonneg (le_of_lt hLpos) 3) (by positivity)
      nlinarith [h2, hBnn, hC3nn, hL7]
    have e4 : cBil * (100000 * (mainLog x Q) ^ 3) * mainBracket x Q
        ≤ 100000 * cBil * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
      have h2 : (mainLog x Q) ^ 3 * mainBracket x Q ≤ mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hL3 hBnn
        nlinarith [h]
      nlinarith [h2, hcBilnn, hBnn, hL7, pow_nonneg (le_of_lt hLpos) 3]
    have e5 : C5 * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
          + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
          + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ))
        * (mainLog x Q) ^ 3 * Real.sqrt (mainLog x Q)
        ≤ 8 * C5 * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
      have h' : C5 * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
            + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
            + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ)) ≤ C5 * (8 * mainBracket x Q) := by
        have := mul_le_mul_of_nonneg_left hSB hC5nn
        linarith [this]
      have h2 := mul_le_mul h' hL35.le (by positivity) (by positivity)
      nlinarith [h2, hBnn, hC5nn, hL7]
    have hLHSb : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
        ≤ cCh * (T : ℝ) * (Q : ℝ) ^ 2
          + C2 * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ)) * (mainLog x Q) ^ 3
          + C3 * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ)) * (mainLog x Q) ^ 3
          + cBil * (100000 * (mainLog x Q) ^ 3) * mainBracket x Q
          + C5 * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
              + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ))
            * (mainLog x Q) ^ 3 * Real.sqrt (mainLog x Q) := by
      linarith [hdec, b1, b2, b3, b4, b5]
    have hCtot2 : cCh + 2 * C2 + 2 * C3 + 100000 * cBil + 8 * C5
        ≤ 63 * cCh + cCh + 2 * C2 + 2 * C3 + 100000 * cBil + 8 * C5 + 1 := by
      nlinarith [hcChnn]
    calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primChars q, sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
        ≤ cCh * (T : ℝ) * (Q : ℝ) ^ 2
          + C2 * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ)) * (mainLog x Q) ^ 3
          + C3 * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ)) * (mainLog x Q) ^ 3
          + cBil * (100000 * (mainLog x Q) ^ 3) * mainBracket x Q
          + C5 * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
              + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ))
            * (mainLog x Q) ^ 3 * Real.sqrt (mainLog x Q) := hLHSb
      _ ≤ cCh * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ)
          + 2 * C2 * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ)
          + 2 * C3 * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ)
          + 100000 * cBil * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ)
          + 8 * C5 * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
        linarith [e1, e2, e3, e4, e5]
      _ ≤ (63 * cCh + cCh + 2 * C2 + 2 * C3 + 100000 * cBil + 8 * C5 + 1)
            * mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) := by
        have hBL : (0 : ℝ) ≤ mainBracket x Q * (mainLog x Q) ^ (7 / 2 : ℝ) :=
          mul_nonneg hBnn (le_trans zero_le_one hL7)
        have h := mul_le_mul_of_nonneg_right hCtot2 hBL
        nlinarith [h, hBnn, hL7, hcChnn, hC2nn, hC3nn, hcBilnn, hC5nn]

end

end Commons.NumberTheory.BombieriVinogradov

