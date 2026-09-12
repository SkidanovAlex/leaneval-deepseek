import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3H_deriv

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission.Sec3H

/-- exp(c·x) is smooth -/
lemma exp_c_mul_contDiff {n : WithTop ℕ∞} (c : ℂ) :
    ContDiff ℝ n (fun x : ℝ => Complex.exp (c * (x : ℂ))) := by
  let L : ℝ →L[ℝ] ℂ := ((ContinuousLinearMap.mul ℝ ℂ) c).comp Complex.ofRealCLM
  have hL : ContDiff ℝ n (L : ℝ → ℂ) := ContinuousLinearMap.contDiff L
  have hexp : ContDiff ℝ n (Complex.exp : ℂ → ℂ) :=
    (Complex.contDiff_exp : ContDiff ℂ n (Complex.exp : ℂ → ℂ)).restrict_scalars ℝ
  have h : ContDiff ℝ n (fun x : ℝ => Complex.exp (L x)) := by
    change ContDiff ℝ n (Complex.exp ∘ (L : ℝ → ℂ))
    exact hexp.comp hL
  convert h using 1
  ext x
  exact congrArg Complex.exp (by simp [L, ContinuousLinearMap.mul_apply'])

lemma contDiff_eθ {n : WithTop ℕ∞} : ContDiff ℝ n (fun x : ℝ => Sec3.eθ x) := by
  have h := exp_c_mul_contDiff (n := n) Complex.I
  unfold Sec3.eθ
  convert h using 1
  ext x
  ring

lemma contDiff_eθ_mul {n : WithTop ℕ∞} (c : ℝ) : ContDiff ℝ n (fun x : ℝ => Sec3.eθ (c * x)) := by
  have h := exp_c_mul_contDiff (n := n) (((c : ℂ) * Complex.I))
  unfold Sec3.eθ
  convert h using 1
  ext x
  apply congrArg Complex.exp
  rw [Complex.ofReal_mul]
  ring

lemma polyEval_contDiff {n : WithTop ℕ∞} (Q : ℂ[X]) : ContDiff ℝ n (fun z : ℂ => Q.eval z) := by
  simpa using ((Polynomial.contDiff_aeval (R := ℂ) (𝕜 := ℂ) Q n).restrict_scalars ℝ)

lemma contDiff_alpha {n : WithTop ℕ∞} (t : ℕ) : ContDiff ℝ n (fun x : ℝ => alpha t x) := by
  have hmain : ContDiff ℝ n (fun x : ℝ => (RudinShapiro.P t).eval (Sec3.eθ (x / (T t : ℝ)))) := by
    have hin : ContDiff ℝ n (fun x : ℝ => Sec3.eθ (((T t : ℝ)⁻¹) * x)) := by
      have h := contDiff_eθ_mul (n := n) ((T t : ℝ)⁻¹)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hq := polyEval_contDiff (n := n) (RudinShapiro.P t)
    change ContDiff ℝ n ((fun z : ℂ => (RudinShapiro.P t).eval z) ∘ (fun x : ℝ => Sec3.eθ (x / (T t : ℝ))))
    apply hq.comp
    simpa [div_eq_mul_inv, mul_comm] using hin
  have hc : ContDiff ℝ n (fun _ : ℝ => (scale t : ℂ)) := contDiff_const
  have hprod := hc.mul hmain
  unfold alpha
  exact hprod

lemma contDiff_beta {n : WithTop ℕ∞} (t : ℕ) : ContDiff ℝ n (fun x : ℝ => beta t x) := by
  have hmain : ContDiff ℝ n (fun x : ℝ => (RudinShapiro.Q t).eval (Sec3.eθ (x / (T t : ℝ)))) := by
    have hin : ContDiff ℝ n (fun x : ℝ => Sec3.eθ (((T t : ℝ)⁻¹) * x)) := by
      have h := contDiff_eθ_mul (n := n) ((T t : ℝ)⁻¹)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hq := polyEval_contDiff (n := n) (RudinShapiro.Q t)
    change ContDiff ℝ n ((fun z : ℂ => (RudinShapiro.Q t).eval z) ∘ (fun x : ℝ => Sec3.eθ (x / (T t : ℝ))))
    apply hq.comp
    simpa [div_eq_mul_inv, mul_comm] using hin
  have hc : ContDiff ℝ n (fun _ : ℝ => (scale t : ℂ)) := contDiff_const
  have hprod := hc.mul hmain
  unfold beta
  exact hprod

lemma iteratedDeriv_eθ (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => Sec3.eθ y) x = Complex.I ^ k * Sec3.eθ x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun y : ℝ => Sec3.eθ y) = fun y : ℝ => Complex.I ^ k * Sec3.eθ y := by
        funext y
        exact ih y
      rw [hfun]
      have hθ := eθ_hasDerivAt x
      have hc := hθ.const_mul (Complex.I ^ k)
      have hv := hc.deriv
      rw [hv]
      rw [← mul_assoc]
      rw [← pow_succ]

lemma eθ2_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Sec3.eθ (2 * y)) (((2 : ℂ) * Complex.I) * Sec3.eθ (2 * x)) x := by
  have hφ : HasDerivAt (fun y : ℝ => 2 * y) (2 : ℝ) x := by
    simpa using hasDerivAt_const_mul (x := x) (c := (2 : ℝ))
  have hθ := eθ_hasDerivAt (2 * x)
  have hc := hθ.scomp x hφ
  have hsmul : (2 : ℝ) • (Complex.I * Sec3.eθ (2 * x)) = ((2 : ℂ) * Complex.I) * Sec3.eθ (2 * x) := by
    rw [Algebra.smul_def]
    change ((2 : ℝ) : ℂ) * (Complex.I * Sec3.eθ (2 * x)) = ((2 : ℂ) * Complex.I) * Sec3.eθ (2 * x)
    norm_num
    ring
  exact hc.congr_deriv hsmul

lemma iteratedDeriv_eθ2 (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => Sec3.eθ (2 * y)) x = ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun y : ℝ => Sec3.eθ (2 * y)) =
          fun y : ℝ => ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * y) := by
        funext y
        exact ih y
      rw [hfun]
      have hθ := eθ2_hasDerivAt x
      have hc := hθ.const_mul (((2 : ℂ) * Complex.I) ^ k)
      have hv := hc.deriv
      rw [hv]
      rw [← mul_assoc]
      rw [← pow_succ]

/-- product eθ·α (first H term) -/
def FA (t : ℕ) : ℝ → ℂ := fun y => Sec3.eθ y * alpha t y
/-- product eθ(2·)·β (second H term) -/
def FB (t : ℕ) : ℝ → ℂ := fun y => Sec3.eθ (2 * y) * beta t y

lemma H_eq_FA_add_FB (t : ℕ) : H t = FA t + FB t := by
  funext x
  rfl

lemma iteratedDeriv_FA_sum (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (FA t) x =
      ∑ i ∈ Finset.range (k + 1),
        (((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x) := by
  have hf : ContDiffAt ℝ k (fun y : ℝ => Sec3.eθ y) x := (contDiff_eθ (n := k)).contDiffAt
  have hg : ContDiffAt ℝ k (alpha t) x := (contDiff_alpha (n := k) t).contDiffAt
  unfold FA
  change iteratedDeriv k ((fun y : ℝ => Sec3.eθ y) * alpha t) x =
      ∑ i ∈ Finset.range (k + 1), (((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x)
  rw [iteratedDeriv_mul hf hg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_eθ i x]

lemma iteratedDeriv_FB_sum (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (FB t) x =
      ∑ i ∈ Finset.range (k + 1),
        (((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x) := by
  have hf : ContDiffAt ℝ k (fun y : ℝ => Sec3.eθ (2 * y)) x := (contDiff_eθ_mul (n := k) 2).contDiffAt
  have hg : ContDiffAt ℝ k (beta t) x := (contDiff_beta (n := k) t).contDiffAt
  unfold FB
  change iteratedDeriv k ((fun y : ℝ => Sec3.eθ (2 * y)) * beta t) x =
      ∑ i ∈ Finset.range (k + 1), (((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x)
  rw [iteratedDeriv_mul hf hg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_eθ2 i x]

/-- cancellation: FA^k minus its leading term is a sum over i < k -/
lemma FA_sub_target (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)
      = ∑ i ∈ Finset.range k,
          (((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x) := by
  rw [iteratedDeriv_FA_sum]
  rw [Finset.sum_range_succ]
  simp [Nat.choose_self]

/-- cancellation: FB^k minus leading term -/
lemma FB_sub_target (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)
      = ∑ i ∈ Finset.range k,
          (((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x) := by
  rw [iteratedDeriv_FB_sum]
  rw [Finset.sum_range_succ]
  simp [Nat.choose_self]

lemma norm_mul_mul (a b c : ℂ) : ‖(a * b) * c‖ = ‖a‖ * ‖b‖ * ‖c‖ := by
  rw [norm_mul, norm_mul]

lemma norm_eθ_I_pow (i : ℕ) (x : ℝ) : ‖(Complex.I ^ i * Sec3.eθ x)‖ = 1 := by
  rw [norm_mul, norm_pow, Complex.norm_I, Sec3.norm_eθ]
  norm_num

lemma norm_eθ_2I_pow (i : ℕ) (x : ℝ) : ‖(((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))‖ = (2 : ℝ) ^ i := by
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, Sec3.norm_eθ]
  norm_num

lemma norm_choose_natCast (k i : ℕ) : ‖(k.choose i : ℂ)‖ = (k.choose i : ℝ) := by
  change ‖(((k.choose i : ℝ) : ℂ))‖ = (k.choose i : ℝ)
  rw [norm_of_real]
  rw [abs_of_nonneg (show 0 ≤ (k.choose i : ℝ) by exact_mod_cast (Nat.zero_le _))]

lemma alpha_deriv_bound (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (alpha t) x‖ ≤ 1 / (2 : ℝ) ^ (9 * k) := alpha_iter_deriv_le t hk1 hk4 x

lemma beta_deriv_bound (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (beta t) x‖ ≤ 1 / (2 : ℝ) ^ (9 * k) := beta_iter_deriv_le t hk1 hk4 x

lemma norm_FA_term_le (t : ℕ) {k : ℕ} {i : ℕ} (x : ℝ) (hki1 : 1 ≤ k - i) (hki4 : k - i ≤ 4) :
    ‖(((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x)‖
      ≤ (k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))) := by
  have hnm := norm_mul_mul (k.choose i : ℂ) (Complex.I ^ i * Sec3.eθ x) (iteratedDeriv (k - i) (alpha t) x)
  rw [hnm]
  rw [norm_choose_natCast]
  rw [norm_eθ_I_pow]
  have hb := alpha_iter_deriv_le t hki1 hki4 x
  have hc0 : 0 ≤ (k.choose i : ℝ) := by exact_mod_cast (Nat.zero_le _)
  -- (choose:ℝ) * 1 * ‖w‖ ≤ choose * (1/2^(9(k-i)))
  calc
    (k.choose i : ℝ) * 1 * ‖iteratedDeriv (k - i) (alpha t) x‖
        = (k.choose i : ℝ) * ‖iteratedDeriv (k - i) (alpha t) x‖ := by ring
    _ ≤ (k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))) := mul_le_mul_of_nonneg_left hb hc0

lemma norm_FB_term_le (t : ℕ) {k : ℕ} {i : ℕ} (x : ℝ) (hki1 : 1 ≤ k - i) (hki4 : k - i ≤ 4) :
    ‖(((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x)‖
      ≤ (k.choose i : ℝ) * (2 : ℝ) ^ i * (1 / (2 : ℝ) ^ (9 * (k - i))) := by
  have hnm := norm_mul_mul (k.choose i : ℂ) (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x)) (iteratedDeriv (k - i) (beta t) x)
  rw [hnm]
  rw [norm_choose_natCast]
  rw [norm_eθ_2I_pow]
  have hb := beta_iter_deriv_le t hki1 hki4 x
  have hc0 : 0 ≤ (k.choose i : ℝ) := by exact_mod_cast (Nat.zero_le _)
  calc
    (k.choose i : ℝ) * (2 : ℝ) ^ i * ‖iteratedDeriv (k - i) (beta t) x‖
        ≤ (k.choose i : ℝ) * (2 : ℝ) ^ i * (1 / (2 : ℝ) ^ (9 * (k - i))) := by
            exact mul_le_mul_of_nonneg_left hb (mul_nonneg hc0 (pow_nonneg (by norm_num) i))

lemma norm_FA_sub_target_le (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)‖
      ≤ ∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i)))) := by
  rw [FA_sub_target]
  calc
    ‖∑ i ∈ Finset.range k, (((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x)‖
        ≤ ∑ i ∈ Finset.range k, ‖(((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i)))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hlt : i < k := Finset.mem_range.mp hi
        exact norm_FA_term_le t x (by omega) (by omega)

lemma norm_FB_sub_target_le (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)‖
      ≤ ∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (2 : ℝ) ^ i * (1 / (2 : ℝ) ^ (9 * (k - i)))) := by
  rw [FB_sub_target]
  calc
    ‖∑ i ∈ Finset.range k, (((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x)‖
        ≤ ∑ i ∈ Finset.range k, ‖(((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (2 : ℝ) ^ i * (1 / (2 : ℝ) ^ (9 * (k - i)))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hlt : i < k := Finset.mem_range.mp hi
        exact norm_FB_term_le t x (by omega) (by omega)

/-- auxiliary arithmetic bound for the H approximation -/
lemma H_bound_aux (k : ℕ) (hk : k ≤ 4) :
    (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))))) +
      (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (2 ^ i) * (1 / (2 : ℝ) ^ (9 * (k - i))))) ≤ 1 / 8 := by
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num [Finset.sum_range_succ, show Nat.choose 1 0 = 1 by native_decide]
  · norm_num [Finset.sum_range_succ, show Nat.choose 2 0 = 1 by native_decide,
      show Nat.choose 2 1 = 2 by native_decide]
  · norm_num [Finset.sum_range_succ, show Nat.choose 3 0 = 1 by native_decide,
      show Nat.choose 3 1 = 3 by native_decide, show Nat.choose 3 2 = 3 by native_decide]
  · norm_num [Finset.sum_range_succ, show Nat.choose 4 0 = 1 by native_decide,
      show Nat.choose 4 1 = 4 by native_decide, show Nat.choose 4 2 = 6 by native_decide,
      show Nat.choose 4 3 = 4 by native_decide]


lemma H_iter_deriv_approx (t : ℕ) {k : ℕ} (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (H t) x -
        ((Complex.I ^ k) * Sec3.eθ x * alpha t x +
          ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)‖ ≤ 1 / 8 := by
  by_cases hk0 : k = 0
  · subst k
    simp [H]
    norm_num
  · have hk1 : 1 ≤ k := by omega
    have hFA : ContDiffAt ℝ k (FA t) x := by
      unfold FA
      exact ((contDiff_eθ (n := k)).contDiffAt.mul (contDiff_alpha (n := k) t).contDiffAt)
    have hFB : ContDiffAt ℝ k (FB t) x := by
      unfold FB
      exact ((contDiff_eθ_mul (n := k) 2).contDiffAt.mul (contDiff_beta (n := k) t).contDiffAt)
    rw [H_eq_FA_add_FB]
    have hadd := iteratedDeriv_add (n := k) (f := FA t) (g := FB t) hFA hFB
    rw [hadd]
    -- target split
    have htarget : (iteratedDeriv k (FA t) x + iteratedDeriv k (FB t) x) -
        ((Complex.I ^ k * Sec3.eθ x * alpha t x) + (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x))
        = (iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)) +
          (iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)) := by ring
    rw [htarget]
    have h1 := norm_FA_sub_target_le t hk1 hk4 x
    have h2 := norm_FB_sub_target_le t hk1 hk4 x
    calc
      ‖(iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)) +
          (iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x))‖
          ≤ ‖iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)‖ +
              ‖iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)‖ := norm_add_le _ _
      _ ≤ (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))))) +
            (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (2 ^ i) * (1 / (2 : ℝ) ^ (9 * (k - i))))) := by
            exact add_le_add h1 h2
      _ ≤ 1 / 8 := H_bound_aux k hk4

lemma H_iter_deriv_norm_le (t : ℕ) {k : ℕ} (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (H t) x‖ ≤ (2 : ℝ) ^ k + 2 := by
  -- target := T1 + T2 ; H^k = target + diff
  let T1 : ℂ := Complex.I ^ k * Sec3.eθ x * alpha t x
  let T2 : ℂ := ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x
  have hdiff : ‖iteratedDeriv k (H t) x - (T1 + T2)‖ ≤ 1 / 8 := by
    simpa [T1, T2] using (H_iter_deriv_approx t hk4 x)
  have hT1 : ‖T1‖ ≤ 1 := by
    unfold T1
    calc
      ‖(Complex.I ^ k * Sec3.eθ x) * alpha t x‖ ≤ ‖Complex.I ^ k * Sec3.eθ x‖ * ‖alpha t x‖ := by
        rw [norm_mul]
      _ ≤ 1 * 1 := by
        exact mul_le_mul (norm_eθ_I_pow k x).le (Sec3H.norm_alpha_le t x) (norm_nonneg _) (by norm_num)
      _ ≤ 1 := by norm_num
  have hT2 : ‖T2‖ ≤ (2 : ℝ) ^ k := by
    unfold T2
    calc
      ‖(((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x)) * beta t x‖ ≤ ‖((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x)‖ * ‖beta t x‖ := by
        rw [norm_mul]
      _ ≤ (2 : ℝ) ^ k * 1 := by
        exact mul_le_mul (norm_eθ_2I_pow k x).le (Sec3H.norm_beta_le t x) (norm_nonneg _) (by norm_num)
      _ ≤ (2 : ℝ) ^ k := by ring
  have hnorm : ‖iteratedDeriv k (H t) x‖ ≤ ‖T1 + T2‖ + 1 / 8 := by
    calc
      ‖iteratedDeriv k (H t) x‖ = ‖(T1 + T2) + (iteratedDeriv k (H t) x - (T1 + T2))‖ := by ring
      _ ≤ ‖T1 + T2‖ + ‖iteratedDeriv k (H t) x - (T1 + T2)‖ := norm_add_le _ _
      _ ≤ ‖T1 + T2‖ + 1 / 8 := by exact add_le_add_left hdiff _
  have hTsum : ‖T1 + T2‖ ≤ ‖T1‖ + ‖T2‖ := norm_add_le T1 T2
  calc
    ‖iteratedDeriv k (H t) x‖ ≤ ‖T1 + T2‖ + 1 / 8 := hnorm
    _ ≤ (‖T1‖ + ‖T2‖) + 1 / 8 := by exact add_le_add_right hTsum _
    _ ≤ (1 + (2 : ℝ) ^ k) + 1 / 8 := by exact add_le_add (add_le_add hT1 hT2) (le_refl _)
    _ ≤ (2 : ℝ) ^ k + 2 := by nlinarith

lemma H_deriv_norm_le_four (t : ℕ) (x : ℝ) : ‖deriv (H t) x‖ ≤ 4 := by
  have h := H_iter_deriv_norm_le t (k := 1) (hk4 := by norm_num) x
  -- ‖iteratedDeriv 1 (H t) x‖ ≤ 2^1 + 2
  simpa using h

end Submission.Sec3H
