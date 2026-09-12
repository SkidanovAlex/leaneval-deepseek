import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Multiset.Fintype

open scoped Real BigOperators
open Polynomial Filter

noncomputable section

namespace MarkovSHelper

/-- degree-≤ n trigonometric polynomial with cos-coeffs `a`, sin-coeffs `b` -/
def TPoly (n : ℕ) (a b : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (a k * Real.cos ((k : ℝ) * θ) + b k * Real.sin ((k : ℝ) * θ))

lemma TPoly_zero (n : ℕ) (θ : ℝ) : TPoly n (fun _ => 0) (fun _ => 0) θ = 0 := by
  simp [TPoly]

lemma TPoly_add (n : ℕ) (a b c d : ℕ → ℝ) (θ : ℝ) :
    TPoly n (fun k => a k + c k) (fun k => b k + d k) θ = TPoly n a b θ + TPoly n c d θ := by
  simp [TPoly, add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma TPoly_neg (n : ℕ) (a b : ℕ → ℝ) (θ : ℝ) :
    TPoly n (fun k => - a k) (fun k => - b k) θ = - TPoly n a b θ := by
  have h := TPoly_add n a b (fun k => - a k) (fun k => - b k) θ
  have hz : TPoly n (fun k => a k + -a k) (fun k => b k + -b k) θ = 0 := by
    unfold TPoly
    apply Finset.sum_eq_zero
    intro x hx
    ring
  rw [h] at hz
  linarith

lemma TPoly_sub (n : ℕ) (a b c d : ℕ → ℝ) (θ : ℝ) :
    TPoly n (fun k => a k - c k) (fun k => b k - d k) θ = TPoly n a b θ - TPoly n c d θ := by
  calc
    TPoly n (fun k => a k - c k) (fun k => b k - d k) θ
        = TPoly n (fun k => a k + - c k) (fun k => b k + - d k) θ := by
          unfold TPoly
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = TPoly n a b θ + TPoly n (fun k => - c k) (fun k => - d k) θ := by
          exact TPoly_add n a b (fun k => - c k) (fun k => - d k) θ
    _ = TPoly n a b θ - TPoly n c d θ := by
          rw [TPoly_neg n c d θ]
          ring

lemma TPoly_smul (n : ℕ) (α : ℝ) (a b : ℕ → ℝ) (θ : ℝ) :
    TPoly n (fun k => α * a k) (fun k => α * b k) θ = α * TPoly n a b θ := by
  unfold TPoly
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma TPoly_const_eval {n : ℕ} (θ : ℝ) (c : ℝ) :
    (∑ k ∈ Finset.range (n + 1), (if k = 0 then c else 0)) = c := by
  rw [Finset.sum_ite_eq']
  simp

/-- Constant functions are trig polys of any degree. -/
lemma TPoly_of_const {n : ℕ} (θ : ℝ) (c : ℝ) :
    TPoly n (fun k => if k = 0 then c else 0) (fun _ => 0) θ = c := by
  unfold TPoly
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb0
    simp [hb0]
  · intro h0
    simp at h0

lemma TPoly_one (n : ℕ) (θ : ℝ) : TPoly n (fun k => if k = 0 then 1 else 0) (fun _ => 0) θ = 1 :=
  TPoly_of_const θ 1

/-- trig poly that is a pure cosine wave cos(mθ), degree ≥ m -/
lemma TPoly_cos_wave {n m : ℕ} (hm : m ≤ n) (θ : ℝ) :
    TPoly n (fun k => if k = m then 1 else 0) (fun _ => 0) θ = Real.cos ((m : ℝ) * θ) := by
  unfold TPoly
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hm'
    have : m ∈ Finset.range (n + 1) := by simp [Nat.lt_succ_of_le hm]
    exact (hm' this).elim


/-- derivative expression of a degree-≤ n trig poly -/
def TDiff (n : ℕ) (a b : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (a k * (-(k : ℝ)) * Real.sin ((k : ℝ) * θ) + b k * (k : ℝ) * Real.cos ((k : ℝ) * θ))

lemma hasDerivAt_cos_mul (k : ℕ) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos ((k : ℝ) * x)) (-(k : ℝ) * Real.sin ((k : ℝ) * θ)) θ := by
  simpa [Function.comp_def, mul_comm, mul_one] using
    (Real.hasDerivAt_cos ((k : ℝ) * θ)).comp θ ((hasDerivAt_id θ).const_mul (k : ℝ))

lemma hasDerivAt_sin_mul (k : ℕ) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin ((k : ℝ) * x)) ((k : ℝ) * Real.cos ((k : ℝ) * θ)) θ := by
  simpa [Function.comp_def, mul_comm, mul_one] using
    (Real.hasDerivAt_sin ((k : ℝ) * θ)).comp θ ((hasDerivAt_id θ).const_mul (k : ℝ))

lemma deriv_cos_scaled (k : ℕ) (c : ℝ) (θ : ℝ) :
    deriv (fun x : ℝ => c * Real.cos ((k : ℝ) * x)) θ = c * (-(k : ℝ) * Real.sin ((k : ℝ) * θ)) := by
  exact ((hasDerivAt_cos_mul k θ).const_mul c).deriv

lemma deriv_sin_scaled (k : ℕ) (c : ℝ) (θ : ℝ) :
    deriv (fun x : ℝ => c * Real.sin ((k : ℝ) * x)) θ = c * ((k : ℝ) * Real.cos ((k : ℝ) * θ)) := by
  exact ((hasDerivAt_sin_mul k θ).const_mul c).deriv

lemma deriv_summand (k : ℕ) (a b : ℕ → ℝ) (θ : ℝ) :
    deriv (fun x : ℝ => a k * Real.cos ((k : ℝ) * x) + b k * Real.sin ((k : ℝ) * x)) θ
      = a k * (-(k : ℝ)) * Real.sin ((k : ℝ) * θ) + b k * (k : ℝ) * Real.cos ((k : ℝ) * θ) := by
  have hd1 : DifferentiableAt ℝ (fun x : ℝ => a k * Real.cos ((k : ℝ) * x)) θ := by
    fun_prop
  have hd2 : DifferentiableAt ℝ (fun x : ℝ => b k * Real.sin ((k : ℝ) * x)) θ := by
    fun_prop
  change deriv ((fun x : ℝ => a k * Real.cos ((k : ℝ) * x)) +
      (fun x : ℝ => b k * Real.sin ((k : ℝ) * x))) θ
      = a k * (-(k : ℝ)) * Real.sin ((k : ℝ) * θ) + b k * (k : ℝ) * Real.cos ((k : ℝ) * θ)
  rw [deriv_add hd1 hd2, deriv_cos_scaled, deriv_sin_scaled]
  ring

lemma deriv_TPoly (n : ℕ) (a b : ℕ → ℝ) (θ : ℝ) : deriv (TPoly n a b) θ = TDiff n a b θ := by
  have hfun : TPoly n a b =
      fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (a k * Real.cos ((k : ℝ) * x) + b k * Real.sin ((k : ℝ) * x)) := by rfl
  rw [hfun, TDiff]
  rw [deriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact deriv_summand k a b θ
  · intro k hk
    fun_prop

lemma continuous_TPoly (n : ℕ) (a b : ℕ → ℝ) : Continuous (TPoly n a b) := by
  -- each summand is continuous; sum is continuous
  have hsum : TPoly n a b =
      fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (a k * Real.cos ((k : ℝ) * x) + b k * Real.sin ((k : ℝ) * x)) := by rfl
  rw [hsum]
  fun_prop

lemma continuousOn_TPoly (n : ℕ) (a b : ℕ → ℝ) (s : Set ℝ) : ContinuousOn (TPoly n a b) s :=
  (continuous_TPoly n a b).continuousOn

/-! ## Complexification: zeros of a trig polynomial from roots of a complex polynomial -/

/-- e^{iθ} -/
def E (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

lemma E_zero : E 0 = 1 := by
  simp [E]

lemma E_ne_zero (θ : ℝ) : E θ ≠ 0 := by
  exact Complex.exp_ne_zero _

lemma E_nat_mul (θ : ℝ) (k : ℕ) : (E θ) ^ k = E ((k : ℝ) * θ) := by
  unfold E
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma E_ofReal_cos_sin (θ : ℝ) : E θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  simpa [E] using Complex.exp_ofReal_mul_I θ

lemma E_neg_mul (θ : ℝ) : E (-θ) * E θ = 1 := by
  unfold E
  rw [← Complex.exp_add]
  have h : (-(θ : ℂ)) * Complex.I + (θ : ℂ) * Complex.I = 0 := by ring
  simp [h]

lemma E_neg (θ : ℝ) : E (-θ) = (E θ)⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (E_neg_mul θ)

lemma E_add (θ φ : ℝ) : E (θ + φ) = E θ * E φ := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma E_nat (θ : ℝ) (k : ℕ) : E (k * θ) = E θ ^ k := (E_nat_mul θ k).symm

/-- (Eθ)^(n-k) = (Eθ)^n · (Eθ)^k⁻¹ when k ≤ n -/
lemma E_pow_sub (θ : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (E θ) ^ (n - k) = (E θ) ^ n * ((E θ) ^ k)⁻¹ := by
  have hpow : (E θ) ^ n = (E θ) ^ (n - k) * (E θ) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (E θ) ^ (n - k) = ((E θ) ^ n) * (((E θ) ^ k)⁻¹) := by
      rw [hpow]
      field_simp [E_ne_zero θ]

lemma E_cos_plus (θ : ℝ) : E θ + E (-θ) = (2 * Real.cos θ : ℂ) := by
  unfold E
  simp_rw [Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

lemma E_sin_diff (θ : ℝ) : E θ - E (-θ) = (2 * (Real.sin θ : ℂ)) * Complex.I := by
  unfold E
  simp_rw [Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring


/-- complex polynomial P_w with P_w(e^{iθ}) = e^{inθ}·W(θ) for the trig poly W with coeffs a,b -/
def Pc (n : ℕ) (a b : ℕ → ℝ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    (C ((a k : ℂ) / 2) * (X ^ (n + k) + X ^ (n - k)) +
     C (((b k : ℂ) * (-Complex.I)) / 2) * (X ^ (n + k) - X ^ (n - k)))

lemma Pc_eval (n : ℕ) (a b : ℕ → ℝ) (θ : ℝ) :
    (Pc n a b).eval (E θ) = (E θ) ^ n * (TPoly n a b θ : ℂ) := by
  -- per-k identity
  have per_k (k : ℕ) (hk : k ≤ n) :
      ((a k : ℂ) / 2) * ((E θ) ^ (n + k) + (E θ) ^ (n - k)) +
      (((b k : ℂ) * (-Complex.I)) / 2) * ((E θ) ^ (n + k) - (E θ) ^ (n - k))
      = (E θ) ^ n * ((a k * Real.cos ((k : ℝ) * θ) + b k * Real.sin ((k : ℝ) * θ) : ℝ) : ℂ) := by
    have hpow1 : (E θ) ^ (n + k) = (E θ) ^ n * (E θ) ^ k := by
      rw [← pow_add]
    have hpow2 : (E θ) ^ (n - k) = (E θ) ^ n * ((E θ) ^ k)⁻¹ := E_pow_sub θ n k hk
    have hz0 : (E θ) ^ k = E ((k : ℝ) * θ) := E_nat_mul θ k
    have hz : (E θ) ^ k + ((E θ) ^ k)⁻¹ = (2 * Real.cos ((k : ℝ) * θ) : ℂ) := by
      calc
        (E θ) ^ k + ((E θ) ^ k)⁻¹ = E ((k : ℝ) * θ) + (E ((k : ℝ) * θ))⁻¹ := by rw [hz0]
        _ = E ((k : ℝ) * θ) + E (-((k : ℝ) * θ)) := by rw [E_neg]
        _ = 2 * Real.cos ((k : ℝ) * θ) := E_cos_plus ((k : ℝ) * θ)
    have hd : (E θ) ^ k - ((E θ) ^ k)⁻¹ = (2 * (Real.sin ((k : ℝ) * θ) : ℂ)) * Complex.I := by
      calc
        (E θ) ^ k - ((E θ) ^ k)⁻¹ = E ((k : ℝ) * θ) - (E ((k : ℝ) * θ))⁻¹ := by rw [hz0]
        _ = E ((k : ℝ) * θ) - E (-((k : ℝ) * θ)) := by rw [E_neg]
        _ = (2 * (Real.sin ((k : ℝ) * θ) : ℂ)) * Complex.I := E_sin_diff ((k : ℝ) * θ)
    calc
      ((a k : ℂ) / 2) * ((E θ) ^ (n + k) + (E θ) ^ (n - k)) +
      (((b k : ℂ) * (-Complex.I)) / 2) * ((E θ) ^ (n + k) - (E θ) ^ (n - k))
        = (E θ) ^ n * (((a k : ℂ) / 2) * ((E θ) ^ k + ((E θ) ^ k)⁻¹) +
            (((b k : ℂ) * (-Complex.I)) / 2) * ((E θ) ^ k - ((E θ) ^ k)⁻¹)) := by
          rw [hpow1, hpow2]
          ring
      _ = (E θ) ^ n * (((a k : ℂ) / 2) * (2 * Real.cos ((k : ℝ) * θ) : ℂ) +
          (((b k : ℂ) * (-Complex.I)) / 2) * ((2 * (Real.sin ((k : ℝ) * θ) : ℂ)) * Complex.I)) := by
          rw [hz, hd]
      _ = (E θ) ^ n * ((a k * Real.cos ((k : ℝ) * θ) + b k * Real.sin ((k : ℝ) * θ) : ℝ) : ℂ) := by
          congr 1
          ring_nf
          rw [pow_two, Complex.I_mul_I]
          ring_nf
          norm_num
  -- main proof
  calc
    (Pc n a b).eval (E θ)
        = ∑ k ∈ Finset.range (n + 1),
            (((a k : ℂ) / 2) * ((E θ) ^ (n + k) + (E θ) ^ (n - k)) +
             (((b k : ℂ) * (-Complex.I)) / 2) * ((E θ) ^ (n + k) - (E θ) ^ (n - k))) := by
          unfold Pc
          simp [eval_finsetSum]
          -- hmm: simp may fully compute eval of the sum; verify
      _ = ∑ k ∈ Finset.range (n + 1), (E θ) ^ n * ((a k * Real.cos ((k : ℝ) * θ) +
            b k * Real.sin ((k : ℝ) * θ) : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact per_k k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      _ = (E θ) ^ n * (TPoly n a b θ : ℂ) := by
          rw [← Finset.mul_sum]
          congr 1
          unfold TPoly
          push_cast
          simp


lemma C_mul_X_pow_natDegree_le (m : ℕ) (c : ℂ) : (C c * X ^ m).natDegree ≤ m := by
  by_cases hc : c = 0
  · rw [hc]
    simp
  · exact le_of_eq (natDegree_C_mul_X_pow m c hc)

lemma natDegree_sum_le_of_le {ι : Type*} {d : ℕ} (s : Finset ι) (f : ι → ℂ[X])
    (h : ∀ i ∈ s, (f i).natDegree ≤ d) : (∑ i ∈ s, f i).natDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' has' ih =>
      rw [Finset.sum_insert has']
      exact (natDegree_add_le (f a) (∑ i ∈ s', f i)).trans (by
        rw [Nat.max_le]
        exact ⟨h a (by simp), ih (by intro i hi; exact h i (by simp [hi]))⟩)

lemma natDegree_mul_add_X_pow_le (a b : ℕ) (c : ℂ) :
    (C c * (X ^ a + X ^ b)).natDegree ≤ max a b := by
  have h1 := C_mul_X_pow_natDegree_le a c
  have h2 := C_mul_X_pow_natDegree_le b c
  calc
    (C c * (X ^ a + X ^ b)).natDegree = (C c * X ^ a + C c * X ^ b).natDegree := by
      rw [mul_add]
    _ ≤ max (C c * X ^ a).natDegree (C c * X ^ b).natDegree := natDegree_add_le _ _
    _ ≤ max a b := by
      exact max_le_max h1 h2

lemma natDegree_mul_sub_X_pow_le (a b : ℕ) (c : ℂ) :
    (C c * (X ^ a - X ^ b)).natDegree ≤ max a b := by
  have h1 := C_mul_X_pow_natDegree_le a c
  have h2 := C_mul_X_pow_natDegree_le b c
  calc
    (C c * (X ^ a - X ^ b)).natDegree = (C c * X ^ a - C c * X ^ b).natDegree := by
      rw [mul_sub]
    _ = (C c * X ^ a + -(C c * X ^ b)).natDegree := by simp [sub_eq_add_neg]
    _ ≤ max (C c * X ^ a).natDegree (-(C c * X ^ b)).natDegree := by
      exact natDegree_add_le (C c * X ^ a) (-(C c * X ^ b))
    _ ≤ max a b := by
      have h2' : (-(C c * X ^ b)).natDegree ≤ b := by simpa using h2
      exact max_le_max h1 h2'

lemma Pc_natDegree_le (n : ℕ) (a b : ℕ → ℝ) : (Pc n a b).natDegree ≤ 2 * n := by
  unfold Pc
  apply natDegree_sum_le_of_le
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hn1 : n + k ≤ 2 * n := by omega
  have hn2 : n - k ≤ 2 * n := by omega
  have hA : (C ((a k : ℂ) / 2) * (X ^ (n + k) + X ^ (n - k))).natDegree ≤ 2 * n := by
    exact le_trans (natDegree_mul_add_X_pow_le (n + k) (n - k) ((a k : ℂ) / 2)) (by
      exact max_le hn1 hn2)
  have hB : (C (((b k : ℂ) * (-Complex.I)) / 2) * (X ^ (n + k) - X ^ (n - k))).natDegree ≤ 2 * n := by
    exact le_trans (natDegree_mul_sub_X_pow_le (n + k) (n - k) (((b k : ℂ) * (-Complex.I)) / 2)) (by
      exact max_le hn1 hn2)
  have hmain : (C ((a k : ℂ) / 2) * (X ^ (n + k) + X ^ (n - k)) +
      C (((b k : ℂ) * (-Complex.I)) / 2) * (X ^ (n + k) - X ^ (n - k))).natDegree ≤ 2 * n := by
    exact le_trans (natDegree_add_le _ _) (by
      rw [Nat.max_le]
      exact ⟨hA, hB⟩)
  exact hmain

/-! ## Zero counting for trigonometric polynomials -/

lemma TPoly_eq_zero_of_eval_zero (n : ℕ) (a b : ℕ → ℝ)
    (h : ∀ θ : ℝ, TPoly n a b θ = 0) : ∀ θ : ℝ, (Pc n a b).eval (E θ) = 0 := by
  intro θ
  rw [Pc_eval]
  simp [h θ]

lemma Pc_ne_zero_of_exists_ne (n : ℕ) (a b : ℕ → ℝ) (h : ∃ θ, TPoly n a b θ ≠ 0) :
    Pc n a b ≠ 0 := by
  intro hP
  rcases h with ⟨θ, hθ⟩
  have hz := Pc_eval n a b θ
  rw [hP] at hz
  have hz0 : (TPoly n a b θ : ℂ) = 0 := by
    have hmul : (E θ) ^ n * (TPoly n a b θ : ℂ) = 0 := by
      simpa using hz.symm
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero n (E_ne_zero θ))
  exact hθ (by exact_mod_cast hz0)

lemma E_inj_window (lo : ℝ) : Set.InjOn E (Set.Ioo lo (lo + 2 * π)) := by
  intro x hx y hy hxy
  unfold E at hxy
  have hk := (Complex.exp_eq_exp_iff_exists_int.mp hxy)
  rcases hk with ⟨k, hk⟩
  have hz : (((x : ℂ) - (y : ℂ)) - (2 * π * (k : ℂ))) * Complex.I = 0 := by
    calc
      (((x : ℂ) - (y : ℂ)) - (2 * π * (k : ℂ))) * Complex.I
          = (x : ℂ) * Complex.I - (y : ℂ) * Complex.I - (2 * π * (k : ℂ)) * Complex.I := by ring
      _ = 0 := by
        rw [hk]
        ring
  have hx0 : (x : ℂ) - (y : ℂ) - (2 * π * (k : ℂ)) = 0 :=
    (mul_eq_zero.mp hz).resolve_right Complex.I_ne_zero
  have hreal : (x - y - 2 * π * (k : ℝ) : ℝ) = 0 := by
    have hkr : ((k : ℝ) : ℂ) = (k : ℂ) := by exact Complex.ofReal_intCast k
    rw [← hkr] at hx0
    exact_mod_cast hx0
  have hdiff : x - y = 2 * π * (k : ℝ) := by linarith
  have hbd : |x - y| < 2 * π := by
    rw [abs_lt]
    constructor
    · linarith [hx.1, hy.2]
    · linarith [hy.1, hx.2]
  rw [hdiff] at hbd
  have hk0 : k = 0 := by
    have h2π : 0 < 2 * π := by positivity
    have habs : (2 * π) * |(k : ℝ)| < 2 * π := by
      have htmp : |2 * π * (k : ℝ)| < 2 * π := by simpa using hbd
      simpa [abs_mul, abs_of_pos h2π] using htmp
    have habs1 : (2 * π) * |(k : ℝ)| < (2 * π) * 1 := by simpa using habs
    have hkabs : |(k : ℝ)| < 1 := lt_of_mul_lt_mul_left habs1 (le_of_lt h2π)
    have hk2 : (|k| : ℝ) < 1 := by
      simpa [Int.cast_abs] using hkabs
    have hkabs' : |k| < 1 := by exact_mod_cast hk2
    have hh : (-1 < k) ∧ k < 1 := (abs_lt.mp hkabs')
    omega
  subst k
  norm_num at hdiff
  linarith

lemma E_inj_image_card {lo : ℝ} (s : Finset ℝ)
    (hgt : ∀ x ∈ s, lo < x) (hlt : ∀ x ∈ s, x < lo + 2 * π) :
    (s.image E).card = s.card := by
  exact Finset.card_image_of_injOn (by
    intro x hx y hy hxy
    exact E_inj_window lo (by exact ⟨hgt x hx, hlt x hx⟩) (by exact ⟨hgt y hy, hlt y hy⟩) hxy)

lemma manyZeros {n : ℕ} {a b : ℕ → ℝ} (hW : ∃ θ, TPoly n a b θ ≠ 0)
    {s : Finset ℝ} (hs : s.card ≥ 2 * n + 1)
    (hz : ∀ x ∈ s, TPoly n a b x = 0)
    {lo : ℝ} (hgt : ∀ x ∈ s, lo < x) (hlt : ∀ x ∈ s, x < lo + 2 * π) :
    False := by
  have hP : Pc n a b ≠ 0 := Pc_ne_zero_of_exists_ne n a b hW
  let t : Finset ℂ := s.image E
  have hroot : ∀ z ∈ t, (Pc n a b).IsRoot z := by
    intro z hzmem
    rcases Finset.mem_image.mp hzmem with ⟨x, hxs, rfl⟩
    change (Pc n a b).eval (E x) = 0
    rw [Pc_eval]
    simp [hz x hxs]
  have hmem : ∀ z ∈ t, z ∈ (Pc n a b).roots := by
    intro z hzmem
    exact (Polynomial.mem_roots hP).mpr (hroot z hzmem)
  have hcard1 : t.card ≤ (Pc n a b).roots.card := by
    have hsub : t ⊆ (Pc n a b).roots.toFinset := by
      intro z hzmem
      exact Multiset.mem_toFinset.mpr (hmem z hzmem)
    exact le_trans (Finset.card_le_card hsub) (Multiset.toFinset_card_le (Pc n a b).roots)
  have hcard2 : (Pc n a b).roots.card ≤ 2 * n := by
    have hcr := Polynomial.card_roots hP
    have hdeg : (Pc n a b).degree = ↑(Pc n a b).natDegree := Polynomial.degree_eq_natDegree hP
    have hcr2 : ((Pc n a b).roots.card : WithBot ℕ) ≤ ((Pc n a b).natDegree : WithBot ℕ) := by
      simpa [hdeg] using hcr
    have hcr3 : (Pc n a b).roots.card ≤ (Pc n a b).natDegree := by exact_mod_cast hcr2
    exact le_trans hcr3 (Pc_natDegree_le n a b)
  have hcard3 : t.card = s.card := E_inj_image_card s hgt hlt
  omega

/-! ## Real analysis glue -/

/-- intermediate value with f(a) < 0 < f(b) -/
lemma exists_zero_neg_pos (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (h : f a < 0) (h' : 0 < f b) :
    ∃ z ∈ Set.Ioo a b, f z = 0 := by
  have hivt := intermediate_value_Icc (α := ℝ) (δ := ℝ) (f := f) (a := a) (b := b)
    (by exact le_of_lt hab) hf
  have hmem : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt h, le_of_lt h'⟩
  rcases hivt hmem with ⟨z, hzIcc, hz⟩
  refine ⟨z, ?_, hz⟩
  exact ⟨lt_of_le_of_ne hzIcc.1 (by intro h0; subst z; linarith),
    lt_of_le_of_ne hzIcc.2 (by intro h0; subst z; linarith)⟩

/-- sign change ⟹ zero in the open interval -/
lemma exists_zero_of_mul_neg (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (h : f a * f b < 0) :
    ∃ z ∈ Set.Ioo a b, f z = 0 := by
  rcases (mul_neg_iff.mp h) with ⟨hfa, hfb⟩ | ⟨hfa, hfb⟩
  · -- 0 < f a and f b < 0: apply to -f
    have h2 : (-f) a < 0 := by simpa
    have h3 : 0 < (-f) b := by simpa
    rcases exists_zero_neg_pos (-f) hab hf.neg h2 h3 with ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩
  · exact exists_zero_neg_pos f hab hf hfa hfb

/-- f'(η)>0, f(η)=0 ⟹ f<0 on a left-neighborhood of η -/
lemma lt_zero_left_of_deriv_pos (f : ℝ → ℝ) (η : ℝ) {c : ℝ} (hc : 0 < c)
    (h : HasDerivAt f c η) (h0 : f η = 0) :
    ∃ δ > 0, ∀ x, η - δ < x → x < η → f x < 0 := by
  have hc2 : 0 < c / 2 := by linarith
  have hEv0 : ∀ᶠ t in nhdsWithin 0 ({0}ᶜ : Set ℝ),
      ‖t⁻¹ • (f (η + t) - f η) - c‖ < c / 2 :=
    (h.tendsto_slope_zero).eventually (Metric.ball_mem_nhds c hc2)
  have hEv : ∀ᶠ t in nhdsWithin 0 ({0}ᶜ : Set ℝ), |t⁻¹ * (f (η + t) - f η) - c| < c / 2 := by
    simpa [Real.norm_eq_abs, smul_eq_mul] using hEv0
  rw [eventually_nhdsWithin_iff] at hEv
  rw [Metric.eventually_nhds_iff] at hEv
  rcases hEv with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx1 hx2
  let t : ℝ := x - η
  have ht : t < 0 := by dsimp [t]; linarith
  have htδ : |t| < δ := by
    dsimp [t]
    rw [abs_of_neg (by linarith : x - η < 0)]
    linarith
  have htnz : t ∈ ({0}ᶜ : Set ℝ) := by
    simpa using (ne_of_lt ht)
  have hp : |t⁻¹ * (f (η + t) - f η) - c| < c / 2 := by
    exact hδ' (y := t) (by simpa [Real.dist_eq] using htδ) htnz
  have hlo : c / 2 < t⁻¹ * (f (η + t) - f η) := by
    have hneg : -(c / 2) < t⁻¹ * (f (η + t) - f η) - c := (abs_lt.mp hp).1
    linarith
  have hy : f (η + t) - f η < (c / 2) * t := by
    have h1 : (t⁻¹ * (f (η + t) - f η)) * t < (c / 2) * t :=
      (mul_lt_mul_of_neg_right hlo ht)
    have hc2' : (t⁻¹ * (f (η + t) - f η)) * t = f (η + t) - f η := by
      field_simp [ne_of_lt ht]
    rwa [hc2'] at h1
  have hy0 : f (η + t) - f η < 0 := by
    have hpos : 0 < c / 2 := by linarith
    exact lt_trans hy (mul_neg_of_pos_of_neg hpos ht)
  have hy' : f (η + t) < 0 := by
    simpa [h0] using hy0
  simpa [t, add_comm, add_left_comm, add_assoc] using hy'


/-! ## Alternation / zero-counting contradiction -/

lemma strict_mono_of_step {p : ℕ → ℝ} {N : ℕ} (h : ∀ m, m < N → p m < p (m + 1)) :
    ∀ ⦃a b : ℕ⦄, a < b → b ≤ N → p a < p b := by
  intro a b hab hbN
  induction b with
  | zero => omega
  | succ b ih =>
      by_cases ha : a < b
      · have hb : b ≤ N := by omega
        have hpb := ih ha hb
        have hstep : p b < p (b + 1) := by
          have hb' : b < N := by omega
          exact h (b) hb'
        -- p a < p b < p (b+1) = p (succ b): rewrite succ
        simpa [Nat.succ_eq_add_one] using lt_trans hpb hstep
      · have : a = b := by omega
        subst a
        have hb' : b < N := by omega
        simpa [Nat.succ_eq_add_one] using h b hb'

lemma manyZeros_param {n : ℕ} {a b : ℕ → ℝ} (hW : ∃ θ, TPoly n a b θ ≠ 0)
    {p : ℕ → ℝ}
    (hmonop : ∀ m, m < 2 * n → p m < p (m + 1))
    (hz : ∀ m ≤ 2 * n, TPoly n a b (p m) = 0)
    {lo : ℝ} (hgt : ∀ m ≤ 2*n, lo < p m) (hhi : ∀ m ≤ 2*n, p m < lo + 2 * π) :
    False := by
  let s : Finset ℝ := (Finset.range (2 * n + 1)).image p
  have hcard : s.card = 2 * n + 1 := by
    dsimp [s]
    rw [Finset.card_image_of_injOn]
    · simp
    · -- injective on the finset
      intro x hx y hy hxy
      have hx' : x ≤ 2 * n := by
        simpa using (Finset.mem_range.mp hx)
      have hy' : y ≤ 2 * n := by
        simpa using (Finset.mem_range.mp hy)
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hpxy : p x < p y := strict_mono_of_step hmonop hlt hy'
        exact (ne_of_lt hpxy) hxy
      · have hpyx : p y < p x := strict_mono_of_step hmonop hlt hx'
        exact (ne_of_lt hpyx) hxy.symm
  have hzeros : ∀ z ∈ s, TPoly n a b z = 0 := by
    intro z hzmem
    rcases Finset.mem_image.mp hzmem with ⟨m, hm, rfl⟩
    have hm' : m ≤ 2 * n := by simpa using (Finset.mem_range.mp hm)
    exact hz m hm'
  have hgt' : ∀ z ∈ s, lo < z := by
    intro z hzmem
    rcases Finset.mem_image.mp hzmem with ⟨m, hm, rfl⟩
    exact hgt m (by simpa using (Finset.mem_range.mp hm))
  have hhi' : ∀ z ∈ s, z < lo + 2 * π := by
    intro z hzmem
    rcases Finset.mem_image.mp hzmem with ⟨m, hm, rfl⟩
    exact hhi m (by simpa using (Finset.mem_range.mp hm))
  have hcard' : s.card ≥ 2 * n + 1 := by omega
  exact manyZeros hW hcard' hzeros hgt' hhi'



/-- Contradiction from strict sign alternation at 2n+1 points plus an interior zero with
positive derivative. -/
lemma alternation_contradiction {n : ℕ} (hn : 1 ≤ n) {a b : ℕ → ℝ}
    (hW : ∃ θ, TPoly n a b θ ≠ 0)
    {t : ℕ → ℝ} (hpos : 0 < TPoly n a b (t 0))
    (halt : ∀ m, m < 2 * n → (TPoly n a b (t m)) * (TPoly n a b (t (m + 1))) < 0)
    (hmono : ∀ m, m < 2 * n → t m < t (m + 1))
    (hend : t (2 * n) = t 0 + 2 * π)
    {η : ℝ} (ht0η : t 0 < η) (hηt1 : η < t 1)
    (hWη : TPoly n a b η = 0)
    (hW' : 0 < deriv (TPoly n a b) η) : False := by
  have hfun : TPoly n a b =
      fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (a k * Real.cos ((k : ℝ) * x) + b k * Real.sin ((k : ℝ) * x)) := by rfl
  have hD : DifferentiableAt ℝ (TPoly n a b) η := by
    rw [hfun]
    fun_prop
  have hd := lt_zero_left_of_deriv_pos (TPoly n a b) η (c := deriv (TPoly n a b) η) hW'
    hD.hasDerivAt hWη
  rcases hd with ⟨δ, hδ, hδ'⟩
  let x0 : ℝ := (max (t 0) (η - δ) + η) / 2
  have hx0a : t 0 < x0 := by
    dsimp [x0]
    have hu : max (t 0) (η - δ) < η := max_lt ht0η (by linarith)
    have hu' : t 0 ≤ max (t 0) (η - δ) := le_max_left _ _
    linarith
  have hx0b : x0 < η := by
    dsimp [x0]
    have hu : max (t 0) (η - δ) < η := max_lt ht0η (by linarith)
    linarith
  have hx0c : η - δ < x0 := by
    dsimp [x0]
    have hu' : η - δ ≤ max (t 0) (η - δ) := le_max_right _ _
    have hu : max (t 0) (η - δ) < η := max_lt ht0η (by linarith)
    linarith
  have hWx0 : TPoly n a b x0 < 0 := hδ' x0 hx0c hx0b
  have hprod0 : TPoly n a b (t 0) * TPoly n a b x0 < 0 := mul_neg_of_pos_of_neg hpos hWx0
  rcases exists_zero_of_mul_neg (TPoly n a b) hx0a (continuousOn_TPoly n a b (Set.Icc (t 0) x0)) hprod0 with
    ⟨zL, hzL, hWzL⟩
  let zz : ℕ → ℝ := fun m =>
    if h : m < 2 * n then
      Classical.choose (exists_zero_of_mul_neg (TPoly n a b) (hmono m h)
        (continuousOn_TPoly n a b (Set.Icc (t m) (t (m + 1)))) (halt m h))
    else 0
  have hzz : ∀ m, m < 2 * n → zz m ∈ Set.Ioo (t m) (t (m + 1)) ∧ TPoly n a b (zz m) = 0 := by
    intro m hm
    dsimp [zz]
    rw [dif_pos hm]
    exact Classical.choose_spec (exists_zero_of_mul_neg (TPoly n a b) (hmono m hm)
      (continuousOn_TPoly n a b (Set.Icc (t m) (t (m + 1)))) (halt m hm))
  let q : ℕ → ℝ := fun j => if j = 0 then zL else if j = 1 then η else zz (j - 1)
  -- increasing
  have hmono_t : ∀ ⦃a b : ℕ⦄, a < b → b ≤ 2 * n → t a < t b := strict_mono_of_step hmono
  have hqmono : ∀ m, m < 2 * n → q m < q (m + 1) := by
    intro m hm
    by_cases hm0 : m = 0
    · subst m
      dsimp [q]
      have h : zL < η := lt_trans hzL.2 hx0b
      simpa
    · have hm1a : 1 ≤ m := by omega
      by_cases hm1 : m = 1
      · subst m
        dsimp [q]
        -- η < zz 1
        have h1' : zz 1 > t 1 := (hzz 1 (by omega)).1.1
        exact lt_trans hηt1 h1'
      · -- m ≥ 2: zz(m-1) < t_m < zz m
        have hm2 : 2 ≤ m := by omega
        have h1 : m ≠ 1 := by omega
        have hz1 : zz (m - 1) < t m := by
          have hmm : m - 1 < 2 * n := by omega
          have h := (hzz (m - 1) hmm).1.2
          have hstep : m - 1 + 1 = m := by omega
          rwa [hstep] at h
        have hz2 : t m < zz m := by
          exact (hzz m hm).1.1
        -- q m = zz (m-1); q (m+1) = zz m
        dsimp [q]
        simp [hm0, h1]
        exact lt_trans hz1 hz2
  -- zeros
  have hqz : ∀ m ≤ 2 * n, TPoly n a b (q m) = 0 := by
    intro m hm
    by_cases hm0 : m = 0
    · subst m; dsimp [q]; exact hWzL
    · by_cases hm1 : m = 1
      · subst m; dsimp [q]; exact hWη
      · dsimp [q]
        simp [hm0, hm1]
        have hmm : m - 1 < 2 * n := by omega
        exact (hzz (m - 1) hmm).2
  -- bounds below: t 0 < q m
  have hqgt : ∀ m ≤ 2 * n, t 0 < q m := by
    intro m hm
    by_cases hm0 : m = 0
    · subst m; dsimp [q]; exact hzL.1
    · by_cases hm1 : m = 1
      · subst m; dsimp [q]; exact ht0η
      · have hm2 : 1 ≤ m := by omega
        have hmm : m - 1 < 2 * n := by omega
        have hz1 : t (m - 1) < zz (m - 1) := (hzz (m - 1) hmm).1.1
        have ht01 : t 0 < t (m - 1) := by
          have hmm' : 0 < m - 1 := by omega
          exact hmono_t hmm' (by omega)
        dsimp [q]
        simp [hm0, hm1]
        exact lt_trans ht01 hz1
  -- bounds above: q m < t (2n)
  have hqhi : ∀ m ≤ 2 * n, q m < t (2 * n) := by
    intro m hm
    by_cases hm0 : m = 0
    · subst m
      dsimp [q]
      have ht1n : t 1 < t (2 * n) := by
        have h1 : 1 < 2 * n := by omega
        exact hmono_t h1 (by omega)
      exact lt_trans hzL.2 (lt_trans hx0b (lt_trans hηt1 ht1n))
    · by_cases hm1 : m = 1
      · subst m
        dsimp [q]
        have ht1n : t 1 < t (2 * n) := by
          have h1 : 1 < 2 * n := by omega
          exact hmono_t h1 (by omega)
        exact lt_trans hηt1 ht1n
      · have hm2 : 1 ≤ m := by omega
        have hmm : m - 1 < 2 * n := by omega
        have hz2 : zz (m - 1) < t m := by
          have h := (hzz (m - 1) hmm).1.2
          have hstep : m - 1 + 1 = m := by omega
          rwa [hstep] at h
        have htm : t m ≤ t (2 * n) := by
          by_cases hmlt : m < 2 * n
          · exact le_of_lt (hmono_t hmlt (by omega))
          · have : m = 2 * n := by omega
            subst m
            rfl
        dsimp [q]
        simp [hm0, hm1]
        exact lt_of_lt_of_le hz2 htm
  -- apply manyZeros_param
  exact manyZeros_param (a := a) (b := b) hW hqmono hqz hqgt (by
    intro m hm
    rw [← hend]
    exact hqhi m hm)


