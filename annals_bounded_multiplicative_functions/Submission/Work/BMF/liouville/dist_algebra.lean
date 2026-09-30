import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Polynomial BoundedMultiplicativeFunctions
open scoped ComplexConjugate

/-! ### Pointwise complex inequalities

These are the two elementary inequalities behind the `𝔻`-algebra: the power bound
`1 - Re(u^m) ≤ m²(1 - Re u)` and the "quasi-triangle" bound for `1 - Re(zw)`,
both for arguments in the closed unit disc.
-/

/-- `2 (1 - Re x) = ‖1 - x‖² + (1 - ‖x‖²)` for complex `x`. -/
private lemma two_mul_one_sub_re (x : ℂ) :
    2 * (1 - x.re) = ‖(1:ℂ) - x‖ ^ 2 + (1 - ‖x‖ ^ 2) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  simp [Complex.conj_re]
  ring

/-- For `‖u‖ ≤ 1`: `‖1 - u^m‖ ≤ m ‖1 - u‖`. -/
private lemma norm_one_sub_pow_le (u : ℂ) (hu : ‖u‖ ≤ 1) (m : ℕ) :
    ‖(1:ℂ) - u^m‖ ≤ (m:ℝ) * ‖(1:ℂ) - u‖ := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hstep : (1:ℂ) - u^(k+1) = u^k * (1-u) + (1 - u^k) := by
        rw [pow_succ]; ring
      have hnk : ‖u^k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hu
      calc ‖(1:ℂ) - u^(k+1)‖
          = ‖u^k * (1-u) + (1 - u^k)‖ := by rw [hstep]
        _ ≤ ‖u^k * (1-u)‖ + ‖(1:ℂ) - u^k‖ := norm_add_le _ _
        _ = ‖u^k‖ * ‖(1:ℂ) - u‖ + ‖(1:ℂ) - u^k‖ := by rw [norm_mul]
        _ ≤ 1 * ‖(1:ℂ) - u‖ + (k:ℝ) * ‖(1:ℂ) - u‖ :=
              add_le_add (mul_le_mul_of_nonneg_right hnk (norm_nonneg _)) ih
        _ = ((k:ℝ) + 1) * ‖(1:ℂ) - u‖ := by ring
        _ = ((k+1 : ℕ) : ℝ) * ‖(1:ℂ) - u‖ := by push_cast; ring

/-- For `‖u‖ ≤ 1` and `1 ≤ m`: `1 - Re(u^m) ≤ m² (1 - Re u)`. -/
private lemma one_sub_re_pow_le (u : ℂ) (hu : ‖u‖ ≤ 1) (m : ℕ) (hm : 1 ≤ m) :
    1 - (u ^ m).re ≤ (m : ℝ) ^ 2 * (1 - u.re) := by
  have hnorm : ‖u^m‖ ^ 2 = (‖u‖^2)^m := by
    rw [norm_pow, ← pow_mul, ← pow_mul, mul_comm]
  have h1 : ‖(1:ℂ) - u^m‖ ^ 2 ≤ (m:ℝ)^2 * ‖(1:ℂ) - u‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg ((1:ℂ) - u^m)) (norm_one_sub_pow_le u hu m) 2
    rwa [mul_pow] at h
  have h2 : 1 - ‖u^m‖^2 ≤ (m:ℝ)^2 * (1 - ‖u‖^2) := by
    have hr2 : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u, hu]
    have hbern := one_add_mul_le_pow (show (-2:ℝ) ≤ ‖u‖^2 - 1 by nlinarith [sq_nonneg ‖u‖]) m
    have hb : 1 - (‖u‖^2)^m ≤ (m:ℝ) * (1 - ‖u‖^2) := by
      have h2' : 1 + (‖u‖^2 - 1) = ‖u‖^2 := by ring
      rw [h2'] at hbern
      linarith
    have hm2 : (m:ℝ) ≤ (m:ℝ)^2 := by
      have : (1:ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    have h3 : 0 ≤ 1 - ‖u‖^2 := by linarith
    calc 1 - ‖u^m‖^2 = 1 - (‖u‖^2)^m := by rw [hnorm]
      _ ≤ (m:ℝ) * (1 - ‖u‖^2) := hb
      _ ≤ (m:ℝ)^2 * (1 - ‖u‖^2) := mul_le_mul_of_nonneg_right hm2 h3
  have hsum : ‖(1:ℂ) - u^m‖ ^ 2 + (1 - ‖u^m‖^2) ≤ (m:ℝ)^2 * (2 * (1 - u.re)) := by
    calc ‖(1:ℂ) - u^m‖ ^ 2 + (1 - ‖u^m‖^2)
        ≤ (m:ℝ)^2 * ‖(1:ℂ) - u‖ ^ 2 + (m:ℝ)^2 * (1 - ‖u‖^2) := add_le_add h1 h2
      _ = (m:ℝ)^2 * (‖(1:ℂ) - u‖ ^ 2 + (1 - ‖u‖^2)) := by ring
      _ = (m:ℝ)^2 * (2 * (1 - u.re)) := by rw [two_mul_one_sub_re u]
  rw [← two_mul_one_sub_re (u^m)] at hsum
  linarith

/-- For `‖z‖, ‖w‖ ≤ 1`: `1 - Re(zw) ≤ (1-Re z) + (1-Re w) + 2√((1-Re z)(1-Re w))`. -/
private lemma one_sub_re_mul_le (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    1 - (z*w).re ≤ (1 - z.re) + (1 - w.re) + 2*Real.sqrt ((1-z.re)*(1-w.re)) := by
  have hA : 0 ≤ 1 - z.re := by have := Complex.re_le_norm z; linarith
  have hB : 0 ≤ 1 - w.re := by have := Complex.re_le_norm w; linarith
  have ha2 : ‖(1:ℂ)-z‖^2 ≤ 2*(1 - z.re) := by
    have h := two_mul_one_sub_re z
    have hz2 : ‖z‖^2 ≤ 1 := by nlinarith [norm_nonneg z]
    linarith
  have hb2 : ‖(1:ℂ)-w‖^2 ≤ 2*(1 - w.re) := by
    have h := two_mul_one_sub_re w
    have hw2 : ‖w‖^2 ≤ 1 := by nlinarith [norm_nonneg w]
    linarith
  have hprod : ‖(1:ℂ)-z‖ * ‖(1:ℂ)-w‖ ≤ 2 * Real.sqrt ((1-z.re)*(1-w.re)) := by
    have hxx : (‖(1:ℂ)-z‖ * ‖(1:ℂ)-w‖)^2 ≤ (2 * Real.sqrt ((1-z.re)*(1-w.re)))^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hA hB)]
      nlinarith [ha2, hb2, norm_nonneg ((1:ℂ)-z), norm_nonneg ((1:ℂ)-w)]
    have hle := sq_le_sq.mp hxx
    rwa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
         abs_of_nonneg (by positivity)] at hle
  have hre : (1:ℂ) - z*w = (1 - z) + (1 - w) - (1 - z)*(1 - w) := by ring
  have hbound : 1 - (z*w).re ≤ (1 - z.re) + (1 - w.re) + ‖(1:ℂ)-z‖ * ‖(1:ℂ)-w‖ := by
    have h1 : 1 - (z*w).re = (1 - z.re) + (1 - w.re) - ((1 - z)*(1 - w)).re := by
      have e : 1 - (z*w).re = ((1:ℂ) - z*w).re := by rw [Complex.sub_re, Complex.one_re]
      rw [e, hre]
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
    have h2 : -(((1 - z)*(1 - w)).re) ≤ ‖(1:ℂ)-z‖ * ‖(1:ℂ)-w‖ := by
      have h := Complex.re_le_norm (-((1 - z)*(1 - w)))
      rw [Complex.neg_re, norm_neg, norm_mul] at h
      exact h
    rw [h1]; linarith
  linarith

/-- Division under a square root: `√(A/p · B/p) = √(A·B)/p` for `A,B,p ≥ 0`. -/
private lemma sqrt_mul_div_eq (A B p : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) :
    Real.sqrt (A / p * (B / p)) = Real.sqrt (A * B) / p := by
  rw [show A / p * (B / p) = A * B / p ^ 2 by ring,
      Real.sqrt_div (mul_nonneg hA hB) (p^2), Real.sqrt_sq hp]

/-! ### The `𝔻` sums -/

/-- The `p`-th summand of `𝔻` is nonnegative for one-bounded `f`, `g`. -/
private lemma D_term_nonneg {f g : ℕ → ℂ} (hf : IsOneBounded f) (hg : IsOneBounded g) (p : ℕ) :
    0 ≤ (1 - (f p * conj (g p)).re) / (p : ℝ) := by
  have hle : (f p * conj (g p)).re ≤ 1 := by
    have h := Complex.re_le_norm (f p * conj (g p))
    have h2 : ‖f p * conj (g p)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg (f p), norm_nonneg (g p), hf p, hg p]
    linarith
  exact div_nonneg (by linarith) (Nat.cast_nonneg p)

/-- `𝔻 f g X` is the square root of the defining prime sum. -/
private lemma dist_eq_sqrt (f g : ℕ → ℂ) (X : ℝ) :
    𝔻 f g X = Real.sqrt (∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) := by
  rw [BoundedMultiplicativeFunctions.𝔻, ← Real.sqrt_eq_rpow]

/-- The squared identity for `𝔻`. -/
private lemma dist_sq_eq {f g : ℕ → ℂ} (hf : IsOneBounded f) (hg : IsOneBounded g) (X : ℝ) :
    (𝔻 f g X) ^ 2 = ∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ) := by
  rw [dist_eq_sqrt f g X]
  exact Real.sq_sqrt (Finset.sum_nonneg (fun p _ => D_term_nonneg hf hg p))

/-- Monotonicity of the `𝔻`-sum over sub-families of primes. -/
private lemma dist_subset_le {f g : ℕ → ℂ} (hf : IsOneBounded f) (hg : IsOneBounded g)
    {X : ℝ} {S : Finset ℕ} (hS : S ⊆ ⌊X⌋₊.primesLE) :
    (∑ p ∈ S, (1 - (f p * conj (g p)).re) / (p : ℝ)) ≤ (𝔻 f g X) ^ 2 := by
  rw [dist_sq_eq hf hg X]
  exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun i _ _ => D_term_nonneg hf hg i)

/-- Numeric bound on the pointwise quotient `(1 - Re(f p conj (g p)))/p`. -/
private lemma norm_mul_conj_le_one {f g : ℕ → ℂ} (hf : IsOneBounded f) (hg : IsOneBounded g)
    (n : ℕ) : ‖f n * conj (g n)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg (f n), norm_nonneg (g n), hf n, hg n]

/-! ### The power inequality -/

/-- Conjugation commutes with powers. -/
private lemma conj_pow_eq (z : ℂ) (m : ℕ) : conj (z ^ m) = (conj z) ^ m := map_pow _ z m

private lemma pow_term_le {f g : ℕ → ℂ} (hf : IsOneBounded f) (hg : IsOneBounded g)
    (m : ℕ) (hm : 1 ≤ m) (p : ℕ) :
    (1 - (f p ^ m * conj (g p ^ m)).re) / (p : ℝ) ≤
      (m : ℝ) ^ 2 * ((1 - (f p * conj (g p)).re) / (p : ℝ)) := by
  have hu : ‖f p * conj (g p)‖ ≤ 1 := norm_mul_conj_le_one hf hg p
  have hpw : f p ^ m * conj (g p ^ m) = (f p * conj (g p)) ^ m := by
    rw [conj_pow_eq, ← mul_pow]
  rw [hpw]
  calc (1 - ((f p * conj (g p)) ^ m).re) / (p:ℝ)
      ≤ ((m:ℝ)^2 * (1 - (f p * conj (g p)).re)) / (p:ℝ) :=
        div_le_div_of_nonneg_right (one_sub_re_pow_le _ hu m hm) (Nat.cast_nonneg p)
    _ = (m:ℝ)^2 * ((1 - (f p * conj (g p)).re) / (p:ℝ)) := by ring

private lemma dist_pow_le {f g : ℕ → ℂ} (hf : IsOneBounded f) (hg : IsOneBounded g)
    (X : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    𝔻 (fun n ↦ f n ^ m) (fun n ↦ g n ^ m) X ≤ (m : ℝ) * 𝔻 f g X := by
  have hle : (∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p ^ m * conj (g p ^ m)).re) / (p : ℝ))
      ≤ (m:ℝ)^2 * ∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _ => pow_term_le hf hg m hm p)
  calc 𝔻 (fun n ↦ f n ^ m) (fun n ↦ g n ^ m) X
      = Real.sqrt (∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p ^ m * conj (g p ^ m)).re) / (p : ℝ)) :=
        dist_eq_sqrt _ _ X
    _ ≤ Real.sqrt ((m:ℝ)^2 * ∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) :=
        Real.sqrt_le_sqrt hle
    _ = (m:ℝ) * Real.sqrt (∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg m)]
    _ = (m:ℝ) * 𝔻 f g X := by rw [dist_eq_sqrt f g X]

/-! ### The triangle inequality -/

private lemma dist_mul_le (f₁ f₂ g₁ g₂ : ℕ → ℂ) (X : ℝ)
    (h1 : IsOneBounded f₁) (h2 : IsOneBounded f₂) (h3 : IsOneBounded g₁) (h4 : IsOneBounded g₂) :
    𝔻 (fun n ↦ f₁ n * f₂ n) (fun n ↦ g₁ n * g₂ n) X ≤ 𝔻 f₁ g₁ X + 𝔻 f₂ g₂ X := by
  set A : ℕ → ℝ := fun p => (1 - (f₁ p * conj (g₁ p)).re) / (p : ℝ) with hA
  set B : ℕ → ℝ := fun p => (1 - (f₂ p * conj (g₂ p)).re) / (p : ℝ) with hB
  have hA0 : ∀ p, 0 ≤ A p := fun p => D_term_nonneg h1 h3 p
  have hB0 : ∀ p, 0 ≤ B p := fun p => D_term_nonneg h2 h4 p
  have hsumA : (∑ p ∈ ⌊X⌋₊.primesLE, A p) = (𝔻 f₁ g₁ X) ^ 2 := (dist_sq_eq h1 h3 X).symm
  have hsumB : (∑ p ∈ ⌊X⌋₊.primesLE, B p) = (𝔻 f₂ g₂ X) ^ 2 := (dist_sq_eq h2 h4 X).symm
  have hpt : ∀ p ∈ ⌊X⌋₊.primesLE,
      (1 - ((f₁ p * f₂ p) * conj (g₁ p * g₂ p)).re) / (p : ℝ)
        ≤ A p + B p + 2 * Real.sqrt (A p * B p) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesLE hp).two_le
    have hpp : (0:ℝ) < (p:ℝ) := by
      have h2' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
      linarith
    have hz : ‖f₁ p * conj (g₁ p)‖ ≤ 1 := norm_mul_conj_le_one h1 h3 p
    have hw : ‖f₂ p * conj (g₂ p)‖ ≤ 1 := norm_mul_conj_le_one h2 h4 p
    have hmul := one_sub_re_mul_le (f₁ p * conj (g₁ p)) (f₂ p * conj (g₂ p)) hz hw
    have hzw : f₁ p * f₂ p * conj (g₁ p * g₂ p)
        = (f₁ p * conj (g₁ p)) * (f₂ p * conj (g₂ p)) := by rw [map_mul]; ring
    have hzA : 0 ≤ 1 - (f₁ p * conj (g₁ p)).re := by
      have h := Complex.re_le_norm (f₁ p * conj (g₁ p)); linarith
    have hzB : 0 ≤ 1 - (f₂ p * conj (g₂ p)).re := by
      have h := Complex.re_le_norm (f₂ p * conj (g₂ p)); linarith
    have hsqrt := sqrt_mul_div_eq (1 - (f₁ p * conj (g₁ p)).re)
      (1 - (f₂ p * conj (g₂ p)).re) (p:ℝ) hzA hzB (le_of_lt hpp)
    rw [hzw]
    have hgoal := div_le_div_of_nonneg_right hmul (le_of_lt hpp)
    calc (1 - ((f₁ p * conj (g₁ p)) * (f₂ p * conj (g₂ p))).re) / (p:ℝ)
        ≤ ((1 - (f₁ p * conj (g₁ p)).re) + (1 - (f₂ p * conj (g₂ p)).re)
            + 2 * Real.sqrt ((1 - (f₁ p * conj (g₁ p)).re)
                * (1 - (f₂ p * conj (g₂ p)).re))) / (p:ℝ) := hgoal
      _ = A p + B p + 2 * Real.sqrt (A p * B p) := by
          rw [hA, hB, hsqrt]; ring
  have hsumC : (∑ p ∈ ⌊X⌋₊.primesLE, (1 - ((f₁ p * f₂ p) * conj (g₁ p * g₂ p)).re) / (p : ℝ))
      ≤ ∑ p ∈ ⌊X⌋₊.primesLE, (A p + B p + 2 * Real.sqrt (A p * B p)) :=
    Finset.sum_le_sum hpt
  have hsplit : (∑ p ∈ ⌊X⌋₊.primesLE, (A p + B p + 2 * Real.sqrt (A p * B p)))
      = (∑ p ∈ ⌊X⌋₊.primesLE, A p) + (∑ p ∈ ⌊X⌋₊.primesLE, B p)
        + 2 * ∑ p ∈ ⌊X⌋₊.primesLE, Real.sqrt (A p * B p) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcs : (∑ p ∈ ⌊X⌋₊.primesLE, Real.sqrt (A p * B p))
      ≤ Real.sqrt (∑ p ∈ ⌊X⌋₊.primesLE, A p) * Real.sqrt (∑ p ∈ ⌊X⌋₊.primesLE, B p) := by
    have h := Real.sum_sqrt_mul_sqrt_le ⌊X⌋₊.primesLE hA0 hB0
    have heq : (∑ p ∈ ⌊X⌋₊.primesLE, Real.sqrt (A p * B p))
        = ∑ p ∈ ⌊X⌋₊.primesLE, Real.sqrt (A p) * Real.sqrt (B p) :=
      Finset.sum_congr rfl (fun p _ => Real.sqrt_mul (hA0 p) (B p))
    rw [heq]; exact h
  have hD1 : Real.sqrt (∑ p ∈ ⌊X⌋₊.primesLE, A p) = 𝔻 f₁ g₁ X := by
    have hnn : 0 ≤ 𝔻 f₁ g₁ X := by rw [dist_eq_sqrt f₁ g₁ X]; exact Real.sqrt_nonneg _
    rw [hsumA, Real.sqrt_sq hnn]
  have hD2 : Real.sqrt (∑ p ∈ ⌊X⌋₊.primesLE, B p) = 𝔻 f₂ g₂ X := by
    have hnn : 0 ≤ 𝔻 f₂ g₂ X := by rw [dist_eq_sqrt f₂ g₂ X]; exact Real.sqrt_nonneg _
    rw [hsumB, Real.sqrt_sq hnn]
  have hfinal : (∑ p ∈ ⌊X⌋₊.primesLE, (1 - ((f₁ p * f₂ p) * conj (g₁ p * g₂ p)).re) / (p : ℝ))
      ≤ (𝔻 f₁ g₁ X + 𝔻 f₂ g₂ X) ^ 2 := by
    calc (∑ p ∈ ⌊X⌋₊.primesLE, (1 - ((f₁ p * f₂ p) * conj (g₁ p * g₂ p)).re) / (p : ℝ))
        ≤ ∑ p ∈ ⌊X⌋₊.primesLE, (A p + B p + 2 * Real.sqrt (A p * B p)) := hsumC
      _ = (∑ p ∈ ⌊X⌋₊.primesLE, A p) + (∑ p ∈ ⌊X⌋₊.primesLE, B p)
            + 2 * ∑ p ∈ ⌊X⌋₊.primesLE, Real.sqrt (A p * B p) := hsplit
      _ ≤ (∑ p ∈ ⌊X⌋₊.primesLE, A p) + (∑ p ∈ ⌊X⌋₊.primesLE, B p)
            + 2 * (Real.sqrt (∑ p ∈ ⌊X⌋₊.primesLE, A p)
                * Real.sqrt (∑ p ∈ ⌊X⌋₊.primesLE, B p)) := by linarith [hcs]
      _ = (𝔻 f₁ g₁ X) ^ 2 + (𝔻 f₂ g₂ X) ^ 2 + 2 * (𝔻 f₁ g₁ X * 𝔻 f₂ g₂ X) := by
            rw [hD1, hD2, hsumA, hsumB]
      _ = (𝔻 f₁ g₁ X + 𝔻 f₂ g₂ X) ^ 2 := by ring
  calc 𝔻 (fun n ↦ f₁ n * f₂ n) (fun n ↦ g₁ n * g₂ n) X
      = Real.sqrt (∑ p ∈ ⌊X⌋₊.primesLE,
          (1 - ((f₁ p * f₂ p) * conj (g₁ p * g₂ p)).re) / (p : ℝ)) := dist_eq_sqrt _ _ X
    _ ≤ Real.sqrt ((𝔻 f₁ g₁ X + 𝔻 f₂ g₂ X) ^ 2) := Real.sqrt_le_sqrt hfinal
    _ = 𝔻 f₁ g₁ X + 𝔻 f₂ g₂ X := by
        rw [Real.sqrt_sq]
        have hnn : 0 ≤ 𝔻 f₁ g₁ X := by rw [dist_eq_sqrt f₁ g₁ X]; exact Real.sqrt_nonneg _
        have hnn2 : 0 ≤ 𝔻 f₂ g₂ X := by rw [dist_eq_sqrt f₂ g₂ X]; exact Real.sqrt_nonneg _
        linarith

/-- The elementary algebra of the pretentious distance `𝔻` for `1`-bounded functions:
the squared identity, monotonicity under sub-sums over primes, the
Granville–Soundararajan triangle inequality, and its `m`-th power consequence. -/
theorem dist_algebra :
    (∀ (f g : ℕ → ℂ) (X : ℝ), IsOneBounded f → IsOneBounded g →
        (𝔻 f g X) ^ 2 = ∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p * conj (g p)).re) / p) ∧
    (∀ (f g : ℕ → ℂ) (X : ℝ) (S : Finset ℕ), IsOneBounded f → IsOneBounded g →
        S ⊆ ⌊X⌋₊.primesLE →
        (∑ p ∈ S, (1 - (f p * conj (g p)).re) / p) ≤ (𝔻 f g X) ^ 2) ∧
    (∀ (f g : ℕ → ℂ) (X : ℝ) (m : ℕ), 1 ≤ m → IsOneBounded f → IsOneBounded g →
        𝔻 (fun n ↦ f n ^ m) (fun n ↦ g n ^ m) X ≤ (m : ℝ) * 𝔻 f g X) ∧
    (∀ (f₁ f₂ g₁ g₂ : ℕ → ℂ) (X : ℝ), IsOneBounded f₁ → IsOneBounded f₂ → IsOneBounded g₁ →
        IsOneBounded g₂ →
        𝔻 (fun n ↦ f₁ n * f₂ n) (fun n ↦ g₁ n * g₂ n) X ≤
          𝔻 f₁ g₁ X + 𝔻 f₂ g₂ X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f g X hf hg; exact dist_sq_eq hf hg X
  · intro f g X S hf hg hS; exact dist_subset_le hf hg hS
  · intro f g X m hm hf hg; exact dist_pow_le hf hg X m hm
  · intro f₁ f₂ g₁ g₂ X h1 h2 h3 h4; exact dist_mul_le f₁ f₂ g₁ g₂ X h1 h2 h3 h4

end Work.BMF.liouville
