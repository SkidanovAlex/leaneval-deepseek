import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Algebra.Binomial.trunc_inv_add_one

open Polynomial
open scoped BigOperators

namespace Commons.FieldTheory.Polynomial

/-- Scalar left-multiplication distributes into a sum of monomials. -/
private lemma scalar_mul_sum_X_pow {K : Type*} [CommSemiring K] (s : Finset ℕ) (a : K)
    (g : ℕ → K) :
    C a * (∑ k ∈ s, C (g k) * X ^ k) = ∑ k ∈ s, C (a * g k) * X ^ k := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_assoc, ← C_mul]

/-- `(C b * X)^k = C (b^k) * X^k`. -/
private lemma pow_C_mul_X {K : Type*} [CommSemiring K] (b : K) (k : ℕ) :
    (C b * X) ^ k = C (b ^ k) * X ^ k := by
  rw [mul_pow, ← C_pow]

/-- A sum whose monomials are scaled by powers of `C b * X` is a monomial sum. -/
private lemma sum_pow_C_mul_X {K : Type*} [CommSemiring K] (s : Finset ℕ) (g : ℕ → K) (b : K) :
    (∑ k ∈ s, C (g k) * (C b * X) ^ k) = ∑ k ∈ s, C (g k * b ^ k) * X ^ k := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_C_mul_X]
  rw [← mul_assoc, ← C_mul]

/-- `C (b^n)` times the truncated scaled series gives the shifted coefficient series:
`C(b^n) * Σ C(g k) * (C b * X)^k = Σ C(g k * b^(n+k)) * X^k`. -/
private lemma invpow_scale_sum {K : Type*} [Field K] (b : K) (n : ℕ) (s : Finset ℕ)
    (g : ℕ → K) :
    C (b ^ n) * (∑ k ∈ s, C (g k) * (C b * X) ^ k) = ∑ k ∈ s, C (g k * b ^ (n + k)) * X ^ k := by
  rw [sum_pow_C_mul_X]
  rw [scalar_mul_sum_X_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hc : b ^ n * (g k * b ^ k) = g k * b ^ (n + k) := by
    calc
      b ^ n * (g k * b ^ k) = g k * (b ^ n * b ^ k) := by ring
      _ = g k * b ^ (n + k) := by rw [pow_add]
  rw [hc]

/-- `(X + C u)^n = C (u^n) * (1 + C (u⁻¹) * X)^n` for a unit `u`. -/
private lemma unit_factor_pow {K : Type*} [Field K] (u : Kˣ) (n : ℕ) :
    (X + C (u : K)) ^ n = C ((u : K) ^ n) * (1 + C ((u : K)⁻¹) * X) ^ n := by
  have hb : X + C (u : K) = C (u : K) * (1 + C ((u : K)⁻¹) * X) := by
    rw [mul_add, mul_one]
    rw [← mul_assoc]
    rw [← C_mul]
    have hu : (u : K) * (u : K)⁻¹ = 1 := mul_inv_cancel₀ u.ne_zero
    rw [hu, C_1, one_mul]
    ring
  rw [hb, mul_pow, ← C_pow]

/-- `C (u^n) * (A * (C (u⁻¹^n) * B)) = A * B`: the unit scalars cancel. -/
private lemma unit_scale_cancel {K : Type*} [Field K] (u : Kˣ) (n : ℕ) (A B : K[X]) :
    C ((u : K) ^ n) * (A * (C ((u : K)⁻¹ ^ n) * B)) = A * B := by
  have hc : C ((u : K) ^ n) * C ((u : K)⁻¹ ^ n) = 1 := by
    rw [← C_mul]
    have h : (u : K) ^ n * (u : K)⁻¹ ^ n = 1 := by
      rw [← mul_pow]
      simp
    rw [h, C_1]
  calc
    C ((u : K) ^ n) * (A * (C ((u : K)⁻¹ ^ n) * B))
        = (C ((u : K) ^ n) * (A * C ((u : K)⁻¹ ^ n))) * B := by ring
    _ = (C ((u : K) ^ n) * C ((u : K)⁻¹ ^ n)) * A * B := by ring
    _ = A * B := by
          rw [hc]
          ring

/-- The truncated scaled series identity over the field: substituting `X ↦ C (u⁻¹) * X`
into the integer identity `Commons.Algebra.Binomial.trunc_inv_add_one` gives
`(1 + C (u⁻¹) X)^n · Σ_{k<N} C ((-1)^k * C(n+k-1,k)) * (C (u⁻¹) X)^k ≡ 1  mod (C (u⁻¹) X)^N`. -/
private lemma unit_trunc_inv {K : Type*} [Field K] (u : Kˣ) (n N : ℕ) (hN : 1 ≤ N)
    (hn : 1 ≤ n) :
    ∃ R : K[X],
      (1 + C ((u : K)⁻¹) * X) ^ n *
          (∑ k ∈ Finset.range N,
            Polynomial.C ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : K)) *
              (C ((u : K)⁻¹) * X) ^ k) =
        1 + (C ((u : K)⁻¹) * X) ^ N * R := by
  obtain ⟨Rz, hRz⟩ := Commons.Algebra.Binomial.trunc_inv_add_one n (N - 1) hn
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel hN
  rw [hsub] at hRz
  let φ : ℤ[X] →+* K[X] :=
    Polynomial.eval₂RingHom ((Polynomial.C : K →+* K[X]).comp (Int.castRingHom K))
      (C ((u : K)⁻¹) * X)
  refine ⟨φ Rz, ?_⟩
  have hh := congrArg φ hRz
  simpa [φ, map_pow, map_mul, map_add, map_one, map_sum] using hh

theorem unit_inv_cong {K : Type*} [Field K] (u : Kˣ) (n N : ℕ) (hn : 1 ≤ n) :
    X ^ N ∣
      (X + C (u : K)) ^ n *
          (∑ k ∈ Finset.range N,
            Polynomial.C ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : K) *
              (u : K)⁻¹ ^ (n + k)) * X ^ k) -
        1 := by
  by_cases hN0 : N = 0
  · subst N
    simp
  · have hN : 1 ≤ N := by omega
    obtain ⟨R, hR⟩ := unit_trunc_inv u n N hN hn
    -- hS : goal series = C ((u⁻¹)^n) · substituted series
    have hS : (∑ k ∈ Finset.range N,
            Polynomial.C ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : K) *
              (u : K)⁻¹ ^ (n + k)) * X ^ k) =
        C ((u : K)⁻¹ ^ n) *
          (∑ k ∈ Finset.range N,
            Polynomial.C ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : K)) *
              (C ((u : K)⁻¹) * X) ^ k) := by
      exact (invpow_scale_sum ((u : K)⁻¹) n (Finset.range N)
        (fun k => ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : K)))).symm
    have hG : (X + C (u : K)) ^ n *
          (∑ k ∈ Finset.range N,
            Polynomial.C ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : K) *
              (u : K)⁻¹ ^ (n + k)) * X ^ k) =
        1 + (C ((u : K)⁻¹) * X) ^ N * R := by
      calc
        (X + C (u : K)) ^ n *
            (∑ k ∈ Finset.range N,
              Polynomial.C ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : K) *
                (u : K)⁻¹ ^ (n + k)) * X ^ k)
            = C ((u : K) ^ n) *
                ((1 + C ((u : K)⁻¹) * X) ^ n *
                  (C ((u : K)⁻¹ ^ n) *
                    (∑ k ∈ Finset.range N,
                      Polynomial.C ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : K)) *
                        (C ((u : K)⁻¹) * X) ^ k))) := by
                rw [unit_factor_pow u n, hS]
                ring
        _ = (1 + C ((u : K)⁻¹) * X) ^ n *
            (∑ k ∈ Finset.range N,
              Polynomial.C ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : K)) *
                (C ((u : K)⁻¹) * X) ^ k) := by
                apply unit_scale_cancel
        _ = 1 + (C ((u : K)⁻¹) * X) ^ N * R := by
                exact hR
    refine ⟨C ((u : K)⁻¹) ^ N * R, ?_⟩
    rw [hG]
    rw [show (C ((u : K)⁻¹) * X) ^ N = C ((u : K)⁻¹) ^ N * X ^ N by
        rw [mul_pow, ← C_pow]]
    ring

end Commons.FieldTheory.Polynomial