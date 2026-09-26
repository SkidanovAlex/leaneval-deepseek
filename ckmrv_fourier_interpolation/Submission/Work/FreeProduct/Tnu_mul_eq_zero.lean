import Mathlib
import Submission.Work.FreeProduct.shiftedDefs
import Submission.Work.FreeProduct.Basic
import Submission.Work.FreeProduct.T_zpow_injective
import Submission.Work.FreeProduct.shifted_orbit_corollary

/-!
# Injectivity of the shifted difference operator `T - ν` for `ν ≠ 0`

The element `T = X * Y` of `RR = ℂ[ℤ/2 ∗ ℤ/3]` has infinite order, and `T` acts on `RR` by
left multiplication preserving every `⟨T⟩`-orbit of the underlying group `FP`.

The coefficients of `(T - ν) * u` along the orbit `{Tⁿ γ}` of a group element `γ` satisfy the
recursion `a (n - 1) = ν * a n` where `a n = coeff u (Tⁿ γ)` (this is
`Work.FreeProduct.coeff_Tnu_mul`).  Solving the recursion gives `a (-m) = ν ^ m * a 0` for every
`m : ℕ`, so as soon as some coefficient of `u` is non-zero and `ν ≠ 0` the function `a` is
supported on infinitely many points of the orbit — impossible, since the orbit map `n ↦ Tⁿ γ` is
injective and `u` has finite support.

Hence `T - ν` is a non-zero-divisor for `ν ≠ 0`.
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

theorem Tnu_mul_eq_zero {ν : ℂ} (hν : ν ≠ 0) {u : Work.FreeProduct.RR}
    (h : Work.FreeProduct.Tnu ν * u = 0) : u = 0 := by
  classical
  by_contra hu
  have hex : ∃ γ : FP, MonoidAlgebra.coeff u γ ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hu (by ext γ; exact hc γ)
  obtain ⟨γ, hγne⟩ := hex
  set a : ℤ → ℂ := fun n => MonoidAlgebra.coeff u (T ^ n * γ) with ha
  have hap : ∀ n : ℤ, a n = MonoidAlgebra.coeff u (T ^ n * γ) := fun n => by rw [ha]
  -- The recursion along the orbit: `a (n - 1) = ν * a n`.
  have hrec : ∀ n : ℤ, a (n - 1) = ν * a n := by
    intro n
    have h0 : MonoidAlgebra.coeff (Tnu ν * u) (T ^ n * γ) = 0 := by
      rw [h]; simp
    rw [coeff_Tnu_mul] at h0
    have h2 : T⁻¹ * T ^ n = T ^ (n - 1) := by rw [← zpow_neg_one, ← zpow_add]; ring_nf
    rw [← mul_assoc, h2] at h0
    have h3 : a (n - 1) - ν * a n = 0 := by rw [hap (n - 1), hap n]; exact h0
    exact sub_eq_zero.mp h3
  have ha0 : a 0 ≠ 0 := by rw [hap 0]; simpa using hγne
  -- Backwards solution of the recursion: `a (-m) = ν ^ m * a 0`.
  have hfwd : ∀ m : ℕ, a (-(m : ℤ)) = ν ^ m * a 0 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have hk := hrec (-(k : ℤ))
      have hk' : (-(k : ℤ) - 1 : ℤ) = -(((k + 1 : ℕ)) : ℤ) := by omega
      rw [hk', ih] at hk
      rw [hk, pow_succ]
      ring
  -- Finiteness of the support of `a` along the orbit.
  have hinj : Function.Injective (fun n : ℤ => T ^ n * γ) :=
    fun n m h => T_zpow_injective (mul_right_cancel h)
  have hfin : ({n : ℤ | a n ≠ 0}).Finite := by
    have hset : {n : ℤ | a n ≠ 0}
        = (fun n : ℤ => T ^ n * γ) ⁻¹' (↑(MonoidAlgebra.coeff u).support : Set FP) := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff, hap]
    rw [hset]
    exact ((MonoidAlgebra.coeff u).support.finite_toSet).preimage hinj.injOn
  obtain ⟨M₀, hM₀⟩ := hfin.bddBelow
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ n : ℤ, n < M → a n = 0 := by
    refine ⟨M₀, fun n hn => ?_⟩
    by_contra hne
    have : M₀ ≤ n := hM₀ (show n ∈ {n : ℤ | a n ≠ 0} from hne)
    omega
  -- A point of the orbit at which `a` vanishes, but the recursion forces it to be non-zero.
  set n₀ : ℤ := min M 0 - 1 with hn₀def
  have hn0lt : n₀ < M := by omega
  have hn0le : n₀ ≤ 0 := by omega
  have hzero : a n₀ = 0 := hM n₀ hn0lt
  have hneg : 0 ≤ -n₀ := by omega
  have htoNat : (((-n₀).toNat : ℤ)) = -n₀ := Int.toNat_of_nonneg hneg
  have h2 : a n₀ = ν ^ ((-n₀).toNat) * a 0 := by
    have hm : -(((-n₀).toNat : ℤ)) = n₀ := by rw [htoNat]; ring
    have hthis := hfwd ((-n₀).toNat)
    rwa [hm] at hthis
  rw [h2] at hzero
  exact (mul_ne_zero (pow_ne_zero _ hν) ha0) hzero

end

end Work.FreeProduct
