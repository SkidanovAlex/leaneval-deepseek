import Mathlib
import Submission.Work.FreeProduct.shiftedDefs
import Submission.Work.FreeProduct.orbit_corollary

/-!
# The shifted orbit corollary

The odd-weight directness theorem of the CKMRV interpolation proof needs a **shifted** form of
the orbit corollary `Work.FreeProduct.orbit_corollary`: with `Tnu ν = T - ν` the difference
operator `T - ν` (instead of `T - 1`), the coefficients of `(T - ν) * u` along an orbit of the
infinite cyclic subgroup `⟨T⟩` cannot be supported at a single point.

The recursion is `a (n - 1) = ν * a n` instead of `a (n-1) = a n`; consequently the coefficient
at `γ` is `coeff u (T⁻¹ γ) - ν * coeff u γ`, and both `coeff u γ` and `coeff u (T⁻¹ γ)` vanish
(finiteness of the support of `u`, together with `ν ≠ 0` for the negative direction).

This is the shifted analogue of Corollary 3.4 of CKMRV.
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-- The coefficients of `(T - ν) * u`: along an orbit, `T - ν` acts as
`coeff u (T⁻¹ δ) - ν * coeff u δ`. -/
lemma coeff_Tnu_mul {ν : ℂ} (u : RR) (δ : FP) :
    MonoidAlgebra.coeff (Tnu ν * u) δ =
      MonoidAlgebra.coeff u (T⁻¹ * δ) - ν * MonoidAlgebra.coeff u δ := by
  rw [Tnu_apply, sub_mul]
  rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  rw [show (TT : RR) = MonoidAlgebra.single T (1 : ℂ) from rfl,
    MonoidAlgebra.coeff_single_mul_apply]
  rw [smul_mul_assoc, one_mul, MonoidAlgebra.coeff_smul_apply]
  simp

theorem shifted_orbit_corollary {ν : ℂ} (hν : ν ≠ 0) {u w : Work.FreeProduct.RR}
    {γ : Work.Modular.PresGroup.FP} {c : ℂ}
    (hT : Function.Injective (fun n : ℤ => Work.FreeProduct.T ^ n))
    (hw : w = Work.FreeProduct.Tnu ν * u)
    (hγ : MonoidAlgebra.coeff w γ = c) (hc : c ≠ 0)
    (hrest : ∀ n : ℤ, n ≠ 0 → MonoidAlgebra.coeff w (Work.FreeProduct.T ^ n * γ) = 0) : False := by
  set a : ℤ → ℂ := fun n => MonoidAlgebra.coeff u (T ^ n * γ) with ha
  have hap : ∀ n : ℤ, a n = MonoidAlgebra.coeff u (T ^ n * γ) := fun n => by rw [ha]
  -- The recursion along the orbit: `a (n - 1) = ν * a n` for `n ≠ 0`.
  have hrec : ∀ n : ℤ, n ≠ 0 → a (n - 1) = ν * a n := by
    intro n hn
    have h := hrest n hn
    rw [hw, coeff_Tnu_mul] at h
    have h2 : T⁻¹ * T ^ n = T ^ (n - 1) := by
      rw [← zpow_neg_one, ← zpow_add]
      ring_nf
    rw [← mul_assoc, h2] at h
    have h' : a (n - 1) - ν * a n = 0 := by
      rw [hap (n - 1), hap n]
      exact h
    exact sub_eq_zero.mp h'
  have hstep : ∀ k : ℤ, k ≠ -1 → a k = ν * a (k + 1) := by
    intro k hk
    have h := hrec (k + 1) (by omega)
    rwa [show k + 1 - 1 = k by ring] at h
  -- Forwards: `a 0 = ν ^ m * a m`.
  have hfwd : ∀ m : ℕ, a 0 = ν ^ m * a (m : ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h := hstep (k : ℤ) (by omega)
      have hk : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by omega
      rw [hk] at h
      rw [h] at ih
      rw [ih, pow_succ]
      ring
  -- Backwards: `a (-(m + 1)) = ν ^ m * a (-1)`.
  have hbwd : ∀ m : ℕ, a (-(m : ℤ) - 1) = ν ^ m * a (-1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h := hstep (-(k : ℤ) - 2) (by omega)
      have hk : (-(((k + 1 : ℕ)) : ℤ) - 1) = -(k : ℤ) - 2 := by omega
      have hk' : (-(k : ℤ) - 2 + 1) = -(k : ℤ) - 1 := by ring
      rw [hk, h, hk', ih, pow_succ]
      ring
  -- The support of `u` restricts to a finite set on the orbit.
  have hinj : Function.Injective (fun n : ℤ => T ^ n * γ) := fun n m h => hT (mul_right_cancel h)
  have hfin : ({n : ℤ | a n ≠ 0}).Finite := by
    have hset : {n : ℤ | a n ≠ 0}
        = (fun n : ℤ => T ^ n * γ) ⁻¹' (↑(MonoidAlgebra.coeff u).support : Set FP) := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff,
        hap]
    rw [hset]
    exact ((MonoidAlgebra.coeff u).support.finite_toSet).preimage hinj.injOn
  obtain ⟨N₀, hN₀⟩ := hfin.bddAbove
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ n : ℤ, N < n → a n = 0 := by
    refine ⟨N₀, fun n hn => ?_⟩
    by_contra hne
    have : n ≤ N₀ := hN₀ (show n ∈ {n : ℤ | a n ≠ 0} from hne)
    omega
  obtain ⟨M₀, hM₀⟩ := hfin.bddBelow
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ n : ℤ, n < M → a n = 0 := by
    refine ⟨M₀, fun n hn => ?_⟩
    by_contra hne
    have : M₀ ≤ n := hM₀ (show n ∈ {n : ℤ | a n ≠ 0} from hne)
    omega
  have ha0 : a 0 = 0 := by
    have hle : 0 ≤ max N 0 + 1 := by omega
    have h := hfwd (max N 0 + 1).toNat
    rw [Int.toNat_of_nonneg hle] at h
    rw [h, hN _ (by omega), mul_zero]
  have ha1 : a (-1) = 0 := by
    have h0 : a (min M 0 - 2) = 0 := hM _ (by omega)
    have hmn : 0 ≤ -(min M 0 - 2) - 1 := by omega
    have h := hbwd ((-(min M 0 - 2) - 1)).toNat
    rw [Int.toNat_of_nonneg hmn] at h
    rw [show (-(-(min M 0 - 2) - 1) - 1 : ℤ) = min M 0 - 2 by ring, h0] at h
    have hne : ν ^ ((-(min M 0 - 2) - 1)).toNat ≠ 0 := pow_ne_zero _ hν
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hne
    · exact h'
  refine hc ?_
  rw [← hγ, hw, coeff_Tnu_mul]
  rw [show T⁻¹ * γ = T ^ (-1 : ℤ) * γ by rw [zpow_neg_one]]
  have h1 : MonoidAlgebra.coeff u (T ^ (-1 : ℤ) * γ) = a (-1) := (hap (-1)).symm
  have h0 : MonoidAlgebra.coeff u γ = a 0 := by rw [hap 0]; simp
  rw [h1, h0, ha1, ha0]
  ring

end

end Work.FreeProduct
