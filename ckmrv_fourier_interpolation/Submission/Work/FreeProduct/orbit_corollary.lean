import Mathlib
import Submission.Work.FreeProduct.Basic
import Submission.Work.FreeProduct.Length
import Submission.Work.FreeProduct.T_zpow_injective

/-!
# The orbit corollary for the difference operator `T - 1`

If `w = (T - 1) * u` in `ℂ[ℤ/2 ∗ ℤ/3]`, the coefficients of `w` along an orbit of the infinite
cyclic subgroup `⟨T⟩` cannot be supported at a single point: `T - 1` is a discrete derivative
and its image is cut out by the vanishing of the orbit sums.

Concretely: if `coeff w (T ^ n * γ) = 0` for all `n ≠ 0`, then `coeff w γ = 0` as well.

This is Corollary 3.4 of CKMRV (there used as `w ∉ (T - I)R`).
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-- The coefficients of `(T - 1) * u` along the orbit: `coeff w δ = u(T⁻¹δ) - u(δ)`. -/
theorem coeff_sub_one_mul {u w : MonoidAlgebra ℂ FP}
    (hw : w = (MonoidAlgebra.of ℂ FP T - 1) * u) (δ : FP) :
    MonoidAlgebra.coeff w δ =
      MonoidAlgebra.coeff u (T⁻¹ * δ) - MonoidAlgebra.coeff u δ := by
  rw [hw, sub_mul, one_mul, MonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  rw [show (MonoidAlgebra.of ℂ FP) T = MonoidAlgebra.single T (1 : ℂ) from rfl,
    MonoidAlgebra.coeff_single_mul_apply]
  simp

/-- **The orbit corollary.**  If `w = (T - 1) * u` and the coefficients of `w` along the
`⟨T⟩`-orbit of `γ` all vanish except possibly at `γ` itself, then the coefficient at `γ`
vanishes too. -/
theorem orbit_corollary {u w : MonoidAlgebra ℂ FP} {γ : FP} {c : ℂ}
    (hT : Function.Injective (fun n : ℤ => T ^ n))
    (hw : w = (MonoidAlgebra.of ℂ FP T - 1) * u)
    (hγ : MonoidAlgebra.coeff w γ = c) (hc : c ≠ 0)
    (hrest : ∀ n : ℤ, n ≠ 0 → MonoidAlgebra.coeff w (T ^ n * γ) = 0) : False := by
  set a : ℤ → ℂ := fun n => MonoidAlgebra.coeff u (T ^ n * γ) with ha
  have hap : ∀ n : ℤ, a n = MonoidAlgebra.coeff u (T ^ n * γ) := fun n => by rw [ha]
  have hcoe := coeff_sub_one_mul hw
  have hrec : ∀ n : ℤ, n ≠ 0 →
      MonoidAlgebra.coeff u (T ^ (n - 1) * γ) = MonoidAlgebra.coeff u (T ^ n * γ) := by
    intro n hn
    have h := hrest n hn
    rw [hcoe (T ^ n * γ)] at h
    have h2 : T⁻¹ * T ^ n = T ^ (n - 1) := by
      rw [← zpow_neg_one, ← zpow_add]; ring_nf
    rw [← mul_assoc, h2] at h
    exact sub_eq_zero.mp h
  have hpos : ∀ n : ℤ, 0 ≤ n →
      MonoidAlgebra.coeff u (T ^ n * γ) = MonoidAlgebra.coeff u γ := by
    intro n hn
    induction n, hn using Int.le_induction with
    | base => simp
    | succ k hk ih =>
      have h := hrec (k + 1) (by omega)
      have hk' : (k + 1 - 1 : ℤ) = k := by ring
      rw [hk'] at h
      rw [← h]
      exact ih
  have hstep : ∀ m : ℤ, 0 ≤ m → MonoidAlgebra.coeff u (T ^ (-(m + 1)) * γ) =
      MonoidAlgebra.coeff u (T ^ (-(m + 1) - 1) * γ) := by
    intro m hm
    exact (hrec (-(m + 1)) (by omega)).symm
  have hb : ∀ m : ℤ, 0 ≤ m → MonoidAlgebra.coeff u (T ^ (-(m + 1)) * γ) =
      MonoidAlgebra.coeff u (T ^ (-1 : ℤ) * γ) := by
    intro m hm
    induction m, hm using Int.le_induction with
    | base => simp
    | succ k hk ih =>
      have h := hstep k (by omega)
      rw [show (-(k + 1 + 1) : ℤ) = -(k + 1) - 1 by ring, ← h]
      exact ih
  have hneg : ∀ n : ℤ, n ≤ -1 → MonoidAlgebra.coeff u (T ^ n * γ) =
      MonoidAlgebra.coeff u (T ^ (-1 : ℤ) * γ) := by
    intro n hn
    have hm : 0 ≤ -n - 1 := by omega
    have h := hb (-n - 1) hm
    have h2 : (-(-n - 1 + 1) : ℤ) = n := by ring
    rw [h2] at h
    exact h
  have hinj : Function.Injective (fun n : ℤ => T ^ n * γ) := fun n m h => hT (mul_right_cancel h)
  have hfin : ({n : ℤ | a n ≠ 0}).Finite := by
    have hset : {n : ℤ | a n ≠ 0}
        = (fun n : ℤ => T ^ n * γ) ⁻¹' (↑(MonoidAlgebra.coeff u).support : Set FP) := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff,
        hap]
    rw [hset]
    exact ((MonoidAlgebra.coeff u).support.finite_toSet).preimage hinj.injOn
  obtain ⟨N₀, hN₀⟩ := hfin.bddAbove
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ n : ℤ, N < n → MonoidAlgebra.coeff u (T ^ n * γ) = 0 := by
    refine ⟨N₀, fun n hn => ?_⟩
    by_contra hne
    have hne' : a n ≠ 0 := by rw [hap]; exact hne
    have : n ≤ N₀ := hN₀ (show n ∈ {n : ℤ | a n ≠ 0} from hne')
    omega
  obtain ⟨M₀, hM₀⟩ := hfin.bddBelow
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ n : ℤ, n < M → MonoidAlgebra.coeff u (T ^ n * γ) = 0 := by
    refine ⟨M₀, fun n hn => ?_⟩
    by_contra hne
    have hne' : a n ≠ 0 := by rw [hap]; exact hne
    have : M₀ ≤ n := hM₀ (show n ∈ {n : ℤ | a n ≠ 0} from hne')
    omega
  have h0 : MonoidAlgebra.coeff u γ = 0 := by
    have h := hpos (max N 0 + 1) (by omega)
    have h2 : MonoidAlgebra.coeff u (T ^ (max N 0 + 1) * γ) = 0 := hN _ (by omega)
    rw [h] at h2
    exact h2
  have hm1 : MonoidAlgebra.coeff u (T ^ (-1 : ℤ) * γ) = 0 := by
    have h := hneg (min M 0 - 1) (by omega)
    have h2 : MonoidAlgebra.coeff u (T ^ (min M 0 - 1) * γ) = 0 := hM _ (by omega)
    rw [h] at h2
    exact h2
  refine hc ?_
  rw [← hγ, hcoe γ, show T⁻¹ * γ = T ^ (-1 : ℤ) * γ from by rw [zpow_neg_one], hm1, h0,
    sub_zero]

end

end Work.FreeProduct
