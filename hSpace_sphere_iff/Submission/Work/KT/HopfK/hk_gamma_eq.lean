import Mathlib
import Submission.Work.KT.k0_basic

/-!
# `Work.KT.HopfK.hk_gamma_eq` — uniqueness of the disk-side class `γ`

Given the external product `μx` on `K̃(S^{2m}) × K̃(S^{2m}) → K̃(S^{4m})` (`IsExtProd`), the
statement compares two reduced classes `γ, μx t s ∈ K̃(Kpair (E×E))`: if `γ` has the same image
under the smash inclusion as `μx t s` in the ring `K₀(prodAlg E E)` — namely the external product
of `s` and `t` — then `γ = μx t s`.

The only mathematics is that the ring product of `K₀` of a *commutative* ring is commutative, so
that the two orderings of the external product agree; injectivity of `smashIncl` on classes that
are reduced under the augmentation finishes the job.
-/

namespace Work.KT.HopfK

set_option maxHeartbeats 3200000 in
theorem hk_gamma_eq (m : ℕ)
    (y0E : Ball (Eu m)) (y0 : Ball (Eu m × Eu m))
    (μx : K0 (Kpair (Eu m)) →+ K0 (Kpair (Eu m)) →+ K0 (Kpair (Eu m × Eu m)))
    (hμx : IsExtProd (Eu m) (Eu m) y0E y0E y0 μx)
    (hinj : ∀ w, K0.mapA (augPair (Eu m × Eu m) y0) w = 0 →
      K0.mapA (smashIncl (Eu m) (Eu m)) w = 0 → w = 0)
    (s t : K0 (Kpair (Eu m))) (γ : K0 (Kpair (Eu m × Eu m)))
    (hs : K0.mapA (augPair (Eu m) y0E) s = 0)
    (ht : K0.mapA (augPair (Eu m) y0E) t = 0)
    (hγ : K0.mapA (augPair (Eu m × Eu m) y0) γ = 0)
    (hprod : ∀ μ' : K0 (prodAlg (Eu m) (Eu m)) →+ K0 (prodAlg (Eu m) (Eu m)) →+
        K0 (prodAlg (Eu m) (Eu m)), IsK0Mul μ' →
      K0.mapA (smashIncl (Eu m) (Eu m)) γ =
        μ' (K0.mapA (pullSnd (Eu m) (Eu m)) s) (K0.mapA (pullFst (Eu m) (Eu m)) t)) :
    γ = μx t s := by
  -- `prodAlg` is a subalgebra of a *commutative* ring, hence commutative.
  have hcommP : ∀ x y : prodAlg (Eu m) (Eu m), x * y = y * x :=
    fun x y => Subtype.ext (mul_comm x.1 y.1)
  -- the external-product axiom for the pair `(t, s)`
  obtain ⟨haug_ts, hsm_ts⟩ := hμx t s ht hs
  -- evaluate the smash image of `μx t s` at the canonical product
  have hsm_ts' : K0.mapA (smashIncl (Eu m) (Eu m)) (μx t s)
      = k0Mul (prodAlg (Eu m) (Eu m)) hcommP
          (K0.mapA (pullFst (Eu m) (Eu m)) t) (K0.mapA (pullSnd (Eu m) (Eu m)) s) :=
    hsm_ts (k0Mul (prodAlg (Eu m) (Eu m)) hcommP)
      (k0Mul_isK0Mul (prodAlg (Eu m) (Eu m)) hcommP)
  -- the assumed smash image of `γ`
  have hsm_gam : K0.mapA (smashIncl (Eu m) (Eu m)) γ
      = k0Mul (prodAlg (Eu m) (Eu m)) hcommP
          (K0.mapA (pullSnd (Eu m) (Eu m)) s) (K0.mapA (pullFst (Eu m) (Eu m)) t) :=
    hprod (k0Mul (prodAlg (Eu m) (Eu m)) hcommP)
      (k0Mul_isK0Mul (prodAlg (Eu m) (Eu m)) hcommP)
  -- `μx t s` and `γ` have the same augmentation and the same smash image
  have hdiff : μx t s - γ = 0 := by
    refine hinj (μx t s - γ) ?_ ?_
    · rw [map_sub, haug_ts, hγ, sub_zero]
    · rw [map_sub, hsm_ts', hsm_gam,
        k0Mul_comm (prodAlg (Eu m) (Eu m)) hcommP
          (K0.mapA (pullFst (Eu m) (Eu m)) t) (K0.mapA (pullSnd (Eu m) (Eu m)) s),
        sub_self]
  exact (sub_eq_zero.mp hdiff).symm

end Work.KT.HopfK
