import Mathlib
import Submission.Work.Higman.Q3.irred_natDegree_dvd_of_dvd_X_pow_sub_one
import Submission.Work.Higman.Q3.minpoly_natDegree_eq_finrank_of_irreducible
import Submission.Work.Higman.Q3.irreducible_minpoly_of_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Polynomial

namespace Work.Higman.Q3

/-- **The dimension of an irreducible `𝔽₂[σ]`-module divides `n`.**

Let `V ≠ 0` be a finite `𝔽₂`-vector space, `σ` a linear automorphism with `σ ^ (2 ^ n - 1) = 1`,
and suppose the only `σ`-invariant subspaces are `⊥` and `⊤`.  Then `finrank 𝔽₂ V ∣ n`.

Indeed `V` is a simple module over the PID `𝔽₂[X]` (with `X` acting as `σ`), so if `a` is the
underlying endomorphism then `μ := minpoly 𝔽₂ a` is irreducible and `finrank 𝔽₂ V = μ.natDegree`;
moreover `μ ∣ X ^ (2 ^ n - 1) - 1`.  The finite-field lemma
`irred_natDegree_dvd_of_dvd_X_pow_sub_one` then gives `μ.natDegree ∣ n`. -/
theorem finrank_dvd_of_irreducible_pow_sub_one
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    (σ : V ≃ₗ[ZMod 2] V) {n : ℕ} (hn : 1 ≤ n) (hσ : σ ^ (2 ^ n - 1) = 1)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ v ∈ U, σ v ∈ U) → U = ⊥ ∨ U = ⊤) :
    Module.finrank (ZMod 2) V ∣ n := by
  set a : V →ₗ[ZMod 2] V := (σ : V →ₗ[ZMod 2] V) with ha
  -- The `𝔽₂`-linear equivalence `σ` and its underlying linear map `a` have the same powers.
  have hcoepow : ∀ k : ℕ, ((σ ^ k : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = a ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, LinearEquiv.coe_toLinearMap_one, Module.End.one_eq_id]
    | succ k ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]
  have ha1 : a ^ (2 ^ n - 1) = 1 := by
    rw [← hcoepow, hσ, LinearEquiv.coe_toLinearMap_one, Module.End.one_eq_id]
  -- hence the minimal polynomial of `a` divides `X ^ (2 ^ n - 1) - 1`.
  have hdiv : minpoly (ZMod 2) a ∣ Polynomial.X ^ (2 ^ n - 1) - 1 := by
    apply minpoly.dvd
    rw [map_sub, map_pow, aeval_X, map_one, ha1, sub_self]
  -- the irreducibility hypothesis transfers from `σ` to `a`.
  have hirr' : ∀ U : Submodule (ZMod 2) V, (∀ v ∈ U, a v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hirr U (fun v hv => ?_)
    simpa [ha] using hU v hv
  have hdeg := minpoly_natDegree_eq_finrank_of_irreducible a hirr'
  have hμirr := irreducible_minpoly_of_irreducible a hirr'
  have h := irred_natDegree_dvd_of_dvd_X_pow_sub_one (minpoly (ZMod 2) a) hμirr hdiv
  rwa [hdeg] at h

end Work.Higman.Q3
