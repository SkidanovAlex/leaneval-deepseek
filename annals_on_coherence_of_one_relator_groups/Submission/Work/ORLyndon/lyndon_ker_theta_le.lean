import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.Fox

/-!
# The annihilator of the Fox derivative vector contains `u - 1`

Let `r = u ^ l` be a relator of the one-relator presentation `⟨X | r⟩` and let
`w = (of K (OneRelatorGroup r)) (presentRho r u)` be the image of the root `u` in `K[G]`.
Then `w - 1` annihilates the Fox derivative vector `relatorVec K r`, i.e.
`(w - 1) • relatorVec K r = 0`: this is the "easy" inclusion
`K[G](u - 1) ≤ ker θ` of Lyndon's identity theorem.

The proof is the classical computation `(w - 1) * ∂(u^l)/∂x = (w^l - 1) * ∂u/∂x = 0`, where
`w^l = presentRho r (u ^ l) = presentRho r r = 1` in `K[G]`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- Geometric identity: if `q` satisfies `q 0 = 0` and `q (n+1) = q n + w^n * p`, then
`(w - 1) * q n = (w^n - 1) * p`. -/
private lemma geom_fox {A : Type*} [Ring A] (w p : A) (q : ℕ → A) (h0 : q 0 = 0)
    (hstep : ∀ n, q (n + 1) = q n + w ^ n * p) (n : ℕ) :
    (w - 1) * q n = (w ^ n - 1) * p := by
  induction n with
  | zero => rw [h0, mul_zero, pow_zero, sub_self, zero_mul]
  | succ n ih => rw [hstep n, mul_add, ih, pow_succ']; noncomm_ring

variable {X : Type*} [DecidableEq X] {K : Type*} [Field K]

/-- For `r = u ^ l`, the element `w - 1` (with `w` the image of `u` in `K[⟨X | r⟩]`) annihilates
the `x`-th Fox derivative of the relator `r`. -/
private lemma foxD_pow_eq (r u : FreeGroup X) (l : ℕ) (hpow : r = u ^ l) (x : X) :
    ((MonoidAlgebra.of K (OneRelatorGroup r)) (presentRho r u) - 1) *
      (presentAlg K r) (foxD (K := K) x r) = 0 := by
  subst hpow
  have hof : ∀ n : ℕ, (presentAlg K (u ^ l)) ((MonoidAlgebra.of K (FreeGroup X)) (u ^ n)) =
      ((MonoidAlgebra.of K (OneRelatorGroup (u ^ l))) (presentRho (u ^ l) u)) ^ n := by
    intro n
    rw [presentAlg_of]
    rw [show (presentRho (u ^ l)) (u ^ n) = ((presentRho (u ^ l)) u) ^ n from map_pow _ _ _]
    exact map_pow _ _ _
  have hq0 : (presentAlg K (u ^ l)) (foxD (K := K) x (u ^ 0)) = 0 := by
    rw [pow_zero, foxD_one, map_zero]
  have hqstep : ∀ n : ℕ, (presentAlg K (u ^ l)) (foxD (K := K) x (u ^ (n + 1))) =
      (presentAlg K (u ^ l)) (foxD (K := K) x (u ^ n)) +
        ((MonoidAlgebra.of K (OneRelatorGroup (u ^ l))) (presentRho (u ^ l) u)) ^ n *
          (presentAlg K (u ^ l)) (foxD (K := K) x u) := by
    intro n
    rw [pow_succ (u) n, foxD_mul, map_add, map_mul, hof n]
  have h := geom_fox ((MonoidAlgebra.of K (OneRelatorGroup (u ^ l))) (presentRho (u ^ l) u))
      ((presentAlg K (u ^ l)) (foxD (K := K) x u))
      (fun n => (presentAlg K (u ^ l)) (foxD (K := K) x (u ^ n))) hq0 hqstep l
  rw [h]
  have hw : ((MonoidAlgebra.of K (OneRelatorGroup (u ^ l))) (presentRho (u ^ l) u)) ^ l = 1 := by
    rw [show ((MonoidAlgebra.of K (OneRelatorGroup (u ^ l))) (presentRho (u ^ l) u)) ^ l =
        (MonoidAlgebra.of K (OneRelatorGroup (u ^ l))) ((presentRho (u ^ l) u) ^ l) from
        (map_pow _ _ _).symm]
    rw [show (presentRho (u ^ l) u) ^ l = presentRho (u ^ l) (u ^ l) from (map_pow _ _ _).symm]
    rw [presentRho_relator, map_one]
  rw [hw, sub_self, zero_mul]

theorem lyndon_ker_theta_le {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r u : FreeGroup X) (l : ℕ) (hpow : r = u ^ l) :
    Ideal.span {((MonoidAlgebra.of K (Work.ORLyndon.OneRelatorGroup r))
        (Work.ORLyndon.presentRho r u)) - 1} ≤
      LinearMap.ker (Work.ORLyndon.lyndonTheta K r) := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show ((MonoidAlgebra.of K (OneRelatorGroup r)) (presentRho r u)) - 1 ∈ (lyndonTheta K r).ker
  rw [LinearMap.mem_ker, lyndonTheta_apply]
  apply Finsupp.ext
  intro x
  rw [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul, relatorVec_apply]
  exact foxD_pow_eq r u l hpow x

end Work.ORLyndon
