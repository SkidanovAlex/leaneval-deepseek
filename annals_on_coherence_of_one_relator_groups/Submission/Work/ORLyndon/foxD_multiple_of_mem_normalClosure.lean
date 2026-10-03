import Mathlib
import Submission.Work.ORLyndon.Lyndon

/-!
# Fox derivatives of elements of the normal closure of a relator

Let `X` be a set, `K` a field, `r : F(X)` a relator and `G = ⟨X | r⟩` the associated one-relator
group.  The Fox derivative vector `x ↦ ∂r/∂x` of the relator, pushed forward to `K[G]`, is
`Work.ORLyndon.relatorVec`; its `K[G]`-span is the image of the *relation Jacobian* of the
presentation.

The main result of this file, `Work.ORLyndon.foxD_multiple_of_mem_normalClosure`, shows that for
**every** element `n` of the normal closure of `r` the pushed-forward Fox derivative vector of `n`
lies in that cyclic submodule: there is `β : K[G]` with

`presentAlg K r (∂n/∂x) = β * relatorVec K r x`   for all `x : X`.

The proof uses only the twisted derivation (cocycle) property `∂(gh)/∂x = ∂g/∂x + g·∂h/∂x` of the
Fox calculus together with `presentRho r = 1` on the relator; no one-relator-specific input (such
as Lyndon's identity theorem) is required.  Concretely, we prove that the set of `t` with
`presentRho r t = 1` and such that `x ↦ presentAlg K r (∂t/∂x)` is a `K[G]`-multiple of the relator
vector is a subgroup, closed under conjugation, and contains `r`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

variable {X : Type u} {K : Type v}

section FoxPresent

variable [Field K] [DecidableEq X]

/-- The derivation property of the Fox derivative, pushed forward along `presentAlg`. -/
theorem presentAlg_foxD_mul (r : FreeGroup X) (x : X) (g h : FreeGroup X) :
    presentAlg K r (foxD (K := K) x (g * h)) =
      presentAlg K r (foxD (K := K) x g) +
        presentAlg K r (MonoidAlgebra.of K (FreeGroup X) g) *
          presentAlg K r (foxD (K := K) x h) := by
  rw [foxD_mul, map_add, map_mul]

/-- The Fox derivative of an inverse, pushed forward along `presentAlg`. -/
theorem presentAlg_foxD_inv (r : FreeGroup X) (x : X) (g : FreeGroup X) :
    presentAlg K r (foxD (K := K) x g⁻¹) =
      -(presentAlg K r (MonoidAlgebra.of K (FreeGroup X) g⁻¹) *
        presentAlg K r (foxD (K := K) x g)) := by
  rw [foxD_inv, map_neg, map_mul]

/-- The cocycle identity for a group element and its inverse: `∂g/∂x + g·∂g⁻¹/∂x = 0`, pushed
forward along `presentAlg`. -/
theorem presentAlg_foxD_add_mul_inv (r : FreeGroup X) (x : X) (g : FreeGroup X) :
    presentAlg K r (foxD (K := K) x g) +
      presentAlg K r (MonoidAlgebra.of K (FreeGroup X) g) *
        presentAlg K r (foxD (K := K) x g⁻¹) = 0 := by
  rw [← map_mul, ← map_add, ← foxD_mul, mul_inv_cancel, foxD_one, map_zero]

/-- Conjugation step: if the pushed-forward Fox derivative vector of `t` is a `K[G]`-multiple of
the relator vector and `t` dies in `G`, then the same holds for any conjugate `c * t * c⁻¹`. -/
theorem presentAlg_foxD_conj (r : FreeGroup X) (x : X) (c t : FreeGroup X)
    (β : MonoidAlgebra K (OneRelatorGroup r))
    (hβ : presentAlg K r (foxD (K := K) x t) = β * relatorVec K r x)
    (ht : presentRho r t = 1) :
    presentAlg K r (foxD (K := K) x (c * t * c⁻¹)) =
      (presentAlg K r (MonoidAlgebra.of K (FreeGroup X) c) * β) * relatorVec K r x := by
  have hcancel := presentAlg_foxD_add_mul_inv (K := K) r x c
  have hof : presentAlg K r (MonoidAlgebra.of K (FreeGroup X) t) = 1 := by
    rw [presentAlg_of, ht, map_one]
  have hofc : presentAlg K r (MonoidAlgebra.of K (FreeGroup X) (c * t)) =
      presentAlg K r (MonoidAlgebra.of K (FreeGroup X) c) := by
    rw [map_mul (MonoidAlgebra.of K (FreeGroup X)), map_mul, hof, mul_one]
  rw [foxD_mul, foxD_mul, map_add, map_add, map_mul, map_mul, hofc, hβ]
  rw [show presentAlg K r (foxD (K := K) x c) +
        presentAlg K r (MonoidAlgebra.of K (FreeGroup X) c) * (β * relatorVec K r x) +
        presentAlg K r (MonoidAlgebra.of K (FreeGroup X) c) *
          presentAlg K r (foxD (K := K) x c⁻¹) =
      (presentAlg K r (foxD (K := K) x c) +
        presentAlg K r (MonoidAlgebra.of K (FreeGroup X) c) *
          presentAlg K r (foxD (K := K) x c⁻¹)) +
      presentAlg K r (MonoidAlgebra.of K (FreeGroup X) c) * (β * relatorVec K r x)
      from by abel]
  rw [hcancel, zero_add, mul_assoc]

end FoxPresent

/-- **Fox derivatives of elements of the normal closure.**  If `n` lies in the normal closure of
the relator `r`, then its pushed-forward Fox derivative vector is a `K[G]`-multiple of the Fox
derivative vector of the relator: there is `β : K[G]` with
`presentAlg K r (∂n/∂x) = β * relatorVec K r x` for every generator `x`. -/
theorem foxD_multiple_of_mem_normalClosure {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r : FreeGroup X) {n : FreeGroup X}
    (hn : n ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X))) :
    ∃ β : MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r),
      ∀ x : X, Work.ORLyndon.presentAlg K r (Work.ORLyndon.foxD (K := K) x n) =
        β * Work.ORLyndon.relatorVec K r x := by
  -- The elements whose pushed-forward Fox derivative vector is a multiple of the relator vector
  -- and which die in `G` form a subgroup `H`.
  let H : Subgroup (FreeGroup X) :=
    { carrier := {t | presentRho r t = 1 ∧ ∃ β : MonoidAlgebra K (OneRelatorGroup r),
        ∀ x : X, presentAlg K r (foxD (K := K) x t) = β * relatorVec K r x}
      one_mem' := by
        refine ⟨map_one (presentRho r), 0, fun x => ?_⟩
        rw [foxD_one, map_zero, zero_mul]
      mul_mem' := by
        rintro t₁ t₂ ⟨h1, β1, hβ1⟩ ⟨h2, β2, hβ2⟩
        refine ⟨?_, β1 + presentAlg K r (MonoidAlgebra.of K (FreeGroup X) t₁) * β2,
          fun x => ?_⟩
        · rw [map_mul, h1, h2, mul_one]
        · rw [foxD_mul, map_add, map_mul, hβ1 x, hβ2 x, add_mul, mul_assoc]
      inv_mem' := by
        rintro t ⟨h1, β, hβ⟩
        refine ⟨?_, -(presentAlg K r (MonoidAlgebra.of K (FreeGroup X) t⁻¹) * β),
          fun x => ?_⟩
        · rw [map_inv, h1, inv_one]
        · rw [foxD_inv, map_neg, map_mul, hβ x, neg_mul, mul_assoc] }
  -- The relator itself lies in `H`.
  have hgen : ({r} : Set (FreeGroup X)) ⊆ (H : Set (FreeGroup X)) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact ⟨presentRho_relator r, 1, fun x => by rw [one_mul, relatorVec_apply]⟩
  -- `H` is closed under conjugation.
  have hconj : ∀ (c t : FreeGroup X), t ∈ H → c * t * c⁻¹ ∈ H := by
    intro c t ht
    obtain ⟨ht1, β, hβ⟩ := ht
    refine ⟨?_, presentAlg K r (MonoidAlgebra.of K (FreeGroup X) c) * β, fun x => ?_⟩
    · simp only [map_mul, map_inv, ht1, mul_one, mul_inv_cancel]
    · exact presentAlg_foxD_conj r x c t β (hβ x) ht1
  -- Hence `H` contains the normal closure of `r`.
  have hle : Subgroup.normalClosure ({r} : Set (FreeGroup X)) ≤ H := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro t ht
    rw [Group.mem_conjugatesOfSet_iff] at ht
    obtain ⟨a, ha, hconjp⟩ := ht
    rw [Set.mem_singleton_iff] at ha
    rw [ha] at hconjp
    rw [isConj_iff] at hconjp
    obtain ⟨c, hc⟩ := hconjp
    rw [← hc]
    exact hconj c r (hgen (Set.mem_singleton r))
  exact (hle hn).2

end Work.ORLyndon
