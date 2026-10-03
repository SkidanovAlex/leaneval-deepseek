import Mathlib
import Submission.Work.ORLyndon.LyndonConjDefs

/-!
# Conjugation invariance of the Fox derivative vector

Let `r, c : F(X)` and let `x : X`.  Conjugating the relator by `c` conjugates the Fox derivative
vector `relatorVec K r = (∂r/∂x)_x` accordingly, transported along the isomorphism of presentations
`conjHom r c : ⟨X | r⟩ →* ⟨X | c r c⁻¹⟩`:

`relatorVec K (c r c⁻¹) x = mapDomainRingHom K (conjHom r c) (relatorVec K r x) * of (ρ(c))`.

Equivalently both sides are the image, under `presentAlg K (c r c⁻¹)`, of the element
`∂c/∂x` for the conjugating factor: the ring-theoretic content is that the Fox derivative of
`c r c⁻¹` equals `(∂c/∂x) + c (∂r/∂x) + c r (∂c⁻¹/∂x)` in `K[F(X)]`, and the "correction" terms
involving `∂c/∂x` die in the presented group because the relator `c r c⁻¹` becomes trivial there.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

theorem relatorVec_conj {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r c : FreeGroup X) (x : X) :
    Work.ORLyndon.relatorVec K (c * r * c⁻¹) x =
      MonoidAlgebra.mapDomainRingHom K (Work.ORLyndon.conjHom r c)
          (Work.ORLyndon.relatorVec K r x) *
        MonoidAlgebra.of K (Work.ORLyndon.OneRelatorGroup (c * r * c⁻¹))
          (Work.ORLyndon.presentRho (c * r * c⁻¹) c) := by
  -- The Fox derivative of the conjugate, inside the free group algebra `K[F(X)]`.
  have hfox : foxD (K := K) x (c * r * c⁻¹) =
      (MonoidAlgebra.of K (FreeGroup X)) c * foxD (K := K) x r +
        (1 - (MonoidAlgebra.of K (FreeGroup X)) (c * r * c⁻¹)) * foxD (K := K) x c := by
    conv_lhs => rw [mul_assoc]
    rw [foxD_mul (K := K) x c (r * c⁻¹), foxD_mul (K := K) x r c⁻¹, foxD_inv (K := K) x c]
    rw [show (MonoidAlgebra.of K (FreeGroup X)) (c * r * c⁻¹)
        = (MonoidAlgebra.of K (FreeGroup X)) c * (MonoidAlgebra.of K (FreeGroup X)) r *
            (MonoidAlgebra.of K (FreeGroup X)) c⁻¹ from by rw [map_mul, map_mul]]
    noncomm_ring
  -- The map on monoid algebras induced by `w ↦ c w c⁻¹` is conjugation by `of c`.
  have hconj : ∀ D : MonoidAlgebra K (FreeGroup X),
      MonoidAlgebra.mapDomainRingHom K (conjAut c) D =
        (MonoidAlgebra.of K (FreeGroup X)) c * D *
          (MonoidAlgebra.of K (FreeGroup X)) c⁻¹ := by
    intro D
    induction D using MonoidAlgebra.induction_linear with
    | zero => rw [map_zero, mul_zero, zero_mul]
    | add x y hx hy => rw [map_add, hx, hy, mul_add, add_mul]
    | single w a =>
        rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply]
        rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, one_mul,
          conjAut_apply]
  -- `conjHom r c` intertwines `presentRho r` with `presentRho (c r c⁻¹) ∘ conjAut c`.
  have hcomp : (MonoidAlgebra.mapDomainRingHom K (conjHom r c)).comp (presentAlg K r)
      = (presentAlg K (c * r * c⁻¹)).comp
          (MonoidAlgebra.mapDomainRingHom K (conjAut c)) := by
    simp only [presentAlg]
    rw [← MonoidAlgebra.mapDomainRingHom_comp, ← MonoidAlgebra.mapDomainRingHom_comp]
    congr 1
  have hφc : presentAlg K (c * r * c⁻¹) ((MonoidAlgebra.of K (FreeGroup X)) c)
      = MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹)) (presentRho (c * r * c⁻¹) c) :=
    presentAlg_of K (c * r * c⁻¹) c
  have hφrel : presentAlg K (c * r * c⁻¹)
      ((MonoidAlgebra.of K (FreeGroup X)) (c * r * c⁻¹)) = 1 := by
    rw [presentAlg_of, presentRho_relator, map_one]
  have harg : ∀ D : MonoidAlgebra K (FreeGroup X),
      ((MonoidAlgebra.of K (FreeGroup X)) c * D * (MonoidAlgebra.of K (FreeGroup X)) c⁻¹) *
          (MonoidAlgebra.of K (FreeGroup X)) c = (MonoidAlgebra.of K (FreeGroup X)) c * D := by
    intro D
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hpsi : MonoidAlgebra.mapDomainRingHom K (conjHom r c) (presentAlg K r (foxD (K:=K) x r))
      = presentAlg K (c * r * c⁻¹)
          ((MonoidAlgebra.mapDomainRingHom K (conjAut c)) (foxD (K:=K) x r)) := by
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply]
  -- Left hand side, in `K[⟨X | c r c⁻¹⟩]`.
  have hL : presentAlg K (c * r * c⁻¹) (foxD (K:=K) x (c * r * c⁻¹)) =
      presentAlg K (c * r * c⁻¹) ((MonoidAlgebra.of K (FreeGroup X)) c) *
        presentAlg K (c * r * c⁻¹) (foxD (K:=K) x r) := by
    have h0 : presentAlg K (c*r*c⁻¹)
        ((1 - (MonoidAlgebra.of K (FreeGroup X)) (c*r*c⁻¹)) * foxD (K:=K) x c) = 0 := by
      rw [map_mul, map_sub, map_one, hφrel, sub_self, zero_mul]
    rw [hfox, map_add, map_mul, h0, add_zero]
  -- Right hand side, in `K[⟨X | c r c⁻¹⟩]`.
  have hR : MonoidAlgebra.mapDomainRingHom K (conjHom r c) (presentAlg K r (foxD (K:=K) x r)) *
        MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹)) (presentRho (c * r * c⁻¹) c)
      = presentAlg K (c * r * c⁻¹) ((MonoidAlgebra.of K (FreeGroup X)) c) *
        presentAlg K (c * r * c⁻¹) (foxD (K:=K) x r) := by
    rw [hpsi, hconj (foxD (K := K) x r), ← hφc]
    conv_lhs => rw [← map_mul]
    rw [harg (foxD (K := K) x r), map_mul]
  rw [relatorVec_apply, relatorVec_apply, hL, hR]

end Work.ORLyndon
