import Mathlib
import Submission.Work.ORLyndon.mmConnDefs
import Submission.Work.ORLyndon.mmBaseHom_comp_mk
import Submission.Work.ORLyndon.foxD_map_of_injective
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero
import Submission.Work.OROneRel.magnus_step_root

/-!
# The Fox chain rule across the Magnus rewriting of the base

The workspace's exponent-sum-zero Magnus step produces, for a cyclically reduced root `u` with
`t ∈ relatorLetters u` and `eps t u = 0`, the one-relator base `⟨mmBeta t (u ^ l) | mmW t (u ^ l)⟩`
with root `rootW t u l …` (`rootW ^ l = mmW t (u ^ l)`), together with the canonical map
`mmBaseHom : ⟨mmBeta t (u ^ l) | mmW t (u ^ l)⟩ →* ⟨α | u ^ l⟩` induced by the conjugates
`(x, k) ↦ t ^ k * x * t ^ (-k)`.

This file computes the image of the *Fox vector of the base root* under `mmBaseHom`: for a decorated
letter `q : mmBeta t (u ^ l)`, the base component `∂ (rootW) / ∂q`, pushed forward along `mmBaseHom`,
is the image of the component `∂ (magRewRel t u) / ∂ q.1` of the Fox derivative of the Magnus
rewriting `magRewRel t u` of `u`, pushed forward along `presentRho (u ^ l) ∘ zeta t`.

The proof is the chain rule for the free-group inclusion `mmBeta t (u ^ l) ↪ MMAlpha t` of the
occurring decorations into all decorations, combined with the defining property of `mmBaseHom`
(`mmBaseHom_comp_mk`).
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- `Work.OROneRel.magRewRel` and the list `Work.OROneRel.mmList` describe the same Magnus
rewriting of a word (`rewrite` and `magRew` are the same recursion, shifted by zero). -/
theorem magRewRel_eq_mk_mmList {α : Type*} (t : α) (u : FreeGroup α) :
    Work.OROneRel.magRewRel t u = FreeGroup.mk (Work.OROneRel.mmList t u) := by
  classical
  rw [Work.OROneRel.magRewRel, Work.OROneRel.mmList, Work.OROneRel.magRew_eq_rewriteAux]
  rfl

/-- The inclusion of the occurring decorated alphabet `mmBeta t (u ^ l)` into all decorations
`MMAlpha t` carries the root `rootW t u l …` (the Magnus rewriting of `u` over the occurring
decorations) to the Magnus rewriting `magRewRel t u` (over all decorations). -/
theorem map_subtype_val_rootW {α : Type*} (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : Work.OROneRel.IsCyclicallyReducedRelator u)
    (he : Work.OROneRel.eps t u = 0) (hl : 1 ≤ l) :
    FreeGroup.map (fun p : Work.OROneRel.mmBeta t (u ^ l) => (p.1 : Work.OROneRel.MMAlpha t))
        (Work.OROneRel.rootW t u l hu he hl) = Work.OROneRel.magRewRel t u := by
  classical
  rw [Work.OROneRel.rootW, FreeGroup.map.comp]
  rw [show (fun p : Work.OROneRel.mmBeta t (u ^ l) => (p.1 : Work.OROneRel.MMAlpha t)) ∘
        (Work.OROneRel.mmTransFun t u l hu he hl)
      = (fun p : Work.OROneRel.mmBeta t u => (p.1 : Work.OROneRel.MMAlpha t)) from
    funext fun p => Work.OROneRel.mmTransFun_val t u l hu he hl p]
  rw [Work.OROneRel.mmW_map_val]
  exact (magRewRel_eq_mk_mmList t u).symm

/-- `MonoidAlgebra.mapDomainRingHom` is compatible with composition of the underlying monoid
homomorphisms, in the applied form used below. -/
theorem mapDomainRingHom_comp_apply {M N O : Type*} [Monoid M] [Monoid N] [Monoid O]
    {K : Type*} [Semiring K] (f : N →* O) (g : M →* N) (x : MonoidAlgebra K M) :
    MonoidAlgebra.mapDomainRingHom K (f.comp g) x =
      MonoidAlgebra.mapDomainRingHom K f (MonoidAlgebra.mapDomainRingHom K g x) := by
  rw [MonoidAlgebra.mapDomainRingHom_comp]
  rfl

/-- The Fox chain rule in the decorated alphabet: the `q`-component of the Fox derivative of the
root `rootW t u l …`, pushed along the inclusion of the occurring decorations `mmBeta t (u ^ l)`
into all decorations `MMAlpha t`, is the `q.1`-component of the Fox derivative of the Magnus
rewriting `magRewRel t u`. -/
theorem mapDomainRingHom_foxD_rootW_eq {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : Work.OROneRel.IsCyclicallyReducedRelator u)
    (he : Work.OROneRel.eps t u = 0) (hl : 1 ≤ l)
    (q : Work.OROneRel.mmBeta t (u ^ l)) :
    MonoidAlgebra.mapDomainRingHom K
        (FreeGroup.map (fun p : Work.OROneRel.mmBeta t (u ^ l) =>
          (p.1 : Work.OROneRel.MMAlpha t)))
        (foxD (K := K) (X := Work.OROneRel.mmBeta t (u ^ l)) q
          (Work.OROneRel.rootW t u l hu he hl))
      = foxD (K := K) (X := Work.OROneRel.MMAlpha t)
          (q.1 : Work.OROneRel.MMAlpha t) (Work.OROneRel.magRewRel t u) := by
  have h := foxD_map_of_injective (K := K) (X := Work.OROneRel.mmBeta t (u ^ l))
    (Y := Work.OROneRel.MMAlpha t)
    (fun p : Work.OROneRel.mmBeta t (u ^ l) => (p.1 : Work.OROneRel.MMAlpha t))
    Subtype.val_injective q (Work.OROneRel.rootW t u l hu he hl)
  rw [← map_subtype_val_rootW t u l hu he hl]
  exact h.symm

/-- **The chain rule across the Magnus rewriting, in the group algebra of the base.**

For a cyclically reduced root `u` with `eps t u = 0`, the image under the canonical map
`mmBaseHom` of the `q`-component of the Fox vector of the base root `rootW t u l …` is the image
under `presentRho (u ^ l) ∘ zeta t` of the `q.1`-component of the Fox derivative of the Magnus
rewriting `magRewRel t u`. -/
theorem mapDomainRingHom_mmBaseHom_rootVec_eq {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : Work.OROneRel.IsCyclicallyReducedRelator u)
    (he : Work.OROneRel.eps t u = 0) (hl : 1 ≤ l)
    (q : Work.OROneRel.mmBeta t (u ^ l)) :
    MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
        (Work.ORLyndon.mmEpsPow t u l he))
      (rootVec K (Work.OROneRel.mmW t (u ^ l)) (Work.OROneRel.rootW t u l hu he hl) q)
    = MonoidAlgebra.mapDomainRingHom K
        ((Work.ORLyndon.presentRho (u ^ l)).comp (Work.OROneRel.zeta t))
        (foxD (K := K) (X := Work.ORLyndon.MagnusBeta t)
          (q.1 : Work.OROneRel.MMAlpha t) (Work.OROneRel.magRewRel t u)) := by
  classical
  rw [rootVec_apply, Work.ORLyndon.presentAlg]
  rw [← mapDomainRingHom_comp_apply]
  rw [Work.ORLyndon.presentRho, Work.ORLyndon.mmBaseHom_comp_mk t (u ^ l)
      (Work.ORLyndon.mmEpsPow t u l he)]
  rw [Work.ORLyndon.mmZeta]
  rw [← MonoidHom.comp_assoc]
  rw [mapDomainRingHom_comp_apply]
  rw [← mapDomainRingHom_foxD_rootW_eq t u l hu he hl q]

end Work.ORLyndon
