import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.OROneRel.mmStepData_of_expsum_zero

/-!
# Connecting the Cohen--Lyndon induction to the workspace's Magnus step

The workspace's exponent-sum-zero Magnus step (`Work.OROneRel.magnus_step_root_eps_zero`) produces,
for a cyclically reduced root `u` with `t ∈ relatorLetters u` and `eps t u = 0`, the one-relator
group `⟨β | w ^ l⟩` on the *occurring* decorated alphabet `β = mmBeta t (u ^ l)` together with the
explicit isomorphism `e : ⟨α | u ^ l⟩ ≃* HNNExtension ⟨β | w ^ l⟩ A B φ` and the root
`w = rootW t u l …` with `w ^ l = mmW t (u ^ l)`.

The base of the HNN extension embeds into `G = ⟨α | u ^ l⟩` by the **canonical map**
`Work.OROneRel.mmBaseHom`, the map `⟨β | w ^ l⟩ →* G` induced by
`(x, k) ↦ t ^ k * x * t ^ (-k)` (`Work.OROneRel.mmRhoFun`), well defined because
`u ^ l = ζ_t (mmW t (u ^ l))`.

This file contains only *definitions* (no proofs beyond `rfl`-level transport), so that lemma
requests may import it and state their results in this vocabulary.

## Main definitions

* `Work.ORLyndon.mmZeta t r u l hpow` -- the free group homomorphism
  `F(mmBeta t (u ^ l)) →* F(α)`, `p ↦ t ^ (p.2) * p.1 * t ^ (-(p.2))`, the free-group shadow of
  `mmBaseHom`; `mmBaseHom he` is `PresentedGroup.toGroup (presentRho r ∘ mmZeta …)`, i.e.
  `mmBaseHom he ∘ PresentedGroup.mk = presentRho r ∘ mmZeta …` (`mmBaseHom_comp_mk`).
* `Work.ORLyndon.mmEpsPow he` -- `eps t (u ^ l) = 0` from `eps t u = 0`, the argument that
  `mmBaseHom` consumes.
* `Work.ORLyndon.mmRootRel t l hu he hl` -- the relator `rootW t u l … ^ l` of the Magnus base
  (`= mmW t (u ^ l)` by `Work.OROneRel.rootW_pow`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

/-- The exponent sum of `t` in `u ^ l` vanishes when it vanishes in `u`. -/
theorem mmEpsPow {α : Type*} (t : α) (u : FreeGroup α) (l : ℕ) (he : Work.OROneRel.eps t u = 0) :
    Work.OROneRel.eps t (u ^ l) = 0 := by
  have h : Work.OROneRel.sigma t (u ^ l) = 1 := by
    rw [map_pow, (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t u).mp he, one_pow]
  exact (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t (u ^ l)).mpr h

/-- The free-group map underlying the canonical map from the Magnus base: the symbol `p` of the
decorated alphabet is sent to the conjugate `t ^ (p.2) * p.1 * t ^ (-(p.2))`.  It is the composite
of `Work.OROneRel.zeta t` with the inclusion of the occurring decorations into all decorations. -/
noncomputable def mmZeta {α : Type*} (t : α) (r : FreeGroup α) :
    FreeGroup (Work.OROneRel.mmBeta t r) →* FreeGroup α :=
  (Work.OROneRel.zeta t).comp
    (FreeGroup.map fun p : Work.OROneRel.mmBeta t r => (p.1 : Work.OROneRel.MMAlpha t))

@[simp] theorem mmZeta_of {α : Type*} (t : α) (r : FreeGroup α)
    (p : Work.OROneRel.mmBeta t r) :
    mmZeta t r (FreeGroup.of p) =
      Work.OROneRel.zeta t (FreeGroup.of (p.1 : Work.OROneRel.MMAlpha t)) :=
  rfl

end Work.ORLyndon
