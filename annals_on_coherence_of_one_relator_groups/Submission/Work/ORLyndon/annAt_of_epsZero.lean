import Mathlib
import Submission.Work.ORLyndon.annAtDefs
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero_mm
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero
import Submission.Work.ORLyndon.mmBaseHom_injective
import Submission.Work.ORLyndon.mmBaseHom_transport
import Submission.Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq
import Submission.Work.ORLyndon.mmTopSym_mem_relatorLetters
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.joint_annihilator_transport
import Submission.Work.ORLyndon.levelPart_top_mul_mmTopSym
import Submission.Work.ORLyndon.exists_levelPart_max_ne_zero

/-!
# The set-indexed annihilator statement across the exponent-sum-zero Magnus step

This file proves the *set-indexed* transfer of the exponent-sum-zero Magnus step of the
Cohen--Lyndon induction, in the `Work.ORLyndon.annAt` form of
`Submission/Work/ORLyndon/annAtDefs.lean`.

Let `u` be cyclically reduced, not a proper power, with a letter `t` of vanishing `t`-exponent sum
(`eps t u = 0`), and let `l ≥ 1`.  The workspace's Magnus step provides the Magnus base
`H = ⟨mmBeta t (u^l) | mmW t (u^l)⟩` with root `rootW t u l hcyc he hl`, together with the
canonical map `mmBaseHom : H →* G = ⟨α | u^l⟩`, which is injective under these hypotheses.

The theorem states: **if the base satisfies the set-indexed annihilator statement `annAt` for the
set of top decorated symbols `mmTopSym t u l x` of the letters `x` of a set `Em`, then `G`
satisfies `annAt` for the root `u` and the relator `u ^ l` at the set `insert t Em`** — the letters
of `Em` together with the framing letter `t`.

## Proof

Write `τ = presentRho (u^l) (of t)` and `lev = levelOf t (u^l) u l rfl hσ`
(`hσ : sigma t u = 1` from `eps t u = 0`), so that `K[G]` is graded by `lev` over the base
`K[B]`, `B = ker lev`; `levelPart lev k` is the `k`-th graded piece.

Let `b : K[G]` annihilate `rootVec K (u^l) u x` for every `x ∈ insert t Em`; suppose `b ≠ 0` and
let `N` be the **top level** occurring in `b` (`Work.ORLyndon.exists_levelPart_max_ne_zero`):
`levelPart lev N b ≠ 0`, while every level in `b` is `≤ N`.

For a letter `x ≠ t`, the top level occurring in the `x`-component of the root Fox vector is
`i = mmHi t (u^l) ⟨x, xt⟩` (`Work.ORLyndon.level_le_of_foxD_eq_zero`, vacuous when `x` is not a
letter of `u`), and the `i`-th graded piece of that component is the transported base Fox derivative
of the *top decorated symbol* of `x`, times `τ ^ i` (the chain rule
`Work.ORLyndon.levelPart_rootVec_eq_base` together with
`Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq`).  Multiplying the top graded piece of `b`
with it and using `Work.ORLyndon.topPart_mul` gives, after cancelling `τ ^ i`
(`Work.ORLyndon.levelPart_top_mul_mmTopSym`):

`levelPart lev N b * mmBaseHom_*(rootVec K (mmW t (u^l)) (rootW t u l …) (mmTopSym t u l x xt)) = 0`.

Since `x ↦ mmTopSym t u l x xt` is injective, the base hypothesis `annAt` at `mmTopSym '' Em` is a
*joint* statement about these transported base Fox derivatives, and
`Work.ORLyndon.joint_annihilator_transport` (triviality of a set-indexed right annihilator
transports along the injective `mmBaseHom`, `K[G]` being free as a right `K[m.range]`-module) yields
`levelPart lev N b = 0`, contradicting the choice of `N`.  Hence `b = 0`.

The statement is *set-indexed* in `Em` precisely because the induction needs it in that form: it is
monotone in the set (`Work.ORLyndon.annAt_mono`), so the framing letter `t` — whose component has no
base-side counterimage in the decorated alphabet of the Magnus step — is simply *added* to the set,
and no regularity of `(∂u/∂t)_t` on its own is claimed.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

/-- **The exponent-sum-zero Magnus step, in the set-indexed annihilator form.**  With
`hσ : sigma t u = 1` the map `levelOf t (u ^ l) u l rfl hσ` grades `K[G]` over the Magnus base
`K[ker (levelOf)]`, and `mmBaseHom` embeds the base `⟨mmBeta t (u^l) | mmW t (u^l)⟩`.  If the base
satisfies `annAt` at the set of top decorated symbols `mmTopSym t u l x`, `x ∈ Em`, then `G`
satisfies `annAt` at the letters of `Em` together with the framing letter `t`. -/
theorem annAt_of_epsZero {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    (Em : Set {x : α // x ≠ t})
    (h : Work.ORLyndon.annAt K (Work.OROneRel.mmW t (u ^ l))
          (Work.OROneRel.rootW t u l hcyc he hl)
          ((fun x : {x : α // x ≠ t} => Work.ORLyndon.mmTopSym t u l x.1 x.2) '' Em)) :
    Work.ORLyndon.annAt K (u ^ l) u (insert t (Subtype.val '' Em)) := by
  classical
  have hσ : Work.OROneRel.sigma t u = 1 :=
    (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t u).mp he
  have hm : Function.Injective (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
      (Work.ORLyndon.mmEpsPow t u l he)) :=
    mmBaseHom_injective t u l hl hpp hcyc ht he
  -- the base hypothesis, transported across the injective `mmBaseHom` to all of `K[G]`
  have htrans : ∀ c : MonoidAlgebra K (OneRelatorGroup (u ^ l)),
      (∀ q ∈ ((fun x : {x : α // x ≠ t} => mmTopSym t u l x.1 x.2) '' Em),
        c * MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
          (Work.ORLyndon.mmEpsPow t u l he))
          (rootVec K (Work.OROneRel.mmW t (u ^ l))
            (Work.OROneRel.rootW t u l hcyc he hl) q) = 0) → c = 0 := by
    intro c hc
    refine joint_annihilator_transport
      (m := Work.OROneRel.mmBaseHom (t := t) (r := u ^ l) (Work.ORLyndon.mmEpsPow t u l he))
      hm
      (rootVec K (Work.OROneRel.mmW t (u ^ l)) (Work.OROneRel.rootW t u l hcyc he hl) ''
        ((fun x : {x : α // x ≠ t} => mmTopSym t u l x.1 x.2) '' Em))
      (fun z hz => h z fun q hq => hz _ ⟨q, hq, rfl⟩) c ?_
    rintro Y ⟨q, hq, rfl⟩
    exact hc q hq
  intro b hb
  by_contra hbne
  -- the top level part of `b` is non-zero, and every level in `b` is at most `N`
  obtain ⟨N, hpartN, hbN⟩ :=
    exists_levelPart_max_ne_zero (t := t) (hpow := rfl) (hσ := hσ) hbne
  -- the top level part of `b` annihilates the transported base Fox derivative at every top
  -- decorated symbol of a letter of `Em`
  refine hpartN (htrans (levelPart t (u ^ l) u l rfl hσ N b) ?_)
  rintro q ⟨x, hxEm, rfl⟩
  refine levelPart_top_mul_mmTopSym t u l hl hcyc he x.1 x.2 N b hbN ?_
  exact hb x.1 (by rw [Set.mem_insert_iff]; exact Or.inr ⟨x, hxEm, rfl⟩)

end Work.ORLyndon
