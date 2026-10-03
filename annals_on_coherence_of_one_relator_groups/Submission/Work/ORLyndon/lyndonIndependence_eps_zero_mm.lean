import Mathlib
import Submission.Work.ORLyndon.mmConnDefs
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero
import Submission.Work.ORLyndon.ann_rootVec_of_level
import Submission.Work.ORLyndon.mmBaseHom_transport
import Submission.Work.ORLyndon.mmBaseHom_injective
import Submission.Work.ORLyndon.mmBaseHom_comp_mk
import Submission.Work.ORLyndon.range_mmBaseHom_ncl
import Submission.Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq
import Submission.Work.OROneRel.magnus_step_root

/-!
# The exponent-sum-zero Magnus step of the Cohen--Lyndon induction, in the decorated alphabet

This file reworks the `σ_t = 0` step of `Submission/Work/ORLyndon/lyndonIndependence_eps_zero.lean`
in the alphabet in which the workspace's Magnus step actually lives.

## The problem with the `MagnusBeta` (all decorations) interface

`lyndonIndependence_eps_zero.lean` states the step with the *canonical* map
`m : ⟨β | (magRewRel t u) ^ l⟩ →* G` on the *full* decorated alphabet
`MagnusBeta t = ({a // a ≠ t} × ℤ)`, whose `(x, k)`-generators are `t ^ k * x * t ^ (-k)`, and
takes its *injectivity* as a hypothesis.  That injectivity is **false** in general: the generators
of the base that do not occur in the Magnus rewriting `magRewRel t u` generate a free factor which
the canonical map does not see (e.g. `u = [x, y]`, `t = x`: the rewriting collapses and every
`(y, i)` maps to the class of `y`).  Consequently the `MagnusBeta` interface can only be instantiated
in the degenerate cases where the occurring decorations exhaust `MagnusBeta`.

## The correct interface: the occurring decorations

The workspace's Magnus step (`Work.OROneRel.magnus_step_root_eps_zero`, `Submission/Work/OROneRel/`)
uses instead the *occurring* decorated alphabet `mmBeta t (u ^ l)` (the interval closure `mmDecSet` of
the decorations actually appearing) and produces the explicit isomorphism
`G ≃* HNNExtension ⟨mmBeta t (u^l) | mmW t (u^l)⟩ A B φ` and the root
`rootW t u l hcyc he hl` with `rootW ^ l = mmW t (u ^ l)`.  In this alphabet the canonical map
`Work.OROneRel.mmBaseHom : ⟨mmBeta t (u^l) | mmW t (u^l)⟩ →* G` **is** injective
(`Work.ORLyndon.mmBaseHom_injective`, from `Work.OROneRel.mmBaseHom_injective`), and its range has
normal closure exactly the Magnus base `ker (levelOf)`
(`Work.ORLyndon.range_mmBaseHom_ncl`).

## What is proved here

* `Work.ORLyndon.mmTopSym` -- the top decorated symbol `(x, mmHi)` of a letter `x`;
* `Work.ORLyndon.hbase_of_ih_mm` -- the *base transport*: the induction hypothesis at the base
  (right regularity of the base root Fox vector at the symbol `q` of the decorated alphabet) is
  moved along `mmBaseHom` across the normal closure `ncl (mmBaseHom.range) = ker (levelOf)` by
  `Work.ORLyndon.base_regularity_transport_of_le`; the identification of the transported base element
  with the Fox derivative appearing in the chain rule is
  `Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq`;
* `Work.ORLyndon.orderOf_of_mmBaseHom` -- the order of the class of the root is unchanged;
* `Work.ORLyndon.lyndon_independence_of_pow_eps_zero_mm` -- the assembled step: from the base
  induction hypothesis at the top decorated symbol of some letter `x ≠ t` and the base order
  statement, `LyndonIndependence K (u ^ l) u`.  No injectivity of a *canonical* map is assumed: it is
  proved here.

## Hypotheses of the assembled step

Besides the geometry (`u` cyclically reduced with `t ∈ relatorLetters u` and `eps t u = 0`,
`l ≥ 1`, `x ∈ relatorLetters u`, `x ≠ t`), the step consumes exactly the two halves of the
induction hypothesis at the Magnus base `⟨mmBeta t (u^l) | mmW t (u^l)⟩` with root
`v = rootW t u l hcyc he hl` (`v ^ l = mmW t (u ^ l)`):

* `hIH`: multiplication by the `mmTopSym`-component of the Fox vector of `v` in `K[⟨β|v^l⟩]`
  (`β = mmBeta t (u^l)`) is injective — the base regularity at the *top decorated symbol* of `x`;
* `hIHord`: the class of `v` has order exactly `l` in the base.

The root `v` has strictly smaller relator norm than `u` (`Work.OROneRel.relatorNorm_rootW_lt`) and is
again not a proper power (`Work.OROneRel.not_isProperPower_rootW`), so these are exactly the
induction hypotheses of the strong induction on `relatorNorm`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ORLyndon

open MonoidAlgebra

variable {α : Type*} [DecidableEq α] {K : Type*} [Field K]

/-- **The top decorated symbol of a letter.**  For a letter `x ≠ t`, the symbol
`(x, mmHi t (u^l) x)` of the occurring decorated alphabet `mmBeta t (u ^ l)`: the occurrence of `x`
with the largest `t`-exponent-sum decoration. -/
noncomputable def mmTopSym (t : α) (u : FreeGroup α) (l : ℕ) (x : α) (hxt : x ≠ t) :
    Work.OROneRel.mmBeta t (u ^ l) :=
  ⟨((⟨x, hxt⟩ : {a : α // a ≠ t}), Work.OROneRel.mmHi t (u ^ l) ⟨x, hxt⟩),
    Work.OROneRel.mmHi_mem_decSet t (u ^ l) ⟨x, hxt⟩⟩

@[simp] theorem mmTopSym_val (t : α) (u : FreeGroup α) (l : ℕ) (x : α) (hxt : x ≠ t) :
    ((mmTopSym t u l x hxt : Work.OROneRel.mmBeta t (u ^ l)) : Work.OROneRel.MMAlpha t) =
      ((⟨x, hxt⟩ : {a : α // a ≠ t}), Work.OROneRel.mmHi t (u ^ l) ⟨x, hxt⟩) := rfl

/-- **The base transport.**  Let `u` be cyclically reduced with `t ∈ relatorLetters u` and
`eps t u = 0`.  The induction hypothesis at the Magnus base — right regularity of the `q`-component
of the Fox vector of the base root `rootW t u l hcyc he hl` in the base group
`⟨mmBeta t (u^l) | mmW t (u^l)⟩` — transports along `mmBaseHom` to the corresponding statement for
the element `∂(magRewRel t u)/∂q.1` of `K[G]`, restricted to elements of `K[G]` supported on the
Magnus base `ker (levelOf)`.

The transport uses that `mmBaseHom` is injective and that the normal closure of its range is
`ker (levelOf)`; no normality of the range itself is needed
(`Work.ORLyndon.base_regularity_transport_of_le`). -/
theorem hbase_of_ih_mm (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : Work.OROneRel.IsCyclicallyReducedRelator u) (he : Work.OROneRel.eps t u = 0)
    (hl : 1 ≤ l) (q : Work.OROneRel.mmBeta t (u ^ l))
    (hm : Function.Injective (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
      (Work.ORLyndon.mmEpsPow t u l he)))
    (hIH : ∀ c : MonoidAlgebra K (Work.OROneRel.mmH t (u ^ l)),
      c * rootVec K (Work.OROneRel.mmW t (u ^ l))
        (Work.OROneRel.rootW t u l hu he hl) q = 0 → c = 0) :
    ∀ c : MonoidAlgebra K (OneRelatorGroup (u ^ l)),
      c * MonoidAlgebra.mapDomainRingHom K
            ((presentRho (u ^ l)).comp (Work.OROneRel.zeta t))
            (foxD (K := K) (X := MagnusBeta t) (q.1 : Work.OROneRel.MMAlpha t)
              (Work.OROneRel.magRewRel t u)) = 0 → c = 0 := by
  intro c hcE
  have hcE' : c * MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.mmBaseHom (t := t)
        (r := u ^ l) (Work.ORLyndon.mmEpsPow t u l he))
      (rootVec K (Work.OROneRel.mmW t (u ^ l)) (Work.OROneRel.rootW t u l hu he hl) q) = 0 := by
    rw [mapDomainRingHom_mmBaseHom_rootVec_eq (K := K) t u l hu he hl q]
    exact hcE
  exact mmBaseHom_transport (K := K) (t := t) (r := u ^ l)
    (Work.ORLyndon.mmEpsPow t u l he) hm _ hIH c hcE'

/-- **The order of the class of the root is unchanged by the Magnus step** (decorated-alphabet
form).  If the class of the base root `rootW t u l hcyc he hl` has order `l` in the Magnus base
`⟨mmBeta t (u^l) | mmW t (u^l)⟩`, then the class of `u` has order `l` in `G = ⟨α | u^l⟩`, because the
injective map `mmBaseHom` carries the former to the latter. -/
theorem orderOf_of_mmBaseHom (t : α) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    (hord : orderOf (presentRho (Work.OROneRel.mmW t (u ^ l))
      (Work.OROneRel.rootW t u l hcyc he hl)) = l) :
    orderOf (presentRho (u ^ l) u) = l := by
  classical
  have hm : Function.Injective (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
      (Work.ORLyndon.mmEpsPow t u l he)) :=
    mmBaseHom_injective t u l hl hpp hcyc ht he
  -- the canonical map carries the base root to the class of `u`
  have hval : Work.OROneRel.mmBaseHom (t := t) (r := u ^ l) (Work.ORLyndon.mmEpsPow t u l he)
      (presentRho (Work.OROneRel.mmW t (u ^ l))
        (Work.OROneRel.rootW t u l hcyc he hl)) = presentRho (u ^ l) u := by
    have hcomp := mmBaseHom_comp_mk t (u ^ l) (Work.ORLyndon.mmEpsPow t u l he)
    have h1 : Work.OROneRel.mmBaseHom (t := t) (r := u ^ l) (Work.ORLyndon.mmEpsPow t u l he)
        (presentRho (Work.OROneRel.mmW t (u ^ l))
          (Work.OROneRel.rootW t u l hcyc he hl))
        = presentRho (u ^ l) (Work.ORLyndon.mmZeta t (u ^ l)
          (Work.OROneRel.rootW t u l hcyc he hl)) := by
      have h := DFunLike.congr_fun hcomp (Work.OROneRel.rootW t u l hcyc he hl)
      simpa only [MonoidHom.comp_apply, presentRho] using h
    rw [h1]
    congr 1
    -- `mmZeta` on the root is `u`, by the telescoping identity `lift_mmRho_rootW`
    have hzeta : Work.ORLyndon.mmZeta t (u ^ l) =
        FreeGroup.lift (fun p : Work.OROneRel.mmBeta t (u ^ l) =>
          Work.OROneRel.mmRhoFun t p.1) := by
      refine FreeGroup.ext_hom _ _ fun p => ?_
      rw [Work.ORLyndon.mmZeta_of]
      rfl
    rw [hzeta, Work.OROneRel.lift_mmRho_rootW t u l hcyc he hl]
  rw [← hval]
  rw [orderOf_injective _ hm (presentRho (Work.OROneRel.mmW t (u ^ l))
    (Work.OROneRel.rootW t u l hcyc he hl))]
  exact hord

/-- **The exponent-sum-zero Magnus step of the Cohen--Lyndon induction** (decorated-alphabet form).

Let `u` be cyclically reduced, not a proper power, with `t ∈ relatorLetters u`, `eps t u = 0`, and
let `x ≠ t` be another letter of `u`.  Assume the induction hypothesis at the Magnus base
`⟨mmBeta t (u^l) | mmW t (u^l)⟩` at the top decorated symbol `mmTopSym t u l x hxt` of `x`
(`hIH`) and the order of the base root (`hIHord`).  Then the Cohen--Lyndon independence holds for
the root `u` and the relator `u ^ l`.

The proof is the leading-level transfer
(`Work.ORLyndon.ann_rootVec_of_magnusRewriting`): the `i`-th level part of the `x`-component of the
Fox vector of `u` is the transported base Fox derivative times `τ ^ i`
(`Work.ORLyndon.levelPart_rootVec_eq_base`), whose top level is at `i = mmHi t (u^l) x`
(`Work.ORLyndon.level_le_of_foxD_eq_zero`), and the base regularity at that top level is supplied by
`Work.ORLyndon.hbase_of_ih_mm`. -/
theorem lyndon_independence_of_pow_eps_zero_mm (t : α) (u : FreeGroup α) (l : ℕ)
    (hl : 1 ≤ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    (x : α) (hxt : x ≠ t) (hx : x ∈ Work.OROneRel.relatorLetters u)
    (hIH : ∀ c : MonoidAlgebra K (Work.OROneRel.mmH t (u ^ l)),
      c * rootVec K (Work.OROneRel.mmW t (u ^ l))
        (Work.OROneRel.rootW t u l hcyc he hl) (mmTopSym t u l x hxt) = 0 → c = 0)
    (hIHord : orderOf (presentRho (Work.OROneRel.mmW t (u ^ l))
      (Work.OROneRel.rootW t u l hcyc he hl)) = l) :
    LyndonIndependence K (u ^ l) u := by
  classical
  have hσ : Work.OROneRel.sigma t u = 1 :=
    (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t u).mp he
  have hm : Function.Injective (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
      (Work.ORLyndon.mmEpsPow t u l he)) :=
    mmBaseHom_injective t u l hl hpp hcyc ht he
  have hdec : ∀ j : ℤ, Work.OROneRel.mmHi t (u ^ l) ⟨x, hxt⟩ < j →
      foxD (K := K) (X := MagnusBeta t) ((⟨x, hxt⟩ : {a : α // a ≠ t}), j)
        (Work.OROneRel.magRewRel t u) = 0 := by
    intro j hj
    refine foxD_eq_zero_of_notMem_relatorLetters (K := K) _ _ fun hmemj => ?_
    have hle := (mmHi_mem_relatorLetters t u ⟨x, hxt⟩ hx).2 j hmemj
    rw [Work.OROneRel.mmHi_pow t u hcyc he l hl ⟨x, hxt⟩] at hj
    omega
  have hbase := hbase_of_ih_mm (K := K) t u l hcyc he hl (mmTopSym t u l x hxt) hm hIH
  have hann : ∀ b : MonoidAlgebra K (OneRelatorGroup (u ^ l)),
      b * rootVec K (u ^ l) u x = 0 → b = 0 :=
    fun b hb => ann_rootVec_of_magnusRewriting (K := K) t x hxt (u ^ l) u l rfl hσ
      (Work.OROneRel.mmHi t (u ^ l) ⟨x, hxt⟩) hdec (fun c _ hcE => hbase c hcE) b hb
  have hord : orderOf (presentRho (u ^ l) u) = l :=
    orderOf_of_mmBaseHom t u l hl hpp hcyc ht he hIHord
  exact lyndon_independence_of_rootVec_inj (u ^ l) u l hl rfl hord
    (ann_rootVec_of_component (u ^ l) u x hann)

end Work.ORLyndon
