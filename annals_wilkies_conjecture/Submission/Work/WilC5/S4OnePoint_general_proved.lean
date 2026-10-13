/-
  WilC5 — **the general case of the one-element step of vdDMM §4** (their Lemmas 4.2 and 4.4).

  `Work.WilC5.S4OnePoint_general` (`S4OnePointCases.lean`) is the one-element step of the §4
  iteration in the case where the prescribed element `x ∈ K` is *not* the exponential of an element
  of the domain; the case `x = expE a` is `Work.WilC5.S4OnePoint_exp` (the companion file
  `S4OnePoint_exp_proved.lean`), and the two give `Work.WilC5.S4OnePoint` by
  `Work.WilC5.S4OnePoint_of_cases`.

  The proof runs the three extension lemmas of van den Dries–Macintyre–Marker §4 at a *maximal*
  member of the Zorn poset `Work.WilC5.S4Pair A σ` of partial extensions of the given pair
  (`S4Setup.lean`): domains `B ≤ K` which are `Dcl`-closed in the `rexp`-reduct and log-closed
  (`S4Dom`), embeddings `LRc`-embeddings of the `rexp`-reducts commuting with the definable
  logarithm (`LogPreserving`).

  * A maximal member `p` exists by Zorn's lemma: the union of a chain of partial extensions is one
    (`Work.WilC5.S4Pair_chain_upper`, `S4SubTE_of_S4OnePoint.lean`).

  * At a maximal `p = (B, τ)` — write `B` for `p.dom` — no element of `K \ B` can have the value of
    an element of `B`: otherwise vdDMM's Lemma 4.2 would extend `p` strictly
    (`Work.WilC5.S4StepNoNew`, `S4StepNoNew.lean`), contradicting maximality.  Hence every element
    outside `B` is *value-new* over `B` (`hvalnew` below).

  * For the same reason no element of `B` can have its exponential outside `B`: otherwise vdDMM's
    Lemma 4.3 would extend `p` strictly (`Work.WilC5.S4StepExp`, `S4StepExp.lean`), its hypothesis
    `ValueNew (expE b)` being the `hvalnew` just derived.  Hence `B` is closed under `expE`.

  * In that fortified situation vdDMM's Lemma 4.4 (`Work.WilC5.S4StepNew`, `S4StepNew.lean`)
    extends `p` strictly past any `x ∈ K \ B`.

  All three cases contradict maximality, so `x ∈ B`: the maximal partial extension already contains
  the prescribed element, and `A' := B`, `σ' := τ` is the required extension.
-/
import Mathlib
import Submission.Work.WilC5.S4OnePointCases
import Submission.Work.WilC5.S4OnePoint
import Submission.Work.WilC5.dmm42_cut_extend
import Submission.Work.WilC5.realizes_cut
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.valIneq_span
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.ExistsEmbeddingClosurePoint
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.S4StepNoNewCut
import Submission.Work.WilC5.S4StepExp
import Submission.Work.WilC5.S4StepNew
import Submission.Work.WilC5.ValProp

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct

/-- **The general case of the one-element step of vdDMM §4**: Lemmas 4.2 and 4.4 of
van den Dries–Macintyre–Marker, run at a maximal partial extension of the §4 iteration.

The hypothesis `hVP : Work.WilC5.ValProp` is the value-theoretic input of vdDMM §3 ((3.4)+(3.7),
the containment half) which is *not* derivable from `hMCr`, `hOM`, `hVI`; it is a lead-sanctioned
explicit hypothesis (`Submission/Work/WilC5/ValProp.lean`), discharged by the node `ValProp_TR`
at the final wire. -/
theorem S4OnePoint_general_proved (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels) (hVI : WilkiesDesign.CG.ValIneq)
    (hVP : Work.WilC5.ValProp) :
    Work.WilC5.S4OnePoint_general := by
  intro K L instK instL hK hL κ hκ hsat A hA σ hlog x hx hxne
  -- The bottom element of the Zorn poset of partial extensions of `(A, σ)`.
  let base : S4Pair A σ :=
    { dom := A
      emb := σ
      h4 := hA
      logpres := hlog
      le_dom := le_refl A
      agrees := fun a => congrArg σ (Subtype.ext rfl) }
  haveI : Nonempty (S4Pair A σ) := ⟨base⟩
  -- Zorn: a maximal partial extension.
  obtain ⟨p, hmax⟩ := zorn_le_nonempty (α := S4Pair A σ)
    (fun c hc hne => S4Pair_chain_upper hc hne)
  -- Its domain contains every prescribed element, by the three extension lemmas of §4.
  have hxmem : x ∈ (p.dom : Set K) := by
    by_contra hx'
    -- Lemma 4.2 contrapositive: for every `y` outside `p.dom`, the definable closure of
    -- `p.dom ∪ {y}` has a value that no element of `p.dom` has.
    have hvalnew : ∀ y : K, y ∉ (p.dom : Set K) →
        ¬ (∀ w : K, w ∈ Work.WilC2.Dcl ((p.dom : Set K) ∪ {y}) →
            ∃ b : ↥p.dom, SameVal K hK (b : K) w) := by
      intro y hy hvg
      obtain ⟨q, hpq, b, hb⟩ := S4StepNoNew hMCr hOM hVI hK hL κ hκ hsat p hy hvg
      have hqp : q ≤ p := hmax hpq
      exact hy (hb ▸ S4Pair.dom_le_of_le hqp b.2)
    -- Lemma 4.3: `p.dom` is closed under the exponential.
    have hexp : ∀ b : ↥p.dom, expE (b : K) ∈ (p.dom : Set K) := by
      intro b
      by_contra hb
      obtain ⟨q, hpq, c, hc⟩ :=
        S4StepExp hMCr hOM hVI hK hL κ hκ hsat p b hb hvalnew
      have hqp : q ≤ p := hmax hpq
      exact hb (hc ▸ S4Pair.dom_le_of_le hqp c.2)
    -- If the closure of `p.dom ∪ {x}` does not change the value group, `S4StepNoNew` applies;
    -- otherwise the fortified situation of `S4StepNew` does.
    by_cases hvgx : ∀ w : K, w ∈ Work.WilC2.Dcl ((p.dom : Set K) ∪ {x}) →
        ∃ b : ↥p.dom, SameVal K hK (b : K) w
    · obtain ⟨q, hpq, b, hb⟩ := S4StepNoNew hMCr hOM hVI hK hL κ hκ hsat p hx' hvgx
      have hqp : q ≤ p := hmax hpq
      exact hx' (hb ▸ S4Pair.dom_le_of_le hqp b.2)
    · obtain ⟨q, hpq, b, hb⟩ := S4StepNew hMCr hOM hVI hVP hK hL κ hκ hsat p hexp hvalnew hx'
      have hqp : q ≤ p := hmax hpq
      exact hx' (hb ▸ S4Pair.dom_le_of_le hqp b.2)
  refine ⟨p.dom, p.h4, p.emb, p.le_dom, ⟨⟨x, hxmem⟩, rfl⟩, ?_, p.logpres⟩
  intro a h
  exact p.agrees a

end Work.WilC5
