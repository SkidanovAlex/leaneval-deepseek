import Mathlib
import Submission.Work.OROneRel.wgtMMDefs
import Submission.Work.OROneRel.magnusSubgroupOf_equiv_freeGroup

/-!
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The weighted Magnus--Moldavanskii step: the chain relations

This file proves `Work.OROneRel.wgtPhiChain`, the collection of computation rules for the weighted
Magnus--Moldavanskii step defined in `Submission.Work.OROneRel.wgtMMDefs`:

* `wgtPhiChain_phi_gen` -- the value of the isomorphism `wPhi : wA ≃* wB` on the generator
  `PresentedGroup.of p` of `wA` attached to a symbol `p ∈ wTA` (this is the hypothesis
  `Work.OROneRel.wPhiOfHyp` consumed by `wgtCompositions`);
* `wgtPhiChain_phi_wGA` -- the same computation with the distinguished element `wGA e` of `wA`
  (here the statement is an equality in `wB`, not only after coercing to `wH`);
* `wgtPhiChain_hnn` -- the resulting HNN relation `of (φ a) = t * of a * t⁻¹` in `wK`;
* `wgtPhiChain_shift_step`, `wgtPhiChain_chain` -- the iterated conjugation formula
  `t ^ m * of (x i) * t ^ (-m) = of (x (i+m))` (the hypothesis `Work.OROneRel.wChainHyp` consumed
  by `wgtThetaFacts` and `wgtCompositions`).

All four conjuncts of `wgtPhiChain` are pure consequences of the definitions: no Freiheitssatz-type
input beyond the injectivity hypotheses `hFw hc hA hB` already appearing in the definitions is
needed.
-/

namespace Work.OROneRel

universe u

set_option linter.unusedVariables false

variable {α : Type u} [DecidableEq α]

/-- The isomorphism `wIsoA : F(wTA) ≃* wA` sends the generator `FreeGroup.of e` to the element
`wGA e` of `wA`: both are `PresentedGroup.of e` and the congruence of subgroups does not change the
underlying element. -/
theorem wgtPhiChain_isoA_of {c : α → ℤ} {t : α} {u : FreeGroup α}
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u)) (e : wTA c t u) :
    wIsoA (c := c) (t := t) (u := u) hFw hc hA (FreeGroup.of e) = wGA e := by
  have hx : (wIsoA (c := c) (t := t) (u := u) hFw hc hA (FreeGroup.of e) : wH c t u)
      = presentedGroupMap (wW c t u) (wTA c t u) (FreeGroup.of e) := rfl
  apply Subtype.ext
  rw [hx, presentedGroupMap_of_apply]
  rfl

/-- The isomorphism `wIsoB : F(wTB) ≃* wB` sends the generator `FreeGroup.of e` to `wGB e`. -/
theorem wgtPhiChain_isoB_of {c : α → ℤ} {t : α} {u : FreeGroup α}
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) (e : wTB c t u) :
    wIsoB (c := c) (t := t) (u := u) hFw hc hB (FreeGroup.of e) = wGB e := by
  have hx : (wIsoB (c := c) (t := t) (u := u) hFw hc hB (FreeGroup.of e) : wH c t u)
      = presentedGroupMap (wW c t u) (wTB c t u) (FreeGroup.of e) := rfl
  apply Subtype.ext
  rw [hx, presentedGroupMap_of_apply]
  rfl

/-- `wPhi` sends the generator `wGA e` of `wA` to the generator `wGB (wTshift e)` of `wB`: the two
isomorphisms `wIsoA`, `wIsoB` are inverted by the shift of the decorations. -/
theorem wgtPhiChain_phi_wGA {c : α → ℤ} {t : α} {u : FreeGroup α}
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) (e : wTA c t u) :
    wPhi (c := c) (t := t) (u := u) hFw hc hA hB (wGA e) = wGB (wTshift c t u e) := by
  have hsymm : (wIsoA (c := c) (t := t) (u := u) hFw hc hA).symm (wGA e) = FreeGroup.of e := by
    rw [MulEquiv.symm_apply_eq]
    exact (wgtPhiChain_isoA_of hFw hc hA e).symm
  have hcomp : wPhi (c := c) (t := t) (u := u) hFw hc hA hB (wGA e)
      = wIsoB (c := c) (t := t) (u := u) hFw hc hB
          (FreeGroup.freeGroupCongr (wTshift c t u)
            ((wIsoA (c := c) (t := t) (u := u) hFw hc hA).symm (wGA e))) := rfl
  rw [hcomp, hsymm, FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
  exact wgtPhiChain_isoB_of hFw hc hB (wTshift c t u e)

/-- The value of `wPhi` on an arbitrary element `⟨PresentedGroup.of p, hy⟩` of `wA` is
`PresentedGroup.of (wBetaOf ((p.1.1, p.1.2 + 1)))`.  This is the statement `wPhiOfHyp` of
`wgtMMDefs`. -/
theorem wgtPhiChain_phi_gen {c : α → ℤ} {t : α} {u : FreeGroup α}
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (p : wBeta c t u) (hy : PresentedGroup.of p ∈ wA c t u) (hp : p ∈ wTA c t u) :
    ((wPhi (c := c) (t := t) (u := u) hFw hc hA hB ⟨PresentedGroup.of p, hy⟩ : wB c t u) :
        wH c t u)
      = PresentedGroup.of (wBetaOf c t u ((p.1.1, p.1.2 + 1) : WgtBeta t)) := by
  have h1 : (⟨PresentedGroup.of p, hy⟩ : wA c t u) = wGA (⟨p, hp⟩ : wTA c t u) :=
    Subtype.ext rfl
  rw [h1, wgtPhiChain_phi_wGA hFw hc hA hB ⟨p, hp⟩]
  have hbeta : ((wTshift c t u ⟨p, hp⟩ : wTB c t u) : wBeta c t u)
      = wBetaOf c t u ((p.1.1, p.1.2 + 1) : WgtBeta t) := by
    apply Subtype.ext
    rw [wBetaOf_val c t u hp]
    rfl
  show PresentedGroup.of ((wTshift c t u ⟨p, hp⟩ : wTB c t u) : wBeta c t u)
      = PresentedGroup.of (wBetaOf c t u ((p.1.1, p.1.2 + 1) : WgtBeta t))
  rw [hbeta]

/-- The HNN relation attached to a symbol `p ∈ wTA` of the base group: conjugating the loop class of
`p` by the stable letter gives the loop class of the shifted symbol. -/
theorem wgtPhiChain_hnn {c : α → ℤ} {t : α} {u : FreeGroup α}
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (p : wBeta c t u) (hp : p ∈ wTA c t u) :
    HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((p.1.1, p.1.2 + 1) : WgtBeta t)))
      = (HNNExtension.t : wK c t u hFw hc hA hB) *
          HNNExtension.of (PresentedGroup.of p) *
          (HNNExtension.t : wK c t u hFw hc hA hB)⁻¹ := by
  have hy : PresentedGroup.of p ∈ wA c t u := Subgroup.subset_closure ⟨⟨p, hp⟩, rfl⟩
  have key := HNNExtension.equiv_eq_conj
      (φ := wPhi (c := c) (t := t) (u := u) hFw hc hA hB)
      (⟨PresentedGroup.of p, hy⟩ : wA c t u)
  rw [wgtPhiChain_phi_gen hFw hc hA hB p hy hp] at key
  simpa using key

/-- The HNN relation in the form used for the iterated conjugation: for a symbol `q = (x, i)` of the
base of the interval closure whose shift `(x, i+1)` is still a symbol, conjugation by the stable
letter moves the loop class of `q` to the loop class of the shifted symbol. -/
theorem wgtPhiChain_shift_step {c : α → ℤ} {t : α} {u : FreeGroup α}
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (q : WgtBeta t) (hq : q ∈ wDecSet c t u)
    (hq1 : ((q.1, q.2 + 1) : WgtBeta t) ∈ wDecSet c t u) :
    (HNNExtension.t : wK c t u hFw hc hA hB) *
        HNNExtension.of (PresentedGroup.of (wBetaOf c t u q)) *
        (HNNExtension.t : wK c t u hFw hc hA hB)⁻¹
      = HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((q.1, q.2 + 1) : WgtBeta t))) := by
  have hp : (⟨q, hq⟩ : wBeta c t u) ∈ wTA c t u := by
    show ((q.1, q.2 + 1) : WgtBeta t) ∈ wDecSet c t u
    exact hq1
  have h := (wgtPhiChain_hnn hFw hc hA hB (⟨q, hq⟩ : wBeta c t u) hp).symm
  have heq : (⟨q, hq⟩ : wBeta c t u) = wBetaOf c t u q :=
    Subtype.ext (wBetaOf_val c t u hq).symm
  have hcong : (HNNExtension.of (PresentedGroup.of (⟨q, hq⟩ : wBeta c t u)) :
        wK c t u hFw hc hA hB)
      = HNNExtension.of (PresentedGroup.of (wBetaOf c t u q)) := by
    apply congrArg HNNExtension.of
    apply congrArg PresentedGroup.of
    exact heq
  calc (HNNExtension.t : wK c t u hFw hc hA hB) *
        HNNExtension.of (PresentedGroup.of (wBetaOf c t u q)) *
        (HNNExtension.t : wK c t u hFw hc hA hB)⁻¹
      = (HNNExtension.t : wK c t u hFw hc hA hB) *
        HNNExtension.of (PresentedGroup.of (⟨q, hq⟩ : wBeta c t u)) *
        (HNNExtension.t : wK c t u hFw hc hA hB)⁻¹ := by rw [hcong]
    _ = HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((q.1, q.2 + 1) : WgtBeta t))) := h

/-- The iterated conjugation formula `wChainHyp` of `wgtMMDefs`: as long as the symbols
`(x, i+1), …, (x, i+m)` stay inside the interval closure, conjugating the loop class of `(x, i)` by
`t ^ m` gives the loop class of `(x, i+m)`. -/
theorem wgtPhiChain_chain {c : α → ℤ} {t : α} {u : FreeGroup α}
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) :
    wChainHyp c t u hFw hc hA hB := by
  intro x i hi m
  induction m with
  | zero =>
      intro _
      simp
  | succ n ih =>
      intro hm
      have hstepS : ((x, i + (n : ℤ) + 1) : WgtBeta t) ∈ wDecSet c t u :=
        hm n (Nat.lt_succ_self n)
      have hmid : ((x, i + (n : ℤ)) : WgtBeta t) ∈ wDecSet c t u := by
        have h1 : wLo c t u x ≤ i := ((wDecSet_def c t u).mp hi).1
        have h2 : i ≤ wHi c t u x := ((wDecSet_def c t u).mp hi).2
        have h3 : wLo c t u x ≤ i + (n : ℤ) + 1 := ((wDecSet_def c t u).mp hstepS).1
        have h4 : i + (n : ℤ) + 1 ≤ wHi c t u x := ((wDecSet_def c t u).mp hstepS).2
        refine (wDecSet_def c t u).mpr ⟨?_, ?_⟩
        · show wLo c t u x ≤ i + (n : ℤ)
          omega
        · show i + (n : ℤ) ≤ wHi c t u x
          omega
      have ih' := ih (fun s hs => hm s (Nat.lt_succ_of_lt hs))
      calc (HNNExtension.t : wK c t u hFw hc hA hB) ^ ((n + 1 : ℕ) : ℤ) *
              HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((x, i) : WgtBeta t))) *
              (HNNExtension.t : wK c t u hFw hc hA hB) ^ (-(((n + 1 : ℕ)) : ℤ))
          = (HNNExtension.t : wK c t u hFw hc hA hB) *
              ((HNNExtension.t : wK c t u hFw hc hA hB) ^ ((n : ℕ) : ℤ) *
                HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((x, i) : WgtBeta t))) *
                (HNNExtension.t : wK c t u hFw hc hA hB) ^ (-((n : ℕ) : ℤ))) *
              (HNNExtension.t : wK c t u hFw hc hA hB)⁻¹ := by
            rw [Nat.cast_succ]; group
        _ = (HNNExtension.t : wK c t u hFw hc hA hB) *
              HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((x, i + (n : ℤ)) : WgtBeta t))) *
              (HNNExtension.t : wK c t u hFw hc hA hB)⁻¹ := by rw [ih']
        _ = HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((x, i + (n : ℤ) + 1) : WgtBeta t))) := by
              rw [wgtPhiChain_shift_step hFw hc hA hB ((x, i + (n : ℤ)) : WgtBeta t) hmid hstepS]
        _ = HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((x, i + ((n + 1 : ℕ) : ℤ)) : WgtBeta t))) := by
              have hii : (i + ((n + 1 : ℕ) : ℤ)) = i + (n : ℤ) + 1 := by push_cast; ring
              rw [hii]

theorem wgtPhiChain {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : Work.OROneRel.FreiheitssatzAt (Work.OROneRel.wW c t u))
    (hc : Work.OROneRel.IsCyclicallyReducedRelator (Work.OROneRel.wW c t u))
    (hA : Work.OROneRel.wW c t u ∉ Subgroup.closure (FreeGroup.of '' Work.OROneRel.wTA c t u))
    (hB : Work.OROneRel.wW c t u ∉ Subgroup.closure (FreeGroup.of '' Work.OROneRel.wTB c t u)) :
    (∀ (p : Work.OROneRel.wBeta c t u) (hy : PresentedGroup.of p ∈ Work.OROneRel.wA c t u)
        (hp : p ∈ Work.OROneRel.wTA c t u),
        ((Work.OROneRel.wPhi hFw hc hA hB ⟨PresentedGroup.of p, hy⟩ : Work.OROneRel.wB c t u)
            : Work.OROneRel.wH c t u)
          = PresentedGroup.of (Work.OROneRel.wBetaOf c t u ((p.1.1, p.1.2 + 1) : Work.OROneRel.WgtBeta t))) ∧
      (∀ e : Work.OROneRel.wTA c t u,
        Work.OROneRel.wPhi hFw hc hA hB (Work.OROneRel.wGA e)
          = Work.OROneRel.wGB (Work.OROneRel.wTshift c t u e)) ∧
      (∀ (p : Work.OROneRel.wBeta c t u) (hp : p ∈ Work.OROneRel.wTA c t u),
        HNNExtension.of (PresentedGroup.of (Work.OROneRel.wBetaOf c t u ((p.1.1, p.1.2 + 1) : Work.OROneRel.WgtBeta t)))
          = (HNNExtension.t : Work.OROneRel.wK c t u hFw hc hA hB) *
              HNNExtension.of (PresentedGroup.of p) *
              (HNNExtension.t : Work.OROneRel.wK c t u hFw hc hA hB)⁻¹) ∧
      (∀ (x : {x : α // x ≠ t}) (i : ℤ) (hi : ((x, i) : Work.OROneRel.WgtBeta t) ∈ Work.OROneRel.wDecSet c t u),
        ∀ (m : ℕ), (∀ s : ℕ, s < m → ((x, i + s + 1) : Work.OROneRel.WgtBeta t) ∈ Work.OROneRel.wDecSet c t u) →
          (HNNExtension.t : Work.OROneRel.wK c t u hFw hc hA hB) ^ (m : ℤ) *
              HNNExtension.of (PresentedGroup.of (Work.OROneRel.wBetaOf c t u ((x, i) : Work.OROneRel.WgtBeta t))) *
              (HNNExtension.t : Work.OROneRel.wK c t u hFw hc hA hB) ^ (-(m : ℤ))
            = HNNExtension.of (PresentedGroup.of (Work.OROneRel.wBetaOf c t u ((x, i + m) : Work.OROneRel.WgtBeta t)))) :=
  ⟨fun p hy hp => wgtPhiChain_phi_gen hFw hc hA hB p hy hp,
    fun e => wgtPhiChain_phi_wGA hFw hc hA hB e,
    fun p hp => wgtPhiChain_hnn hFw hc hA hB p hp,
    wgtPhiChain_chain hFw hc hA hB⟩

end Work.OROneRel
