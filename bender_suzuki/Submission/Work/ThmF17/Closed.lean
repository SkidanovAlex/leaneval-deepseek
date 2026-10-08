import Submission.Work.ThmF17.ThmF17
import Submission.Work.ThmF17.AppXI.Defs
import Submission.Work.Step7Comm.sig_inf_centralizer_CQ_eq_bot_of_comm
import Submission.Work.AppXIField.Main.nearFieldFieldPropNI_of
import Submission.Work.AppXIDickson.AppXI2
import Submission.Work.AppXIShadow.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF17.Closed` — `thmF_appXI_closed`, the App. XI inputs produced

`Work.ThmF17.ThmF17` proves Théorème F from the *named* App. XI inputs

* `NearFieldAppXIProp` (App. XI Prop. 1, the near-field shadow),
* `AppXIProp2` (App. XI Prop. 2: a non-abelian `C_Q(P)` has order `8`),
* `NearFieldFieldProp` (App. XI Prop. 1 (2)b, the field/Galois shadow),
* `HigmanProp`,

together with the §3 chain.  This module is the *assembly point*: it produces those inputs from
the App. XI areas and calls `ThmF17`, so that the caller of Théorème F no longer has to supply
them.

## What is produced, and by whom

| producer | area (BS pass 17 brief) | status |
|---|---|---|
| `Work.AppXIShadow.nearFieldAppXIPropPlus_of` (App. III (2) + Prop. 1) | `AppXIShadow` (Brief 3) | **wired in** (axiom-clean) |
| `Work.AppXIField.nearFieldFieldPropNI_of` (Prop. 1 (2)b) | `AppXIField` (Brief 4) | **wired in** (axiom-clean) |
| `Work.Step7Comm.sig_inf_centralizer_CQ_eq_bot_of_comm` (step (7)) | `Step7Comm` (Brief 5) | **wired in** (axiom-clean) |
| `Work.AppXIDickson.appXIProp2_of` (Prop. 2) | `AppXIDickson` (Brief 6) | **wired in** (axiom-clean) |

Two extra steps of glue live here (they are the *consumer's* business, not any leaf owner's):

* `NearFieldFieldPropNI` (Prop. 1 (2)b without the injectivity clause, which is not an App. XI
  fact but step (7), BS pass 17 item D5) plus `sig_inf_centralizer_CQ_eq_bot_of_comm` rebuild the
  full `NearFieldFieldProp` — this is `nearFieldFieldProp_of`;
* the shadow `NearFieldAppXIProp` is `NearFieldAppXIPropPlus.toShadow`.

The four areas each keep their own copy of the `Prop`s; all of them are *definitionally* the
`Work.ThmF17.AppXI.*` copies of the design (`rfl`-checked in `AppXI/_bridge_probe.lean`), so the
wiring is by `defeq`.

## Main declarations

* `Work.ThmF17.thmF_appXI_closed_of` — the interface: the three App. XI `Prop`s as hypotheses;
* `Work.ThmF17.nearFieldFieldProp_of` — the step-(7) glue (Prop. 1 (2)b + step (7) ⟹ Prop. 1 (2)b);
* `Work.ThmF17.thmF_appXI_closed_of_producers` — Théorème F with App. XI Prop. 2 and Prop. 1 (2)b
  *produced* (only `hNFp : NearFieldAppXIPropPlus` is left as an App. XI hypothesis);
* **`Work.ThmF17.thmF_appXI_closed`** — the same with `hNFp` produced by
  `Work.AppXIShadow.nearFieldAppXIPropPlus_of`: Théorème F with **every** App. XI input produced
  (BS pass 17 Brief 2 item 2).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section
open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF17

open Work.ThmF.ChV3 Work.ThmF

/-- **Théorème F, with the App. XI inputs as hypotheses in their reduced form.**

This is the interface the App. XI areas plug into: given

* `hNFp : NearFieldAppXIPropPlus` (App. III (2) + App. XI Prop. 1 without the exponent clause),
* `hXI2 : AppXIProp2` (App. XI Prop. 2),
* `hNFF : NearFieldFieldProp` (App. XI Prop. 1 (2)b),

Théorème F holds from `hFT hC4 hTh hW hHW hA hHig`.  (`NearFieldExpProp` is not needed: it is a
consequence of the chain, `Work.ThmF17.exp_of_chain`.) -/
theorem thmF_appXI_closed_of (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (hTh : ThompsonFrobeniusProp) (hW : Work.ThmF.WielandtFixedPoint)
    (hHW : Work.ThmF.HallWielandtProp) (hA : Work.ThmF.ArithmeticNineTwoSeven)
    (hHig : HigmanProp) (hBrSz : BrauerSuzukiProp)
    (hNFp : AppXI.NearFieldAppXIPropPlus) (hXI2 : AppXIProp2)
    (hNFF : NearFieldFieldProp) : ThmFProp :=
  ThmF17 hFT hC4 hTh hW hHW hA hNFp.toShadow hXI2 hNFF hHig

/-! ## The step-(7) glue: rebuilding `NearFieldFieldProp` -/

/-- **`NearFieldFieldProp` from `NearFieldFieldPropNI`** (App. XI Prop. 1 (2)b without the
injectivity clause) **and the step-(7) crux** `Σ ⊓ C_G(C_Q(P)) = 1`.

The injectivity of `act : Σ →* Aut F` is *not* an App. XI fact (BS pass 17 item D5): if
`1 ≠ w ∈ Σ` lay in its kernel, then `w` would fix every element of `F`, so by the fixed-point
clause `|C_Q(P)| ≤ |C_Q(P) ⊓ C_G(w)|`, i.e. `w` centralises `C_Q(P)` and `w ∈ Σ ⊓ C_G(C_Q(P))`,
which is trivial by `Work.Step7Comm.sig_inf_centralizer_CQ_eq_bot_of_comm`. -/
theorem nearFieldFieldProp_of (hFT : FeitThompsonProp) (hW : Work.ThmF.WielandtFixedPoint)
    (hTh : ThompsonFrobeniusProp) (hNF : NearFieldAppXIProp) (hXI2 : AppXIProp2)
    (hC4 : ChIIFourProp) (hA : Work.ThmF.ArithmeticNineTwoSeven)
    (hNI : AppXI.NearFieldFieldPropNI) : NearFieldFieldProp := by
  intro G _ _ H Q t s r P m c hm hcq hcomm
  obtain ⟨h15⟩ := chain15 hFT hW hTh hNF hXI2 hC4 c
  have hnil : Group.IsNilpotent ↥Q :=
    Work.ThmF.ChV12.prop1b c.sit hC4 hTh H Q t c.split (CtxF.Kset_nontrivial c)
  have hbot :=
    Work.Step7Comm.sig_inf_centralizer_CQ_eq_bot_of_comm hA hFT hC4 hnil c h15 hcomm
  obtain ⟨F, hF, hFt, hch, hfa, act, hcard, hfix⟩ := hNI c hm hcq hcomm
  refine ⟨F, hF, hFt, hch, hfa, act, hcard, ?_, hfix⟩
  rw [injective_iff_map_eq_one]
  intro w hw1
  by_contra hne
  have hall : Nat.card (Function.fixedPoints (act w)) = Nat.card F := by
    have : Function.fixedPoints (act w) = Set.univ := by
      ext k
      simp [Function.mem_fixedPoints, Function.IsFixedPt, hw1]
    rw [this, Nat.card_univ]
  have hle : Nat.card ↥(CQ Q P) ≤
      Nat.card ↥(CQ Q P ⊓ Subgroup.centralizer ({(w : G)} : Set G)) := by
    have h1 := hfix w hne
    rw [hall, hcard, ← hcq] at h1
    omega
  have hEq : CQ Q P ⊓ Subgroup.centralizer ({(w : G)} : Set G) = CQ Q P :=
    Subgroup.eq_of_le_of_card_ge inf_le_left hle
  have hwC : (w : G) ∈ Sig H t P ⊓ Subgroup.centralizer ((CQ Q P : Subgroup G) : Set G) := by
    refine ⟨w.2, ?_⟩
    show (w : G) ∈ Subgroup.centralizer ((CQ Q P : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ CQ Q P ⊓ Subgroup.centralizer ({(w : G)} : Set G) := by rw [hEq]; exact hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hy'.2)
  rw [hbot] at hwC
  exact hne (Subtype.ext (Subgroup.mem_bot.mp hwC))

/-! ## The producers wired in -/

/-- **Théorème F from App. XI Prop. 1 alone**: App. XI Prop. 2 (`Work.AppXIDickson.appXIProp2_of`)
and App. XI Prop. 1 (2)b + step (7) (`Work.AppXIField.nearFieldFieldPropNI_of` +
`Work.Step7Comm.sig_inf_centralizer_CQ_eq_bot_of_comm`, through `nearFieldFieldProp_of`) are
produced here, so the only remaining App. XI input is `hNFp : NearFieldAppXIPropPlus` (App. III (2)
+ App. XI Prop. 1), which `Work.AppXIShadow.nearFieldAppXIPropPlus_of` supplies. -/
theorem thmF_appXI_closed_of_producers (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (hTh : ThompsonFrobeniusProp) (hW : Work.ThmF.WielandtFixedPoint)
    (hHW : Work.ThmF.HallWielandtProp) (hA : Work.ThmF.ArithmeticNineTwoSeven)
    (hHig : HigmanProp) (hBrSz : BrauerSuzukiProp)
    (hNFp : AppXI.NearFieldAppXIPropPlus) : ThmFProp :=
  have hXI2 : AppXIProp2 := Work.AppXIDickson.appXIProp2_of hNFp hFT hC4 hTh hHig
  have hNFF : NearFieldFieldProp :=
    nearFieldFieldProp_of hFT hW hTh hNFp.toShadow hXI2 hC4 hA
      (Work.AppXIField.nearFieldFieldPropNI_of hNFp)
  thmF_appXI_closed_of hFT hC4 hTh hW hHW hA hHig hBrSz hNFp hXI2 hNFF

-- **The final form** — Théorème F with *every* App. XI input produced (BS pass 17 Brief 2 item 2).

/-- **Théorème F with every App. XI input produced**: App. XI Prop. 1 (App. III (2) +
`NearFieldAppXIPropPlus`, `Work.AppXIShadow.nearFieldAppXIPropPlus_of`), App. XI Prop. 2
(`Work.AppXIDickson.appXIProp2_of`) and App. XI Prop. 1 (2)b
(`Work.AppXIField.nearFieldFieldPropNI_of` + step (7) `Work.Step7Comm...`, through
`nearFieldFieldProp_of`).  Only `hFT` (Feit–Thompson), `hC4` (Ch. II §4), `hTh`
(Thompson–Frobenius), `hW` (Wielandt's fixed-point formula), `hHW` (Hall–Wielandt — *false at*
`p = 2`, audit D2; use `Work.ThmF17.thmF17_appXI_odd_closed` in `OddForm.lean` instead), `hA`
(HB IX 2-7) and `hHig` (Higman) remain as hypotheses. -/
theorem thmF_appXI_closed (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (hTh : ThompsonFrobeniusProp) (hW : Work.ThmF.WielandtFixedPoint)
    (hHW : Work.ThmF.HallWielandtProp) (hA : Work.ThmF.ArithmeticNineTwoSeven)
    (hHig : HigmanProp) (hBrSz : BrauerSuzukiProp) : ThmFProp :=
  thmF_appXI_closed_of_producers hFT hC4 hTh hW hHW hA hHig hBrSz
    (Work.AppXIShadow.nearFieldAppXIPropPlus_of hFT hBrSz hC4 hTh)

end Work.ThmF17

#print axioms Work.ThmF17.thmF_appXI_closed_of
#print axioms Work.ThmF17.nearFieldFieldProp_of
#print axioms Work.ThmF17.thmF_appXI_closed_of_producers
#print axioms Work.ThmF17.thmF_appXI_closed
