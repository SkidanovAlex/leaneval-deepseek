/-
Area `A7REC`: the assembly of the amended (design-pass-4) contract.

The deliverable of the area is `Work.A7REC.A7Rec2Prop`, routed through

* **C1** `A7Char6Prop` — the degree-`6` representation with trace `2` at `z`, `3` on `U#` and
  `-1` at elements of order `7` (Suzuki 1959 §8; the sub-leaves are listed in
  `NOTES_LEAVES.md`);
* **C2+C3** `A7IndexSevenFromCharProp` — the fixed-vector argument producing a subgroup of
  index `7`;

and the already proved `IndexSeven.lean` (`index 7 ⟹ G ≃* A₇`).

Nothing in this file is character theory: it is the (elementary) assembly.  The two Props take the
character theory as hypotheses, which is exactly the interface the lead's design pass 4 asks for.
-/
import Submission.Work.A7REC.IndexSeven
import Submission.Work.A7REC.Reduction

namespace Work.A7REC

open Subgroup

/-- The hypothesis bundle `A7RecHyps` is the field list of the structure `A7RecCtx`. -/
def A7RecCtx.ofHyps {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G} {U V : Subgroup G}
    (h : A7RecHyps G S z U V) : A7RecCtx G where
  simple := h.1
  hcard := h.2.1
  S := S
  hSdih := h.2.2.1
  z := z
  hzS := h.2.2.2.1
  hz2 := h.2.2.2.2.1
  hzcen := h.2.2.2.2.2.1
  U := U
  hCz := h.2.2.2.2.2.2.1
  hUcard := h.2.2.2.2.2.2.2.1
  hUnorm := h.2.2.2.2.2.2.2.2.1
  V := V
  hVdef := h.2.2.2.2.2.2.2.2.2.1
  hV4 := h.2.2.2.2.2.2.2.2.2.2.1
  hcross := h.2.2.2.2.2.2.2.2.2.2.2.1
  hNUV := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  hNUcard := h.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The residual `A7IndexSevenProp` (its older, character-free form) implies the amended
residual `A7IndexSevenFromCharProp`. -/
theorem A7IndexSevenFromCharProp_of_A7IndexSevenProp (h : A7IndexSevenProp) :
    A7IndexSevenFromCharProp := by
  intro G _ _ S z U V hyps _hsmall _hchar
  exact h G (A7RecCtx.ofHyps hyps)

/-- **The assembly of the amended contract.**  C1 and C2+C3 give `A7Rec2Prop`: the degree-`6`
representation plus the stabilizer argument produce a subgroup of index `7`, and the coset
action identifies `G` with `A₇`. -/
theorem a7Rec2Prop_of_char6_and_indexSeven (hC1 : A7Char6Prop)
    (hC23 : A7IndexSevenFromCharProp) : A7Rec2Prop := by
  intro G _ _ S z U V hyps hsmall
  have hsimple : IsSimpleGroup G := hyps.1
  have hcard : Nat.card G = 2520 := hyps.2.1
  haveI : IsSimpleGroup G := hsimple
  obtain ⟨H, hH⟩ := hC23 G S z U V hyps hsmall (hC1 G S z U V hyps)
  exact mulEquiv_A7_of_index_seven G hcard H hH

/-- `A7RecProp` is implied by the amended `A7Rec2Prop`, provided the induction premise
`SmallerDGroups` is available for every group. -/
theorem a7RecProp_of_A7Rec2Prop (h : A7Rec2Prop)
    (hsmall : ∀ (G : Type) [Group G] [Finite G], SmallerDGroups G) : A7RecProp := by
  intro G _ _ hsimple hcard S hSdih z U V hzS hz2 hzcen hCz hUcard hUnorm hVdef hV4 hcross hNUV
    hNUcard
  exact h G S z U V ⟨hsimple, hcard, hSdih, hzS, hz2, hzcen, hCz, hUcard, hUnorm, hVdef, hV4,
    hcross, hNUV, hNUcard⟩ (hsmall G)

end Work.A7REC
