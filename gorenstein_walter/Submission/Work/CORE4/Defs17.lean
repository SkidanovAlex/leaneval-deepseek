/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — design pass 17, item A4c2: the `U = F · I_U(s)` input

The `A4c` prover's refutation of design 15's finish was **withdrawn** (lead ruling, 2026-10-07):
its step "`e ∈ Ĥ^e` because `e = e·1·e⁻¹`" is wrong (that product is `1`, not `e`; with either
convention for `conjSub`, `e ∈ Ĥ^e` holds iff `e ∈ Ĥ`, and design 15's `Ĥ^e ≠ Ĥ` forces
`e ∉ Ĥ`).  So `X = U ⊓ U^e` is *not* automatically moved by `e`, and nothing refutes `X ⊴ Ĥ^e`.

What the prover did identify correctly is the *second* point: design 15's A4c step 1 uses
`U = F · I_U(s)` **as sets** (to conclude `K' ≤ C_G(U)` from `K' ≤ C_G(F) ∩ C_G(I)`).  That is
not among `A4c`'s hypotheses, although it *is* a fact of the `Case2InvNormal` branch: it comes from
Bender 1.5's cardinality clause `|I_U(s)| · |C_U(s)| = |U|` together with `C_U(s) = B₀ = F` (the now
proved `Work.CORE4.Case2CU_s`) and `F ∩ I_U(s) = 1`.  `A4a`'s proof already establishes it
internally (`Work.CORE4.A4aAux.U_eq_F_sup_invSet`).

Accordingly (lead ruling, points 2–3):

* `A4a2Prop` — `A4a`'s conclusion **and** the export `(U : Set G) = F * I_U(s)`;
* `A4c2Prop` — `A4c`'s hypotheses plus that export, concluding `False`;
* `invNormalFrom_of_parts2` — the assembly, **proved here**;
* the rest of design 15 (`A4i`, `A4a`, `A4s`, `A4b`) is unchanged.
-/
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.NotA7Defs

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

open Pointwise

namespace C15

/-- **A4a2.**  In the exceptional case `I_U(s) ⊴ Ĥ`: `K = Z(U)`, and additionally the export
`U = F · I_U(s)` as sets, which `A4a`'s proof uses but does not hand on.

(The export is Bender 1.5's `|I_U(s)| · |C_U(s)| = |U|` with `C_U(s) = B₀ = F`
(`Work.CORE4.Case2CU_s`) and `F ∩ I_U(s) = 1`; `Work.CORE4.A4aAux.U_eq_F_sup_invSet` is the
proved auxiliary the current `A4a` proof invokes.) -/
def A4a2Prop (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7UData B C.D →
      Case2InvNormal B C.D →
        C.D.K = (center ↥B.U).map B.U.subtype ∧
        (B.U : Set G) = (C.D.F : Set G) * (invSet B.U C.D.s)

/-- **A4c2.**  `A4c` with the `U = F · I_U(s)` export added as a hypothesis (lead ruling on
`NOTES_TO_LEAD.md` §14; the refutation of the design-15 finish was withdrawn).

Route (design pass 15 §1.3, A4c, with the export available):
1. `K'` centralizes `I := I_U(s)` (A4i: `K' ≤ Ĥ` normalizes `I ⊴ Ĥ`) and `F` (`F ≤ C(E)`), hence
   `K' ≤ C_G(U)` using `U = F · I`;
2. `N_G(K) = Ĥ` (`K = Z(U)` characteristic in `U = O(Ĥ) ⊴ Ĥ`, `Ĥ` a coatom, `G` simple), so
   `U ≤ C(K') ≤ N(K') = Ĥ^e`; and `Ĥ^e ≠ Ĥ` (else `U^e = U` and `K' = Z(U^e) = K`);
3. `K' ⊄ U` (else `K' ⊆ invSet (U ⊓ M) s = K`); `s ∉ V U` and `s ∉ V^e U^e`; `|Ĥ : V U| = 6`
   (`I.thm26`, second case, as `V = O₂(Ĥ)` is a four-group);
4. `T := U U^e` is a 3-subgroup of `Ĥ^e`, so `|T| ≤ 3|U|`; hence `|U : X| ≤ 3`, `U ⊴ T`,
   `U^e ≤ N(U) = Ĥ`, and `|X| ≥ |U|/3 ≥ 3` (as `|U| ≥ |K F| = 9`);
5. `N_Ĥ(X) ⊇ V U, K', s` and `N_{Ĥ^e}(X) ⊇ V^e U^e, U, s`, whence `X ⊴ Ĥ` and `X ⊴ Ĥ^e`
   (both indices divide `|Ĥ : VU| = 6` and are divisible by 2 and 3);
6. `X ⊴ ⟨Ĥ, Ĥ^e⟩ = G` with `1 ≠ X ≤ U < G`, contradicting `BenderCtx.simple`. -/
def A4c2Prop (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G) (C : Case2Ctx6 B),
    Hyp9 G B C → IsA7Case C.D → A7Facts1 C.D → A7Facts2 B C.D → A7UData B C.D →
      Case2InvNormal B C.D → C.D.K = (center ↥B.U).map B.U.subtype →
      (B.U : Set G) = (C.D.F : Set G) * (invSet B.U C.D.s) →
      ∀ e ∈ layerIn C.D.M, e * C.D.s = C.D.s * e → conjSub e C.D.K ≤ B.Hhat →
        conjSub e C.D.K ≠ C.D.K → Inverts C.D.s (conjSub e C.D.K) → False

/-- Assembly of the corrected `A4` from `A4a2`, `A4s`, `A4b`, `A4c2` (no cycle). -/
theorem invNormalFrom_of_parts2 (I : C4Inputs) (ha : A4a2Prop I) (hs : A7S4ConjProp)
    (hb : A4bProp I) (hc : A4c2Prop I) : A7InvNormalFromProp I := by
  intro G _ _ B C h9 hA f1 f2 hU hInv
  obtain ⟨hKZ, hUFI⟩ := ha G B C h9 hA f1 f2 hU hInv
  obtain ⟨e, he, hes, heH, hne, hinv⟩ := hb hs G B C h9 hA f1 f2 hU
  exact hc G B C h9 hA f1 f2 hU hInv hKZ hUFI e he hes heH hne hinv

/-- `A4a2` gives the old `A4a` (drop the export). -/
theorem A4aProp_of_A4a2 (I : C4Inputs) (h : A4a2Prop I) : A4aProp I :=
  fun G _ _ B C h9 hA f1 f2 hU hInv => (h G B C h9 hA f1 f2 hU hInv).1

end C15

end Work.CORE4
