/-
Area BG (Bender–Glauberman 1981): the **wave-5 assemblies** of design pass 16
(`NOTES_LEAD_gw_design16.md` §5, wave 5).  These are the three Prop-valued implications that
turn the character-theoretic leaves into the contract-level Props `KeySmallProp`,
`ThmCBigProp`, `ThmCSmallProp` of `ThmABCDefs.lean`.

Style: the same as `KeyBigAsmProp` of `ThmABCCharDefs.lean` — the leaves are taken as
hypotheses, bundled as a function `(G) (…instances) (D) (C) (K1 K2) ↦ …`, and the conclusion
is the contract Prop itself (restated inline here since the design files do not import each
other; this file *does* import `ThmABCDefs`, so the names resolve — the inline restatements of
`KeyBigAsmProp` are not repeated).

Design routes (`NOTES_LEAD_gw_design16.md` §2, §4):

* `KeySmallAsmProp` (`|S| = 4`): S4-DEC gives `(1 - λ₂)* = 1_G + φ₁ + φ₂ + φ₃` with
  `φᵢ(t) = 1` and odd degrees; `t ∈ G'` (`TDerivedProp`) rules out `φᵢ(1) = -1`; Lemma 2.2 at
  `κ = λ₁`, `β = β₂` and X1 give `2k²/N = 1 + Σ 1/φᵢ(1)`, and `δ(1) = 0` gives
  `1 + φ₁(1) + φ₂(1) + φ₃(1) = 0`.
* `ThmCBigAsmProp` (`|S| ≥ 8`): G6, G8, κ exists (C3-0), DEC-BIG, C3-1 … C3-4 and AR-C3.
* `ThmCSmallAsmProp` (`|S| = 4`): G6, G7, G8, κ exists (C4-0), C4-ID, C4-VAL, C4-DEG, S4-DEC,
  AR-C4 and AR-C4b.
-/
import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs

namespace Work.GW2.C16

open OddOrder.RepresentationTheory Work.GW2 Work.BG Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 1. `|S| = 4`: KEY-SMALL -/

/-- **KEYSMALL-ASM.** S4-DEC + Lemma 2.2 (`κ = λ₁`, `β = β₂`) + X1 + G5 (`k₁ = k₂`) + G10
(`t ∈ G'`) + I-1 give KEY-SMALL. -/
def KeySmallAsmProp : Prop :=
  BridgeProp → ConstituentSumProp →
  (∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)],
      Coherence23Prop C ∧ IndDiffProp C ∧ S4DecompProp D C ∧ Lemma22KappaProp D C) →
  KEqSmallProp → TDerivedProp → KeySmallProp

/-! ## 2. `|S| ≥ 8`: Theorem C -/

/-- The `|S| ≥ 8` bundle of character-theoretic leaves consumed by `ThmCBigAsmProp`, bundled
as a function of `(G, D, C, K1, K2)`. -/
abbrev C3Bundle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] (K1 K2 : Subgroup G),
      Compat D C → ThmCHyps D K1 K2 →
      Coherence23Prop C ∧ IndDiffProp C ∧ DecompBigProp D C ∧ KappaExistsProp D C ∧
      Lemma22KappaProp D C ∧ C3IdentityProp D C ∧
      C3BoundsProp D C K1 K2 ∧ C3NotThreeProp D C K1 K2 ∧ C3DegreeProp D C K1 K2

/-- **THMCBIG-ASM.** G6 (`ThmCSec3Prop`), G8 (`KNeOneProp`), C3-0 (`KappaExistsProp`),
DEC-BIG, Lemma 2.2 (needed for the `2k²/N > 1 - 3/|φ(1)|` input of AR-C3), C3-1 … C3-4 and
AR-C3 give `ThmCBigProp`. -/
def ThmCBigAsmProp : Prop :=
  BridgeProp → ConstituentSumProp → ThmCSec3Prop → KNeOneProp → ArithC3Prop →
  C3Bundle → ThmCBigProp

/-! ## 3. `|S| = 4`: Theorem C -/

/-- The `|S| = 4` bundle of character-theoretic leaves consumed by `ThmCSmallAsmProp`, bundled
as a function of `(G, D, C, K1, K2)`.

It carries `Lemma22KappaProp D C`, `IndDiffProp C`, `S4DecompProp D C`, `ConstituentSumProp`
and `KEqSmallProp`: these are what produce the **second** Lemma 2.2 identity
`2k²/N = 1 + Σ 1/φⱼ(1)` (equation (1) of BG p. 215), which AR-C4 compares with C4-ID's
equation (2).  Without it the case "all `χᵢ(t) = 1`" of C4-VAL cannot be contradicted (this was
caught in review). -/
abbrev C4Bundle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] (K1 K2 : Subgroup G),
      Compat D C → ThmCHyps D K1 K2 →
      Coherence23Prop C ∧ IndDiffProp C ∧ KappaExistsProp D C ∧ Lemma22KappaProp D C ∧
      C4IdentityProp D C ∧ C4ValuesProp D C K1 K2 ∧
      C4DegreeProp D C K1 K2 ∧ S4DecompProp D C

/-- **THMCSMALL-ASM.** G6 (`ThmCSec3Prop`), G7 (`ThmCSmallShapeProp`), G8 (`KNeOneProp`),
C4-0 (`KappaExistsProp`), C4-ID, C4-VAL, C4-DEG, S4-DEC, AR-C4 and AR-C4b give
`ThmCSmallProp`. -/
def ThmCSmallAsmProp : Prop :=
  BridgeProp → ConstituentSumProp → ThmCSec3Prop → ThmCSmallShapeProp → KNeOneProp →
  ArithC4Prop → ArithC4bProp → KEqSmallProp →
  C4Bundle → ThmCSmallProp

end Work.GW2.C16
