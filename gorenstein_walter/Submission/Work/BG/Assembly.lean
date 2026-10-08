/-
Area BG (Bender–Glauberman 1981): **the final assembly** to the contract Props
`Work.GW2.BGThmAProp`, `Work.GW2.BGThmBProp`, `Work.GW2.BGThmCProp` (`GLUE/Defs.lean`).

Nothing is re-proved here: every theorem applies a *proved* assembly
(`ThmABCDefs.thmA_of_leaves` / `thmB_of_leaves` / `thmC_of_leaves`, `ThmABCCharDefs.keyBigAsm`,
`Assemblies.keySmallAsm` / `thmCBigAsm` / `thmCSmallAsm`, `Work.BG.kNeOne_of_thmB` from design
pass 26) to an explicit list of leaves.  Leaves that are still open are **named hypotheses**, so
the exact open-leaf list is in the signatures.

`CentralizerSplitProp` is *not* a parameter: the area proves it itself
(`Work.BG.SplitGlue.centralizerSplitProp`, module `BG/splitglue/Split.lean`), which also avoids
the `FUS.Split`/`ASM.Defs` duplicate-declaration clash (`Work.GW2.BenderSetup.ctorIdx`).

Open leaves (2026-10-08):

| hypothesis | leaf | status |
|---|---|---|
| `hcoh : CohAll` | BG Coherence Theorem 2.3 | **PROVED** (`coherenceAll`) |
| `hS4 : S4All` | S4-DEC (BG §4 end) | **PROVED** (`s4All`, `BG/s4Decomp`) |
| `hD : DecompAll` | DEC-BIG (Lemma 2.5, front half) | **CLOSED** (`Work.BG.decompAll`, from `BG/decompBig`; `#print axioms` clean) |
| `hc3id : C3IdAll` | C3-1 | **CLOSED** by `Work.BG.c3IdAll` (`BG/c3Identity`, clean) |
| `hc3nt : C3NtAll` | C3-3 | **OPEN**: `BG/c3NotThree` is written on `BG/c3Sfixed2` + `BG/c3DegEq2`, but `BG/c3Sfixed2` uses `BG/c3ExcLarge`, which two reviews judge false as stated (`D.n = 8` branch) — see `NOTES_c3ExcLarge_issue.md` |
| `hc3deg : C3DegAll` | C3-4 | **still open**: `BG/c3Degree`, route `C24.lemma36_thmC` + `BG/kInvNormal` + the Lemma 3.6 leaf (`BG/lemma36C` dispatched) |
| `hc4id : C4IdAll` | C4-ID | **CLOSED** by `Work.BG.c4IdAll` (`BG/c4Identity`, clean) |
| `hc4val : C4ValAll` | C4-VAL | **CLOSED** by `Work.BG.c4ValAll` (`BG/c4Values`, clean) |
| `hc4deg : C4DegAll` | C4-DEG | **CLOSED** by `Work.BG.c4DegAll` (`BG/c4DegreeB`, clean) |

G8 is *no longer* a leaf: `Work.BG.kNeOne_of_thmB` (design 26, `BG/kNeOne.lean`) derives
`KNeOneProp` from `BGThmBProp` and `CentralizerSplitProp`, so `bgThmC_of` takes no `hk`.
-/
import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.Assemblies
import Submission.Work.BG.keyBigAsm
import Submission.Work.BG.keySmallAsm
import Submission.Work.BG.thmCBigAsm
import Submission.Work.BG.thmCSmallAsm
import Submission.Work.BG.kNeOne
import Submission.Work.BG.kappaExists
import Submission.Work.BG.c3Bounds
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.thmCSmallShape
import Submission.Work.BG.arithC3
import Submission.Work.BG.arithC4
import Submission.Work.BG.arithC4b
import Submission.Work.BG.bridge
import Submission.Work.BG.constituentSum
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.lemma22Kappa
import Submission.Work.BG.subBGData
import Submission.Work.BG.strongEmbed
import Submission.Work.BG.nCases
import Submission.Work.BG.indexOdd
import Submission.Work.BG.fourDvdK
import Submission.Work.BG.arithBig
import Submission.Work.BG.arithSmall
import Submission.Work.BG.kEqSmall
import Submission.Work.BG.tDerived
import Submission.Work.BG.s02_orbitCoherence
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_assemblyFull
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_bsValueT
import Submission.Work.BG.s4Decomp
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.c4DegreeB
import Submission.Work.BG.decompBig
import Submission.Work.BG.c3Identity
import Submission.Work.BG.c4Values
import Submission.Work.BG.c4Identity
import Submission.Work.BG.c3NotThree

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

/-! ## 0. The leaf hypotheses, as abbreviations -/

/-- BG Coherence Theorem 2.3 for every §2 context. -/
abbrev CohAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)], Coherence23Prop C

/-- S4-DEC for every §2 context. -/
abbrev S4All : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)], S4DecompProp D C

/-- DEC-BIG (front half of Lemma 2.5) for every §2 context. -/
abbrev DecompAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)], DecompBigProp D C

/-- C3-1 for every §2 context. -/
abbrev C3IdAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)], C3IdentityProp D C

/-- C3-3 for every §2 context. -/
abbrev C3NtAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] (K1 K2 : Subgroup G),
    C3NotThreeProp D C K1 K2

/-- C3-4 for every §2 context. -/
abbrev C3DegAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] (K1 K2 : Subgroup G),
    C3DegreeProp D C K1 K2

/-- C4-ID for every §2 context. -/
abbrev C4IdAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)], C4IdentityProp D C

/-- C4-VAL for every §2 context. -/
abbrev C4ValAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] (K1 K2 : Subgroup G),
    C4ValuesProp D C K1 K2

/-- C4-DEG for every §2 context. -/
abbrev C4DegAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] (K1 K2 : Subgroup G),
    C4DegreeProp D C K1 K2

/-! ## 1. The bridge (the splitting is proved in this area) -/

/-- `CentralizerSplitProp` is proved in the area (`BG/splitglue/Split.lean`). -/
theorem centralizerSplit : CentralizerSplitProp := SplitGlue.centralizerSplitProp

/-- `BridgeProp` (G1): a compatible `Sec2Ctx` for every `BGData`. -/
theorem bridgeProp : BridgeProp := bridge centralizerSplit

/-! ## 2. The Coherence Theorem 2.3 and S4-DEC (both PROVED) -/

/-- `Coherence23CoreProp` (A-1) from the per-orbit form. -/
theorem coherence23Core {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Coherence23CoreProp C :=
  s02_assemblyCore C (sconjLam C) (s02_orbitCoherence C)

/-- **BG Coherence Theorem 2.3** (A-2 applied to I-2 and I-3′). -/
theorem coherenceAll : CohAll :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] =>
    s02_assemblyFull C (s02_gram C) (s02_bsValueT C) (coherence23Core C)

/-- **S4-DEC** for every §2 context. -/
theorem s4All : S4All :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] =>
    s4Decomp D C

/-! ## 3. KEY-BIG and KEY-SMALL -/

/-- The bundle consumed by `keyBigAsm`. -/
theorem keyBigBundle (hcoh : CohAll) (hD : DecompAll) :
    ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)],
      Coherence23Prop C ∧ IndDiffProp C ∧ DecompBigProp D C ∧ Lemma22KappaProp D C :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)] =>
    ⟨hcoh G C, s02_indDiff C, hD G D C, lemma22Kappa D C⟩

/-- The bundle consumed by `keySmallAsm`. -/
theorem keySmallBundle (hcoh : CohAll) (hD : DecompAll) (hS4 : S4All) :
    ∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)],
      Coherence23Prop C ∧ IndDiffProp C ∧ S4DecompProp D C ∧ Lemma22KappaProp D C :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)] =>
    ⟨hcoh G C, s02_indDiff C, hS4 G D C, lemma22Kappa D C⟩

/-- **KEY-BIG** (`|S| ≥ 8`, Lemma 2.5). -/
theorem keyBig_of (hcoh : CohAll) (hD : DecompAll) : KeyBigProp :=
  keyBigAsm bridgeProp constituentSum (keyBigBundle hcoh hD)

/-- **KEY-SMALL** (`|S| = 4`). -/
theorem keySmall_of (hcoh : CohAll) (hD : DecompAll) (hS4 : S4All) : KeySmallProp :=
  keySmallAsm bridgeProp constituentSum (keySmallBundle hcoh hD hS4) kEqSmall tDerived

/-! ## 4. Theorems A and B -/

/-- **Theorem A.**  (`hcoh` and `hS4` are discharged by `coherenceAll` and `s4All`; the single
open leaf is `hD`.) -/
theorem bgThmA_of (hcoh : CohAll) (hD : DecompAll) (hS4 : S4All) : BGThmAProp :=
  thmA_of_leaves nCases indexOdd fourDvdK (keyBig_of hcoh hD) (keySmall_of hcoh hD hS4)
    arithBig arithSmall

/-- **Theorem B from any proof of Theorem A** (BG p. 201). -/
theorem bgThmB_of_A (hA : BGThmAProp) : BGThmBProp :=
  thmB_of_leaves hA subBGData strongEmbed

/-- **Theorem B.** -/
theorem bgThmB_of (hcoh : CohAll) (hD : DecompAll) (hS4 : S4All) : BGThmBProp :=
  bgThmB_of_A (bgThmA_of hcoh hD hS4)

/-! ## 5. G8 (`KNeOneProp`, BG Remark 3.5) via design 26 -/

/-- **G8**, from Theorem B: design 26's `kNeOne_of_thmB` with the area's own
`CentralizerSplitProp`.  No new hypothesis. -/
theorem kNeOneProp_of (hcoh : CohAll) (hD : DecompAll) (hS4 : S4All) : KNeOneProp :=
  kNeOne_of_thmB (bgThmB_of hcoh hD hS4) centralizerSplit

/-! ## 6. Theorem C -/

/-- The `|S| ≥ 8` bundle, from the leaf hypotheses. -/
theorem c3Bundle_of (hcoh : CohAll) (hD : DecompAll) (hc3id : C3IdAll) (hc3nt : C3NtAll)
    (hc3deg : C3DegAll) : C3Bundle :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)] (K1 K2 : Subgroup G) _ _ =>
    ⟨hcoh G C, s02_indDiff C, hD G D C, kappaExists D C, lemma22Kappa D C,
      hc3id G D C, c3Bounds D C K1 K2, hc3nt G D C K1 K2, hc3deg G D C K1 K2⟩

/-- The `|S| = 4` bundle, from the leaf hypotheses. -/
theorem c4Bundle_of (hcoh : CohAll) (hS4 : S4All) (hc4id : C4IdAll) (hc4val : C4ValAll)
    (hc4deg : C4DegAll) : C4Bundle :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)] (K1 K2 : Subgroup G) _ _ =>
    ⟨hcoh G C, s02_indDiff C, kappaExists D C, lemma22Kappa D C,
      hc4id G D C, hc4val G D C K1 K2, hc4deg G D C K1 K2, hS4 G D C⟩

/-- **Theorem C.**  G8 is supplied by `kNeOneProp_of`, so there is no `hk` parameter. -/
theorem bgThmC_of (hcoh : CohAll) (hD : DecompAll) (hS4 : S4All)
    (hc3id : C3IdAll) (hc3nt : C3NtAll) (hc3deg : C3DegAll)
    (hc4id : C4IdAll) (hc4val : C4ValAll) (hc4deg : C4DegAll) : BGThmCProp :=
  thmC_of_leaves nCases
    (thmCBigAsm bridgeProp constituentSum thmCSec3 (kNeOneProp_of hcoh hD hS4) arithC3
      (c3Bundle_of hcoh hD hc3id hc3nt hc3deg))
    (thmCSmallAsm bridgeProp constituentSum thmCSec3 thmCSmallShape (kNeOneProp_of hcoh hD hS4)
      arithC4 arithC4b kEqSmall (c4Bundle_of hcoh hS4 hc4id hc4val hc4deg))

/-- **C4-DEG is CLOSED**: `BG/c4DegreeB` is proved and `#print axioms`-clean. -/
theorem c4DegAll : C4DegAll :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
      (K1 K2 : Subgroup G) =>
    c4DegreeB D C K1 K2

/-- **Theorem C** with the closed leaf C4-DEG already substituted; the remaining open leaf
hypotheses are `hD : DecompAll` and `hc3deg : C3DegAll` (plus the cleanliness of
`hc3id`/`hc3nt`/`hc4id`/`hc4val`). -/
theorem bgThmC_of_open (hcoh : CohAll) (hD : DecompAll) (hS4 : S4All)
    (hc3id : C3IdAll) (hc3nt : C3NtAll) (hc3deg : C3DegAll)
    (hc4id : C4IdAll) (hc4val : C4ValAll) : BGThmCProp :=
  bgThmC_of hcoh hD hS4 hc3id hc3nt hc3deg hc4id hc4val c4DegAll

/-! ## 7. The closed leaves, and the unconditional Theorems A and B -/

/-- **DEC-BIG is CLOSED** (`BG/decompBig`, `#print axioms`-clean). -/
theorem decompAll : DecompAll :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] =>
    decompBig D C

/-- **C3-1 is CLOSED** (`BG/c3Identity`, clean). -/
theorem c3IdAll : C3IdAll :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)] =>
    c3Identity D C

/-- **C4-ID is CLOSED** (`BG/c4Identity`, clean). -/
theorem c4IdAll : C4IdAll :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)] =>
    c4Identity D C

/-- **C4-VAL is CLOSED** (`BG/c4Values`, clean). -/
theorem c4ValAll : C4ValAll :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
      (K1 K2 : Subgroup G) =>
    c4Values D C K1 K2

/-- **C3-3 is CLOSED** (`BG/c3NotThree`, built on `BG/c3Sfixed2` + `BG/c3DegEq2` + the
corrected exception `BG/c3ExcFinal`; `#print axioms` clean). -/
theorem c3NtAll : C3NtAll :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
      (K1 K2 : Subgroup G) =>
    c3NotThree D C K1 K2

/-- **Theorem A, unconditional.** -/
theorem bgThmA : BGThmAProp := bgThmA_of coherenceAll decompAll s4All

/-- **Theorem B, unconditional.** -/
theorem bgThmB : BGThmBProp := bgThmB_of_A bgThmA


end Work.BG
