import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.BSW.Defs

/-!
# AREA CORE2B — Bender 1981 §2.7–§2.10 (pp. 221–222)

Deliverables: `Lemma27Prop`, `Lemma28Prop`, `Lemma29Prop`, `Thm210Prop`.

This is the definition module of the area.  The `Work.GW2` vocabulary and all Prop contracts are
copied **verbatim** from the lead's design file `Submission/Work/_design_gw/Contracts2.lean`
(namespace `GW2` there), placed in namespace `Work.GW2` here as the area rules require.  The copy
stops just before `Contracts2`'s §5 (the stub area theorems), which is the only part of that file
containing `sorry`s.  Every declaration below is textually identical to the contract.

Conventions (see `Contracts2.lean` §0):
* subgroups of an ambient `G` are used throughout; `…In K` is the corresponding subgroup of
  `↥K` mapped back into `G`;
* `OddCore`, `pCore`, `fitting`, `layer` are `sSup`s of normal subgroups, wrapped in
  `normalCore` only so that normality is an instance.

Area-specific definitions and the four deliverables live in namespace `Work.CORE2B`
(see `Submission/Work/CORE2B/Steps.lean`, `.../API.lean`, `.../Deliverable.lean`).
-/

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

/-! ## 0. Vocabulary -/

section Vocabulary

variable {G : Type*} [Group G]


end Vocabulary

/-! ## 1. D-groups and the global statements -/


/-! ## 2. Bender's minimal-counterexample context -/


namespace BenderSetup
variable {G : Type} [Group G] [Finite G] (B : BenderSetup G)
end BenderSetup


/-! ## 3. Area deliverables (Props) -/

/-! ### FUS: dihedral fusion (Gorenstein 7.7) -/


/-! ### COPR: Bender 1.1, 1.3, 1.5 (coprime action; FT-free since `P` is a `p`-group) -/


/-! ### DSTR: D-group structure (Bender 1.6, 1.9, 1.10) -/


/-! ### AUTL2 / AUTA7: almost-simple overgroups with dihedral Sylow 2-subgroups -/


/-! ### L2F / A7F: model facts. These are the initial lists. CORE owners request more facts
through the lead, stated on the concrete models. -/


/-! ### BMAX: Bender 1970 1.6/1.7 = Bender 1981 Lemma 2.3 -/


/-! ### ZJ: Glauberman 1968, Theorems A and B, for groups with dihedral/cyclic Sylow 2 -/


/-! ### BG: Bender–Glauberman 1981, Theorems A, B, C -/


namespace BGData
variable {G : Type} [Group G] [Finite G] (D : BGData G)
end BGData


/-! ### BSW / ZASS / A7REC: recognition -/


/-! ### CORE2A: Bender Lemmas 2.1, 2.2, 2.4, 2.5 and Theorem 2.6 -/


/-! ### CORE2B: Bender Lemmas 2.7–2.9 and Theorem 2.10 -/


/-! ### CORE3 / CORE4: elimination of the two cases -/


/-! ## 4. Bundles: the shared local toolkit consumed by the CORE areas -/


/-! ## 0b. Helper vocabulary from `_design_gw/Core2.lean` §Helpers (verbatim, one fix)

These live in namespace `GW2` in `Core2.lean`; they are repeated here because area contracts use
them (`Inverts` in `Case1aData`, `conjSub` in `Lemma25Prop`, …) and an area must be able to
state them without importing a design file.

The single deviation from the design text: `bCount` carries an explicit `[Hh.Normal]` argument,
because the quotient notation `G ⧸ Hh` requires a `Normal` instance, which the design file
supplied implicitly (`autoImplicit`).
-/

section Helpers

variable {G : Type*} [Group G]


end Helpers

end Work.GW2
