/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : almost simple overgroups with dihedral Sylow 2-subgroups

This file is the *interface* of the area `Submission/Work/AUTL2/` for the Gorenstein–Walter
project (route: Bender 1981 + Bender–Glauberman 1981, Feit–Thompson available).

## The deliverable

`Work.GW2.AutL2Prop`, copied verbatim from `Submission/Work/_design_gw/Contracts2.lean`:

if `L ◁ Q`, `L ≃ PSL(2,q)` (`q = p^k` odd, `q ≥ 5`), `C_Q(L) = 1` and `Q` has cyclic or
dihedral Sylow 2-subgroups, then `Q` has a normal subgroup `M ⊇ L` of odd index with
`M ≃ PSL(2,q)` or `M ≃ PGL(2,q)`.

## The model used by the proof (design `NOTES_LEAD_gw_design2.md` §5, steps A1–A6)

Everything happens on the projective line `ℙ¹(F) = OnePoint F` of a finite field `F = GF(q)`:

* `Work.AUTL2.P1 F`   : the projective line `OnePoint F` (`∞` adjoined to `F`);
* `Work.AUTL2.pglHom` : `PGL(2,F) →* Perm ℙ¹(F)` (faithful), `pglImage` its range;
* `Work.AUTL2.pslHom` : `PSL(2,F) →* Perm ℙ¹(F)` (faithful), `pslImage` its range;
* `Work.AUTL2.galHom` : `Aut(F) →* Perm ℙ¹(F)`, `σ ↦ (x ↦ σ x, ∞ ↦ ∞)`;  `galSub` its range;
* `Work.AUTL2.pgammaL` : `PΓL(2,F) = pglImage ⊔ galSub`.

The main theorem is `normalizer pslImage = pgammaL` (`Normalizer.lean`, step A3), the Sylow
analysis is `A5`/`A6` (`Sylow.lean`), and the transfer to an abstract group `Q` is `Main.lean`.

## Conventions

* `F` is a field with `[DecidableEq F]` (needed for the Möbius action of Mathlib).
* `pglImage ≤ pgammaL`, `pslImage ≤ pglImage`, `pglImage ◁ pgammaL`;
* for `q = p^k` with `k` even, `sigmaPerm` is the *field involution* `x ↦ x^(p^(k/2))`.

The definitions of the vocabulary and the Prop statements are copied **verbatim** from
`Submission/Work/_design_gw/Contracts2.lean`, in the namespace `Work.GW2`, so that the area can
be composed with the other areas against those contracts.
-/
import Mathlib
import Submission.Work.AUTL2.Defs

open scoped MatrixGroups LinearAlgebra.Projectivization


/-! ## The model: `ℙ¹(F)` and the actions of `PGL`, `PSL`, `Aut F` -/

namespace Work.AUTL2

open OnePoint Subgroup

variable (F : Type*) [Field F] [DecidableEq F]


/-! ## The standard Möbius elements

`transl b` is `x ↦ x + b`, `dil a` is `x ↦ a² x` and `weyl` is `x ↦ -1/x`; all three are
elements of `pslImage F`.  These are the elements out of which the argument of step A3 is
built: the translation group `U_∞`, its normalizer (the Borel), and the Weyl element. -/

section Standard


end Standard

end Work.AUTL2
