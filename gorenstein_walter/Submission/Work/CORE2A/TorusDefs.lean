/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

/-!
# CORE2A: vocabulary for design pass 14 (`Thm26bTorusProp`)

Statements copied verbatim from `Submission/Work/_design_gw/Core14.lean` §0–§1 (design pass 14,
`NOTES_LEAD_gw_design14.md`): the notation of Bender 1981 p. 220 for the second half of
Theorem 2.6,

* `zE B`   : `Z(E(Ĥ))` as a subgroup of `G`;
* `cE B`   : `C_Ĥ(E(Ĥ))`;
* `SE B`   : `⟨S, E(Ĥ)⟩`;
* `torusR B u` : Bender's torus `R_u = [t, C_{E(Ĥ)}(u)]`;
* `kE B`   : `k = |C_{E(Ĥ)}(t) : Z(E(Ĥ))|`;
* `Lsub p k` : `L₂(q) ≤ PGL₂(q)` as the image of `toPGL`;
* `mTor q`, `kTor q` : the two integers `(q ± 1)/2` and `q ∓ 1`;
* `PGLData B p k`  : the `PGL₂(q)`-quotient of `SE` with kernel `Z(E)`;
* `Thm26bAutProp` : the strengthened recognition input `A0` of pass 14 (a `PGLData` whose first
  component is exactly `E`, plus the preimage `Mt` of the odd-index `PGL₂(q) ⊴ Ĥ/C_Ĥ(E)`).
-/

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- `Z(E)`, `E = E(Ĥ)`, as a subgroup of `G`. -/
def zE (B : BenderSetup G) : Subgroup G :=
  (center ↥(layerIn B.Hhat)).map (layerIn B.Hhat).subtype

/-- `C_Ĥ(E)`. -/
def cE (B : BenderSetup G) : Subgroup G :=
  B.Hhat ⊓ centralizer (layerIn B.Hhat : Set G)

/-- `S E`. -/
def SE (B : BenderSetup G) : Subgroup G :=
  (B.S : Subgroup G) ⊔ layerIn B.Hhat

/-- Bender's torus `R_u = [t, C_E(u)]` (`R = R_s`, `R* = R_{ts}`). -/
def torusR (B : BenderSetup G) (u : G) : Subgroup G :=
  ⁅zpowers B.t, layerIn B.Hhat ⊓ centralizer ({u} : Set G)⁆

/-- `k = |C_E(t) : Z(E)|`. -/
noncomputable def kE (B : BenderSetup G) : ℕ :=
  (zE B).relIndex (layerIn B.Hhat ⊓ centralizer ({B.t} : Set G))

/-- `L₂(q)` inside `PGL₂(q)`. -/
noncomputable abbrev Lsub (p k : ℕ) [Fact p.Prime] : Subgroup (PGL(2, GaloisField p k)) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL :
    PSL(2, GaloisField p k) →* PGL(2, GaloisField p k)).range

/-- `m = (q + ε)/2`, `q ≡ ε (mod 4)` — the order of the tori (as in `PGL2CommutatorTorusProp`). -/
def mTor (q : ℕ) : ℕ := if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2

/-- `q − ε` — the order of the involution centralizer of `L₂(q)`. -/
def kTor (q : ℕ) : ℕ := if q % 4 = 1 then q - 1 else q + 1

/-- The `PGL₂` quotient of `SE` (the data of `Thm26bAutProp`, part (a)). -/
structure PGLData (B : BenderSetup G) (p k : ℕ) [Fact p.Prime] where
  φ : ↥(SE B) →* PGL(2, GaloisField p k)
  surj : Function.Surjective φ
  ker : φ.ker = (zE B).subgroupOf (SE B)
  mem_layer_iff : ∀ x : ↥(SE B), (x : G) ∈ layerIn B.Hhat ↔ φ x ∈ Lsub p k

/-- **A0 `Thm26bAutProp`.**  (a) = `Thm26bPGLProp` plus `φ(E) = L₂(q)`; (b) the preimage `Mt` of
the odd-index `PGL₂(q) ⊴ Ĥ / C_Ĥ(E)`.  Proof: copy `Work.CORE2A.Thm26bPGL` (same inputs). -/
def Thm26bAutProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    layerIn B.Hhat ≠ ⊥ →
    (∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      ∃ φ : ↥(SE B) →* PGL(2, GaloisField p k),
        Function.Surjective φ ∧ φ.ker = (zE B).subgroupOf (SE B) ∧
        ∀ x : ↥(SE B), (x : G) ∈ layerIn B.Hhat ↔ φ x ∈ Lsub p k) ∧
    ∃ Mt : Subgroup G, Mt ≤ B.Hhat ∧ layerIn B.Hhat ⊔ cE B ≤ Mt ∧
      (∀ h ∈ B.Hhat, ∀ m ∈ Mt, h * m * h⁻¹ ∈ Mt) ∧ Odd (Mt.relIndex B.Hhat) ∧
      (layerIn B.Hhat ⊔ cE B).relIndex Mt = 2

end Work.GW2
