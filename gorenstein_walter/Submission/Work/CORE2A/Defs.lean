/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Submission.Work.ASM.Defs
import Submission.Work.BSW.Defs
import Submission.Work.DSTR.Defs

/-!
# CORE2A: Bender 1981 §2 — the centralizer of an involution

This is the vocabulary file of the area `CORE2A` of the Gorenstein–Walter build.  The area
implements Bender 1981 (J. Algebra 70, 216–228), Section 2, pp. 219–221:

* `Lemma22Prop` (Bender's Lemma 2.2) and `Thm26Prop` (Bender's Theorem 2.6) are the two
  deliverables of the area; their *statements* are dictated by the contract file
  `Submission/Work/_design_gw/Contracts2.lean` (namespace `GW2`).
* the internal leaves of the area are Bender's Lemmas 2.1, 2.4, 2.5 and the three steps of
  Theorem 2.6; they are `Lemma21Prop`, `Lemma24Prop`, `Lemma25Prop`, `Thm26aProp`,
  `Thm26bProp`, `Thm26cProp` below (design pass 2, `_design_gw/Core2.lean` §D), together with
  the auxiliary predicate `Lemma22Config` describing the configuration of Lemma 2.2.

## Where the vocabulary lives

This module imports and re-exports the two shared vocabulary modules of the build, so that a
caller of CORE2A uses the same *constants* as the areas that supply the inputs:

* `Submission.Work.ASM.Defs` is the canonical home of the `Work.GW2` vocabulary of
  `Contracts2.lean`: `oddCore`, `pCore`, `fitting`, `fstar`, …, `DihOrCycSylow`, `DShape`,
  `BenderCtx`, `BenderSetup`, `BRel`, `Case1`, `Case2`, `LocalToolkit` and all the area `Prop`s,
  including `Lemma22Prop`, `Thm26Prop`, `Lemma23Prop`, `ZJAProp`, `ZJBProp`, `BGThmBProp`,
  `BGThmCProp`;
* `Submission.Work.BSW.Defs` is the home of the design-pass-2 amendments of `Core2.lean`
  §0/§A: `conjSub`, `involutionSet`, `OneInvClassIn`, `Inverts`, `cosetInvCount`, `bCount`,
  `BSWHyps2`, `BSW2Prop` (and `ZassHyps2`, `ZassOdd2Prop`, `BSWZass2Prop`).

CORE2A does not redefine them.

## Conventions

All subgroups are subgroups of an ambient group `G`, and `…In K` is the subgroup of `↥K`
carried into `G` along `K.subtype`.  `BenderSetup G` carries Bender's notation `S, S₀, t, Ĥ` for
a minimal counterexample (`BenderCtx G`), with `H = C_G(t) = B.H`, `U = O(H) = B.U` and
`π = π(F(Ĥ)) = B.pi`.
-/

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

/-! ## 1. The configuration of Lemma 2.2 -/

/-- Bender's Lemma 2.2, as a configuration on `B : BenderSetup G`:
(a) `S₀` centralizes `U`;
(b) `I_U(s)` is a normal subgroup of `U` for some `s ∈ S − S₀`;
(c) `N_G(X) ≤ H` for every `1 ≠ X ≤ I_U(s)`.

`Lemma22Prop` (in `Submission.Work.ASM.Defs`) is exactly `¬ Lemma22Config B` for every `B` in a
minimal counterexample; see `Work.CORE2A.lemma22Prop_iff`. -/
def Lemma22Config {G : Type} [Group G] [Finite G] (B : BenderSetup G) : Prop :=
  B.S0 ≤ centralizer (B.U : Set G) ∧
    ∃ s ∈ (B.S : Subgroup G), s ∉ B.S0 ∧
      ∃ I : Subgroup G, (I : Set G) = invSet B.U s ∧ (I.subgroupOf B.U).Normal ∧
        ∀ X : Subgroup G, X ≠ ⊥ → X ≤ I → normalizer (X : Set G) ≤ B.H

/-! ## 2. The CORE2A leaves (design pass 2, §D) -/

/-- Lemma 2.1: `Ĥ` has at least two classes of involutions. -/
def Lemma21Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    ¬ OneInvClassIn B.Hhat

/-- Lemma 2.4. -/
def Lemma24Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    ∀ M : Subgroup G, IsCoatom M → BRel B.Hhat M → ∀ p : ℕ, p.Prime → p ≠ 2 →
      IsPGroup p (fstarIn B.Hhat) → IsPGroup p (fstarIn M) → B.Hhat = M

/-- Lemma 2.5. -/
def Lemma25Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    ∀ g : G, oddCoreIn B.Hhat ≠ ⊥ → BRel B.Hhat (conjSub g B.Hhat) → conjSub g B.Hhat = B.Hhat

/-- The conclusion of Theorem 2.6, as a predicate. -/
def Thm26Concl {G : Type} [Group G] [Finite G] (B : BenderSetup G) : Prop :=
  oddCoreIn B.Hhat = B.U ∧
    (B.S : Subgroup G) ⊓ centralizer (B.U : Set G) = pCoreIn 2 B.Hhat ∧
    ((pCoreIn 2 B.Hhat ≤ B.S0 ∧ B.Hhat = B.H) ∨
     (IsFourGroup (pCoreIn 2 B.Hhat) ∧ (pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 ∧
       ∃ a ∈ B.Hhat, ∃ b ∈ B.Hhat, a * b * a⁻¹ * b⁻¹ ∉ pCoreIn 2 B.Hhat ⊔ B.U))

/-- Thm 2.6, step 1 (first paragraph): `O₂(Ĥ) ≠ 1` gives the conclusion. -/
def Thm26aProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    pCoreIn 2 B.Hhat ≠ ⊥ → Thm26Concl B

/-- Thm 2.6, step 2: `E(Ĥ) = 1`. -/
def Thm26bProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    layerIn B.Hhat = ⊥

/-- Thm 2.6, step 3: `t` centralizes every `H`-invariant odd `p`-subgroup. -/
def Thm26cProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G, IsPGroup p P →
      B.H ≤ normalizer (P : Set G) → P ≤ centralizer ({B.t} : Set G)

/-- Thm 2.6, step 2 (B81 p. 220, "`SE/Z(E)` is some `PGL₂(q)`, again by Lemma 2.1").  If
`E := E(Ĥ) ≠ 1`, then `SE/Z(E) ≅ PGL₂(q)`, as a surjection from `S ⊔ E` with kernel `Z(E)`.
Statement copied verbatim from `Submission/Work/_design_gw/Core4.lean` §2 (design pass 4); the
inputs are `AutL2Prop`, `AutA7Prop`, `LayerShapeProp`, `LayerOneInvClassProp`, `TwoRankProp`
and `Lemma21Prop` (route: design4 §3). -/
def Thm26bPGLProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    layerIn B.Hhat ≠ ⊥ →
    ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      ∃ φ : ↥((B.S : Subgroup G) ⊔ layerIn B.Hhat) →* PGL(2, GaloisField p k),
        Function.Surjective φ ∧
        φ.ker = (((center ↥(layerIn B.Hhat)).map (layerIn B.Hhat).subtype).subgroupOf
          ((B.S : Subgroup G) ⊔ layerIn B.Hhat))

/-- Thm 2.6, step 2, in the form in which Bender's paragraph actually establishes it
(pp. 220–221): if `E := E(Ĥ) ≠ 1`, then `Ĥ` has a **single** class of involutions — which
contradicts Lemma 2.1 and hence gives `E(Ĥ) = 1`.

This is deliberately stated with the full `BenderCtx` binder (unlike the intermediate claims of
the paragraph, which are *not* consequences of the local data alone: in `G = A₇`,
`Ĥ = S₅`, `E(Ĥ) = A₅` the local data hold but `Ĥ` has two classes of involutions — the
exclusion of that model is exactly `BenderCtx.notA7`). -/
def Thm26bOneClassProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    layerIn B.Hhat ≠ ⊥ → OneInvClassIn B.Hhat

/-! ## 3. Glauberman Theorem B in the product order the source proves -/

/-- **`ZJBProp` restated** (design pass 11, §1 of `_design_gw/Core11ZJB.lean`): Theorem B with
the conclusion `g = n * c`, `n ∈ N_G(Z(J(P)))`, `c ∈ C_G(W)`.  This is the order the source
proves (`(C_p)` in Mathlib's convention); the older order `g = c * n` is not derivable from it.

The Prop is owned by area ZJB; it is copied here (verbatim from the design file) only because
the ZJB `Defs` module does not carry it yet.  When it does, import that module instead. -/
def ZJBProp' : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 → DihOrCycSylow X →
    ∀ (P : Sylow p X) (W : Set X) (g : X), W.Nonempty → W ⊆ (P : Subgroup X) →
      (∀ w ∈ W, g * w * g⁻¹ ∈ (P : Subgroup X)) →
      ∃ n c : X, n ∈ normalizer (ZJ (P : Subgroup X) : Set X) ∧ c ∈ centralizer W ∧ g = n * c

/-! ## 4. Theorem 2.6 step 2 revisited (design pass 13 §2): the single crux -/

/-- **The crux of `Thm26bOneClass`** (design pass 13, `_design_gw/Core13.lean` §2): Bender p. 220,
with `R = [t, C_E(s)]`, `R* = [t, C_E(ts)]` and `y` an involution of `C_G(ts) ∩ N_G(R*)` with
`t^y = s`, the subgroup `⟨t, R, R*⟩ ≤ E ∩ Ĥ^y` has order divisible by `4`; here that is recorded
as `4 ∣ |E ∩ Ĥ^y|` for some such `y`.  `Thm26bOneClassProp` is reduced to it by
`Work.CORE2A.c13_thm26bOneClass` (K1–K3 + this input). -/
def Thm26bTorusProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    B.t ∈ layerIn B.Hhat → 8 ≤ Nat.card (B.S : Subgroup G) →
    ∀ s ∈ (B.S : Subgroup G), orderOf s = 2 → s ∉ layerIn B.Hhat →
      ∃ y ∈ normalizer ((zpowers B.t ⊔ zpowers s : Subgroup G) : Set G), y * B.t * y⁻¹ = s ∧
        4 ∣ Nat.card (layerIn B.Hhat ⊓ conjSub y B.Hhat : Subgroup G)

end Work.GW2
