/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — elimination of the second case of Bender's Theorem 2.10 (§4 of Bender 1981)

This is the interface/definition module of area `CORE4` of the `gorenstein_walter` project
(route: Bender 1981, *Finite groups with dihedral Sylow 2-subgroups*, J. Algebra **70** (1981)
216–228, plus Bender–Glauberman 1981, ibid. 200–215; Feit–Thompson is available separately).

Everything here is **copied verbatim** from the two design files

* `Submission/Work/_design_gw/Contracts2.lean` (namespace `GW2`), and
* `Submission/Work/_design_gw/Core2.lean` (namespace `GW2`),

and placed in namespace `Work.GW2` as requested by the lead.  This file imports Mathlib only (so
that it stays cheap and so that the names never clash with another area's copies); the
mathematical content lives in the sibling files:

* `Submission/Work/CORE4/Arith.lean`     — `Work.GW2.Case2ArithProp` (pure arithmetic, PROVED here);
* `Submission/Work/CORE4/Assembly.lean`  — `Work.GW2.Case2FalseProp` from the leaves.

## The deliverable

`Work.GW2.Case2FalseProp` (§4 of Bender's paper).  Its leaves are

* `Case2SetupProp`   — §4 (1)–(5);
* `Case2SixProp`     — §4 (6);
* `Case2NotA7Prop`   — §4, elimination of `E/Z(E) ≅ A₇`;
* `Case2NineProp`    — §4 (9): `E ≅ L₂(q)`, `Z(E) = 1`, `S ≤ E`, `q ≥ 7`;
* `Case2CountProp`   — §4 (7)–(12), the case analysis producing the numbers;
* `Case2ArithProp`   — §4 final arithmetic (p. 228), no such numbers exist.

The five group-theoretic leaves are proved from the *other areas'* Props by name; the bundle of
those Props is `Work.GW2.C4Inputs` below.  Since the props the leaves consume are produced by
other areas (CORE2A, CORE2B, L2F, DSTR), each leaf is stated in the form

    Case2XxxImpl (I : C4Inputs) : Prop

with the *same* conclusion as the design's `Case2XxxProp`, and `Case2XxxProp` is recovered from
`Case2XxxImpl` for any input bundle (see `Assembly.lean`).
-/
import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.BSW.Defs

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

/-! ## 0. Vocabulary (verbatim from `Contracts2.lean`) -/

section Vocabulary

variable {G : Type*} [Group G]


end Vocabulary

/-! ## 1. D-groups and the global vocabulary (verbatim from `Contracts2.lean`) -/


/-! ## 2. Bender's minimal-counterexample context (verbatim from `Contracts2.lean`) -/


namespace BenderSetup
variable {G : Type} [Group G] [Finite G] (B : BenderSetup G)
end BenderSetup


/-! ## 3. Helpers (verbatim from `Core2.lean` §Helpers) -/

section Helpers

variable {G : Type*} [Group G]


end Helpers

/-! ## 4. The other areas' Props that CORE4 consumes (copied verbatim) -/

/-! ### FUS -/


/-! ### COPR -/


/-! ### DSTR -/


/-! ### AUTL2 / AUTA7 -/


/-! ### L2F / A7F -/


/-! ### L2F extensions requested by CORE4 (Core2 §G) -/

/-- §4 (1): odd-order subgroups of `C_L(t)` are cyclic and inverted by an involution of
`C_L(t)` (the dihedral group `D_{q±1}`). -/
def L2CentOddCyclicProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    ∀ t : PSL(2, GaloisField p k), orderOf t = 2 → ∀ Y : Subgroup (PSL(2, GaloisField p k)),
      Y ≤ centralizer ({t} : Set _) → Odd (Nat.card Y) →
        IsCyclic Y ∧ ∃ s ∈ centralizer ({t} : Set (PSL(2, GaloisField p k))), orderOf s = 2 ∧ Inverts s Y

/-- §4 (11): number of subgroups of odd prime order `r ∣ (q ± 1)/2` in `L₂(q)`. -/
def L2PrimeSubgroupCountProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k → ∀ (r : ℕ), r.Prime → r ≠ 2 → r ≠ p →
    ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → (r : ℤ) ∣ ((p ^ k : ℕ) + ε) / 2 →
      2 * ({Y : Subgroup (PSL(2, GaloisField p k)) | Nat.card Y = r}.ncard : ℤ) =
        (p ^ k : ℕ) * ((p ^ k : ℕ) - ε)

/-- §4 (11)/(12): for an odd prime `r ∤ q`, a subgroup `Y` of order `r` has a cyclic centralizer
of order `(q±1)/2` and a dihedral normalizer of order `q±1`. -/
def L2TorusNormalizerProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k → ∀ (r : ℕ), r.Prime → r ≠ 2 → r ≠ p →
    ∀ Y : Subgroup (PSL(2, GaloisField p k)), Nat.card Y = r →
      IsCyclic (centralizer (Y : Set (PSL(2, GaloisField p k)))) ∧
      (2 * Nat.card (centralizer (Y : Set (PSL(2, GaloisField p k)))) = p ^ k + 1 ∨
        2 * Nat.card (centralizer (Y : Set (PSL(2, GaloisField p k)))) = p ^ k - 1) ∧
      Nonempty (normalizer (Y : Set (PSL(2, GaloisField p k))) ≃*
        DihedralGroup (Nat.card (centralizer (Y : Set (PSL(2, GaloisField p k))))))

/-- §4 (12): a subgroup of order `r ∤ q` (`r` odd) normalizes at most two subgroups of order `q`. -/
def L2NormalizesTwoSylowProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k → ∀ (r : ℕ), r.Prime → r ≠ 2 → r ≠ p →
    ∀ Y : Subgroup (PSL(2, GaloisField p k)), Nat.card Y = r →
      {Q : Subgroup (PSL(2, GaloisField p k)) | Nat.card Q = p ^ k ∧
          Y ≤ normalizer (Q : Set (PSL(2, GaloisField p k)))}.ncard ≤ 2

/-! ### BMAX (Lemma 2.3) and CORE2A/B Props consumed by CORE4 -/


/-! ### BG: Bender–Glauberman 1981, Theorem A -/


namespace BGData
variable {G : Type} [Group G] [Finite G] (D : BGData G)
end BGData


/-! ### The shared toolkit (verbatim from `Contracts2.lean` §4) -/


/-! ## 5. CORE4: the §4 objects and the deliverable's leaves (verbatim from `Core2.lean` §F) -/

/-- The §4 objects: `M`, `E = E(M)`, an involution `s ∈ S ∩ E`, and
* `K = [S∩E, U∩M] = I_{U∩M}(s)`;
* `B₀ = C_{U∩M}(S∩E) = C_{U∩M}(s)`;
* `F = B₀ ∩ F(U)`;
* `K₀ = F(U) ∩ K`. -/
structure Case2Data {G : Type} [Group G] [Finite G] (B : BenderSetup G) where
  M : Subgroup G
  X : Subgroup G
  s : G
  K : Subgroup G
  B0 : Subgroup G
  F : Subgroup G
  M_coatom : IsCoatom M
  t_mem : B.t ∈ layerIn M
  X_ne : X ≠ ⊥
  X_le : X ≤ fittingIn B.U
  NX_le : normalizer (X : Set G) ≤ M
  s_mem : s ∈ (B.S : Subgroup G) ⊓ layerIn M
  s_order : orderOf s = 2
  K_def : (K : Set G) = invSet (B.U ⊓ M) s
  B0_def : B0 = (B.U ⊓ M) ⊓ centralizer ({s} : Set G)
  F_def : F = B0 ⊓ fittingIn B.U

/-- §4 (1)–(5). -/
def Case2SetupProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case2 B → ∃ D : Case2Data B,
      ¬ B.H ≤ D.M ∧ OneInvClassIn (layerIn D.M) ∧
      IsCyclic D.K ∧ B.U ⊓ D.M = D.K ⊔ D.B0 ∧
      D.F ≠ ⊥ ∧ D.F ≤ centralizer ((layerIn D.M : Subgroup G) : Set G) ∧
      normalizer (D.F : Set G) = D.M ∧ D.B0 = B.U ⊓ centralizer ({D.s} : Set G)

/-- §4 (6): `F ∩ F^g = 1` for `g ∉ M`, and `F` is cyclic. -/
def Case2SixProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    ∀ D : Case2Data B, ¬ B.H ≤ D.M → D.F ≠ ⊥ →
      (∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥) ∧ IsCyclic D.F

/-- §4: `E(M)/Z ≇ A₇`. -/
def Case2NotA7Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    ∀ D : Case2Data B,
      IsEmpty ((↥(layerIn D.M) ⧸ center ↥(layerIn D.M)) ≃* alternatingGroup (Fin 7))

/-- §4 (9): `E ≅ L₂(q)` with `Z(E) = 1`, and `S ≤ E`, with `q ≥ 7`. -/
def Case2NineProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    ∀ D : Case2Data B, ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 7 ≤ p ^ k ∧
      Nonempty (layerIn D.M ≃* PSL(2, GaloisField p k)) ∧ (B.S : Subgroup G) ≤ layerIn D.M

/-- §4 final arithmetic (pure). The page-228 chain, checked by brute force for odd prime powers
`q ≤ 400`: no tuple satisfies the hypotheses.
* `{k, k'} = {(q+1)/2, (q−1)/2}` with `k` even;
* `3 ≤ p₀ ≤ p₁ ≤ p+1` and `p₀ ≤ p ≤ k/2`, with `p` prime and `p₀` odd;
* `1 ≤ u ≤ p`;
* (12): `q k'(p₁−1) q k' ((p₁−1)(q k'−1) − (q−1)q/p) ≤ 6k²u³p₀³` (over ℚ). -/
def Case2ArithProp : Prop :=
  ∀ (q k k' p p0 p1 u : ℕ), 7 ≤ q → Odd q →
    ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) → Even k →
    p.Prime → 3 ≤ p0 → Odd p0 → p0 ≤ p1 → p1 ≤ p + 1 → p0 ≤ p → 2 * p ≤ k → 1 ≤ u → u ≤ p →
    ¬ (((q * k' * (p1 - 1) * (q * k')) : ℚ) *
          (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p) ≤
        6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3)

/-- §4 (7)–(12): the case analysis produces numbers violating `Case2ArithProp`'s conclusion,
i.e. `False`. -/
def Case2CountProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case2 B → ∃ (q k k' p p0 p1 u : ℕ), 7 ≤ q ∧ Odd q ∧
      ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧ Even k ∧
      p.Prime ∧ 3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p ∧
      (((q * k' * (p1 - 1) * (q * k')) : ℚ) *
          (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p) ≤
        6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3)


/-! ## 6. Two further named inputs of area CORE4

`LayerOneInvClassPropC4` is produced by DSTR (design3 §4): the normal quasisimple subgroup of a
group with dihedral/cyclic Sylow 2-subgroups has one class of involutions.  It is used in the `A₇`
sub-case of §4 (p. 226) to get `M = E C_M(t)`.

`A7S4Prop` is the §4 `A₇` structure fact of p. 226 ("by the structure of `A₇`, some subgroup
`K' ≠ K` of `N_E(V) = Ĥ ∩ E` is inverted by `s`").  Its formalisation is stated below; it is a
finite computation in `A₇` (`N_{A₇}(V)` for `V` the `O₂` of a Sylow 2-subgroup).  Verified
exhaustively in the model: for every four-group `V` of `A₇` lying in a Sylow 2-subgroup, every
involution `s` normalizing `V`, and every subgroup `K ≤ N_{A₇}(V)` of order 3 inverted by `s`,
there is a second such subgroup `K' ≠ K`. -/

/-- DSTR's `LayerOneInvClassPropC4` (design3 §4), in our vocabulary: in a group with dihedral or
cyclic Sylow 2-subgroups, a normal quasisimple subgroup has one class of involutions. -/
def LayerOneInvClassPropC4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FeitThompsonProp → DihOrCycSylow X →
    ∀ E : Subgroup X, E.Normal → IsQuasisimple E → OneInvClassIn E

/-- The `A₇` fact of Bender §4, p. 226.  `E ≅ A₇`, `V ≤ E` a four-group contained in a Sylow
2-subgroup `S` of `E` (for `A₇`, `S ≅ D₈` has a unique four-subgroup, namely the set of the four
elements of order dividing 2, and `V` is it), `s ∈ N_E(V)` an involution, `K ≤ N_E(V)` a subgroup
of order 3 inverted by `s`.  Then there is a second such subgroup `K' ≠ K` of order 3 in
`N_E(V)`, also inverted by `s`.

CORRECTION (design pass 15 §1.1): the earlier remark that "all subgroups of order 3 of `A₇` are
conjugate" is **false** — `A₇` has *two* classes of order-3 subgroups (3-cycles and products of two
disjoint 3-cycles), and both kinds occur among the subgroups of `N(V)` inverted by `s`.  So the
companion `K'` above need not be an `E`-conjugate of `K`; the conjugate statement is the separate
leaf `Work.CORE4.C15.A7S4ConjProp` (design pass 15, GAP-checked, `CORE4/A4s`). -/
def A7S4Prop : Prop :=
  ∀ (E : Type) [Group E] [Finite E], Nonempty (E ≃* alternatingGroup (Fin 7)) →
    ∀ (S : Sylow 2 E) (V : Subgroup E), V ≤ (S : Subgroup E) → IsFourGroup V →
      ∀ s ∈ normalizer (V : Set E), orderOf s = 2 →
        ∀ K : Subgroup E, K ≤ normalizer (V : Set E) → Nat.card K = 3 → Inverts s K →
          ∃ K' : Subgroup E, K' ≤ normalizer (V : Set E) ∧ Nat.card K' = 3 ∧ K' ≠ K ∧
            Inverts s K'

/-- The input bundle for CORE4's group-theoretic leaves.

The five group-theoretic leaves of §4 are proved from the Props of the other areas, named here.
`toolkit` is the shared `LocalToolkit`; the four `l2…` fields are the `L2F` extensions requested in
`NOTES_LEAD_gw_design2.md` §12 (recommended there for `LocalToolkit` in §14); `thm26`, `lem27`,
`lem28` are the CORE2A/CORE2B deliverables, `bgA` is BG Theorem A, `layerOneInvClass` is DSTR's
`LayerOneInvClassPropC4` (design3 §4) and `a7s4` is the `A₇` structure fact above. -/
structure C4Inputs : Prop where
  toolkit : LocalToolkit
  l2centOdd : L2CentOddCyclicProp
  l2primeCount : L2PrimeSubgroupCountProp
  l2torusNorm : L2TorusNormalizerProp
  l2normTwo : L2NormalizesTwoSylowProp
  thm26 : Thm26Prop
  lem27 : Lemma27Prop
  lem28 : Lemma28Prop
  bgA : BGThmAProp
  layerOneInvClass : LayerOneInvClassPropC4
  a7s4 : A7S4Prop

/-- The §4 data `(1)`–`(5)`: the facts Bender fixes at the start of §4.  `Case2Six` and
`Case2NotA7` take exactly these as hypotheses (Bender's (6), (7)–(9) all use this data). -/
def Case2Pre {G : Type} [Group G] [Finite G] (B : BenderSetup G) (D : Case2Data B) : Prop :=
  ¬ B.H ≤ D.M ∧ OneInvClassIn (layerIn D.M) ∧
  IsCyclic D.K ∧ B.U ⊓ D.M = D.K ⊔ D.B0 ∧
  D.F ≠ ⊥ ∧ D.F ≤ centralizer ((layerIn D.M : Subgroup G) : Set G) ∧
  normalizer (D.F : Set G) = D.M ∧ D.B0 = B.U ⊓ centralizer ({D.s} : Set G)

/-- `Case2SetupProp`, with the other areas' Props supplied as the bundle `I`. -/
def Case2SetupImpl (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    Case2 B → ∃ D : Case2Data B, Case2Pre B D

/-- `Case2SixProp`, with the bundle.  Hypothesis list: `Case2Pre B D` (§4 (1)–(5)). -/
def Case2SixImpl (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    ∀ D : Case2Data B, Case2Pre B D →
      (∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥) ∧ IsCyclic D.F

/-- `Case2NotA7Prop`, with the bundle.  Hypothesis list: §4 (1)–(6). -/
def Case2NotA7Impl (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    ∀ D : Case2Data B, Case2Pre B D →
      (∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥) → IsCyclic D.F →
        IsEmpty ((↥(layerIn D.M) ⧸ center ↥(layerIn D.M)) ≃* alternatingGroup (Fin 7))

/-- `Case2NineProp`, with the bundle.  Hypothesis list: §4 (1)–(6) and the exclusion of `A₇`. -/
def Case2NineImpl (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    ∀ D : Case2Data B, Case2Pre B D →
      (∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥) → IsCyclic D.F →
        IsEmpty ((↥(layerIn D.M) ⧸ center ↥(layerIn D.M)) ≃* alternatingGroup (Fin 7)) →
          ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 7 ≤ p ^ k ∧
            Nonempty (layerIn D.M ≃* PSL(2, GaloisField p k)) ∧ (B.S : Subgroup G) ≤ layerIn D.M

/-- The §4 data `(1)`–`(9)` produced by the four structural leaves `Case2Setup`, `Case2Six`,
`Case2NotA7`, `Case2Nine`: the subgroup `M` and its layer `E`, with all the properties Bender
derives before the counting starts at (10).  This is the hypothesis list of `Case2CountImpl`. -/
structure Case2Ctx {G : Type} [Group G] [Finite G] (B : BenderSetup G) where
  /-- the §4 objects `M, X, s, K, B₀, F` -/
  D : Case2Data B
  /-- §4 (1)–(5) -/
  pre : Case2Pre B D
  /-- §4 (6), first half -/
  F_ti : ∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥
  /-- §4 (6), second half -/
  F_cyclic : IsCyclic D.F
  /-- §4: `E/Z(E) ≇ A₇` -/
  notA7 : IsEmpty ((↥(layerIn D.M) ⧸ center ↥(layerIn D.M)) ≃* alternatingGroup (Fin 7))
  /-- §4 (9) -/
  nine : ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 7 ≤ p ^ k ∧
    Nonempty (layerIn D.M ≃* PSL(2, GaloisField p k)) ∧ (B.S : Subgroup G) ≤ layerIn D.M

/-- `Case2CountProp`, with the bundle and the §4 data `(1)`–`(9)` supplied.  This is §4 (7)–(12):
the case analysis producing the numbers `q, k, k', p, p₀, p₁, u` violating `Case2ArithProp`. -/
def Case2CountImpl (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    Case2 B → Case2Ctx B → ∃ (q k k' p p0 p1 u : ℕ), 7 ≤ q ∧ Odd q ∧
      ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧ Even k ∧
      p.Prime ∧ 3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p ∧
      (((q * k' * (p1 - 1) * (q * k')) : ℚ) *
          (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p) ≤
        6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3)

/-! ## The merged §4 tail: (7)–(12) as a single leaf

Bender's §4 from (7) on is one unbroken argument, carried by the objects introduced on p. 225
(`P ≤ F` of prime order `p`, the `(p,p)`-subgroup `A ≤ F × K₁`, `p₀, p₁, u`, `π`): (7),(8) feed the
elimination of `A₇`, then (9) (`E ≅ L₂(q)`, `Z(E) = 1`, `q ≥ 7`, `S ≤ E`), then (10),(11),(12).
Three independent provers of the separate leaves `Case2NotA7` and `Case2Nine` — and the first
prover of `Case2Count` — reported that these objects are not part of any leaf's hypotheses
(see `NOTES_CORE4.md` §6 and `NOTES_CASE2NINE.md`): the fine split needs a `Case2SevenEight`
object layer which the design did not specify.

`Case2TailImpl` below is the merged target, stated exactly as `Case2CountImpl` but from the
data `(1)`–`(6)` alone: it absorbs (7), (8), the `A₇` elimination, (9) and the counting of
(10)–(12).  It is *implied by* the fine split (`Assembly.case2Tail_of_parts`), so proving the
separate leaves also delivers it; and it can be attacked on its own without the missing layer. -/

/-- The §4 data `(1)`–`(6)`: the objects `M, X, s, K, B₀, F` with (1)–(5) and (6). -/
structure Case2Ctx6 {G : Type} [Group G] [Finite G] (B : BenderSetup G) where
  /-- the §4 objects `M, X, s, K, B₀, F` -/
  D : Case2Data B
  /-- §4 (1)–(5) -/
  pre : Case2Pre B D
  /-- §4 (6), first half -/
  F_ti : ∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥
  /-- §4 (6), second half -/
  F_cyclic : IsCyclic D.F

/-- §4 (7)–(12), merged: from the data `(1)`–`(6)` alone, produce Bender's numbers and (12). -/
def Case2TailImpl (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    Case2 B → Case2Ctx6 B → ∃ (q k k' p p0 p1 u : ℕ), 7 ≤ q ∧ Odd q ∧
      ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧ Even k ∧
      p.Prime ∧ 3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p ∧
      (((q * k' * (p1 - 1) * (q * k')) : ℚ) *
          (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p) ≤
        6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3)


/-! ## 9. Design pass 9: the §4 (7)–(8) object layer (copied verbatim from `_design_gw/Core9.lean`)

The design pass 9 rulings (settled from 500-dpi page images of Bender pp. 225–228):

* (7) `O₂(H ∩ M) = O₂(H)` and `π(K F(M) [S∩M, B]) = π(C_U(K₀F)) = π = π(K₀)`, `π := π(F(U))`
  — it is `C_U`, not `C_H`.
* (8) `|U : B K F(U)| ≤ p` and, *unless `I_U(s) ⊲ Ĥ`*, `u ≤ p` and `A ⊲ F(U)`; all bounds are `≤`.
* `2p ≤ k` (not `p < k/2`), `q ≥ 7`.
* `Case2Pre` drops Bender's Sylow condition `S ∩ M ∈ Syl₂(M)` and (1),(2); `Case2PrePlus` adds them.
-/

section Layer

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Objects -/

/-- Bender's `K₀ := F(U) ∩ K` (p. 225, display (3)). The CORE4 files call it `K₁`. -/
def Case2Data.K0 {B : BenderSetup G} (D : Case2Data B) : Subgroup G :=
  fittingIn B.U ⊓ D.K

/-- Bender's `π := π(F(U))` (p. 225, line before (7)). Not `BenderSetup.pi`, which is
`π(F(Ĥ))`. -/
abbrev BenderSetup.piFU (B : BenderSetup G) : Set ℕ :=
  primesOf (fittingIn B.U)

/-- `u := |U : N_U(A)|`. -/
noncomputable def Case2EightU (B : BenderSetup G) (A : Subgroup G) : ℕ :=
  (B.U ⊓ normalizer (A : Set G)).relIndex B.U

/-- `p₀ := |N_U(A) : N_U(P)|`. -/
noncomputable def Case2EightP0 (B : BenderSetup G) (P A : Subgroup G) : ℕ :=
  (B.U ⊓ normalizer (P : Set G)).relIndex (B.U ⊓ normalizer (A : Set G))

/-- `p₁ :=` the number of `G`-conjugates of `P` lying in `A`. -/
noncomputable def Case2EightP1 (P A : Subgroup G) : ℕ :=
  {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = conjSub g P}.ncard

/-! ## 1. The missing pieces of §4 (1)–(2) -/

/-- What `Case2Pre` leaves out of Bender's (1)–(2), p. 224–225.

* `S ∩ M ∈ Syl₂(M)`. This is Bender's choice of `S` ("`C_M(t)` contains an `S₂`-subgroup of `M`,
  say `S ∩ M`"). It is not implied by `Case2Pre`. It is needed for `S ∩ E ∈ Syl₂(E)` in (1), for
  `S ≤ E` in the `A₇` case, and for `S ≤ E` in (9).
* (1) `K = [S ∩ E, U ∩ M]`. This gives `K ⊴ H ∩ M = (U ∩ M)(S ∩ M)`, which (7) uses.
* (2) `B = C_{U∩M}(S ∩ E)`. With (5) this gives `C_{F(U)}(S ∩ E) = F`, which (9) uses
  ("`N_S(S∩E)` normalizes `C_{F(U)}(S∩E) = F`").

(3) `F(U) ∩ M = K₀F` is not listed: it is derivable from `Case2Pre` (`CORE4/SixThree.lean`,
proved). -/
def Case2PrePlus (B : BenderSetup G) (D : Case2Data B) : Prop :=
  ¬ 2 ∣ ((B.S : Subgroup G) ⊓ D.M).relIndex D.M ∧
  D.K = ⁅(B.S : Subgroup G) ⊓ layerIn D.M, B.U ⊓ D.M⁆ ∧
  D.B0 = (B.U ⊓ D.M) ⊓
    centralizer ((((B.S : Subgroup G) ⊓ layerIn D.M : Subgroup G)) : Set G)

/-! ## 2. §4 (7) -/

/-- Bender §4 (7), p. 225, as printed, with the product `K F(M) [S∩M, B]` split into its three
factors.

Route (Bender): `F` and `K₀` are cyclic and normal in `H ∩ M` (`K ⊴ H ∩ M` by (1) and the Sylow
choice), so `(H ∩ M)'` centralizes `K₀F`. By 1.1(iv) (`I.toolkit.c11iv`), every `π'`-subgroup
of `H` centralizing `K₀F = N_{F(U)}(F)` lies in `C_H(F(U)) = O₂(H) × Z(F(U))`.
* `O₂(H ∩ M) ≤ O₂(H)` follows from this.
* `O₂(H) ≤ C_H(F(U)) ≤ N_G(X) ≤ M` gives the reverse inclusion.
* `π(K₀) = π`: for `r ∈ π ∖ π(K₀F)`, `O_r(F(U))` centralizes `X ≤ K₀F`, so it lies in `M`, so it
  lies in `F(U) ∩ M = K₀F`, so it is trivial. Then `π(F) ⊆ π(K₀)` by (6).
* `F(M)` is odd (`O₂(M)` centralizes the dihedral `S ∩ E`), and `F(M) ≤ C_M(E) ≤ H ∩ M`, hence
  `F(M) ≤ O(H ∩ M) = U ∩ M`. Its `π'`-part centralizes `F` (coprime normal subgroups) and `K₀`
  (`K₀ ≤ E`), so it lies in `C_U(K₀F)`, which is a `π`-group.
* `K` and `[S ∩ M, B]` lie in `(H ∩ M)' ∩ U ≤ C_U(K₀F)`. -/
def Case2SevenFacts (B : BenderSetup G) (D : Case2Data B) : Prop :=
  pCoreIn 2 (B.H ⊓ D.M) = pCoreIn 2 B.H ∧
  primesOf D.K0 = B.piFU ∧
  primesOf (B.U ⊓ centralizer (((D.K0 ⊔ D.F : Subgroup G)) : Set G)) = B.piFU ∧
  primesOf D.K ⊆ B.piFU ∧
  primesOf (fittingIn D.M) ⊆ B.piFU ∧
  primesOf ⁅(B.S : Subgroup G) ⊓ D.M, D.B0⁆ ⊆ B.piFU

/-! ## 3. §4 (8) -/

/-- The objects of p. 225: `p` prime, `P ≤ F` of order `p`, `A` the unique subgroup of type
`(p,p)` of `F × K` (equivalently of `F × K₀`: `K` is cyclic and `p ∣ |K₀|`), with `P ≤ A`.
The shape matches the in-flight `CORE4/Case2Numeric.lean` and `Case2LowerBound.lean`. -/
def Case2EightObj {B : BenderSetup G} (D : Case2Data B) (p : ℕ) (P A : Subgroup G) : Prop :=
  p.Prime ∧ P ≤ D.F ∧ Nat.card P = p ∧
  A ≤ D.F ⊔ D.K ∧ Nat.card A = p ^ 2 ∧ (∀ x ∈ A, x ^ p = 1) ∧ P ≤ A ∧
  ∀ A' : Subgroup G, A' ≤ D.F ⊔ D.K → Nat.card A' = p ^ 2 → (∀ x ∈ A', x ^ p = 1) → A' = A

/-- Bender's exceptional clause in (8): `I_U(s) ⊲ H̃`. By Coprime15 (`I.toolkit.c15`),
`I_U(s)` is a subgroup. -/
def Case2InvNormal (B : BenderSetup G) (D : Case2Data B) : Prop :=
  ∃ I : Subgroup G, (I : Set G) = invSet B.U D.s ∧ I ≤ B.Hhat ∧ (I.subgroupOf B.Hhat).Normal

/-- Bender §4 (8), p. 225–226, together with "obviously `p₀ ≤ p₁ ≤ p + 1`, hence `p₀ ≤ p`".

Route (Bender p. 226): put `Q := Ω₁(Z₂(O_p(U)))`, which is non-cyclic of exponent `p`. Then
exactly one of the following holds.
1. `Q ≤ M`. Then `Q = A`, `N_U(A) = U`, `u = 1`, and `p₀ = |U : U ∩ M|`.
2. `Z(Q) < A < Q` with `|Q : A| = p`. Then `u ≤ p + 1`, so `u ≤ p` (odd), and
   `N_U(A) = N_U(P)Q = BKF(U)`, so `p₀ = |Q : Q ∩ M|`, a power of `p` greater than 1. Also
   `A ⊴ O_p(U)`, since `[Q, O_p(U)] ≤ Z(Q) ≤ A`.
3. `s` inverts `Q`. Then `U = BF(U)` and `I_U(s) = F(C_U(Q))`, which is characteristic in `U`,
   so `I_U(s) ⊲ H̃` (`U ⊴ H̃` by Theorem 2.6).

The last conjunct `¬ U ≤ M → 3 ≤ p₀` covers cases 1–2. In the `L₂(q)` case, `U ⊄ M` holds
because `H = U S`, `S ≤ E ≤ M` and `H ⊄ M`. -/
def Case2EightFacts (B : BenderSetup G) (D : Case2Data B) (p : ℕ) (P A : Subgroup G) : Prop :=
  p ∣ Nat.card D.K0 ∧ A ≤ D.F ⊔ D.K0 ∧
  B.U ⊓ normalizer (P : Set G) = B.U ⊓ D.M ∧
  B.U ⊓ normalizer (P : Set G) ≤ normalizer (A : Set G) ∧
  Odd (Case2EightP0 B P A) ∧
  Case2EightP0 B P A ≤ Case2EightP1 P A ∧ Case2EightP1 P A ≤ p + 1 ∧
  Case2EightP0 B P A ≤ p ∧
  (D.B0 ⊔ D.K ⊔ fittingIn B.U).relIndex B.U ≤ p ∧
  (Case2InvNormal B D ∨
    (Case2EightU B A ≤ p ∧ (A.subgroupOf (fittingIn B.U)).Normal ∧
      (¬ B.U ≤ D.M → 3 ≤ Case2EightP0 B P A)))

/-- (8) for every choice of `P` (Bender's `P` is an arbitrary subgroup of prime order of `F`). -/
def Case2EightAll (B : BenderSetup G) (D : Case2Data B) : Prop :=
  ∀ (p : ℕ) (P : Subgroup G), p.Prime → P ≤ D.F → Nat.card P = p →
    ∃ A : Subgroup G, Case2EightObj D p P A ∧ Case2EightFacts B D p P A


end Layer

/-! ## 4. The leaves -/

/-- §4 (1)–(5), restated. The leaf may replace `B` by an `H`-conjugate `B'` (same `t`, same `H`,
same `U`, so `Case2 B' ↔ Case2 B`). This is Bender's "say `S ∩ M`": a Sylow 2-subgroup of
`C_M(t)` is Sylow in `M` (`M = E C_M(t)`, one class of involutions in `E`) and lies in some
`S^h`, `h ∈ H`. Every downstream leaf quantifies over all `B`, so the change of `B` is free. -/
def Case2SetupImpl9 (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G, Case2 B →
    ∃ B' : BenderSetup G, B'.t = B.t ∧ Case2 B' ∧
      ∃ D : Case2Data B', Case2Pre B' D ∧ Case2PrePlus B' D

/-- §4 (6) with the extra (1)–(2) data. This is the old `Case2SixImpl` plus the hypothesis
`Case2PrePlus`, so it only gets easier. -/
def Case2SixImpl9 (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    ∀ D : Case2Data B, Case2Pre B D → Case2PrePlus B D →
      (∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥) ∧ IsCyclic D.F

/-- NEW LEAF `Case2Seven`: §4 (7) from (1)–(6). -/
def Case2SevenImpl (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G, Case2 B →
    ∀ C : Case2Ctx6 B, Case2PrePlus B C.D → Case2SevenFacts B C.D

/-- NEW LEAF `Case2Eight`: §4 (8) from (1)–(7), for every `P`. -/
def Case2EightImpl (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G, Case2 B →
    ∀ C : Case2Ctx6 B, Case2PrePlus B C.D → Case2SevenFacts B C.D → Case2EightAll B C.D

/-- RESTATED `Case2NotA7` (p. 226): the old hypotheses plus `Case2 B`, `Case2PrePlus`, (7), (8). -/
def Case2NotA7Impl9 (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G, Case2 B →
    ∀ C : Case2Ctx6 B, Case2PrePlus B C.D → Case2SevenFacts B C.D → Case2EightAll B C.D →
      IsEmpty ((↥(layerIn C.D.M) ⧸ center ↥(layerIn C.D.M)) ≃* alternatingGroup (Fin 7))

/-- RESTATED `Case2Nine` (p. 226–227): the same hypotheses plus `E/Z(E) ≇ A₇`. Conclusion
unchanged (= `Case2Ctx.nine`).
* `Z(E) = 1`: `Z(E) ≤ F(M)`, which is a `π`-group by (7); `π = π(K₀) ⊆ π(K)`, and the primes of
  `|K|` divide `k`, which is prime to `q`. Then use `I.toolkit.l19`.
* `7 ≤ q`: `K₀ ≠ 1`, and `|K₀|` is odd and divides the even half `k` of `q ± 1`. That excludes
  `q ∈ {5, 7, 9}`; see also `seven_le_of_numeric`.
* `S ≤ E`: `|R^y| ≤ p` by (8) (`|U : BKF(U)| ≤ p`), with `|R^y| = k'`; and `p ≤ |K| ≤ k/2`
  because `p ∣ |K₀|`. -/
def Case2NineImpl9 (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G, Case2 B →
    ∀ C : Case2Ctx6 B, Case2PrePlus B C.D → Case2SevenFacts B C.D → Case2EightAll B C.D →
      IsEmpty ((↥(layerIn C.D.M) ⧸ center ↥(layerIn C.D.M)) ≃* alternatingGroup (Fin 7)) →
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 7 ≤ p ^ k ∧
          Nonempty (layerIn C.D.M ≃* PSL(2, GaloisField p k)) ∧
          (B.S : Subgroup G) ≤ layerIn C.D.M

/-- RESTATED `Case2Count`: the old hypotheses plus `Case2PrePlus`, (7), (8). Conclusion
unchanged. -/
def Case2CountImpl9 (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    Case2 B → ∀ h : Case2Ctx B, Case2PrePlus B h.D → Case2SevenFacts B h.D →
      Case2EightAll B h.D →
      ∃ (q k k' p p0 p1 u : ℕ), 7 ≤ q ∧ Odd q ∧
        ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧ Even k ∧
        p.Prime ∧ 3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧
        1 ≤ u ∧ u ≤ p ∧
        (((q * k' * (p1 - 1) * (q * k')) : ℚ) *
            (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p) ≤
          6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3)

/-- RESTATED `Case2Numeric`: the in-flight statement (`CORE4/Case2Numeric.lean`) with the layer
added as hypotheses.
* `p₀ ≤ p₁ ≤ p+1`, `p₀ ≤ p`, odd `p₀`, `p ∣ |K₀|` come straight from `Case2EightAll`.
* The exceptional clause is excluded as follows. `S ≤ E` gives `[S₀, U] = 1` (Bender p. 227:
  `S₀ = O₂(H ∩ E) = O₂(H) = C_S(U)`). Lemma 2.8 (`I.lem28`, contrapositive) then gives some
  `s' ∈ S ∖ S₀` with `I_U(s')` not normal in `U`. Since `S ∖ S₀ = s S₀` and `S₀` centralizes
  `U`, `I_U(s') = I_U(s)`, so `¬ Case2InvNormal` (`s ∉ S₀` because `K ≠ 1`).
* `3 ≤ p₀`: `¬ U ≤ M`, from `H = U S`, `S ≤ M` and `¬ H ≤ M`.
* `2 * p ≤ k`: `p ∣ |K₀|` divides `|K|`, and `k = |K| |S₀|` with `|S₀| ≥ 2`. -/
def Case2NumericImpl9 (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G →
    ∀ (B : BenderSetup G) (h : Case2Ctx B), Case2 B → Case2PrePlus B h.D →
      Case2SevenFacts B h.D → Case2EightAll B h.D →
        ∃ (q k k' p : ℕ) (P A : Subgroup G) (u p0 p1 : ℕ),
          Odd q ∧ 7 ≤ q ∧ Even k ∧ Odd k' ∧
          ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = q * k' ∧
          k = Nat.card ↥h.D.K * Nat.card ↥B.S0 ∧ p ∣ Nat.card ↥h.D.K ∧
          Case2EightObj h.D p P A ∧
          u = Case2EightU B A ∧ p0 = Case2EightP0 B P A ∧ p1 = Case2EightP1 P A ∧
          (h.D.M ⊓ B.H).relIndex B.H = u * p0 ∧
          3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p


end Work.GW2
