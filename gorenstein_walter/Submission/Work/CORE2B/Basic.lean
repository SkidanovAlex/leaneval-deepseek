import Submission.Work.CORE2B.Defs

/-!
# AREA CORE2B — interface: hypothesis bundles and leaf `Prop`s

Bender 1981, §2, pp. 221–222:
* **Lemma 2.7**  `[M,t] ⊆ F_{π'}(M)`, `[S,U] ⊄ F(U)`, `M` solvable.
* **Lemma 2.8**  `[S₀,U] ≠ 1`, and `t ∈ E(M)` whenever `Ĥ ⇝ M ≠ Ĥ` and `S ≤ M`.
* **Lemma 2.9**  `V ∩ O₂(N) ≠ 1` or `V ∩ E(N) ≠ 1`.
* **Theorem 2.10** the dichotomy `Case1 ∨ Case2`.

This file fixes the *shape* of the four deliverables (`Lemma27Prop`, `Lemma28Prop`,
`Lemma29Prop`, `Thm210Prop`, copied verbatim into `Work.GW2` by `Defs.lean`) and splits each
into the leaf `Prop`s of Bender's proof, in a form a prover can attack:

* the hypotheses of a lemma are bundled into a **`Prop`-valued** `structure` (`L27Hyp`,
  `L28Hyp`, `L28MHyp`, `L29Hyp`) — all the *data* (`M`, `V`, `N`) stay explicit arguments, so a
  leaf conclusion mentions them directly and no structure projections have to unfold;
* a leaf `Prop` is closed under the inputs the design allots to the area
  (`LocalToolkit`, and `Lemma22Prop` / `Lemma23Prop` / `Thm26Prop`, always as *leading* `∀`s
  so that the prover may use them), then `FeitThompsonProp → BenderCtx G →` and the data;
* `Deliverable.lean` proves the four contract `Prop`s from the leaves by pure logic; the
  mathematical content is exactly the leaves.

The mapping leaf ↔ sentence of Bender is in `NOTES_CORE2B.md`.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false

namespace Work.CORE2B

open Subgroup

/-! ## 0. The four deliverables, as names of this area -/

abbrev Lemma27Prop := Work.GW2.Lemma27Prop
abbrev Lemma28Prop := Work.GW2.Lemma28Prop
abbrev Lemma29Prop := Work.GW2.Lemma29Prop
abbrev Thm210Prop := Work.GW2.Thm210Prop

/-! ## 0b. `U ≠ 1` (Bender 2.2's rider) -/

/-- `U = O(C(t))` is not trivial.  This is Bender's Lemma 2.2 ("In particular, U is not trivial"):
if `U = ⊥` then all three clauses of 2.2's forbidden configuration hold vacuously, so `Lemma22Prop`
forbids it.  (The contract `Core6.lean` §1 states `UNeBotProp` without the `Lemma22Prop` input;
the provable form takes it, see `UNeBotProp_of_h22`.) -/
def UNeBotProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ B : Work.GW2.BenderSetup G, B.U ≠ ⊥

/-- The provable form of `UNeBotProp`: with Bender 2.2 available, `U ≠ ⊥`. -/
def UNeBotProp_of_h22 : Prop :=
  Work.GW2.Lemma22Prop → UNeBotProp

/-! ## 1. Lemma 2.7 -/

/-- Hypotheses of Bender's Lemma 2.7 for a fixed `M` (contract `Lemma27Prop`). -/
structure L27Hyp {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) : Prop where
  M_ne_top : M ≠ ⊤
  rel : Work.GW2.BRel B.Hhat M
  not_le : ¬ M ≤ B.Hhat
  t_mem : B.t ∈ M
  /-- `t ∉ E(M)`. -/
  t_not_layer : B.t ∉ Work.GW2.layerIn M
  /-- Sylow 2-subgroups of `M` are not cyclic. -/
  sylow_nc : ∀ P : Sylow 2 M, ¬ IsCyclic P
  /-- `|S ∩ M| > 8` or `|S| = 4` or `t ∈ O²(M)`. -/
  size : 8 ≤ Nat.card ((B.S : Subgroup G) ⊓ M : Subgroup G) ∨
    Nat.card (B.S : Subgroup G) = 4 ∨ B.t ∈ Work.GW2.twoResidualIn M

/-- **Convenience bundle, NOT the contract.**  `L27Hyp` plus `IsCoatom M` and the reverse relation
`M ⇝ Ĥ`.  It was introduced while the area believed Bender's step (4) needed maximality of `M`;
the lead's design pass 12 (`NOTES_LEAD_gw_design12.md`) showed that it does **not** (`M ≠ ⊤` is
correct, Bender applies Lemma 2.7 to non-maximal `M` on pp. 222 and 225), and the contract leaf
`L27_commutator_le` is now proved with `L27Hyp` (`Submission.Work.CORE2B.L27_v12_assembly`).  This
structure is kept only because a support file refers to it. -/
structure L27HypS {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) : Prop where
  toHyp : L27Hyp B M
  /-- `M` is maximal. -/
  coatom : IsCoatom M
  /-- `M ⇝ Ĥ`. -/
  rel_rev : Work.GW2.BRel M B.Hhat

/-- *Step 1 of Lemma 2.7*: every normal subgroup of `M` of order divisible by `4` contains
`t`. (Bender: "Our assumptions force every normal subgroup of `M` of order divisible by 4 to
contain `t`.") -/
def L27_normal_contains_t : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M → ∀ N : Subgroup G,
      N ≤ M → (N.subgroupOf M).Normal → 4 ∣ Nat.card N → B.t ∈ N

/-- *Step 2 of Lemma 2.7*: `E(M) = 1`. -/
def L27_layer_eq_bot : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M → Work.GW2.layerIn M = ⊥

/-- *Step 3 of Lemma 2.7*, first half: `t` centralizes `F₂(M)`.  (Since `t ∈ O₂(Ĥ) ≠ 1`, the prime
`2` lies in `π = π(F(Ĥ))`, so `F₂(M) ≤ F_π(M)`; Bender's sentence is about `F_π(M)`.) -/
def L27_two_part_centralized : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M →
      Work.GW2.fittingPiIn {2} M ≤ centralizer ({B.t} : Set G)

/-- *Step 3 of Lemma 2.7*, second half: `t` inverts `F_{π'}(M)` (Bender's `F_{π'}(M)`, the same `π`
as in the conclusion of Lemma 2.7 — Lemma 2.3(ii) gives `F_{π'}(M) ∩ Ĥ = 1`; the odd `π`-part of
`F(M)` is *centralized*, not inverted). -/
def L27_odd_part_inverted : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M →
      Work.GW2.Inverts B.t (Work.GW2.fittingPiIn B.piᶜ M)

/-- *Lemma 2.7 (a)*: `[M,t] ⊆ F_{π'}(M)`, with `π = π(F(Ĥ))`. -/
def L27_commutator_le : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M →
      ⁅M, zpowers B.t⁆ ≤ Work.GW2.fittingPiIn B.piᶜ M

/-- *Lemma 2.7 (b)*: `[S,U] ⊄ F(U)`. -/
def L27_su_not_le : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G) (_D : L27Hyp B M),
      ¬ ⁅(B.S : Subgroup G), B.U⁆ ≤ Work.GW2.fittingIn B.U

/-- *Lemma 2.7 (b), with Bender 2.2 available.*  Bender's proof of `[S,U] ⊄ F(U)` uses
"`U` is not trivial", which is Lemma 2.2 ("In particular, `U` is not trivial"); the configuration of
2.2 is unavailable from `LocalToolkit`/`Lemma23Prop`/`Thm26Prop` alone, and with `U = ⊥` the
statement `[S,U] ⊄ F(U)` is *false* (`[S,U] = ⊥ = F(U)`).  Since `Lemma22Prop` is a CORE2A
deliverable that is already in scope at every CORE2B call site (see `Contracts2.lean` §6, where
`h22` precedes `h27`), this variant takes it as an input.  It is the version to prove. -/
def L27_su_not_le_h22 : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h22 : Work.GW2.Lemma22Prop) (_h23 : Work.GW2.Lemma23Prop)
    (_h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G) (_D : L27Hyp B M),
      ¬ ⁅(B.S : Subgroup G), B.U⁆ ≤ Work.GW2.fittingIn B.U

/-- *Lemma 2.7 (c)*: `M` is solvable. -/
def L27_solvable : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M → Group.IsSolvable ↥M

/-! ### Lemma 2.7 under the hypotheses its proof consumes (`L27HypS`) -/

/-- *Lemma 2.7 (a)* with the maximality inputs available. -/
def L27_commutator_leS : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27HypS B M →
      ⁅M, zpowers B.t⁆ ≤ Work.GW2.fittingPiIn B.piᶜ M

/-- *Lemma 2.7 (b)* with the maximality inputs and Bender 2.2 available. -/
def L27_su_not_le_h22S : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h22 : Work.GW2.Lemma22Prop) (_h23 : Work.GW2.Lemma23Prop)
    (_h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G) (_D : L27HypS B M),
      ¬ ⁅(B.S : Subgroup G), B.U⁆ ≤ Work.GW2.fittingIn B.U

/-- *Lemma 2.7 (c)* with the maximality inputs available. -/
def L27_solvableS : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27HypS B M → Group.IsSolvable ↥M

/-- **The contract `Lemma27Prop` with the hypotheses its proof consumes**: `IsCoatom M` (and the
reverse relation `M ⇝ Ĥ`) in place of `M ≠ ⊤`.  This is the corrected form recommended in
`NOTES_CORE2B.md` §4; every use of Lemma 2.7 in Theorem 2.10 and in §4 has a maximal `M`. -/
def Lemma27PropS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27HypS B M →
      ⁅M, zpowers B.t⁆ ≤ Work.GW2.fittingPiIn B.piᶜ M ∧
      ¬ ⁅(B.S : Subgroup G), B.U⁆ ≤ Work.GW2.fittingIn B.U ∧ Group.IsSolvable ↥M

/-! ## 2. Lemma 2.8 -/

/-- Hypothesis of Lemma 2.8: `I_U(s) ⊴ U` for every `s ∈ S − S₀`
(`I_U(s) := {x ∈ U | x^s = x⁻¹}`). -/
structure L28Hyp {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) : Prop where
  inv_normal : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 →
    ∃ I : Subgroup G, (I : Set G) = Work.GW2.invSet B.U s ∧ (I.subgroupOf B.U).Normal

/-! ### The single remaining gap of Lemma 2.7(a)

Everything else in Bender's proof of `[M,t] ⊆ F_{π'}(M)` is formalised sorry-free in the area
(`L27_commutator_le_final.lean`: `L27fin_pi_centralized`, `L27fin_cent`, `L27fin_KF`,
`L27fin_odd_of_O2_bot`, and the reduction `L27_commutator_le_of_O2_bot`), so that the leaf is
equivalent to Bender's step (4), `O₂(M) = 1`.  The area's provers identified the input that step
needs: Bender's sentence "*As `O₂(M)` centralizes `M ∩ F(U)`, 1.1.iv implies `[O₂(M),U] = 1`,
hence `O₂(M) ≤ O₂(Ĥ)`, hence `O₂(M) = 1` (otherwise `N_G(O₂(M)) ⊆ Ĥ`)*" — i.e. that `O₂(M)`
centralizes `F(U)`, equivalently that `Ĥ` normalizes `O₂(M)`
(`L27fin_O2_eq_bot : Ĥ ≤ N_G(O₂(M)) → O₂(M) = ⊥`, sorry-free).  -/

/-- Bender's step (4) of Lemma 2.7: `O₂(M) = 1`. -/
def L27_O2M_eq_bot : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M → Work.GW2.pCoreIn 2 M = ⊥

/-- **Bender's step (4) with its input made explicit**: if `O₂(M)` centralizes `F(U)`, then
`O₂(M) = 1`.  (`[O₂(M),U] = 1` by 1.1.iv — `U` is solvable, `C_U(F(U)) ≤ F(U)` — and then
`O₂(M) ≤ C_Ĥ(U)` is a normal 2-subgroup of `Ĥ`, hence inside `O₂(Ĥ)`.) -/
def L27_O2M_eq_bot_of_centralizes : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M →
      Work.GW2.pCoreIn 2 M ≤ centralizer (Work.GW2.fittingIn B.U : Set G) →
        Work.GW2.pCoreIn 2 M = ⊥

/-- The contract's hypotheses plus Bender's step-(4) input `O₂(M) ≤ C_G(F(U))`. -/
structure L27HypC {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) : Prop where
  toHyp : L27Hyp B M
  centralizes : Work.GW2.pCoreIn 2 M ≤ centralizer (Work.GW2.fittingIn B.U : Set G)

/-- *Lemma 2.7 (a)* with Bender's step-(4) input. -/
def L27_commutator_leC : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27HypC B M →
      ⁅M, zpowers B.t⁆ ≤ Work.GW2.fittingPiIn B.piᶜ M

/-- The second half of Lemma 2.8 needs `M` with `Ĥ ⇝ M ≠ Ĥ` and `S ≤ M`. -/
structure L28MHyp {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) : Prop where
  M_ne_top : M ≠ ⊤
  rel : Work.GW2.BRel B.Hhat M
  not_le : ¬ M ≤ B.Hhat
  S_le_M : (B.S : Subgroup G) ≤ M

/-- *Lemma 2.8, first assertion*: `[S₀,U] ≠ 1`. -/
def L28_S0U_ne_bot : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h22 : Work.GW2.Lemma22Prop)
    (_h27 : Work.GW2.Lemma27Prop) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G), L28Hyp B → ⁅B.S0, B.U⁆ ≠ ⊥

/-- *Lemma 2.8, first assertion, with Theorem 2.6 available.*  Bender's proof needs Theorem 2.6
(the dichotomy `S ⊓ C(U) = O₂(Ĥ)`: if this is `S₀` then `Ĥ = H`), which the design's input list
`(T, h22, h27)` for `lemma28` omits — even though `h26` precedes `h28` at every call site
(`Contracts2.lean` §6).  This is the version to prove. -/
def L28_S0U_ne_bot_h26 : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h22 : Work.GW2.Lemma22Prop) (_h26 : Work.GW2.Thm26Prop)
    (_h27 : Work.GW2.Lemma27Prop) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G), L28Hyp B → ⁅B.S0, B.U⁆ ≠ ⊥

/-- *Lemma 2.8, second assertion*: `t ∈ E(M)`. -/
def L28_t_mem_layer : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h22 : Work.GW2.Lemma22Prop)
    (_h27 : Work.GW2.Lemma27Prop) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G), L28Hyp B → ∀ (M : Subgroup G), L28MHyp B M →
      B.t ∈ Work.GW2.layerIn M

/-! ## 3. Lemma 2.9 -/

/-- Hypotheses of Bender's Lemma 2.9: `V ≤ N ≤ G`, `V ≤ S`, `t ∈ V`, `V` of type (2,2), and
`t ∈ O₂(N_G(X))` for every `1 ≠ X = [s,X] ≤ U`, `s ∈ S`. -/
structure L29Hyp {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (V N : Subgroup G) : Prop where
  V_le_N : V ≤ N
  N_ne_top : N ≠ ⊤
  V_le_S : V ≤ (B.S : Subgroup G)
  t_mem : B.t ∈ V
  four : Work.GW2.IsFourGroup V
  hyp : ∀ (s : G) (X : Subgroup G), s ∈ (B.S : Subgroup G) → X ≤ B.U → X ≠ ⊥ →
    ⁅zpowers s, X⁆ = X → B.t ∈ Work.GW2.pCoreIn 2 (normalizer (X : Set G))

/-- *Lemma 2.9, contradiction form* (what Bender's proof produces): if both
`V ∩ O₂(N) = 1` and `V ∩ E(N) = 1` then `False`. -/
def L29_contra : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (V N : Subgroup G), L29Hyp B V N →
      V ⊓ Work.GW2.pCoreIn 2 N = ⊥ → V ⊓ Work.GW2.layerIn N = ⊥ → False

/-- *Lemma 2.9*, as in the contract: `V ∩ O₂(N) ≠ 1` or `V ∩ E(N) ≠ 1`. -/
def L29_two_core_or_layer : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (V N : Subgroup G), L29Hyp B V N →
      V ⊓ Work.GW2.pCoreIn 2 N ≠ ⊥ ∨ V ⊓ Work.GW2.layerIn N ≠ ⊥

/-! ## 4. Theorem 2.10 -/

/-- *Theorem 2.10, contradiction form*: not both cases fail. -/
def Thm210_contra : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h26 : Work.GW2.Thm26Prop) (_h27 : Work.GW2.Lemma27Prop)
    (_h28 : Work.GW2.Lemma28Prop) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
    ¬ Work.GW2.Case1 B → ¬ Work.GW2.Case2 B → False

end Work.CORE2B
