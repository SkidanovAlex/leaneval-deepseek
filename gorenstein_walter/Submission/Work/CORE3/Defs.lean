import Submission.Work.CORE2A.Defs
import Submission.Work.A7REC.Defs

/-!
# CORE3: elimination of case (1) of Bender's Theorem 2.10

Area `CORE3` of the `gorenstein_walter` build.  Deliverable: `Work.GW2.Case1FalseProp`
(Bender 1981, *Finite groups with dihedral Sylow 2-subgroups*, J. Algebra 70, §3, pp. 222–224).

Sources on disk:
* `Submission/Work/lead_gw_prior/bender2_1981.txt` (Bender 1981, the paper containing §3);
* `Submission/Work/lead_gw_prior/bg1981.txt` (Bender–Glauberman 1981, Theorems A/B/C);
* `Submission/Work/NOTES_LEAD_gw_design2.md` §11 (the leaf list);
* `Submission/Work/_design_gw/Core2.lean` §E (the verbatim statements).

## What lives where (important for imports)

The shared `Work.GW2` vocabulary is *not* re-declared here:

* `Submission/Work/ASM/Defs.lean` is its canonical home (`BenderCtx`, `BenderSetup`, `Case1`,
  `Case2`, `LocalToolkit`, `Lemma22Prop`, `Thm26Prop`, `Lemma29Prop`, `BGThmCProp`,
  `A7RecProp`, `Case1FalseProp`, …);
* `Submission/Work/CORE2A/Defs.lean` adds Bender's §2 helpers (`conjSub`, `involutionSet`,
  `OneInvClassIn`, `Inverts`, `cosetInvCount`, `bCount`) to the same namespace.

This module adds only the CORE3 statements of `Core2.lean` §E (`Case1aData`, `Case1aSetupProp`,
…, `Case1bFalseProp`), copied verbatim, plus `Work.CORE3.Case1Inputs`, the bundle of the six
inputs named by the lead (toolkit Props, `Lemma22Prop`, `Thm26Prop`, `Lemma29Prop`,
`BGThmCProp`, `A7RecProp`).

Everything CORE3-specific (the leaf theorems, their support API and the assembly) lives in
namespace `Work.CORE3` in the other modules of this directory.
-/

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

/-! ## E. CORE3 leaves (B81 §3, pp. 222–224). Throughout: `Case1 B`. -/

/-- Subcase `Ĥ = H`: the data fixed at the start of §3. -/
structure Case1aData {G : Type} [Group G] [Finite G] (B : BenderSetup G) where
  t1 : G
  t2 : G
  p : ℕ
  hp : p.Prime
  t1_mem : t1 ∈ (B.S : Subgroup G)
  t2_mem : t2 ∈ (B.S : Subgroup G)
  t1_nmem : t1 ∉ B.S0
  t2_nmem : t2 ∉ B.S0
  t1_order : orderOf t1 = 2
  t2_order : orderOf t2 = 2
  p_mem : p ∈ primesOf (fittingIn B.U)
  /-- `P = O_p(U)` is centralized by `t₁` and inverted by `t₂`. -/
  cent : pCoreIn p B.U ≤ centralizer ({t1} : Set G)
  inv : Inverts t2 (pCoreIn p B.U)

/-- §3, first lines: `Case1 B`, `Ĥ = H` ⇒ the data exist (uses Lemma 2.2: `[S₀,U] ≠ 1`). -/
def Case1aSetupProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → Nonempty (Case1aData B)

/-- §3: with `Vᵢ = ⟨t, tᵢ⟩`, `B₀ = C_U(S)`, `P₂ ∈ Syl_p(B₀)`, `P₁ = P P₂`:
`N_G(P₁) ⊄ H`, `P₁ ≠ P`, `P₂ ≠ 1`. -/
def Case1aFrattiniProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → ∀ D : Case1aData B,
    ∀ P2 : Subgroup G, P2 ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) →
      ¬ normalizer ((pCoreIn D.p B.U ⊔ P2 : Subgroup G) : Set G) ≤ B.H ∧
        pCoreIn D.p B.U ⊔ P2 ≠ pCoreIn D.p B.U ∧ P2 ≠ ⊥

/-- §3: `P ∩ P^g = 1` and `P P^g` is abelian, for `g ∈ N(V₁) − N_H(V₁)`. -/
def Case1aAbelianProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → ∀ D : Case1aData B, ∀ g : G,
      g ∈ normalizer (((zpowers B.t ⊔ zpowers D.t1 : Subgroup G)) : Set G) → g ∉ B.H →
      pCoreIn D.p B.U ⊓ conjSub g (pCoreIn D.p B.U) = ⊥ ∧
        IsMulCommutative (pCoreIn D.p B.U ⊔ conjSub g (pCoreIn D.p B.U) : Subgroup G)

/-- §3: a maximal `M ⊇ N(P₂)` has `E(M)/Z ≅ A₇`, `|S| = 8` and `|P₀| = 3` (`P₀ = P ∩ M`). -/
def Case1aA7Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → ∀ D : Case1aData B, ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → normalizer (P2 : Set G) ≤ M →
      (B.S : Subgroup G) ≤ M ∧ zpowers B.t ⊔ zpowers D.t2 ≤ layerIn M ∧
        Nonempty ((↥(layerIn M) ⧸ center ↥(layerIn M)) ≃* alternatingGroup (Fin 7)) ∧
        Nat.card (B.S : Subgroup G) = 8 ∧ Nat.card (pCoreIn D.p B.U ⊓ M : Subgroup G) = 3

/-- §3, end of subcase `Ĥ = H`: Theorem C applies. Contradiction. -/
def Case1aFalseProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → False

/-- Subcase `V = O₂(Ĥ)` of type (2,2): the Hall subgroup `K` with `K = I_U(s)` for each
involution `s ∈ Ĥ − V`. -/
structure Case1bData {G : Type} [Group G] [Finite G] (B : BenderSetup G) where
  K : Subgroup G
  four : IsFourGroup (pCoreIn 2 B.Hhat)
  S8 : Nat.card (B.S : Subgroup G) = 8
  hall : IsHallIn K (fittingIn B.U)
  ne : K ≠ ⊥
  inv : ∀ s ∈ B.Hhat, orderOf s = 2 → s ∉ pCoreIn 2 B.Hhat → (K : Set G) = invSet B.U s

def Case1bSetupProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → IsFourGroup (pCoreIn 2 B.Hhat) → Nonempty (Case1bData B)

/-- §3 (1)–(4), with `k = |K|`. -/
def Case1bCountProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → ∀ D : Case1bData B,
      (involutionSet B.H).ncard = 3 + 2 * Nat.card D.K ∧
      (involutionSet B.Hhat).ncard = 3 + 6 * Nat.card D.K ∧
      B.H.index = 3 * B.Hhat.index ∧
      (6 * (Nat.card D.K : ℤ) +
        ∑ n ∈ Finset.range (Nat.card B.Hhat + 1), ((n : ℤ) - 3) * bCount B.Hhat n = 0) ∧
      B.Hhat.index = 1 + ∑ n ∈ Finset.range (Nat.card B.Hhat + 1), bCount B.Hhat n

/-- §3 (5): `I_{VU}(y) = 1` for every involution `y ∉ Ĥ`. -/
def Case1bFiveProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → ∀ _D : Case1bData B, ∀ y : G, orderOf y = 2 → y ∉ B.Hhat →
      invSet (pCoreIn 2 B.Hhat ⊔ B.U) y = {1}

/-- §3 (6)–(9): `b_n = 0` for `n ≥ 5`, `3 b₄ + b₂ = 6k²`, and `b₄ ≠ 0 → |U| = k = 3`. -/
def Case1bEightNineProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → ∀ D : Case1bData B,
      (∀ n, 5 ≤ n → bCount B.Hhat n = 0) ∧
      3 * bCount B.Hhat 4 + bCount B.Hhat 2 = 6 * Nat.card D.K ^ 2 ∧
      (bCount B.Hhat 4 ≠ 0 → Nat.card B.U = 3 ∧ Nat.card D.K = 3)

/-- §3 end: `b₀..b₄ = 4,0,18,0,12`, `|G:Ĥ| = 35`, `|G| = 2520`. -/
def Case1bIndexProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → ∀ _D : Case1bData B, B.Hhat.index = 35 ∧ Nat.card G = 2520

/-- §3 end: the 1.8 data hold, so `A7RecProp` applies. Contradiction with `notA7`. -/
def Case1bFalseProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → IsFourGroup (pCoreIn 2 B.Hhat) → False

end Work.GW2

/-! ## CORE3-specific vocabulary

The design pass 4 leaves (`Submission/Work/_design_gw/Core4.lean` §1) and the area's input
bundle.  These new names live in namespace `Work.CORE3` rather than `Work.GW2` so that the
CORE4 area can copy the same statements without a duplicate-declaration clash. -/

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- `Submission/Work/_design_gw/Core4.lean` §1, verbatim: local control gives a Sylow
subgroup.  Used for `(|K|, |G:H|) = 1` in the Theorem C application (subcase `Ĥ = H`), with
`R = O_r(U) ≤ H`. -/
def SylowFromLocalControlProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (r : ℕ) [Fact r.Prime] (H R : Subgroup G),
    R ≤ H → R ≠ ⊥ → IsPGroup r R → ¬ r ∣ R.relIndex H →
    (∀ X : Subgroup G, X ≠ ⊥ → X ≤ R → normalizer (X : Set G) ≤ H) →
    ¬ r ∣ R.index

/-- Design pass 4 §1: in the subcase `Ĥ = H`, *both* `t₁` and `t₂` invert `F_{3'}(U)`.
(Bender p. 222: "Since `p` necessarily is 3, both `tᵢ` invert `F_p(U)`".) -/
def Case1aBothInvertProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → ∀ D : Case1aData B,
      Inverts D.t1 (fittingPiIn ({3}ᶜ) B.U) ∧ Inverts D.t2 (fittingPiIn ({3}ᶜ) B.U)

/-- Design pass 4 §1: the inputs of Bender–Glauberman Theorem C (`Work.GW2.BGThmCProp`) in the
subcase `Ĥ = H`, assembled from the §3 data.

`BG` is the `BGData` of the pair `(B.S, B.S0, B.t, D.t1, D.t2)` (`gen : S₀ = ⟨t₁t₂⟩` follows
because `t₁t₂` acts by inversion on the nontrivial `p`-group `P`, hence is not in `S₀²`).
`K₁ = I_U(t₁)`, `K₂ = I_U(t₂)` are the maximal odd subgroups of `H = C(t)` inverted by `t₁`,
`t₂` (Bender's Case (1) makes `I_U(tᵢ)` Hall in `F(U)`); `U = (B₁ ∩ K₂) × B K` with
`K = K₁ ∩ K₂ = F_{3'}(U)`; `BK` is Frobenius with kernel `K`; `(|K|, |G:H|) = 1`
(`SylowFromLocalControlProp`); and `B' ≠ B`. -/
def Case1aThmCInputsProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → ∀ D : Case1aData B,
      ∃ BG : BGData G, BG.t = B.t ∧ BG.t1 = D.t1 ∧ BG.t2 = D.t2 ∧
        BG.S = B.S ∧ BG.S0 = B.S0 ∧
        ∃ K1 K2 : Subgroup G,
          IsMaxInverted BG.H BG.t1 K1 ∧ IsMaxInverted BG.H BG.t2 K2 ∧
          IsInternalDirect BG.U (BG.B1 ⊓ K2) (BG.B ⊔ (K1 ⊓ K2)) ∧
          Nat.Coprime (Nat.card (K1 ⊓ K2 : Subgroup G)) BG.H.index ∧
          ⁅BG.B, BG.B⁆ ≠ BG.B ∧
          (BG.U ≠ BG.B ⊔ (K1 ⊓ K2) → IsFrobeniusWith (BG.B ⊔ (K1 ⊓ K2)) (K1 ⊓ K2) BG.B)

/-- The extra numerical facts of Bender 1981 §3, p. 224 that `Case1bIndexProp` needs beyond
(1)–(9) (the reviewers of `Work.CORE3.Case1bIndex` pointed out that `hCount` and `h89` alone do
not determine `b₀, b₁, b₃`):

* `12 ∣ b₄` — `KV` acts fixed-point-freely on the cosets contributing to `b₄`;
* `b₁ = 0` — the `J₁`-argument;
* `b₃ = 0` — the `J₃`-argument (`X = I_Ĥ(y)` of order 3, `C_Ĥ(X)` of odd order);
* `|Ĥ| = 72` — `O(Ĥ) = K` (order 3) and `Ĥ/V·K ≅ D₃`. -/
def Case1bNumericsProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → ∀ D : Case1bData B,
      12 ∣ bCount B.Hhat 4 ∧ bCount B.Hhat 1 = 0 ∧ bCount B.Hhat 3 = 0 ∧
        Nat.card B.Hhat = 72

/-! ### Design pass 5 (`Submission/Work/_design_gw/Core5.lean`), the §3b closing constraints -/

/-- B81 p. 224, "Suppose `y ∈ J₃` … This proves `b₃ = 0`".  Verbatim from Core5 (with our
`bCount`). -/
def Case1bThreeProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → IsFourGroup (pCoreIn 2 B.Hhat) → bCount B.Hhat 3 = 0

/-- B81 p. 224, "since `|S| = 8` divides `b₁` (`S` is fixed-point-free on `J₁`)".  Verbatim
from Core5 (with our `bCount`). -/
def Case1bOneProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → IsFourGroup (pCoreIn 2 B.Hhat) → 8 ∣ bCount B.Hhat 1

/-- The closing arithmetic of §3, a pure statement (Core5, verbatim).  Inputs: (4)+(9)
`6k + Σ (n−3) bₙ = 0`; `bₙ = 0` for `n ≥ 5`; `k = 3`, `b₄ = 12`, `b₂ = 18`; `b₃ = 0` and
`8 ∣ b₁`.  Output: `b₁ = 0`, `b₀ = 4`, and `|G:Ĥ| = 1 + Σ bₙ = 35`.  The counter-tuple
`(b₀,…,b₄) = (0,6,18,0,12)` is excluded by `8 ∣ b₁`. -/
def Case1bArithProp : Prop :=
  ∀ (b : ℕ → ℕ) (k N : ℕ), 5 ≤ N → (∀ n, 5 ≤ n → b n = 0) → k = 3 → b 4 = 12 → b 2 = 18 →
    b 3 = 0 → 8 ∣ b 1 →
    6 * (k : ℤ) + ∑ n ∈ Finset.range (N + 1), ((n : ℤ) - 3) * b n = 0 →
    b 1 = 0 ∧ b 0 = 4 ∧ 1 + ∑ n ∈ Finset.range (N + 1), b n = 35

/-! ### Design pass 6 (`Submission/Work/_design_gw/Core6.lean` §3) -/

/-- Bender 1981 p. 223, the `M`-analysis of §3 (subcase `Ĥ = H`).  The design's `Case1aA7Prop`
records only `S ≤ M`, `⟨t,t₂⟩ ≤ E(M)`, `E(M)/Z ≅ A₇`, `|S| = 8`, `|P₀| = 3`; the paragraph that
follows it ("Again by Lemma 2.9, `E(N_G(X))` contains and hence equals `E` whenever
`1 ≠ X ⊆ B ∩ M`, and this implies `N_G(X) ⊆ M`.  Applying this to the normal subgroup
`X = B ∩ PP^g` … we see that `B ⊆ M`") uses the four further facts collected here, with
`B = C_U(S) = B.U ⊓ centralizer (B.S)`:

* `B ≤ M`;
* `B ∩ M = O(M)`;
* `U ∩ M = P₀ × (B ∩ M)` (a `⊔`-decomposition);
* `N_G(X) ≤ M` for every `1 ≠ X ≤ B` (Lemma 2.9, `I.h29`).

These are exactly the facts that `Case1aBFittingProp`, `Case1aBFpfProp` and the Theorem C
assembly need. -/
def Case1aMDataProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → ∀ D : Case1aData B, ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → normalizer (P2 : Set G) ≤ M →
      B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) ≤ M ∧
        (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ⊓ M = oddCoreIn M ∧
        B.U ⊓ M = (pCoreIn D.p B.U ⊓ M) ⊔ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ∧
        ∀ X : Subgroup G, X ≠ ⊥ → X ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) →
          normalizer (X : Set G) ≤ M

/-- Bender 1981 p. 223, first paragraph of the `M`-analysis: `B = C_U(S)` lies in the maximal
subgroup `M ⊇ N_G(P₂)` ("Applying this to the normal subgroup `X = B ∩ PP^g` … we see that
`B ⊆ M`").  First conjunct of `Case1aMDataProp`; the same hypothesis pattern as `Case1aA7Prop`. -/
def Case1aBleMProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → ∀ D : Case1aData B, ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → normalizer (P2 : Set G) ≤ M →
      B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) ≤ M

/-- Design pass 6 §3(a), verbatim (Core6 §3): `B ∩ F(U) = 1` in the subcase `Ĥ = H`
(`B = C_U(S)`).  `O(M) = B ∩ M` centralizes `E = E(M)`, and Case (1) gives `N_G(Y) ≤ H` for
`Y ≤ F(U)`, so `E ≤ H = C(t)`, contradicting `t ∈ E` with `Z(E)` odd. -/
def Case1aBFittingProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H →
    (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ⊓ fittingIn B.U = ⊥

/-- Design pass 6 §3(a), verbatim (Core6 §3): `B` is fixed-point-free on `F_{3'}(U)`. -/
def Case1aBFpfProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H →
    ∀ b ∈ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G), b ≠ 1 →
      fittingPiIn {3}ᶜ B.U ⊓ centralizer ({b} : Set G) = ⊥

/-- Design pass 6 §3(b), verbatim (Core6 §3): `|S| = 8` in the subcase `V = O₂(Ĥ)`.  Thm 2.6's
second alternative gives `|Ĥ : O₂(Ĥ)U| = 6` with `|O₂(Ĥ)| = 4` and `U` odd, so
`|Ĥ|₂ = 4·2 = 8`, and `S ∈ Syl₂(Ĥ)`. -/
def Case1bSOrderProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    IsFourGroup (pCoreIn 2 B.Hhat) → (pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 →
    pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) → Nat.card (B.S : Subgroup G) = 8

/-- B81 p. 224: `12 ∣ b₄` — `KV` acts fixed-point-freely on the set of cosets `Ĥg` contributing
to `b₄`, so `|KV| = 4·3 = 12` divides `b₄`.  (The reviewers of `Work.CORE3.Case1bNumerics`
noted that this is not a consequence of (1)–(9); it is the remaining numerical input needed for
`b₄ = 12`, `b₂ = 18`.) -/
def Case1bDivProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → IsFourGroup (pCoreIn 2 B.Hhat) → 12 ∣ bCount B.Hhat 4

/-- B81 p. 223, the direct-product form of Bender's `C_U(t₁) = C_U(S) × O_p(U)` in the subcase
`Ĥ = H` (used by the `IsInternalDirect` hypothesis of Theorem C: with `B₁ = C_U(t₁)`, `K₂ = F(U)`
this gives `B₁ ∩ K₂ = O_p(U)` and the elementwise commutation with `B = C_U(S)`).

Found to be *necessary* by the prover of `Work.CORE3.Case1aThmCInputs`: `Case1aMDataProp` records
only the join `U ∩ M = P₀ ⊔ B`, and nothing else in the §3a hypothesis list forces
`[O_p(U), C_U(S)] = 1`. -/
def Case1aDirectProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → ∀ D : Case1aData B,
      (B.U ⊓ centralizer ({D.t1} : Set G) =
          (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ⊔ pCoreIn D.p B.U) ∧
        ∀ a ∈ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G), ∀ b ∈ pCoreIn D.p B.U,
          a * b = b * a

/-- Bender 1981 p. 223, the `M`-analysis in the form Bender actually uses: `Case1aMDataProp`
together with the *direct-product* reading of `U ∩ M = P₀ × (B ∩ M)` and Bender's
`C_U(t₁) = B × O_p(U)` (`C_U(t₁) = C_U(S) ⊔ O_p(U)` with elementwise commutation).

Added because the provers of `Case1aThmCInputs` and `Case1aDirect` both found that the
`IsInternalDirect` conjunct of `BGThmCProp` needs `[O_p(U), C_U(S)] = 1` and that the *join*
form of the display does not give it. -/
def Case1aMData2Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G → ∀ B : BenderSetup G,
    Case1 B → B.Hhat = B.H → ∀ D : Case1aData B, ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → normalizer (P2 : Set G) ≤ M →
      (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) ≤ M ∧
        (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ⊓ M = oddCoreIn M ∧
        B.U ⊓ M = (pCoreIn D.p B.U ⊓ M) ⊔ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ∧
        (∀ X : Subgroup G, X ≠ ⊥ → X ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) →
          normalizer (X : Set G) ≤ M) ∧
        (∀ a ∈ (pCoreIn D.p B.U ⊓ M), ∀ b ∈ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)),
          a * b = b * a)) ∧
      (B.U ⊓ centralizer ({D.t1} : Set G) =
          (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ⊔ pCoreIn D.p B.U) ∧
      ∀ a ∈ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G), ∀ b ∈ pCoreIn D.p B.U,
        a * b = b * a

/-- The six inputs of area CORE3.

`hA7` is `A7Rec2Prop` (design pass 4, `Submission/Work/_design_gw/Core4.lean` §3): the amended
`A7RecProp` contract, whose extra premise `SmallerDGroups G` is `BenderCtx.ih`.  It is
`Work.A7REC.A7Rec2Prop`; `A7RecProp` implies it (`Work.CORE3.a7Rec2Prop_of_a7RecProp`). -/
structure Case1Inputs : Prop where
  T : LocalToolkit
  h22 : Lemma22Prop
  h26 : Thm26Prop
  h29 : Lemma29Prop
  hC : BGThmCProp
  hA7 : Work.A7REC.A7Rec2Prop

end Work.CORE3
