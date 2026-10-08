/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: intermediate contracts of Bender's proof

The file `Submission/Work/BSW/Defs.lean` holds the verbatim copies of the contract vocabulary of
the area (`Work.GW2.BSWHyps2`, `Work.GW2.BSWZass2Prop`, `Work.GW2.BSW2Prop`, ...).  This file
holds the area's *own* intermediate `Prop`s, one per paragraph of

> H. Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235,

together with the `|K| = 4` step from

> H. Bender, *Finite groups with large subgroups*, Illinois J. Math. **18** (1974) 223–228, §3.

The proof of `Work.GW2.BSWZass2Prop` is the following chain (see
`Submission/Work/BSW/Main.lean` for the assembly):

* `|K| = 2` (`ZassConcl G` with `p = 5`): order part `BSWK2OrderProp`, structure part
  `BSWK2StructureProp`;
* `|K| = 4` (`ZassConcl G` with `p ^ k = 7` or `9`): order part `BSWK4OrderProp`, structure part
  `BSWK4StructureProp`;
* `|K| > 4`: order part `BSWOrderProp` (Bender §2, the character-theoretic computation of
  `|G| = q(q²−1)/2`, `q = 2|K| ± 1`), completion `BSWCompletionProp` (Bender §3, 3.1–3.8: the
  subgroup `Q` with `N_G(Q) = QD`), and the recognition step `BSWDataZassProp` (Bender's
  conclusion (1)–(4) together with `|G| = q(q²−1)/2` gives the Zassenhaus action on `G ⧸ N_G(Q)`:
  doubly transitive of degree `q + 1`, every nonidentity element fixes at most two points, and the
  two-point stabilizer has order `(q−1)/2`).

The Bender conclusion (1)–(4) is bundled in the predicate `IsBSWData`.
-/
import Submission.Work.BSW.Defs

open scoped MatrixGroups

namespace Work.BSW

open Subgroup Work.GW2

/-- **The conclusion of `Work.GW2.BSWZass2Prop`**, as a self-contained predicate: there is a
prime power `p ^ k ≥ 5` (`p` odd) and a subgroup `M ≤ G` whose coset space carries the Zassenhaus
hypotheses. -/
def ZassConcl (G : Type) [Group G] [Finite G] : Prop :=
  ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
    ∃ M : Subgroup G, ZassHyps2 G (G ⧸ M) (p ^ k)

/-- **The conclusion of `Work.GW2.BSW2Prop`**: `G ≃ PSL(2, q)` for an odd prime power `q ≥ 5`. -/
def PSL2Concl (G : Type) [Group G] [Finite G] : Prop :=
  ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
    Nonempty (G ≃* PSL(2, GaloisField p k))

/-! ## Bender's conclusion (1)–(4) -/

/-- The conclusion of the Brauer–Suzuki–Wall theorem in Bender's formulation (B74, p. 229), for a
*named* subgroup `Q`: `q` is an odd prime power `≥ 5`, `|Q| = q`, `C_G(Q) = Q`, `Q` is disjoint
from its conjugates (Bender 3.7), and there is `D ≤ N_G(Q)` with `D` abelian of order `(q−1)/2`,
`Q ⊓ D = ⊥`, `N_G(Q) = Q ⊔ D`, every nontrivial subgroup of `D` having the same normalizer as `D`,
and an involution `u ∉ D` inverting `D` (Bender's (3) and (4)); and `|G| = q(q²−1)/2`.

This is the exact output of Bender's §3, 3.7–3.8 (before the Zassenhaus recognition); the transfer
to the Zassenhaus hypotheses is `BSWDataZassProp`.  Two clauses are recorded here beyond a naive
reading of (1)–(3) because the Zassenhaus conversion provably needs them:

* 3.7 (`Q` is disjoint from its conjugates) is *not* derivable from Bender's (1)–(4) alone — two
  distinct abelian Sylow `p`-subgroups of a group can meet nontrivially, e.g. the Klein four-groups
  of `A₄` — but is a theorem of §3 and is used for double transitivity, for the two-point
  stabilizer and for the "at most two fixed points" clause;
* the source's (4) is the equality `N_G(X) = N_G(D) = D⟨u⟩` for every `1 ≠ X ≤ D`, which gives
  `|N_G(D)| = q - 1` and hence (as `p ∤ q - 1`) the absence of `p`-elements in `N_G(D)`, i.e.
  `C_Q(D) = 1`; the weaker `N_G(X) ≤ N_G(D)` does not suffice for the "at most two fixed points"
  clause (the `DataZass` prover showed the clause is *equivalent* to `C_Q(D) = 1`). -/
def IsBSWDataQ (G : Type) [Group G] [Finite G] (q : ℕ) (Q : Subgroup G) : Prop :=
  /- `Q = O_p(G)` has order `q` and `C_G(Q) = Q` -/
  Nat.card Q = q ∧ centralizer (Q : Set G) = Q ∧
  /- Bender 3.7: `Q` is disjoint from its conjugates -/
  (∀ g : G, g ∉ normalizer (Q : Set G) → Q ⊓ conjSub g Q = ⊥) ∧
  /- the complement `D` of `Q` in `N_G(Q)` -/
  ∃ D : Subgroup G, IsMulCommutative D ∧ Nat.card D = (q - 1) / 2 ∧ Q ⊓ D = ⊥ ∧
    /- `N_G(Q) = QD` -/
    normalizer (Q : Set G) = Q ⊔ D ∧
    /- (4): every nontrivial subgroup of `D` has the same normalizer as `D` -/
    (∀ X : Subgroup G, X ≠ ⊥ → X ≤ D → normalizer (X : Set G) = normalizer (D : Set G)) ∧
    /- (4): `N_G(D) = D⟨u⟩` with `u ∉ D` an involution inverting `D`, so `|N_G(D)| = q - 1` -/
    (∃ u : G, orderOf u = 2 ∧ u ∉ D ∧ Inverts u D ∧
      normalizer (D : Set G) = D ⊔ zpowers u) ∧
    /- `|G| = q(q²−1)/2` -/
    Nat.card G = q * (q * q - 1) / 2

/-- Bender's conclusion (1)–(4) together with 3.7: `q` is an odd prime power `≥ 5` and there is a
subgroup `Q` as in `IsBSWDataQ`.

It is stated as a plain `Prop` (rather than a structure with data fields) so that it can be
conjoined inside the intermediate `Prop`s. -/
def IsBSWData (G : Type) [Group G] [Finite G] (q : ℕ) : Prop :=
  (∃ p m : ℕ, Fact p.Prime ∧ Odd p ∧ q = p ^ m) ∧ 5 ≤ q ∧ ∃ Q : Subgroup G, IsBSWDataQ G q Q

/-! ## A parity fact used to split the cases -/

/-- `|K|` is even: `K` is abelian with the unique involution `t`, so the squaring map of `K` has
the two-element kernel `{1, t}`.  This is what makes the case split of `BSWZass2Prop` into
`|K| = 2`, `|K| = 4` and `|K| > 4` exhaustive. -/
def BSWParityProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G),
    BSWHyps2 G t s K → Even (Nat.card K)

/-! ## The `|K| = 2` case (Bender 1974, §1, p. 230) -/

/-- `|K| = 2` forces `|G| = 60`. -/
def BSWK2OrderProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K → Nat.card K = 2 → Nat.card G = 60

/-- `|K| = 2` and `|G| = 60`: Bender's conclusion (1)–(4) with `q = 5` (the Sylow 5-subgroup `Q`
of the group of order `60`, `N_G(Q) ≅ D₁₀`). -/
def BSWK2StructureProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K → Nat.card K = 2 → Nat.card G = 60 →
      IsBSWData G 5

/-- The `|K| = 2` case of `BSWZass2Prop`: `G` satisfies Bender's conclusion with `q = 5`. -/
def BSWK2Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K → Nat.card K = 2 → IsBSWData G 5

/-! ## The `|K| = 4` case (Bender 1974 *large subgroups*, §3) -/

/-- `|K| = 4` forces `C_G(t) ≅ D₈` and `|G| = 168` or `360` (B74L §3). -/
def BSWK4OrderProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K → Nat.card K = 4 →
      Nat.card G = 168 ∨ Nat.card G = 360

/-- `|K| = 4` with `|G| = 168` or `360`: Bender's conclusion (1)–(4) with `q = 7` (the Sylow
7-subgroup of `L₂(7)`, `N_G(Q) ≅ 7:3`, degree `8`) or `q = 9` (the Sylow 3-subgroup of
`A₆ ≅ L₂(9)`, `N_G(Q) ≅ 3²:C₄`, degree `10`). -/
def BSWK4StructureProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K → Nat.card K = 4 →
      (Nat.card G = 168 ∨ Nat.card G = 360) → (IsBSWData G 7 ∨ IsBSWData G 9)

/-- The `|K| = 4` case of `BSWZass2Prop`. -/
def BSWK4Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K → Nat.card K = 4 →
      (IsBSWData G 7 ∨ IsBSWData G 9)

/-! ## The `|K| > 4` case (Bender 1974, §§2–3) -/

/-- **Bender §2**: with `k = |K| > 4` the group has order `(2k−1)(k−1)(2k)` (case `ε = −1`,
`q = 2k−1`) or `(2k+1)(k+1)(2k)` (case `ε = +1`, `q = 2k+1`).

This is the character-theoretic computation: the Brauer–Suzuki TI isometry for the induced
generalized characters `α = (1_K − ρ₁)^G`, `β = (ρ₁ − ρ₂)^G` and the involution-product formula
`i = |G||H|⁻³ Σ_χ χ(t)²χ(x)/χ(1)`. -/
def BSWOrderProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K → 4 < Nat.card K →
      (Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K) ∨
       Nat.card G = (2 * Nat.card K + 1) * (Nat.card K + 1) * (2 * Nat.card K))

/-- **Bender §3** (3.1–3.8): given the order, there is `Q` of order `q = 2k ± 1` with
`N_G(Q) = QD`; i.e. Bender's conclusion (1)–(4) holds. -/
def BSWCompletionProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K → 4 < Nat.card K →
      (Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K) ∨
       Nat.card G = (2 * Nat.card K + 1) * (Nat.card K + 1) * (2 * Nat.card K)) →
      ∃ q : ℕ, (q = 2 * Nat.card K - 1 ∨ q = 2 * Nat.card K + 1) ∧ IsBSWData G q

/-- **Bender §3.8 + the Zassenhaus remark** (p. 229): Bender's conclusion (1)–(4) says exactly
that `G` acts on the `q + 1` conjugates of `Q` as a Zassenhaus group: doubly transitive of degree
`q + 1`, no nonidentity element fixing three points, two-point stabilizer of order `(q−1)/2`. -/
def BSWDataZassProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ q : ℕ, IsBSWData G q → ZassConcl G

/-- The `|K| > 4` case of `BSWZass2Prop`: Bender's conclusion with `q = 2|K| ± 1`. -/
def BSWGt4Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K → 4 < Nat.card K →
      ∃ q : ℕ, (q = 2 * Nat.card K - 1 ∨ q = 2 * Nat.card K + 1) ∧ IsBSWData G q

/-- **Bender 1974 §2 endgame, unified form** (pp. 231–232): the integer arithmetic in the form
covering *both* congruence cases (`q ≡ 3 (mod 4)`, where the constituent shared by `α*` and `β*` is
`γ` with `γ(t) = -2`, and `q ≡ 1 (mod 4)`, where it is `λ` with `λ(t) = 2` and `γ(t) = 1`; see
`Submitted/Work/BSW/NOTES_BSW_order.md` and the reviewers' `PSL(2,29)` computation).

Inputs: `k` even, `k ≥ 6`; `r = |G:H|` odd and coprime to `2k`; `γ`, `λ` are the constituents of
`α* = 1 + γ − λ`, so `λ(1) = γ(1) + 1` (`l1 = g1 + 1`) and `λ(t) = γ(t) + 1` (`lt = gt + 1`);
the shared constituent of `β*` pairs with `γ(t) ∈ {-2, 1}`; and `⟨α*, i⟩ = k` gives
`2k² γ(1)λ(1) = r (γ(1)λ(1) + γ(t)² λ(1) − λ(t)² γ(1))`.  Conclusion: `r = (2k ± 1)(k ± 1)`.

Brute-forced over all even `6 ≤ k ≤ 118` and `|γ(1)| ≤ 2000` (plus the lead's check of the
`γ(t) = -2` branch): no counterexample; the corresponding value data of `PSL(2,11)` (`k = 6`,
`γ(1) = 10`, `gt = -2`, `r = 55`) and of `PSL(2,29)` (`k = 14`, `γ(1) = 29`, `gt = 1`, `r = 435`)
satisfy the hypotheses. -/
def BSWOrderArith2Prop : Prop :=
  ∀ (k r g1 l1 gt lt : ℤ), 6 ≤ k → Even k → 0 < r → Odd r → IsCoprime r (2 * k) →
    g1 ≠ 0 → l1 ≠ 0 → 1 + g1 - l1 = 0 → 1 + gt - lt = 0 → (gt + 2) * (gt - 1) = 0 →
    2 * k ^ 2 * g1 * l1 = r * (g1 * l1 + gt ^ 2 * l1 - lt ^ 2 * g1) →
    r = (2 * k + 1) * (k + 1) ∨ r = (2 * k - 1) * (k - 1)

end Work.BSW

namespace Work.GW2

/-- **Bender 1974 §2 endgame** (pp. 231–232) as pure integer arithmetic, copied verbatim from
`Submission/Work/_design_gw/Core4.lean` §4 (design pass 4, `NOTES_LEAD_gw_design4.md` §4)
[CHECKED on the page images; brute-forced for `k ≤ 38`, `|γ(1)| ≤ 400`].

Inputs: `|H| = 2k` (`k` even, `k ≥ 6`) and `r = |G:H|`, odd and prime to `2k`.
`α* = 1 + γ − λ` and `β* = φ − γ` give `1 + γ(1) − λ(1) = 0`, `φ(1) = γ(1)`, `φ(t) − γ(t) = 4`
and `1 + γ(t) − λ(t) = 0`.  `⟨β*, i⟩ = 0` gives `φ(t)² = γ(t)²`; `⟨α*, i⟩ = 2k²/|H|` gives
`2k² γ(1)λ(1) = r (γ(1)λ(1) + γ(t)² λ(1) − λ(t)² γ(1))`.

Conclusion: `r = (2k+ε)(k+ε)` for some `ε = ±1`.

Proof (the source's pp. 231–232): `r ∣ γ(1)λ(1)` from `IsCoprime r (2k)`; `gcd(λ(1), f) = 1` with
`f = γ(1)λ(1) + 4λ(1) − γ(1)`, so `λ(1) ∣ r` and `λ(1)` is odd; `8 ∣ f`, so `γ(1) ≡ 2 (mod 4)`;
`gcd(γ(1), f) = 2`, so `γ(1)/2 ∣ r`; hence `r = γ(1)λ(1)/2`, `f = 4k²` and `λ(1) + 1 = 2kε`. -/
def BSWOrderArithProp : Prop :=
  ∀ (k r g1 l1 f1 gt lt ft : ℤ), 6 ≤ k → Even k → 0 < r → Odd r → IsCoprime r (2 * k) →
    g1 ≠ 0 → l1 ≠ 0 → f1 = g1 → ft - gt = 4 → ft ^ 2 = gt ^ 2 →
    1 + gt - lt = 0 → 1 + g1 - l1 = 0 →
    2 * k ^ 2 * g1 * l1 = r * (g1 * l1 + gt ^ 2 * l1 - lt ^ 2 * g1) →
    r = (2 * k + 1) * (k + 1) ∨ r = (2 * k - 1) * (k - 1)

end Work.GW2

namespace Work.BSW

/-- Alias of `Work.GW2.BSWOrderArithProp` in the area namespace. -/
abbrev BSWOrderArithProp : Prop := Work.GW2.BSWOrderArithProp

end Work.BSW
