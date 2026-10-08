/-
# Area `NormalComplement`: the interface of Chapter III

Peterfalvi I Ch. III proves that `D = H ∩ H^t` has a normal complement in `H` in three steps:

* **§1 (pp. 172–175).** `p`-control groups; Lemma 1 (transfer), Lemma 2 (normaliser criterion), and
  the *Strategy*: a minimal `W ⊴ H` with `H = W·D` must have `W ∩ D = 1`.
* **§2 (pp. 175–177).** Proposition 1: for `E = W ∩ D` and a prime `p | |E|`, either `E` is
  `p`-control in `W`, or `E` has a `p`-Sylow `P ⊆ V` acting fixed-point-freely on `K` and cyclic.
  In the second case (D1) is assumed and §3–§5 derive a contradiction.
* **§3–§5 (pp. 177–187).** App. V, VI, VII and the structure of `D`; the final contradiction.

This module fixes the interface: the hypotheses of the pieces as `Prop`s, so that §1, §2 and §3–§5
can be proved (and delegated) independently and then assembled in `Assembly.lean`.
-/
import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.Prelim
import Submission.Work.Grun.pResidual

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-! ## The external inputs of the minimal-counterexample argument -/

/-- **Peterfalvi I Ch. III §1 Lemma 1** (p.172), as a `Prop`.  The source's standing hypotheses are
"`W` finite, `E ≤ W`, `p` a prime with `O^p(E) ⊊ E`"; the last is used (as `p ∣ [E : E']`, which
implies it: a quotient of `E/E'` of order `p` shows `O^p(E) ≠ E`) and **cannot be dropped**: for
`E = A₄ ≤ W = S₄`, `p = 3`, every 3-subgroup `U ≤ E` has `C_{S₄}(U)·E = S₄`, so `E` is `3`-control in
`W`, yet the 3-cycle `y ∈ E ∖ E'` lies in `O^3(S₄) = S₄`.  With it, a `p`-element of `E ∖ [E,E]` is
not in `O^p(W)`.  (Proved by transfer as `Work.NormalComplement.pcontrol_transfer_v2`.) -/
def TransferProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {E W : Subgroup G} {y : G},
    IsPControl p E W → y ∈ E → y ≠ 1 → (∃ k : ℕ, orderOf y = p ^ k) → y ∉ ⁅E, E⁆ →
      p ∣ (⁅E, E⁆).relIndex E → y ∉ Work.Grun.pResidual p W

/-- **The Strategy of Peterfalvi I Ch. III §1** (p.175).  If `E ≤ W ∩ D` contains a Sylow
`p`-subgroup of `W` and `y ∈ W ∖ O^p(W)`, then `O^p(W)` is a strictly smaller normal subgroup of
any `H` normalising `W`, with `O^p(W)·D = H`.  (Proved as
`Work.NormalComplement.pResidual_strategy`.) -/
def StrategyProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {E W D H : Subgroup G} {y : G},
    E ≤ W → E ≤ D → ¬ p ∣ (E.subgroupOf W).index → W ≤ H →
    H ≤ Subgroup.normalizer (W : Set G) → W ⊔ D = H → y ∈ W →
    y ∉ Work.Grun.pResidual p W →
      ∃ W₁ : Subgroup G, W₁ < W ∧ W₁ ≤ H ∧ H ≤ Subgroup.normalizer (W₁ : Set G) ∧ W₁ ⊔ D = H

/-- **The elementary part of the minimal-counterexample argument** (Peterfalvi I Ch. III §2,
p.176, first lines): for a nontrivial solvable subgroup `E` and **every** prime `p | [E : E']`
there is a `p`-element of `E` outside `E'`.  (Proved as
`Work.NormalComplement.primes_of_abelianization`.)

The "for every prime" form is what the minimality argument needs: for *each* prime `q | [E:E']`
one must rule out `q`-control of `E` in `W`. -/
def PrimesOfAbelianizationProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G), E ≠ ⊥ → Group.IsSolvable ↥E →
    ∀ p : ℕ, p.Prime → p ∣ (⁅E, E⁆).relIndex E →
      ∃ y : G, y ∈ E ∧ y ∉ ⁅E, E⁆ ∧ ∃ k : ℕ, orderOf y = p ^ k

/-! ## §2: the dichotomy for `E = W ∩ D` -/

/-- **`K` is invariant under `D`-conjugation.**  This is *not* automatic from the definitions
(`K = J(D,t)` is invariant under `V = C_D(t)` (App. I (4)) and inverted by `t`, and one computes
`d k d⁻¹ ∈ K` iff `k₁²` centralises `k` for `d = v k₁` in the decomposition `V × K → D`), and it is
used in §2 Prop. 1 case 3 to transport fixed-point-freeness of a Sylow `P ≤ V` on `K` to its
`D`-conjugates.  In the workspace it is carried as an explicit input (`hAppX` in
`Submission.Work.ThmF.ChV12.prop2v2`), so `Section2Prop` takes it as a hypothesis. -/
def KInvariantUnderD {G : Type*} [Group G] (H : Subgroup G) (t : G) : Prop :=
  ∀ d ∈ twoPoint H t, ∀ k ∈ Kset (twoPoint H t) t, d * k * d⁻¹ ∈ Kset (twoPoint H t) t

/-- The Ch. I/II input behind `KInvariantUnderD`, as a `Prop` (the source's Appendix X, cf.
`Submission.Work.ThmF`): in the situation (B0)–(B2), for a strongly embedded `H` and an involution
`t ∉ H`, `K = J(D,t)` is invariant under conjugation by `D`. -/
def AppXProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H → KInvariantUnderD H t

/-- **Peterfalvi I Ch. III §2 Proposition 1** (p.175).  With `H` strongly embedded, `t ∉ H` an
involution, `D = H ∩ H^t`, `W ⊴ H` with `H = W·D`, `E = W ∩ D`, and `p | |E|`: either `E` is
`p`-control in `W`, or `E` has a `p`-Sylow subgroup `P ⊆ V = C_D(t)` which acts fixed-point-freely
on `K = J(D,t)` and is cyclic.

The statement also carries `KInvariantUnderD H t`, which its proof needs (case 3) and which no area
`Prop` provides; the *proof* additionally assumes `ChIIFourP3SubnormalProp` (Ch. II §4 Prop. 3 with
subnormal `Y`, the blueprint `Prop` added for this purpose) — an area `Prop`, hence not a hypothesis
here. -/
def Section2Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H → ∀ W : Subgroup G, W ≤ H →
      H ≤ Subgroup.normalizer (W : Set G) → W ⊔ twoPoint H t = H →
        KInvariantUnderD H t →
        ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(W ⊓ twoPoint H t) →
          IsPControl p (W ⊓ twoPoint H t) W ∨
            ∃ P : Subgroup G, IsSylowIn p P (W ⊓ twoPoint H t) ∧ P ≤ centD H t ∧
              (∀ x ∈ P, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) ∧
              IsCyclic P

/-! ## §3–§5: hypothesis (D1) is contradictory -/

variable {G : Type*} [Group G]

/-- **Hypothesis (D1)** of Peterfalvi I Ch. III §2 (p.176): for every prime divisor `p` of `|E:E'|`
(`E = W ∩ D`) there is a `p`-Sylow `P` of `E` with `P ⊆ V = C_D(t)`, `P` acting fixed-point-freely
on `K = J(D,t)`, and `P` cyclic. -/
def IsD1 (H : Subgroup G) (t : G) (W : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime →
    p ∣ (⁅W ⊓ twoPoint H t, W ⊓ twoPoint H t⁆).relIndex (W ⊓ twoPoint H t) →
    ∃ P : Subgroup G, IsSylowIn p P (W ⊓ twoPoint H t) ∧ P ≤ centD H t ∧
      (∀ x ∈ P, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) ∧ IsCyclic P

/-- **Minimality of `W` in the set `{W' | W' ≤ H, H ≤ N_G(W'), W' ⊔ D = H}`** (Peterfalvi I
Ch. III §2, p.176: "`W` minimal with `W ⊴ H` and `H = WD`").  We use minimality of the *order*, which
is what the argument needs (`O^p(W) < W` gives `Nat.card`-decrease). -/
def IsMinimalIn (H D W : Subgroup G) : Prop :=
  W ≤ H ∧ H ≤ Subgroup.normalizer (W : Set G) ∧ W ⊔ D = H ∧
    ∀ W' : Subgroup G, W' ≤ H → H ≤ Subgroup.normalizer (W' : Set G) → W' ⊔ D = H →
      Nat.card W ≤ Nat.card W'

/-- **The content of Peterfalvi I Ch. III §3–§5** (pp. 177–187), in the form faithful to the paper:
for a *minimal* `W` (among the `W'` with `W' ⊴ H`, `W'·D = H`) satisfying (D1) and with `E = W ∩ D`
nontrivial, the situation is contradictory.

The proof is the long chain §3 Prop. 1, 2 and its Corollary, §4 Lemma 1, Prop. 1, 2, §5 Lemma 1,
Prop. 1, 2, 3 (App. V, VI, VII, Hering's theorem, Thompson's theorem).  Minimality is used
throughout §4 and §5 (cf. p.176 "minimality is used repeatedly below", p.179 "minimality of `W`"). -/
def NoD1MinProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H → ∀ W : Subgroup G, IsMinimalIn H (twoPoint H t) W →
      W ⊓ twoPoint H t ≠ ⊥ → IsD1 H t W → False

/-- **Hypothesis (D2)** of Peterfalvi I Ch. III §4 (p.179), the case left over after §3: there is
`1 ≠ X ⊴ V` with `C_K(X) ≠ 1`; `C_V(K) = 1`; and `E' ∩ V ≠ 1` (`E = W ∩ D`).

Used to split `NoD1MinProp` into §3 (the case `¬ IsD2` gives the conclusion directly, §3 Corollary)
and §4–§5 (the case `IsD2` is contradictory, and there minimality is used). -/
def IsD2 (H : Subgroup G) (t : G) (W : Subgroup G) : Prop :=
  (∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ centD H t ∧ centD H t ≤ Subgroup.normalizer (X : Set G) ∧
      ∃ k ∈ Kset (twoPoint H t) t, k ≠ 1 ∧ ∀ x ∈ X, k * x * k⁻¹ = x) ∧
    centD H t ⊓ Subgroup.centralizer (Kset (twoPoint H t) t : Set G) = ⊥ ∧
    ⁅W ⊓ twoPoint H t, W ⊓ twoPoint H t⁆ ⊓ centD H t ≠ ⊥

/-- **Peterfalvi I Appendix V (d)** (p.211), in ambient form and with the faithfulness hypothesis
that the source has: `Q` is elementary abelian of exponent `d` (a prime), `U ≤ N_G(Q)` acts
*faithfully* on `Q` (`U ⊓ C_G(Q) = ⊥`), `T ⊴ U` is cyclic and acts irreducibly on `Q`, and
`1 ≠ P ≤ U` has `|C_Q(P₁)| = d` for every `1 ≠ P₁ ≤ P`.  Then `|P| = p` is prime, `|Q| = d^p`, and
`C_U(s) = P` for `1 ≠ s ∈ C_Q(P)`.

(Proved as `Work.NormalComplement.appV`.  Note the faithfulness must be asked of `U`, not of `P`:
with `P`-faithfulness only, `Q = 𝔽₉`, `U = 𝔽₉^* × Gal(𝔽₉/𝔽₃) × C₂`, `P = Gal` is a counterexample.) -/
def AppVProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (d : ℕ) (U Q T P : Subgroup G), d.Prime →
    (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) → (∀ x ∈ Q, x ^ d = 1) → Q ≠ ⊥ →
    U ≤ Subgroup.normalizer (Q : Set G) → T ≤ U → U ≤ Subgroup.normalizer (T : Set G) →
    IsCyclic ↥T →
    (∀ R : Subgroup G, R ≤ Q → T ≤ Subgroup.normalizer (R : Set G) → R = ⊥ ∨ R = Q) →
    U ⊓ Subgroup.centralizer (Q : Set G) = ⊥ →
    P ≤ U → P ≠ ⊥ →
    (∀ P₁ : Subgroup G, P₁ ≤ P → P₁ ≠ ⊥ →
      Nat.card ↥(Q ⊓ Subgroup.centralizer (P₁ : Set G)) = d) →
    (Nat.card P).Prime ∧ Nat.card Q = d ^ Nat.card P ∧
      ∀ s ∈ Q ⊓ Subgroup.centralizer (P : Set G), s ≠ 1 →
        U ⊓ Subgroup.centralizer ({s} : Set G) = P

/-- **Peterfalvi I Appendix III (2)–(5)** (pp. 206–207), as needed by §4 Prop. 1 step 3 and
§5 Prop. 2: `F` transitive and faithful on `α`, of 2-rank 1, with a point stabiliser `F_a` that is
strongly embedded and maximal.  Then `F = Q ⋊ F_a` with `Q` elementary abelian of prime exponent
`f`; `F_a` has a unique involution; distinct involutions multiply into `Q` with order `f`; `Q` is
the set of odd-order elements inverted by an involution; and if `F` is 2-transitive and
`p ∤ |F_a ∩ F_b|`, a `p`-subgroup of `F_a` acts fixed-point-freely on `Q` (cyclic for `p` odd).
Uses `BrauerSuzukiProp` and `hFT`. -/
def AppIIIProp : Prop :=
  ∀ (F : Type) [Group F] [Finite F] (α : Type) [MulAction F α] (a : α),
    MulAction.IsPretransitive F α → (∀ g : F, (∀ x : α, g • x = x) → g = 1) →
    ¬ HasFourGroup F → IsStronglyEmbedded (MulAction.stabilizer F a) →
    IsCoatom (MulAction.stabilizer F a) →
    ∃ (f : ℕ) (Q : Subgroup F), f.Prime ∧ Q.Normal ∧ Q ≠ ⊥ ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ (∀ x ∈ Q, x ^ f = 1) ∧
      Q ⊓ MulAction.stabilizer F a = ⊥ ∧ Q ⊔ MulAction.stabilizer F a = ⊤ ∧
      (∃! u : F, u ∈ MulAction.stabilizer F a ∧ orderOf u = 2) ∧
      (∀ u v : F, orderOf u = 2 → orderOf v = 2 → u ≠ v → u * v ∈ Q ∧ orderOf (u * v) = f) ∧
      (∀ u : F, orderOf u = 2 → ∀ x : F, Odd (orderOf x) → u * x * u⁻¹ = x⁻¹ → x ∈ Q) ∧
      (MulAction.IsMultiplyPretransitive F α 2 → ∀ p : ℕ, p.Prime → ∀ b : α, b ≠ a →
        ¬ p ∣ Nat.card ↥(MulAction.stabilizer F a ⊓ MulAction.stabilizer F b) →
        ∀ R : Subgroup F, R ≤ MulAction.stabilizer F a → IsPGroup p R →
          (∀ r ∈ R, r ≠ 1 → ∀ x ∈ Q, r * x * r⁻¹ = x → x = 1) ∧ (p ≠ 2 → IsCyclic R))

/-- **The Corollary of Peterfalvi I Ch. III §1 Lemma 2** (p.174): `E ≤ W` solvable, `π` the set of
primes of `|E|`; if `N_W(U) = O_{π'}(C_W(U)) · N_E(U)` for every `p`-subgroup `1 ≠ U ≤ E`
(`p ∈ π`), then `E` is a Hall subgroup of `W` and has a normal complement in `W`.  (Proof: the
`p`-control criterion of Lemma 2, Lemma 1 and induction on `|W|` — modules
`pcontrol_criterion` and `pcontrol_transfer`.) -/
def ControlCorollaryProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (E W : Subgroup G), E ≤ W → Group.IsSolvable ↥E →
    (∀ (p : ℕ) (U : Subgroup G), p.Prime → p ∣ Nat.card E → U ≤ E → U ≠ ⊥ → IsPGroup p U →
      W ⊓ Subgroup.normalizer (U : Set G) =
        piPrimeCoreSub {q | q ∣ Nat.card E} (W ⊓ Subgroup.centralizer (U : Set G)) ⊔
          (E ⊓ Subgroup.normalizer (U : Set G))) →
    Nat.Coprime (Nat.card E) (E.relIndex W) ∧
      ∃ N : Subgroup G, N ≤ W ∧ W ≤ Subgroup.normalizer (N : Set G) ∧ N ⊓ E = ⊥ ∧ N ⊔ E = W

/-! ## Appendix VI and §2/§3 inputs, as `Prop`s -/

/-- **Peterfalvi I Appendix VI** (pp. 213–215), the generalisation of Burnside's result on
permutation groups of prime degree.  (Proved as `Work.NormalComplement.appVI`.) -/
def AppVIProp : Prop :=
  ∀ (W : Type) [Group W] [Finite W] {I : Type*} [Fintype I] [MulAction W I] (K : Subgroup W),
    1 < Fintype.card I → (∀ i j : I, ∃! k : K, (k : W) • i = j) →
      (∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) = K) →
      MulAction.IsMultiplyPretransitive W I 2 ∨
        (MulAction.toPermHom W I).ker ⊔ Subgroup.normalizer (K : Set W) = ⊤

/-- **The Corollary of Peterfalvi I Ch. III §2 Prop. 1** (p.176): if `H = C_H(Inv(H))·D` then `D`
has a normal complement in `H`.  (Proof: take `W ⊴ H` minimal with `W ⊆ C_H(Inv H)` and `H = W·D`;
if `E = W ⊓ D ≠ 1` then `E` is solvable by Feit–Thompson and some prime `p | [E:E']`; the second
alternative of `Section2Prop` is impossible because every subgroup of `V ∩ E` centralises
`Inv(H)`; hence `E` is `p`-control in `W` and the transfer Lemma 1 contradicts minimality.) -/
def Section2CorollaryProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H →
      (H ⊓ Subgroup.centralizer (involutions (H : Set G)) : Subgroup G) ⊔ twoPoint H t = H →
      HasNormalComplementIn (twoPoint H t) H

/-- **Peterfalvi I Ch. III §3 Prop. 2** (p.178): if `E = W ⊓ D`, acting on `Inv(H)` by conjugation,
is a Frobenius group with kernel `K = J(D,t)` and complement `E ⊓ V`, then `D` has a normal
complement in `H` (the conclusion of Theorem D).  Uses Appendix VI and Hering's theorem, then the
Corollary of §2 Prop. 1. -/
def Section3Prop2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H → ∀ W : Subgroup G, W ≤ H →
      H ≤ Subgroup.normalizer (W : Set G) → W ⊔ twoPoint H t = H →
      (∃ K : Subgroup G, (K : Set G) = Kset (twoPoint H t) t ∧
        (∀ w ∈ W ⊓ twoPoint H t, ∀ k ∈ K, w * k * w⁻¹ ∈ K) ∧
        K ⊓ (W ⊓ centD H t) = ⊥ ∧ K ⊔ (W ⊓ centD H t) = W ⊓ twoPoint H t ∧
        (∀ k ∈ K, k ≠ 1 → ∀ v ∈ W ⊓ centD H t, v ≠ 1 → v * k * v⁻¹ ≠ k)) →
      HasNormalComplementIn (twoPoint H t) H

/-- **Ch. III §2 Corollary + §3** (pp. 176–178).  If `E = W ⊓ D` is *not* in case (D2), then `D`
has a normal complement in `H`.  This packages three statements of the paper:

* the Corollary of §2 Prop. 1 (p.176): if `C_V(K) ≠ 1` then, by Ch. II §4 Prop. 4(b),
  `H = C_H(Inv H)·D`, and then `D` has a normal complement in `H` (via §2 Prop. 1 and §1 Lemma 2);
* §3 Prop. 1 (p.177): if `C_K(X) = 1` for every `1 ≠ X ⊴ V`, then `E`, acting on `Inv(H)`, is a
  Frobenius group (App. VII is used inside);
* §3 Prop. 2 (p.178) and its Corollary: a Frobenius `E` gives the conclusion of Theorem D
  (App. VI and Hering's theorem `HeringProp` are used).

Since `¬ IsD2` is the disjunction `C_V(K) ≠ 1 ∨ E' ∩ V = 1 ∨ (∀ 1 ≠ X ⊴ V, C_K(X) = 1)`, the
three cases exhaust it. -/
def Section3Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H → ∀ W : Subgroup G, W ≤ H →
      H ≤ Subgroup.normalizer (W : Set G) → W ⊔ twoPoint H t = H → IsD1 H t W →
      ¬ IsD2 H t W → HasNormalComplementIn (twoPoint H t) H

/-- **Ch. III §4–§5** (pp. 179–187): in case (D2) the minimal `W` leads to a contradiction.  This
is the long chain §4 Lemma 1, Prop. 1, Prop. 2 (structure of `D`: `p ≥ 7`, `E = K[A,P]P`,
`E' = K[A,P]` nilpotent and Hall in `G`, `|K| = r^a(2^p - 1)`, `F(V) = E' ∩ V`) and §5 Prop. 1, 2,
3 (`p ≥ 7`; the subgroup `M = {x ∈ C_G(ut) | x^t = x⁻¹}`; `N_H(P) ⊆ N_H(F(V))`, contradicting
§5 Lemma 1), using App. V, VI, VII and `ThompsonFrobeniusProp`. -/
def Section45Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H → ∀ W : Subgroup G, IsMinimalIn H (twoPoint H t) W →
      W ⊓ twoPoint H t ≠ ⊥ → IsD1 H t W → IsD2 H t W → False

/-- The stronger (minimality-free) form of §3–§5.  **The paper's §4–§5 use minimality repeatedly**
(p.176, p.179), so `NoD1MinProp` is the faithful statement; `NoD1Prop` is recorded here because the
assembled theorem `thmD_of_sections` consumes it.  `NoD1Prop` follows from `NoD1MinProp` *only* if
minimality is derivable from (D1) + `W ∩ D ≠ ⊥`, which the paper does not claim. -/
def NoD1Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G → ∀ H : Subgroup G, IsStronglyEmbedded H →
    ∀ t : G, orderOf t = 2 → t ∉ H → ∀ W : Subgroup G, W ≤ H →
      H ≤ Subgroup.normalizer (W : Set G) → W ⊔ twoPoint H t = H → W ⊓ twoPoint H t ≠ ⊥ →
        IsD1 H t W → False

end Work.NormalComplement
