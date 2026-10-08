/-
# NormalComplement §3–§5 design (lead): vocabulary, standing data, external inputs

Design file (statements only, `sorry`-free because it contains no theorems).  Everything here is
stated over the area's existing vocabulary (`Kset`, `twoPoint`, `centD`, `fixedPts`, `involutions`,
`IsD1`, `IsD2`, `IsMinimalIn`, …).  See `NOTES_LEAD_bs_normalcomplement.md` for the plan.
-/
import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.Sections
import Submission.Work.Fitting.Defs
import Submission.Work.NPC.Defs
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.Design

section Vocab

variable {G : Type*} [Group G]

/-- `F(X)`, the Fitting subgroup of a subgroup `X`, as a subgroup of `G`. -/
noncomputable def fitSub (X : Subgroup G) : Subgroup G :=
  (Work.Fitting.fitting ↥X).map X.subtype

/-- `C_K(X) = J(D,t) ∩ C_G(X)`. -/
def CK (H : Subgroup G) (t : G) (X : Subgroup G) : Set G :=
  Kset (twoPoint H t) t ∩ (Subgroup.centralizer (X : Set G) : Set G)

/-- `N_K(X) = J(D,t) ∩ N_G(X)`. -/
def NK (H : Subgroup G) (t : G) (X : Subgroup G) : Set G :=
  Kset (twoPoint H t) t ∩ (Subgroup.normalizer (X : Set G) : Set G)

/-- `X` acts fixed-point-freely, by conjugation, on the set `S`. -/
def FpfOn (X : Subgroup G) (S : Set G) : Prop :=
  ∀ x ∈ X, x ≠ 1 → ∀ k ∈ S, x * k * x⁻¹ = k → k = 1

/-- `E = W ∩ D`. -/
abbrev Egrp (H : Subgroup G) (t : G) (W : Subgroup G) : Subgroup G := W ⊓ twoPoint H t

/-- `E' = [E,E]`. -/
abbrev Ecomm (H : Subgroup G) (t : G) (W : Subgroup G) : Subgroup G :=
  ⁅Egrp H t W, Egrp H t W⁆

/-- The hypothesis of `Section3Prop2` ("`E`, acting on `Inv H`, is a Frobenius group with kernel
`K` and complement `E ∩ V`"), named so that §3 Prop. 1 and the §3 Corollary can produce it. -/
def FrobPacket (H : Subgroup G) (t : G) (W : Subgroup G) : Prop :=
  ∃ K : Subgroup G, (K : Set G) = Kset (twoPoint H t) t ∧
    (∀ w ∈ W ⊓ twoPoint H t, ∀ k ∈ K, w * k * w⁻¹ ∈ K) ∧
    K ⊓ (W ⊓ centD H t) = ⊥ ∧ K ⊔ (W ⊓ centD H t) = W ⊓ twoPoint H t ∧
    (∀ k ∈ K, k ≠ 1 → ∀ v ∈ W ⊓ centD H t, v ≠ 1 → v * k * v⁻¹ ≠ k)

end Vocab

/-! ## Standing data of §3 (no minimality) and of §4–§5 (minimality, (D1), (D2), `p`, `P`) -/

/-- The data of Ch. III §2–§3: `W ⊴ H`, `H = W D`, `E = W ∩ D ≠ 1`, (D1). -/
structure Setup3 (G : Type) [Group G] [Finite G] (H : Subgroup G) (t : G) (W : Subgroup G) :
    Prop where
  sit : Situation G
  se : IsStronglyEmbedded H
  invol : orderOf t = 2
  notMem : t ∉ H
  le : W ≤ H
  normal : H ≤ Subgroup.normalizer (W : Set G)
  sup : W ⊔ twoPoint H t = H
  Ene : W ⊓ twoPoint H t ≠ ⊥
  d1 : IsD1 H t W

/-- The data of Ch. III §4–§5 (p.179): `W` minimal, (D1), (D2), a prime `p ∣ |E : E'|` and a
subgroup `P` of order `p` of `V ∩ E` (it exists by (D1) and Cauchy). -/
structure Setup45 (G : Type) [Group G] [Finite G] (H : Subgroup G) (t : G) (W : Subgroup G)
    (p : ℕ) (P : Subgroup G) : Prop extends Setup3 G H t W where
  minW : IsMinimalIn H (twoPoint H t) W
  d2 : IsD2 H t W
  prime : p.Prime
  dvd : p ∣ (Ecomm H t W).relIndex (Egrp H t W)
  P_le : P ≤ Egrp H t W ⊓ centD H t
  P_card : Nat.card P = p
  P_fpf : FpfOn P (Kset (twoPoint H t) t)

/-- `Setup45` plus the subgroup `A` of §4 Lemma 1 (a), (b): `V = A ⋊ P`, `A ≠ 1`,
`|C_K(A)| = 2^p - 1`, and `C_K(B) = C_K(A)` for every `P`-invariant `1 ≠ B ≤ A`. -/
structure Setup45A (G : Type) [Group G] [Finite G] (H : Subgroup G) (t : G) (W : Subgroup G)
    (p : ℕ) (P A : Subgroup G) : Prop extends Setup45 G H t W p P where
  A_ne : A ≠ ⊥
  A_le : A ≤ centD H t
  A_normal : centD H t ≤ Subgroup.normalizer (A : Set G)
  A_inf : A ⊓ P = ⊥
  A_sup : A ⊔ P = centD H t
  A_CK : (CK H t A).ncard = 2 ^ p - 1
  A_B : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ A → P ≤ Subgroup.normalizer (B : Set G) →
    CK H t B = CK H t A

/-! ## External inputs (not provided by any current area `Prop`) -/

/-- **[EXTERNAL — area `ThreePoints`; already proposed in its `NOTES_ThreePoints_RESTATE.md`]**
Peterfalvi I Ch. II §4 Prop. 3 (a), (b) under the *source* hypothesis, specialised to a **normal**
`Y` (the only form Ch. III §3–§5 use: `A ⊴ V`, `X ∩ A ⊴ X`, `U ⊴ U × P`):
for `X ≤ V` with a normal subgroup `1 ≠ Y ⊴ X` such that `N_K(Y) ≠ 1`, and `F = O^{2'}(C_G(X))`,
`N_G(X) = F N_V(X)` and `N_H(X) = S ⋊ N_D(X)` with `S` a Sylow 2-subgroup of `F ∩ H`.
`ChIIFourProp` only has the case `Y = X`, which does NOT cover §4 Prop. 1 step 1
(`X = U × P`, `N_K(X) = 1`), §5 Lemma 1 (`X = (X ∩ A)P`) or §5 Prop. 2 (a) (`X = V = AP`). -/
def P3NormalProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G →
    ∀ H : Subgroup G, IsStronglyEmbedded H → ∀ t : G, orderOf t = 2 → t ∉ H →
    ∀ X Y : Subgroup G, X ≤ centD H t → Y ≠ ⊥ → Y ≤ X →
      X ≤ Subgroup.normalizer (Y : Set G) →
      (∃ k ∈ invertedBy (twoPoint H t) t, k ≠ 1 ∧ k ∈ Subgroup.normalizer (Y : Set G)) →
      Subgroup.normalizer (X : Set G) =
          (oddResidual ↥(Subgroup.centralizer (X : Set G))).map
              (Subgroup.centralizer (X : Set G)).subtype ⊔
            (centD H t ⊓ Subgroup.normalizer (X : Set G)) ∧
      ∃ S : Subgroup G, IsPGroup 2 S ∧
        S ≤ (oddResidual ↥(Subgroup.centralizer (X : Set G))).map
              (Subgroup.centralizer (X : Set G)).subtype ∧
        S ≤ H ∧ H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
        S ⊓ twoPoint H t = ⊥ ∧
        S ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = H ⊓ Subgroup.normalizer (X : Set G)

/-- **[EXTERNAL — area `Models`, new clause]** Peterfalvi I p.184, facts 1° and 2°, in a form
that needs no coordinates: for a simple Bender group `Y` and a strongly embedded `H`,
(1°) every 2-element of `H` has order dividing 4 (true in all three families: elementary
abelian / Suzuki `A(n,θ)` / the special PSU Sylow);
(2°) if `Y` is a Zassenhaus group on `Y ⧸ H` (this excludes `PSU(3,q)`, whose two-point stabiliser
fixes `q+1` points), `u ∈ Inv H`, `t ∈ Inv Y ∖ H`, then `C_Y(ut)` is cyclic, inverted by `u`, and
(as `|C_Y(ut)| ∈ {q ± 1, q ± √(2q) + 1}` with `q - 1 = |Inv H|`) has order `≥ 6` once `q ≥ 128`. -/
def BenderModelFacts2Prop : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleBenderGroup Y →
    ∀ H : Subgroup Y, IsStronglyEmbedded H →
      (∀ x ∈ H, (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1) ∧
      (IsZassenhaus H → ∀ u ∈ involutions (H : Set Y), ∀ t : Y, orderOf t = 2 → t ∉ H →
        IsCyclic ↥(Subgroup.centralizer ({u * t} : Set Y)) ∧
        (∀ y ∈ Subgroup.centralizer ({u * t} : Set Y), u * y * u⁻¹ = y⁻¹) ∧
        (127 ≤ (involutions (H : Set Y)).ncard →
          6 ≤ Nat.card ↥(Subgroup.centralizer ({u * t} : Set Y))))

/-- **[NEW — this area, App. III (2)–(5), pp.206–207; uses `BrauerSuzukiProp` and `hFT`]**
`F` transitive and faithful on `α`, of 2-rank 1, with a point stabiliser `F_a` that is strongly
embedded and maximal.  Then `F = Q ⋊ F_a` with `Q` elementary abelian of prime exponent `f`;
`F_a` has a unique involution; distinct involutions multiply into `Q` with order `f`, and `Q` is the
set of odd-order elements inverted by an involution; if `F` is 2-transitive and `p ∤ |F_a ∩ F_b|`,
a `p`-subgroup of `F_a` acts fixed-point-freely on `Q` (and is cyclic for `p` odd). -/
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

/-- **[NEW — this area, App. V (d), p.211; Schur + Galois theory of `𝔽_{d^n}`]** in ambient
form (no quotient group): `Q` elementary abelian of exponent `d`, `U ≤ N(Q)`, `T ⊴ U` cyclic and
irreducible on `Q`; `1 ≠ P ≤ U` with `|C_Q(P₁)| = d` for every `1 ≠ P₁ ≤ P`.  Then `|P| = p` is
prime, `|Q| = d^p`, and `C_U(s) = P · C_U(Q)` for `1 ≠ s ∈ C_Q(P)`.  (`P ∩ C_U(Q) = 1` is
Peterfalvi's faithfulness of `U` on `Q`; without it the statement is false for `|Q| = d`.) -/
def AppVProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (d : ℕ) (U Q T P : Subgroup G), d.Prime →
    (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) → (∀ x ∈ Q, x ^ d = 1) → Q ≠ ⊥ →
    U ≤ Subgroup.normalizer (Q : Set G) → T ≤ U → U ≤ Subgroup.normalizer (T : Set G) →
    IsCyclic ↥T →
    (∀ R : Subgroup G, R ≤ Q → T ≤ Subgroup.normalizer (R : Set G) → R = ⊥ ∨ R = Q) →
    P ≤ U → P ≠ ⊥ → P ⊓ Subgroup.centralizer (Q : Set G) = ⊥ →
    (∀ P₁ : Subgroup G, P₁ ≤ P → P₁ ≠ ⊥ →
      Nat.card ↥(Q ⊓ Subgroup.centralizer (P₁ : Set G)) = d) →
    (Nat.card P).Prime ∧ Nat.card Q = d ^ Nat.card P ∧
      ∀ s ∈ Q ⊓ Subgroup.centralizer (P : Set G), s ≠ 1 →
        U ⊓ Subgroup.centralizer ({s} : Set G) = P ⊔ (U ⊓ Subgroup.centralizer (Q : Set G))

/-- **[NEW — this area, App. VII, pp.216–220, in the form all three uses need]** `Q ⋊ P` acting by
conjugation on `K` (all inside `G`), `|P| = p` prime, `p ∤ |Q|`, `|C_Q(P)|` odd,
`(|K|, |QP|) = 1`.  If `C_K(P) = 1` then `[P,Q]` centralises `K`
(App. VII: `K = ⟨C_K([P,Q]), C_K(P^x) | x ∈ Q⟩`, and `C_K(P^x) = C_K(P)^x = 1`).
**Derive it from `Work.Hering.AppVIIProp`** (`Submission/Work/Hering/AppVII/Defs.lean`, the
abstract App. VII, stated there with `MulDistribMulAction`; its proof `appVII` is still `sorry`):
take `A := ↥(Q ⊔ P)` acting on `↥K` by conjugation.  One shared proof of App. VII serves Hering
(Ch. IV §2 step 5) and this area (§3 Prop. 1, §4 Prop. 1 step 5, §5 Prop. 3).
`hFT` only for solvability of `K` (odd order in every application here). -/
def AppVIIProp : Prop :=
  FeitThompsonProp →
  ∀ (G : Type) [Group G] [Finite G] (K Q P : Subgroup G),
    Q ≤ Subgroup.normalizer (K : Set G) → P ≤ Subgroup.normalizer (K : Set G) →
    P ≤ Subgroup.normalizer (Q : Set G) → (Nat.card P).Prime →
    ¬ Nat.card P ∣ Nat.card Q → Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G))) →
    Nat.Coprime (Nat.card K) (Nat.card ↥(Q ⊔ P)) →
    K ⊓ Subgroup.centralizer (P : Set G) = ⊥ →
    ⁅P, Q⁆ ≤ Subgroup.centralizer (K : Set G)

/-- **[NEW — small; `Work.CharCore` internals]** Burnside, Isaacs (3.9): a conjugacy class of
prime-power size `q^d > 1` is central modulo a proper normal subgroup.  The core argument is already
`Work.CharCore.false_of_prime_pow_class_chi` (stated there for simple groups); drop simplicity and
return `N = ker χ`. -/
def BurnsideClassProp : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (x : W) (q d : ℕ), q.Prime → 0 < d →
    Nat.card (ConjClasses.mk x).carrier = q ^ d →
    ∃ N : Subgroup W, N.Normal ∧ N ≠ ⊤ ∧ ∀ g : W, x * g * x⁻¹ * g⁻¹ ∈ N

/-- **[NEW — this area, Ch. III §1 Corollary of Lemma 2, p.174]** `E ≤ W` solvable, `π` the primes
of `|E|`; if `N_W(U) = O_{π'}(C_W(U)) N_E(U)` for every `1 ≠ U` a `p`-subgroup of `E` (`p ∈ π`), then
`E` is a Hall subgroup of `W` with a normal complement.  Proof: Lemma 2 (`pcontrol_criterion`),
Lemma 1 (`pcontrol_transfer`), induction on `|W|`. -/
def ControlCorollaryProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (E W : Subgroup G), E ≤ W → Group.IsSolvable ↥E →
    (∀ (p : ℕ) (U : Subgroup G), p.Prime → p ∣ Nat.card E → U ≤ E → U ≠ ⊥ → IsPGroup p U →
      W ⊓ Subgroup.normalizer (U : Set G) =
        piPrimeCoreSub {q | q ∣ Nat.card E} (W ⊓ Subgroup.centralizer (U : Set G)) ⊔
          (E ⊓ Subgroup.normalizer (U : Set G))) →
    Nat.Coprime (Nat.card E) (E.relIndex W) ∧
      ∃ N : Subgroup G, N ≤ W ∧ W ≤ Subgroup.normalizer (N : Set G) ∧ N ⊓ E = ⊥ ∧ N ⊔ E = W

/-- **[DERIVED — Ch. I §6 Cor. 1 from `ThmAProp` + `BenderPrelimProp`]** in the form §5 Prop. 2 (b)
uses: if `x ≠ 1` lies in a conjugate `H₁` of `H` with `t ∉ H₁` and `t x t⁻¹ = x⁻¹`, then `x` is
conjugate to an element of `K = J(D,t)`. -/
def ChISixCor1Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Situation G →
    ∀ H : Subgroup G, IsStronglyEmbedded H → ∀ t : G, orderOf t = 2 → t ∉ H →
    ∀ (g x : G), x ∈ conj g H → t ∉ conj g H → t * x * t⁻¹ = x⁻¹ →
      ∃ (y : G), y * x * y⁻¹ ∈ Kset (twoPoint H t) t

end Work.NormalComplement.Design
