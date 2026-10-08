/- Ported (gw_stage, 2026-10-08) from the lead design file `Submission/Work/_design_gw/Core2.lean`;
   content unchanged except this header and import paths. Namespace `GW2` (root). -/
import Submission.Work.LEAD.Contracts2

/-!
# gorenstein_walter, design pass 2: lemma-level contracts

Companion to `Submission/Work/NOTES_LEAD_gw_design2.md`. Namespace `GW2`, on top of
`Contracts2.lean`.

* Every leaf is a `Prop`. Area owners copy each statement into its own file; do NOT import
  this file.
* Hypothesis bundles (`Case1aData`, `Case1bData`, `Case2Data`) carry the objects Bender
  constructs, so that later leaves assume only earlier leaves' Props.

Sources (all on 3.129 under `gorenstein_walter/REFS/`, or in `lead_gw_prior/`):
* Bender 1981 (B81);
* Bender–Glauberman 1981 (BG);
* Bender 1970 (B70, Math. Z. 117; OCR text);
* Brauer–Suzuki–Wall 1958 (BSW);
* Bender 1974 "The BSW theorem" (B74) and "Finite groups with large subgroups" (B74L);
* Suzuki 1959 (S59);
* Glauberman 1968 (BS drive `REFS/vision/glauberman1968_zj`);
* HB III Ch. XI (BS drive `REFS/vision/hb3_1982`).
-/

open scoped MatrixGroups

namespace GW2

open Subgroup

section Helpers

variable {G : Type*} [Group G]

/-- `K^g = g K g⁻¹`. -/
def conjSub (g : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj g).toMonoidHom

/-- Involutions lying in `K`. -/
def involutionSet (K : Subgroup G) : Set G := {x | x ∈ K ∧ orderOf x = 2}

/-- `K` has one class of involutions under `K`-conjugation. -/
def OneInvClassIn (K : Subgroup G) : Prop :=
  ∀ x ∈ involutionSet K, ∀ y ∈ involutionSet K, ∃ g ∈ K, g * x * g⁻¹ = y

/-- `s` inverts every element of `K`. -/
def Inverts (s : G) (K : Subgroup G) : Prop := ∀ x ∈ K, s * x * s⁻¹ = x⁻¹

/-- Number of involutions in the left coset `g Ĥ`. Bender uses right cosets; inversion
swaps the two counts. -/
noncomputable def cosetInvCount (Hh : Subgroup G) (g : G) : ℕ :=
  {x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ Hh}.ncard

/-- Bender §3: `b_n` = number of cosets `≠ Ĥ` containing exactly `n` involutions. -/
noncomputable def bCount (Hh : Subgroup G) (n : ℕ) : ℕ :=
  {c : G ⧸ Hh | c ≠ ((1 : G) : G ⧸ Hh) ∧ cosetInvCount Hh (Quotient.out c) = n}.ncard

end Helpers

/-! ## A. Amended recognition contracts (replace the blueprint-2 versions) -/

/-- Zassenhaus hypotheses WITHOUT the cyclicity clause. HB III XI 1.5 (d odd, `G` simple) and
the proof of 1.11 (d even) derive it. -/
def ZassHyps2 (G X : Type) [Group G] [Finite G] [MulAction G X] (q : ℕ) : Prop :=
  FaithfulSMul G X ∧ Nat.card X = q + 1 ∧ MulAction.IsMultiplyPretransitive G X 2 ∧
    (∀ g : G, g ≠ 1 → {x : X | g • x = x}.ncard ≤ 2) ∧
    (∀ x y : X, x ≠ y →
      2 * Nat.card (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y : Subgroup G) = q - 1)

/-- HB III XI Theorems 1.11 + 1.12. ZASS should deliver this; it implies `ZassOddProp`. -/
def ZassOdd2Prop : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → IsSimpleGroup G → ZassHyps2 G X (p ^ k) →
    Nonempty (G ≃* PSL(2, GaloisField p k))

/-- The BSW hypotheses exactly as in Bender 1974, Theorem (i)–(iv).
* `K` is abelian and contains `t`, and `C(t) = K⟨s⟩`;
* `s` inverts `K`;
* `C_K(s) = ⟨t⟩`;
* `K` is TI with respect to `C(t)`;
* there is one class of involutions. -/
def BSWHyps2 (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) : Prop :=
  orderOf t = 2 ∧ orderOf s = 2 ∧ t ∈ K ∧ s ∉ K ∧ IsMulCommutative K ∧
    centralizer ({t} : Set G) = K ⊔ zpowers s ∧ Inverts s K ∧
    K ⊓ centralizer ({s} : Set G) = zpowers t ∧
    (∀ g : G, g ∉ centralizer ({t} : Set G) → K ⊓ conjSub g K = ⊥) ∧
    ∀ x : G, orderOf x = 2 → IsConj x t

/-- B74 §§1–3: a Zassenhaus action on the conjugates of `Q`, i.e. on `G ⧸ N(Q)`.
`G` simple and nonabelian. -/
def BSWZass2Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K →
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        ∃ M : Subgroup G, ZassHyps2 G (G ⧸ M) (p ^ k)

def BSW2Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K →
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (G ≃* PSL(2, GaloisField p k))

/-! ## B. PSTAB leaves -/

/-- A finite group with dihedral or cyclic Sylow 2-subgroups has no section containing `Q₈`.
Stated as: no subgroup `K`, normal `N ≤ K`, and subgroup of `K ⧸ N` with a unique involution
that is not cyclic, among 2-groups. -/
def NoQuaternionSectionProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], DihOrCycSylow X →
    ∀ (K : Subgroup X) (N : Subgroup K) [N.Normal] (Q : Subgroup (K ⧸ N)),
      IsPGroup 2 Q → ¬ IsCyclic Q → ¬ ∃! z : Q, orderOf z = 2

/-- Quadratic-pair lemma (replaces Glauberman L6.2 / Dickson).
* `L` acts faithfully on a finite `𝔽_p`-space `V` (p odd).
* `x ∈ L` is a `p`-element acting quadratically, with `x ∉ O_p(L)`.
* Then `L` has a 2-subgroup that is noncyclic with a unique involution.
Route: Baer–Suzuki, a composition factor of `⟨x, x^g⟩`, BG App. A
`quadratic_two_generated_irreducible_finrank_eq_two` and `thmA2`, SL₂ has unique involution `-1`,
Burnside. -/
def QuadPairProp : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) L V), Function.Injective ρ →
    ∀ x : L, IsPGroup p (zpowers x) → ((ρ x : Module.End (ZMod p) V) - 1) ^ 2 = 0 →
      x ∉ pCore p L →
      ∃ Q : Subgroup L, IsPGroup 2 Q ∧ ¬ IsCyclic Q ∧ ∃! z : Q, orderOf z = 2

/-! ## C. DSTR leaves (Bender 1981 §1.6–1.10) -/

def DihOrCycHeredProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], DihOrCycSylow X →
    (∀ K : Subgroup X, DihOrCycSylow K) ∧ (∀ (N : Subgroup X) [N.Normal], DihOrCycSylow (X ⧸ N))

def OddCoreQuotProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], oddCore (X ⧸ oddCore X) = ⊥

/-- 2-rank at most 2. -/
def TwoRankProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], DihOrCycSylow X →
    ∀ E : Subgroup X, IsMulCommutative E → (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ 4

/-- A quasisimple subgroup has noncyclic Sylow 2-subgroups (FT + Burnside). -/
def QuasisimpleSylowProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FeitThompsonProp → ∀ E : Subgroup X, IsQuasisimple E →
    ∀ P : Sylow 2 E, ¬ IsCyclic P

def LayerUniqueProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FeitThompsonProp → DihOrCycSylow X →
    ∀ E₁ E₂ : Subgroup X, E₁.Normal → E₂.Normal → IsQuasisimple E₁ → IsQuasisimple E₂ → E₁ = E₂

/-- `Z(E)` is odd: a central involution of `E` would be its only involution (FUS). -/
def QuasisimpleCenterOddProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], DihOrCycSylow X → ∀ E : Subgroup X, IsQuasisimple E →
    Odd (Nat.card (center E))

/-- `E/Z(E)` is the simple section of `X/O(X)`. -/
def LayerShapeProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FeitThompsonProp → DihOrCycSylow X → IsDGroup X →
    ∀ E : Subgroup X, E.Normal → IsQuasisimple E →
      Nonempty ((↥E ⧸ center ↥E) ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty ((↥E ⧸ center ↥E) ≃* PSL(2, GaloisField p k))

/-- 1.10(i) in the reduced shapes (`O(Q) = 1`, not a 2-group). These are model facts: L2F/A7F. -/
def D110iModelProp : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], DihOrCycSylow Q → oddCore Q = ⊥ → DShape Q →
    ∀ t : Q, orderOf t = 2 → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Subgroup Q, IsPGroup p P →
      centralizer ({t} : Set Q) ≤ normalizer (P : Set Q) → P ≤ centralizer ({t} : Set Q)

/-- 1.10(i), the case `[P,t] ⊆ O(X)`. B70 (2.4), second paragraph. -/
def D110iOddProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FeitThompsonProp → DihOrCycSylow X → IsDGroup X →
    ∀ t : X, orderOf t = 2 → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Subgroup X, IsPGroup p P →
      centralizer ({t} : Set X) ≤ normalizer (P : Set X) → ⁅P, zpowers t⁆ ≤ oddCore X →
      ⁅P, zpowers t⁆ ≤ pCore p X

/-- 1.10(ii) on the almost simple model: `F_{2'}(C_Q(t)) ≤ L`, i.e. it induces inner automorphisms. -/
def D110iiModelProp : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    L.Normal → Nonempty (L ≃* PSL(2, GaloisField p k)) → centralizer (L : Set Q) = ⊥ →
    DihOrCycSylow Q → ∀ t : Q, orderOf t = 2 →
      fittingPiIn {2}ᶜ (centralizer ({t} : Set Q)) ≤ L

/-- Lifting inner automorphisms from `E/Z(E)` to a perfect `E`. -/
def InnerLiftProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (E : Subgroup X), E.Normal → IsQuasisimple E →
    ∀ x : X, (∃ e ∈ E, ∀ y ∈ E, (x * y * x⁻¹) * (e * y * e⁻¹)⁻¹ ∈ (center E).map E.subtype) →
      ∃ e ∈ E, ∀ y ∈ E, x * y * x⁻¹ = e * y * e⁻¹

/-! ## D. CORE2A leaves (B81 Lemmas 2.1, 2.4, 2.5, Theorem 2.6) -/

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

/-! ## E. CORE3 leaves (B81 §3). Throughout: `Case1 B`. -/

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

/-! ## F. CORE4 leaves (B81 §4). Throughout: `Case2 B`. -/

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

/-! ## G. L2F extensions (requested by DSTR/CORE). All on the concrete models. -/

/-- 1.10(i) in `L₂(q)` (B81 p. 218: "obviously holds"). -/
def L2CentInvariantProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    ∀ t : PSL(2, GaloisField p k), orderOf t = 2 → ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 →
      ∀ P : Subgroup (PSL(2, GaloisField p k)), IsPGroup r P →
        centralizer ({t} : Set _) ≤ normalizer (P : Set _) → P ≤ centralizer ({t} : Set _)

/-- §4 (1): odd-order subgroups of `C_L(t)` are cyclic and inverted by an involution of
`C_L(t)` (the dihedral group `D_{q±1}`). -/
def L2CentOddCyclicProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    ∀ t : PSL(2, GaloisField p k), orderOf t = 2 → ∀ Y : Subgroup (PSL(2, GaloisField p k)),
      Y ≤ centralizer ({t} : Set _) → Odd (Nat.card Y) →
        IsCyclic Y ∧ ∃ s ∈ centralizer ({t} : Set (PSL(2, GaloisField p k))), orderOf s = 2 ∧ Inverts s Y

/-- Thm 2.6 step 2: in `PGL₂(q)`, take an involution `t ∈ L = L₂(q)` and an involution `s ∉ L`
commuting with it, and set `R = [t, C_L(s)]`, `R* = [t, C_L(ts)]`.
* Both are cyclic of the odd order `(q+ε)/2`, where `q ≡ ε (mod 4)`.
* Both are inverted by `t`.
* `⟨t, R, R*⟩` has order divisible by 4.
Checked on `q = 5` (`S₅`). -/
def PGL2CommutatorTorusProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    ∀ t s : PGL(2, GaloisField p k), orderOf t = 2 → orderOf s = 2 → t * s = s * t →
      t ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL(2, GaloisField p k) →* PGL(2, GaloisField p k)).range →
      s ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL(2, GaloisField p k) →* PGL(2, GaloisField p k)).range →
      let L := (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL(2, GaloisField p k) →* PGL(2, GaloisField p k)).range
      let R := ⁅zpowers t, L ⊓ centralizer ({s} : Set _)⁆
      let R' := ⁅zpowers t, L ⊓ centralizer ({t * s} : Set _)⁆
      let m := if p ^ k % 4 = 1 then (p ^ k + 1) / 2 else (p ^ k - 1) / 2
      IsCyclic R ∧ IsCyclic R' ∧ Nat.card R = m ∧ Nat.card R' = m ∧ Inverts t R ∧ Inverts t R' ∧
        4 ∣ Nat.card (zpowers t ⊔ R ⊔ R' : Subgroup _)

/-- §4 (11): number of subgroups of odd prime order `r ∣ (q ± 1)/2` in `L₂(q)`.
For `r ∣ (q+ε)/2`, `ε = ±1`, it is `q(q−ε)/2`. -/
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

/-! ## H. ZASS Z6 leaves (HB III XI 1.5, 1.7–1.12). Setting: `ZassHyps2 G X q`, `G` simple. -/

/-- HB 1.7(a)/(c): some involution interchanges two given points. -/
def ZassInvolutionSwapProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (q : ℕ),
    Odd q → ZassHyps2 G X q → ∀ a b : X, a ≠ b → ∃ s : G, orderOf s = 2 ∧ s • a = b ∧ s • b = a

/-- HB 1.5 (d odd) and the proof of 1.11 (d even): an element interchanging the two fixed points
of `H = G_{a,b}` inverts `H`, and `H` is cyclic. -/
def ZassInvertProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (q : ℕ),
    Odd q → 5 ≤ q → IsSimpleGroup G → ZassHyps2 G X q → ∀ a b : X, a ≠ b →
      IsCyclic (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G) ∧
      ∀ s : G, s • a = b → s • b = a →
        Inverts s (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b)

end GW2
