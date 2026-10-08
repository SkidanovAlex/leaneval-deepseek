/-
GW design pass 23, item B: Bender–Glauberman 1981 §4, Theorem 4.3 (pp. 212–214), split into
leaves with a proved assembly.  Routes, sizes and GAP evidence: `NOTES_LEAD_gw_design23.md` §B.
Vocabulary: area BG's `ThmABCCharDefs` (= design-16 `Core16Char`, namespace `Work.GW2.C16`).

CHANGE vs design 16: `C16.Thm43Prop` ends with `μ₂ 1 = ν 1 ∧ μ₃ 1 = ν 1`.  BG prove only that the
three `ν̂` are `N_G(S)`-conjugate; equal `ν`-degrees are *not* a consequence of their argument
(they follow in C4 from `U = BK`, where `ν̂ = ν|_B`).  `Thm43HatProp` below states the printed
clause.  (GAP `gw23_B.out`: degree equality held in every library triple, but it is unproved;
no consumer of `Thm43Prop` exists yet, so switching costs nothing.)
-/
import Mathlib
import Submission.Work.BG.ThmABCCharDefs

namespace Work.GW2.C23

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Vocabulary: `ν̂`, `N_G(S)`-conjugacy on `Irr(B)`, the graph `Δ` -/

/-- `θ = ν̂`: `θ ∈ Irr(B)` and `ν ≡ θ (mod 2)` on `B` (BG p. 211, Lemma 1.9). -/
def HatOf (D : BGData G) (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)
    (θ : ClassFunction ↥D.B ℂ) : Prop :=
  IsIrreducibleCharacter θ ∧
    ∀ h : ↥C.P.H0, ∀ hb : (h : G) ∈ D.B, AlgIntModTwo (ν h) (θ ⟨h, hb⟩)

/-- `θ' = θ^x`, i.e. `θ'(b) = θ(x⁻¹ b x)` (relational, so no class-function construction). -/
def ConjBy (D : BGData G) (x : G) (θ θ' : ClassFunction ↥D.B ℂ) : Prop :=
  ∀ b b' : ↥D.B, (b' : G) = x⁻¹ * (b : G) * x → θ' b = θ b'

/-- `θ` and `θ'` are `N_G(S)`-conjugate. -/
def NSConj (D : BGData G) (θ θ' : ClassFunction ↥D.B ℂ) : Prop :=
  ∃ x ∈ normalizer ((D.S : Subgroup G) : Set G), ConjBy D x θ θ'

/-- `θ` is fixed by `N_G(S)`. -/
def NSFixed (D : BGData G) (θ : ClassFunction ↥D.B ℂ) : Prop :=
  ∀ x ∈ normalizer ((D.S : Subgroup G) : Set G), ConjBy D x θ θ

section Graph

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- Adjacency in `Δ` (p. 212): distinct, not disjoint. -/
def Adj (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] (β₂ : quotGroup C.P →* ℂˣ)
    (ν μ : ClassFunction ↥C.P.H0 ℂ) : Prop :=
  ν ∈ S4Index C ∧ μ ∈ S4Index C ∧ delta C β₂ ν ≠ delta C β₂ μ ∧
    ¬ DisjointCF (delta C β₂ ν) (delta C β₂ μ)

/-- Same connected component of `Δ`. -/
def Conn (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] (β₂ : quotGroup C.P →* ℂˣ) :
    ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥C.P.H0 ℂ → Prop :=
  Relation.ReflTransGen (Adj C β₂)

theorem adj_symm (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (β₂ : quotGroup C.P →* ℂˣ) {ν μ : ClassFunction ↥C.P.H0 ℂ} (h : Adj C β₂ ν μ) :
    Adj C β₂ μ ν := by
  obtain ⟨hν, hμ, hne, hnd⟩ := h
  refine ⟨hμ, hν, Ne.symm hne, fun hd => hnd fun χ => (hd χ).symm⟩

theorem conn_symm (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (β₂ : quotGroup C.P →* ℂˣ) {ν μ : ClassFunction ↥C.P.H0 ℂ} (h : Conn C β₂ ν μ) :
    Conn C β₂ μ ν :=
by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (adj_symm C β₂ hab) ih

/-- The second alternative of Theorem 4.3 at `ν`, with BG's printed conjugacy clause. -/
def TripleAt (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (β₂ : quotGroup C.P →* ℂˣ) (ν : ClassFunction ↥C.P.H0 ℂ) : Prop :=
  ∃ μ₂ ∈ S4Index C, ∃ μ₃ ∈ S4Index C, ∃ χ₁ χ₂ χ₃ χ₄ : ClassFunction G ℂ,
    IsPmIrr χ₁ ∧ IsPmIrr χ₂ ∧ IsPmIrr χ₃ ∧ IsPmIrr χ₄ ∧
    delta C β₂ ν = χ₁ + χ₂ + χ₃ + χ₄ ∧ delta C β₂ μ₂ = χ₁ - χ₂ + χ₃ - χ₄ ∧
    delta C β₂ μ₃ = χ₁ + χ₂ - χ₃ - χ₄ ∧
    ∀ θ, HatOf D C ν θ →
      (∃ θ₂, HatOf D C μ₂ θ₂ ∧ NSConj D θ θ₂) ∧ (∃ θ₃, HatOf D C μ₃ θ₃ ∧ NSConj D θ θ₃)

/-- **Theorem 4.3 (printed form).** Replaces `C16.Thm43Prop` (see header). -/
def Thm43HatProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 → ∀ ν ∈ S4Index C,
    (∀ μ ∈ S4Index C, delta C β₂ μ ≠ delta C β₂ ν →
        DisjointCF (delta C β₂ ν) (delta C β₂ μ)) ∨
    TripleAt D C β₂ ν

/-! ## 1. Top leaves (consumed by the assembly) -/

/-- **T43-A (case "`μ̂` not `N_G(S)`-fixed", p. 212 bottom – 213 top).**  Every member of the
component of such a `μ` is in the triple pattern.  Route: N-ORB (orbit of `μ̂` has size 3);
for each constituent `χ` of `δ_μ`, L41-v makes the hat-set of `𝒮'(χ)` `N_G(S)`-invariant, so it
contains the orbit; L41 (i) `|𝒮'(χ)| ≤ 3` and HAT-INJ give `𝒮'(χ) =` the three `ν` with `ν̂` in
the orbit, for all four `χ` (DELTA-SHAPE); so the three `δ` have the same 4-element support;
HADAMARD gives the pattern (normalise `χᵢ := (δ_ν, χᵢ)χᵢ` at whichever `ν` is asked); any
`δ` adjacent to one of them shares a `χ`, whose `𝒮'` is the same triple, so the component is
exactly the triple. -/
def CaseAProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 →
    ∀ μ ∈ S4Index C, ∀ θ, HatOf D C μ θ → ¬ NSFixed D θ →
      ∀ ν, Conn C β₂ μ ν → TripleAt D C β₂ ν

/-- **T43-B (case "all hats in the component fixed", p. 213 – 214 top): impossible unless the
component is a singleton.**  Route: L42 + HAT-INJ give ODD-MULT (`δ`'s of the component are
`F₂`-independent as constituent vectors); DELTA-SHAPE, L41 (i) and ODD-MULT feed COMB413,
which yields `ν₁, ν₂, ν₃`, `χ₁` with `𝒮'(χ₁) = {ν₁,ν₂,ν₃}` and `ψⱼ` with `𝒮'(ψⱼ) = {νⱼ}`;
CONG-CONTRA refutes that. -/
def CaseBProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 →
    ∀ ν ∈ S4Index C, (∀ μ, Conn C β₂ ν μ → ∀ θ, HatOf D C μ θ → NSFixed D θ) →
      ∀ μ, ¬ Adj C β₂ ν μ

/-! ## 2. Proved assembly -/

/-- **Theorem 4.3 from T43-A and T43-B.** -/
theorem thm43_of_cases (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hA : CaseAProp D C) (hB : CaseBProp D C) : Thm43HatProp D C := by
  intro hc hn β₂ hβ ν hν
  by_cases hadj : ∃ μ, Adj C β₂ ν μ
  · right
    by_cases hall : ∀ μ, Conn C β₂ ν μ → ∀ θ, HatOf D C μ θ → NSFixed D θ
    · obtain ⟨μ, hμ⟩ := hadj
      exact absurd hμ (hB hc hn β₂ hβ ν hν hall μ)
    · push Not at hall
      obtain ⟨μ, hconn, θ, hθ, hnf⟩ := hall
      have hμ : μ ∈ S4Index C := by
        rcases Relation.ReflTransGen.cases_tail hconn with h | ⟨c, -, hc'⟩
        · exact h ▸ hν
        · exact hc'.2.1
      exact hA hc hn β₂ hβ μ hμ θ hθ hnf ν (conn_symm C β₂ hconn)
  · left
    intro μ hμ hne
    by_contra hnd
    exact hadj ⟨μ, hν, hμ, Ne.symm hne, hnd⟩

/-! ## 3. Sub-leaves of T43-A / T43-B (statements; routes in the notes) -/

/-- **HAT** (Lemma 1.9 for `ν ∈ S4Index`): `ν̂` exists and is unique.  Route: `t ∈ ker ν`, so
`ν|_U ∈ Irr(U)` is `S`-invariant; `C16.GlaubValueProp` (proved: `BG/glaubValue`) gives
existence; uniqueness from MOD2-INDEP. -/
def HatProp (D : BGData G) (C : Sec2Ctx G) : Prop :=
  Compat D C → D.n = 2 → ∀ ν ∈ S4Index C,
    (∃ θ, HatOf D C ν θ) ∧ ∀ θ θ', HatOf D C ν θ → HatOf D C ν θ' → θ = θ'

/-- **HAT-INJ** (`ν ↦ ν̂` is one-to-one, used on p. 212 l. −14).  Glauberman correspondence
injectivity; NOT in the tree (`glaubermanGeneralProp` is existence+uniqueness only).  Route:
`ν ↦ ν|_U` is injective on `S4Index` (`H₀ = U × ⟨t⟩`, `t ∈ ker ν`), then injectivity of the
Glauberman map for the involutions `t₁`, `t₂` in turn (Isaacs 13.1/13.14 via Brauer's
permutation lemma, available in `OddOrder/Peterfalvi/S03`).  RISK leaf. -/
def HatInjProp (D : BGData G) (C : Sec2Ctx G) : Prop :=
  Compat D C → D.n = 2 → ∀ ν ∈ S4Index C, ∀ μ ∈ S4Index C, ∀ θ,
    HatOf D C ν θ → HatOf D C μ θ → ν = μ

/-- **MOD2-INDEP** (Lemma 1.8, algebraic-integer-coefficient form; pure).  On an odd-order
group, `Σ cⱼ βⱼ ≡ 0 (mod 2)` pointwise with distinct irreducible `βⱼ` and algebraic-integer
`cⱼ` forces every `cⱼ ≡ 0 (mod 2)`.  Route: inner product with `βₖ`, times `|B|` odd. -/
def ModTwoIndepProp : Prop :=
  ∀ {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)], Odd (Nat.card K) →
    ∀ {ι : Type} [Fintype ι] (β : ι → ClassFunction K ℂ), (∀ i, IsIrreducibleCharacter (β i)) →
      Function.Injective β → ∀ c : ι → ℂ, (∀ i, IsIntegral ℤ (c i)) →
        (∀ g : K, AlgIntModTwo (∑ i, c i * β i g) 0) → ∀ i, AlgIntModTwo (c i) 0

/-- **L41-iii** (p. 212): `χ ≡ Σ_{ν ∈ 𝒮'(χ)} ν̂` on `B`.  Route: C16 `Lemma24Prop` (iii) on `U`,
the bijection `𝒮(χ) ↔ 𝒮'(χ)` (`ν` or `λ₂ν`, equal on `U`), HAT. -/
def L41iiiProp (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 →
    ∀ χ : ClassFunction G ℂ, IsPmIrr χ → (bset' C β₂ χ).Finite ∧
      ∀ θ : ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥D.B ℂ,
        (∀ ν ∈ bset' C β₂ χ, HatOf D C ν (θ ν)) →
        ∀ b : ↥D.B, AlgIntModTwo (χ (b : G)) (∑ᶠ ν ∈ bset' C β₂ χ, θ ν b)

/-- **L41-v** (p. 212): the hat-set of `𝒮'(χ)` is `N_G(S)`-invariant.  Route: L41-iii,
`χ(x⁻¹bx) = χ(b)`, HAT-INJ, MOD2-INDEP. -/
def L41vProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 →
    ∀ χ : ClassFunction G ℂ, IsPmIrr χ → ∀ ν ∈ bset' C β₂ χ, ∀ θ, HatOf D C ν θ →
      ∀ x ∈ normalizer ((D.S : Subgroup G) : Set G), ∀ θ', ConjBy D x θ θ' →
        ∃ μ ∈ bset' C β₂ χ, HatOf D C μ θ'

/-- **N-ORB**: `C_G(S) = S × B`, `|N_G(S) : C_G(S)| = 3`; hence every `N_G(S)`-orbit on `Irr(B)`
has 1 or 3 elements, and a non-fixed `θ` has three pairwise distinct conjugates.  Route: `S`
abelian Sylow (Burnside fusion: `t ~ t₁` in `N_G(S)`), `N/C ↪ Aut(S) ≅ S₃` of odd order;
`C_G(S) ≤ C_G(t) = H`, `C_H(S) = S × C_U(S)`. -/
def NOrbProp (D : BGData G) : Prop :=
  D.n = 2 → ∀ θ : ClassFunction ↥D.B ℂ, ¬ NSFixed D θ →
    ∃ θ₂ θ₃, NSConj D θ θ₂ ∧ NSConj D θ θ₃ ∧ θ ≠ θ₂ ∧ θ ≠ θ₃ ∧ θ₂ ≠ θ₃ ∧
      ∀ θ', NSConj D θ θ' → θ' = θ ∨ θ' = θ₂ ∨ θ' = θ₃

/-- **DELTA-SHAPE**: `δ_ν` is a sum of four distinct `±Irr`.  Route: `‖δ_ν‖² = 4` (Frobenius +
Lemma 1.3, S02 `IndDiffProp`/`GramProp`: `(δ,δ) = ((ν-λ₂ν) + (ν-λ₂ν)^s, ν-λ₂ν) = 4`),
`δ_ν(1) = 0` excludes `±2χ`. -/
def DeltaShapeProp (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 → ∀ ν ∈ S4Index C,
    ∃ T : Finset (IrreducibleCharacter G), T.card = 4 ∧
      (∀ χ ∈ T, ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) = 1 ∨
        ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) = -1) ∧
      ∀ χ ∉ T, ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) = 0

/-- **HADAMARD** (pure): three pairwise orthogonal `±1`-vectors on a 4-set are, after rescaling
the coordinates by the first, `(1,1,1,1), (1,-1,1,-1), (1,1,-1,-1)` in a suitable order. -/
def HadamardProp : Prop :=
  ∀ {ι : Type} (T : Finset ι) (a b c : ι → ℤ), T.card = 4 →
    (∀ i ∈ T, a i ^ 2 = 1 ∧ b i ^ 2 = 1 ∧ c i ^ 2 = 1) →
    ∑ i ∈ T, a i * b i = 0 → ∑ i ∈ T, a i * c i = 0 → ∑ i ∈ T, b i * c i = 0 →
    ∃ e : Fin 4 → ι, Function.Injective e ∧ (∀ k, e k ∈ T) ∧
      (∀ k, b (e k) * a (e k) = ![1, -1, 1, -1] k) ∧
      (∀ k, c (e k) * a (e k) = ![1, 1, -1, -1] k)

/-- **L42-a**: `δ_ν` vanishes on `B` (odd elements of `H₀` lie in `U`, `λ₂ = 1` on `U`). -/
def DeltaVanishBProp (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 → ∀ ν ∈ S4Index C,
    ∀ b ∈ D.B, delta C β₂ ν b = 0

/-- **L42-b**: `δ_ν(t b) = 4 ν(b)` for `b ∈ B` (Lemma 1.3 value on `T`: `2((ν-λ₂ν)(tb) +
(ν-λ₂ν)(tb)^s)`, `λ₂(t) = -1`, `t ∈ ker ν`). -/
def DeltaAtTBProp (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 → ∀ ν ∈ S4Index C,
    ∀ h : ↥C.P.H0, (h : G) ∈ D.B → delta C β₂ ν ((C.t : G) * h) = 4 * ν h

/-- **L42 (Lemma 4.2)**: `μ' := (1_S × μ̂)^G` is a (virtual) character with
`(δ_ν, μ')` odd iff `ν̂ ~ μ̂` under `N_G(S)`.  Route: L42-a, L42-b, N-ORB (`C_G(S) = S × B`,
coset reps `x` with `{t^x} = S#`), Frobenius on `S × B`, then `ν|_B ≡ ν̂` and
`#{x : ν̂^x = μ̂} ∈ {0, 1, 3}` (odd iff conjugate).  ≈ 800 lines, split L42-c1 (exact identity
`|B|(δ,μ') = Σ_x Σ_b ν(b^{x⁻¹}) conj μ̂(b)`) / L42-c2 (parity). -/
def Lemma42Prop (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 →
    ∀ μ ∈ S4Index C, ∀ θμ, HatOf D C μ θμ →
      ∃ μ' : ClassFunction G ℂ, μ' ∈ ZIrr G ∧
        ∀ ν ∈ S4Index C, ∀ θν, HatOf D C ν θν →
          ∃ k : ℤ, ClassFunction.inner (delta C β₂ ν) μ' = k ∧ (Odd k ↔ NSConj D θν θμ)

/-- **COMB413** (pure, p. 213): a finite family `v` of `{0,±1}`-vectors with supports of size 4,
pairwise orthogonal, every coordinate in 0, 1 or 3 members, `F₂`-independent (any integer
combination with an odd coefficient has an odd entry), and two members sharing a coordinate,
contains `j₁ j₂ j₃` and coordinates `i₀` (`χ₁`: exactly in `j₁ j₂ j₃`) and `p₁ p₂ p₃`
(`ψₘ`: exactly in `jₘ`).  Route: BG's case analysis `δ₁..δ₆`. -/
def Comb413Prop : Prop :=
  ∀ {ι J : Type} [Fintype ι] [Fintype J] [DecidableEq J] (v : J → ι → ℤ),
    (∀ j, (Finset.univ.filter fun i => v j i ≠ 0).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1) →
    (∀ j k, j ≠ k → ∑ i, v j i * v k i = 0) →
    (∀ i, (Finset.univ.filter fun j => v j i ≠ 0).card ∈ ({0, 1, 3} : Finset ℕ)) →
    (∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i)) →
    (∃ j k i, j ≠ k ∧ v j i ≠ 0 ∧ v k i ≠ 0) →
    ∃ j₁ j₂ j₃ : J, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧
      (∃ i₀, ∀ j, v j i₀ ≠ 0 ↔ (j = j₁ ∨ j = j₂ ∨ j = j₃)) ∧
      ∃ p₁ p₂ p₃ : ι, (∀ j, v j p₁ ≠ 0 ↔ j = j₁) ∧ (∀ j, v j p₂ ≠ 0 ↔ j = j₂) ∧
        (∀ j, v j p₃ ≠ 0 ↔ j = j₃)

/-- **CONG-CONTRA** (p. 213 bottom – 214 top): the COMB413 configuration is impossible.
Route: CC1 `ω_χ(ĝ) ≡ χ(b)` if `g ~ sb` (`s ∈ S`, `b ∈ B`), `≡ 0` otherwise (X3, L41 (iv),
`lemma16_mod_two`), hence `ω_{χ₁} ≡ Σ ω_{ψⱼ}` on all classes (L41-iii); CC2 central characters
are multiplicative on class sums, giving `Σ ν̂ⱼ(a)ν̂ⱼ(b) ≡ (Σ ν̂ⱼ(a))(Σ ν̂ⱼ(b))` on `B`;
CC3 MOD2-INDEP twice (`ν̂₂ + ν̂₃ ≡ 0`), with HAT-INJ for distinctness. -/
def CongContraProp (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 →
    ∀ ν₁ ν₂ ν₃ : ClassFunction ↥C.P.H0 ℂ, ν₁ ≠ ν₂ → ν₁ ≠ ν₃ → ν₂ ≠ ν₃ →
    ∀ χ₁ ψ₁ ψ₂ ψ₃ : ClassFunction G ℂ, IsPmIrr χ₁ → IsPmIrr ψ₁ → IsPmIrr ψ₂ → IsPmIrr ψ₃ →
      bset' C β₂ χ₁ = {ν₁, ν₂, ν₃} → bset' C β₂ ψ₁ = {ν₁} → bset' C β₂ ψ₂ = {ν₂} →
      bset' C β₂ ψ₃ = {ν₃} → False

end Graph

end Work.GW2.C23
