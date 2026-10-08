import Submission.Work.BG.H0Conj

/-!
# Area BG: BG §2 vocabulary — Lemma 2.1 and the Coherence Theorem 2.3 (design pass 10)

Copied verbatim from `Submission/Work/_design_gw/Core10.lean` (namespace `GW2.C10BG`) into
`Work.BG`, as instructed by the lead's design pass 10 (message of 2026-10-05, item 2).  These
are the *statements* (as `Prop`-valued definitions or structures), with no proofs; the leaves
are dispatched separately.

Page references are to Bender–Glauberman, J. Algebra 70 (1981), read from the page images.
The paper's `H₀` is the area's `P.H0` (`= U S₀`), `δ*` is induction `H₀ → G` (or `H → G`),
and `|φ| := (φ, φ)` (squared norm, p. 201).

Note for users: `Sec2Ctx` is the standing §2 data (`t`, `s`, one class of involutions,
`H₀/U` cyclic 2-group inverted by `s`, `t` central).  The `…Prop`s are the leaves of
Lemmas 2.1/2.2 and of the Coherence Theorem 2.3.

Page references are to Bender–Glauberman, J. Algebra 70 (1981), read from the page images
(the transcription `BG/PAPER_BG1981.md` is wrong for Lemma 1.7, Lemma 2.1, Lemma 2.2 and
Theorem 2.3, see the notes).  The paper's `H₀` is the area's `P.H0` (`= U S₀`), `δ*` is
induction `H₀ → G` (or `H → G`), and `|φ| := (φ, φ)` (squared norm, p. 201).

Every `…Prop` below is a leaf or an assembly step; no statement here is proved.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Subgroup

/-! ## 0. The §2 context -/

/-- The standing data of BG §2 (Hypotheses 1.1 + 1.2 in the form §2 uses).

* `t` : the involution of `S₀`, central in `H = C_G(t)`, the only involution of `H₀`;
* `s` : an involution of `S ∖ S₀` (so `s ∈ H ∖ H₀`);
* one class of involutions in `G`;
* `H₀/U ≅ S₀` is a cyclic 2-group, inverted by `s`.

The cyclicity and 2-group conditions are written without the quotient group, so that the
structure does not need the normality instance in its own field types. -/
structure Sec2Ctx (G : Type) [Group G] [Finite G] where
  P : Hyp12 G
  U_normal : (P.U.subgroupOf P.H0).Normal
  t : ↥P.H0
  s : ↥P.H
  t_sq : t ^ 2 = 1
  t_not_mem_U : (t : G) ∉ P.U
  t_comm_H : ∀ x ∈ P.H, x * (t : G) = (t : G) * x
  s_sq : s ^ 2 = 1
  s_not_mem_H0 : (s : G) ∉ P.H0
  inv_H0 : ∀ x ∈ P.H0, x ^ 2 = 1 → x = 1 ∨ x = (t : G)
  one_class : ∀ x : G, x ^ 2 = 1 → x ≠ 1 → IsConj x (t : G)
  /-- `H₀/U` is cyclic: generated mod `U` by one element. -/
  quot_cyclic : ∃ c ∈ P.H0, ∀ x ∈ P.H0, ∃ k : ℤ, x * (c ^ k)⁻¹ ∈ P.U
  /-- `H₀/U` is a 2-group. -/
  quot_two : ∀ x ∈ P.H0, ∃ n : ℕ, x ^ (2 ^ n) ∈ P.U
  /-- `s` inverts `H₀/U` (it inverts `S₀`). -/
  s_inverts : ∀ x ∈ P.H0, (s : G) * x * (s : G)⁻¹ * x ∈ P.U

variable {G : Type} [Group G] [Finite G]

instance Sec2Ctx.instUNormal (C : Sec2Ctx G) : (C.P.U.subgroupOf C.P.H0).Normal := C.U_normal

/-- The element `λ_β ∈ Λ` attached to `β : H₀/U →* ℂˣ` (inflated to `H₀`). -/
noncomputable def lamCF (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) : ClassFunction ↥C.P.H0 ℂ :=
  ClassFunction.compHom (quotMk C.P) (linearClassFunction β)

/-- `μ` and `ν` are *equivalent* (same `Λ`-orbit; BG p. 205): `ν = λ μ` for some `λ ∈ Λ`. -/
def LamEquiv (C : Sec2Ctx G) (μ ν : ClassFunction ↥C.P.H0 ℂ) : Prop :=
  ∃ β : quotGroup C.P →* ℂˣ, ν = lamCF C β * μ

/-- The `Λ`-orbit `Λν` (as a set; it is finite). -/
def lamOrbit (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) : Set (ClassFunction ↥C.P.H0 ℂ) :=
  {χ | LamEquiv C ν χ}

/-- `ν ↦ ν^s` (area BG's `conjByH`). -/
noncomputable def sconj (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction ↥C.P.H0 ℂ :=
  conjByH C.P C.s ν

/-- The `G`-class of `t`, as a finset. -/
noncomputable def tClass (C : Sec2Ctx G) [Fintype G] : Finset G := by
  classical exact Finset.univ.filter (fun x : G => IsConj x (C.t : G))

/-- `φ ∈ ±Irr(G)`. -/
def IsPmIrr {K : Type} [Group K] (φ : ClassFunction K ℂ) : Prop :=
  IsIrreducibleCharacter φ ∨ IsIrreducibleCharacter (-φ)

/-- `α` and `β` are *disjoint* (no common irreducible constituent), in the orientation of
area BG's `remark15Disjoint`. -/
def DisjointCF {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    (α β : ClassFunction K ℂ) : Prop :=
  ∀ χ : IrreducibleCharacter K,
    ClassFunction.inner α (χ : ClassFunction K ℂ) = 0 ∨
      ClassFunction.inner β (χ : ClassFunction K ℂ) = 0

/-! ## 1. Lemma 2.1 (p. 204) — as printed: the ORBIT `Λν`, not the stabiliser `Λ_ν` -/

/-- **BG Lemma 2.1.** For `ν ∈ Irr(H₀)`: exactly half of the characters in the orbit `Λν`
have `t` in their kernel; and if `(Λν)^s = Λν`, exactly two characters of `Λν` are fixed
by `s`.  (Printed proof: "the first assertion follows from `Λ_ν ⊆ Λ₁`", where
`Λ₁ = {λ | λ(t) = 1}`.) -/
def Lemma21Prop (C : Sec2Ctx G) : Prop :=
  ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
    2 * {χ ∈ lamOrbit C ν | χ C.t = χ 1}.ncard = (lamOrbit C ν).ncard ∧
    (sconj C '' lamOrbit C ν = lamOrbit C ν →
      {χ ∈ lamOrbit C ν | sconj C χ = χ}.ncard = 2)

/-- L2.1-a. Schur for the central involution `t`: `ν(t) = ±ν(1)`. -/
def CentralValueProp (C : Sec2Ctx G) : Prop :=
  ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
    (ν C.t = ν 1 ∨ ν C.t = -ν 1) ∧ ν 1 ≠ 0

/-- L2.1-b. `s` maps `Λ` to `Λ` by inversion: `(λ_β ν)^s = λ_{β⁻¹} ν^s`. -/
def SconjLamProp (C : Sec2Ctx G) : Prop :=
  ∀ (β : quotGroup C.P →* ℂˣ) (ν : ClassFunction ↥C.P.H0 ℂ),
    sconj C (lamCF C β * ν) = lamCF C β⁻¹ * sconj C ν

/-- L2.1-c. The orbit is finite of 2-power size `≥ 2`. -/
def OrbitCardProp (C : Sec2Ctx G) : Prop :=
  ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
    (lamOrbit C ν).Finite ∧ ∃ k : ℕ, (lamOrbit C ν).ncard = 2 ^ (k + 1)

/-- L2.1-d (the form used by 2.3(vi) and by the choice of `θ₂` on p. 206): if `ν^s ≠ ν`
and not (`|Λν| = 4` and `(Λν)^s = Λν`), some `μ ∈ Λν` has `μ^s ≠ μ` and `μ(t) = -ν(t)`. -/
def Lemma21ExtProp (C : Sec2Ctx G) : Prop :=
  ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν → sconj C ν ≠ ν →
    ¬ ((lamOrbit C ν).ncard = 4 ∧ sconj C '' lamOrbit C ν = lamOrbit C ν) →
    ∃ μ ∈ lamOrbit C ν, sconj C μ ≠ μ ∧ μ C.t = -ν C.t

/-! ## 2. Inputs to Theorem 2.3 from §1 (Lemma 1.3, Remark 1.4, Lemma 1.7) -/

section Inputs

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `ind := Ind_{H₀}^G`. -/
noncomputable abbrev ind (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (θ : ClassFunction ↥C.P.H0 ℂ) : ClassFunction G ℂ :=
  ClassFunction.induce C.P.H0 θ

/-- `(α^H, β^H)_H` for `α, β ∈ Irr(H₀)` (Remark 1.4): `[β = α] + [β = α^s]`. -/
noncomputable def cH (C : Sec2Ctx G) (α β : ClassFunction ↥C.P.H0 ℂ) : ℂ := by
  classical exact (if β = α then 1 else 0) + (if β = sconj C α then 1 else 0)

/-- I-1. Differences of equivalent irreducibles induce to degree-0 virtual characters. -/
def IndDiffProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∀ μ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
    LamEquiv C μ ν → ind C (μ - ν) ∈ ZIrr G ∧ ind C (μ - ν) 1 = 0

/-- I-2. **Brauer–Suzuki Gram matrix** (Lemma 1.3 isometry + Remark 1.4), in `H₀` terms. -/
def GramProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∀ μ ν μ' ν' : ClassFunction ↥C.P.H0 ℂ,
    IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
    IsIrreducibleCharacter μ' → IsIrreducibleCharacter ν' →
    LamEquiv C μ ν → LamEquiv C μ' ν' →
    ClassFunction.inner (ind C (μ - ν)) (ind C (μ' - ν')) =
      cH C μ μ' - cH C μ ν' - cH C ν μ' + cH C ν ν'

/-- I-3. **Lemma 1.3 value at `t`**: `(μ - ν)*(t) = (μ - ν)^H(t) = 2(μ(t) - ν(t))`. -/
def BSValueProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∀ μ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
    LamEquiv C μ ν → ind C (μ - ν) (C.t : G) = 2 * (μ C.t - ν C.t)

/-- I-3'. **Lemma 1.3 value on `T`**, general point: `(μ - ν)*(g) = (μ - ν)^H(g)
= (μ - ν)(g) + (μ - ν)(s g s⁻¹)` for `g ∈ H₀ ∖ U`.  `BSValueProp` is its instance `g = t`. -/
def BSValueTProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∀ μ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
    LamEquiv C μ ν → ∀ g : ↥C.P.H0, (g : G) ∉ C.P.U →
      ind C (μ - ν) (g : G) = (μ - ν) g + (μ - ν) (conjMulEquiv C.P C.s g)

/-- I-4. **Lemma 1.7 (i)+(ii) evaluated on `T`**, with orbit representatives `rep` (constant
on orbits).  No freeness hypothesis is needed in this form (the sum runs over `Irr(H₀)`). -/
def Lemma17TProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (IrreducibleCharacter ↥C.P.H0)] : Prop :=
  ∀ (χ : ClassFunction G ℂ) (rep : ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥C.P.H0 ℂ),
    (∀ ν : IrreducibleCharacter ↥C.P.H0,
      IsIrreducibleCharacter (rep ν) ∧ LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (rep ν)) →
    (∀ ν ν' : IrreducibleCharacter ↥C.P.H0,
      LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) ν' → rep ν = rep ν') →
    ∀ g : ↥C.P.H0, (g : G) ∉ C.P.U →
      χ (g : G) = ∑ ν : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner χ (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - rep ν)) *
          (ν : ClassFunction ↥C.P.H0 ℂ) g

/-- The orbit indicator `[ξ ∈ Λν] · ξ(g)`. -/
noncomputable def orbitTerm (C : Sec2Ctx G) (ν ξ : ClassFunction ↥C.P.H0 ℂ) (g : ↥C.P.H0) : ℂ := by
  classical exact if LamEquiv C ν ξ then ξ g else 0

/-- I-4a. The orbit sum `r(Λν)` vanishes off `U` (Lemma 1.7(i), each orbit member once). -/
def OrbitSumVanishProp (C : Sec2Ctx G) [Fintype (IrreducibleCharacter ↥C.P.H0)] : Prop :=
  ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
    ∀ g : ↥C.P.H0, (g : G) ∉ C.P.U →
      ∑ ξ : IrreducibleCharacter ↥C.P.H0, orbitTerm C ν (ξ : ClassFunction ↥C.P.H0 ℂ) g = 0

end Inputs

/-! ## 3. Lemma 2.2, case 1 (the only case Theorem 2.3 uses) -/

section L22

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- L2.2-a (pure). Central-character square: for a union of classes `X` and `θ ∈ ±Irr(K)`,
`θ(1) · Σ_{x,y ∈ X} θ(xy) = (Σ_{x ∈ X} θ(x))²`. -/
def ClassSumSquareProp : Prop :=
  ∀ {K : Type} [Group K] [Fintype K] (X : Finset K),
    (∀ g x : K, x ∈ X → g * x * g⁻¹ ∈ X) →
    ∀ θ : ClassFunction K ℂ, IsPmIrr θ →
      θ 1 * ∑ x ∈ X, ∑ y ∈ X, θ (x * y) = (∑ x ∈ X, θ x) ^ 2

/-- L2.2-b. Involutions with product in `T` lie in `H ∖ H₀` (p. 205: `x` inverts `xy ∈ T`,
`T` is TI with `N_G(T) = H`, and `t` is the only involution of `H₀`). -/
def InvolutionPairProp (C : Sec2Ctx G) : Prop :=
  ∀ g ∈ Tset C.P.H0 C.P.U, ∀ x y : G, x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x * y = g →
    x ∈ C.P.H ∧ x ∉ C.P.H0

/-- L2.2-c. **Lemma 2.2, first case**, in pair-count form:
`Σ_{x,y ∈ t^G} (μ - ν)*(xy) = 0` when `μ ~ ν` and `μ^s ≠ μ`, `ν^s ≠ ν`.
(Frobenius from `H₀`, then L2.2-b, then L2.2-a inside `H` for the irreducible `μ^H`, `ν^H`
which vanish on `H ∖ H₀`.) -/
def Lemma22CaseOneProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∀ μ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
    LamEquiv C μ ν → sconj C μ ≠ μ → sconj C ν ≠ ν →
    ∑ x ∈ tClass C, ∑ y ∈ tClass C, ind C (μ - ν) (x * y) = 0

/-- L2.2-d. The consequence used in 2.3: if `(μ - ν)* = α - β` with `α, β ∈ ±Irr(G)`, then
`α(t)² = β(t)²` (p. 206, "by Lemma 2.2"). -/
def Lemma22SqProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∀ μ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
    LamEquiv C μ ν → sconj C μ ≠ μ → sconj C ν ≠ ν →
    ∀ α β : ClassFunction G ℂ, IsPmIrr α → IsPmIrr β → ind C (μ - ν) = α - β →
      α (C.t : G) ^ 2 = β (C.t : G) ^ 2

/-- 2.3(vi)-core. With `μ(t) = -ν(t)` and `(μ - ν)* = μ̃ - ν̃` (`μ̃, ν̃ ∈ ±Irr`): `ν̃(t) = 2ν(t)`.
(L2.2-d + I-3 + L2.1-a: `μ̃(t) - ν̃(t) = 4μ(t) ≠ 0` and `μ̃(t)² = ν̃(t)²`.) -/
def ViProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∀ μ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
    LamEquiv C μ ν → sconj C μ ≠ μ → sconj C ν ≠ ν → μ C.t = -ν C.t →
    ∀ gμ gν : ClassFunction G ℂ, IsPmIrr gμ → IsPmIrr gν → ind C (μ - ν) = gμ - gν →
      gν (C.t : G) = 2 * ν C.t

end L22

/-! ## 4. The pure combinatorial core of the construction (p. 206) -/

section Pure

/-- P-1 (pure). **Common constituent** (p. 206, with Remark 1.5): two degree-0 virtual
characters of norms in `{2,3}` with inner product `1` have a unique common constituent `χ`
(`(δ,χ) = (ε,χ) = 1`, `χ ∈ ±Irr`), and `δ - χ`, `ε - χ` are disjoint. -/
def CommonConstituentProp : Prop :=
  ∀ {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    (δ ε : ClassFunction K ℂ), δ ∈ ZIrr K → ε ∈ ZIrr K → δ 1 = 0 → ε 1 = 0 →
    (ClassFunction.inner δ δ = 2 ∨ ClassFunction.inner δ δ = 3) →
    (ClassFunction.inner ε ε = 2 ∨ ClassFunction.inner ε ε = 3) →
    ClassFunction.inner δ ε = 1 →
    ∃ χ : ClassFunction K ℂ, IsPmIrr χ ∧ ClassFunction.inner δ χ = 1 ∧
      ClassFunction.inner ε χ = 1 ∧ DisjointCF (δ - χ) (ε - χ) ∧
      ∀ χ' : ClassFunction K ℂ, IsPmIrr χ' → ClassFunction.inner δ χ' = 1 →
        ClassFunction.inner ε χ' = 1 → χ' = χ

/-- P-2 (pure). The case `n = 2` ("easy"): a degree-0 virtual character of norm `2a`
(`a ∈ {1,2}`) splits as `g₁ - g₂` with `g₁, g₂` disjoint of norm `a`. -/
def TwoCaseProp : Prop :=
  ∀ {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    (D : ClassFunction K ℂ) (a : ℕ), (a = 1 ∨ a = 2) → D ∈ ZIrr K → D 1 = 0 →
    ClassFunction.inner D D = 2 * (a : ℂ) →
    ∃ g₁ g₂ : ClassFunction K ℂ, g₁ ∈ ZIrr K ∧ g₂ ∈ ZIrr K ∧
      ClassFunction.inner g₁ g₁ = a ∧ ClassFunction.inner g₂ g₂ = a ∧
      D = g₁ - g₂ ∧ DisjointCF g₁ g₂

/-- The one configuration the construction of p. 206 cannot handle: `θ̃₁` (`= g₁`) is not a
constituent of `δ_j*` for an index `j ∉ {1,2,3}` with `θ_j` reducible, and then
`δ₂* = g₁ - g₂`, `δ₃* = g₁ - g₃`, `δ_j* = φ - g₂ - g₃` (p. 206 bottom). -/
def FailConfig {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    {ι : Type} (D : ι → ClassFunction K ℂ) (i1 i2 i3 j : ι) : Prop :=
  ∃ g₁ g₂ g₃ φ : ClassFunction K ℂ,
    IsPmIrr g₁ ∧ IsPmIrr g₂ ∧ IsPmIrr g₃ ∧ IsPmIrr φ ∧
    D i2 = g₁ - g₂ ∧ D i3 = g₁ - g₃ ∧ D j = φ - g₂ - g₃ ∧
    ClassFunction.inner g₁ g₂ = 0 ∧ ClassFunction.inner g₁ g₃ = 0 ∧
    ClassFunction.inner g₂ g₃ = 0 ∧ ClassFunction.inner g₁ φ = 0 ∧
    ClassFunction.inner g₂ φ = 0 ∧ ClassFunction.inner g₃ φ = 0 ∧
    ∀ i, i ≠ i1 → i ≠ j → ClassFunction.inner (D i) g₁ = 1

/-- P-3 (pure). **The construction of p. 206**, abstracted.  Index set `ι` = the characters
`θ_i` of `H` induced from one `Λ`-orbit; `a i = |θ_i| ∈ {1,2}`; `D i = δ_i* = (θ₁ - θ_i)*`.
Given the Gram matrix and that the failure configuration never occurs, there are pairwise
disjoint `θ̃_i` with `|θ̃_i| = |θ_i|` and `δ_i* = θ̃₁ - θ̃_i`.  (`θ̃₁ := χ₂₃` from P-1;
`θ̃_i := θ̃₁ - δ_i*`; the only obstruction is `FailConfig`.) -/
def AbstractCoherenceProp : Prop :=
  ∀ {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (i1 i2 i3 : ι),
    i1 ≠ i2 → i1 ≠ i3 → i2 ≠ i3 →
    ∀ (a : ι → ℕ), (∀ i, a i = 1 ∨ a i = 2) → a i1 = 1 →
    (4 ≤ Fintype.card ι → a i2 = 1 ∧ a i3 = 1) →
    ∀ (D : ι → ClassFunction K ℂ), (∀ i, D i ∈ ZIrr K) → D i1 = 0 → (∀ i, D i 1 = 0) →
    (∀ i k, i ≠ i1 → k ≠ i1 →
      ClassFunction.inner (D i) (D k) = (a i1 : ℂ) + if i = k then (a i : ℂ) else 0) →
    (∀ j, j ≠ i1 → j ≠ i2 → j ≠ i3 → a j = 2 → ¬ FailConfig D i1 i2 i3 j) →
    ∃ g : ι → ClassFunction K ℂ,
      (∀ i, g i ∈ ZIrr K ∧ ClassFunction.inner (g i) (g i) = (a i : ℂ)) ∧
      (∀ i, D i = g i1 - g i) ∧ (∀ i k, i ≠ k → DisjointCF (g i) (g k)) ∧ IsPmIrr (g i1)

end Pure

/-! ## 5. Excluding the failure configuration (pp. 206–207) -/

section NoFail

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- N-1. **The failure configuration does not occur** (p. 207: other orbits contribute `0`
because `7x² ≤ 4`; Lemma 1.7 on `T` gives `θ̃₂(t) = 2α(t) + β(t)`; the (vi) argument for
`θ₁, θ₂` gives `θ̃₂(t) = 2α(t)`; and `β(t) ≠ 0`).

`r : ι → Irr(H₀)` is a transversal of one `Λ`-orbit modulo `s`-conjugacy; `r i1`, `r i2` are
not `s`-fixed with `r i2 (t) = -r i1 (t)`; `r j` is `s`-fixed. -/
def NoFailProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (r : ι → ClassFunction ↥C.P.H0 ℂ)
    (i1 i2 i3 j : ι),
    (∀ i, IsIrreducibleCharacter (r i)) → (∀ i, LamEquiv C (r i1) (r i)) →
    (∀ ξ : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ξ → LamEquiv C (r i1) ξ →
      ∃! i, ξ = r i ∨ ξ = sconj C (r i)) →
    i1 ≠ i2 → i1 ≠ i3 → i2 ≠ i3 → j ≠ i1 → j ≠ i2 → j ≠ i3 →
    sconj C (r i1) ≠ r i1 → sconj C (r i2) ≠ r i2 → r i2 C.t = -r i1 C.t →
    sconj C (r j) = r j →
    ¬ FailConfig (fun i => ind C (r i1 - r i)) i1 i2 i3 j

end NoFail

/-! ## 6. Theorem 2.3: per-orbit form, global form, assembly -/

section Coherence

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- The `s`-closed union of an orbit and its conjugate, `Λν ∪ (Λν)^s` (= `Λν ∪ Λν^s`). -/
def orbitKey (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) : Set (ClassFunction ↥C.P.H0 ℂ) :=
  lamOrbit C ν ∪ sconj C '' lamOrbit C ν

/-- What a coherent map must satisfy on one key `E` (2.3 (i), (ii), (iii), (vi) and
`ν̃^s = ν̃`). -/
def GoodOn (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (E : Set (ClassFunction ↥C.P.H0 ℂ))
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) : Prop :=
  ∀ μ ∈ E, ∀ ν ∈ E, IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
    f ν ∈ ZIrr G ∧
    f (sconj C ν) = f ν ∧
    ClassFunction.inner (f ν) (f ν) = (by classical exact if sconj C ν = ν then 2 else 1) ∧
    (LamEquiv C μ ν → ind C (μ - ν) = f μ - f ν) ∧
    (LamEquiv C μ ν → μ ≠ ν → μ ≠ sconj C ν → DisjointCF (f μ) (f ν)) ∧
    (sconj C ν ≠ ν →
      ¬ ((lamOrbit C ν).ncard = 4 ∧ sconj C '' lamOrbit C ν = lamOrbit C ν) →
      f ν (C.t : G) = 2 * ν C.t)

/-- C-1. **Per-orbit coherence**: on every key there is a good map.  Proof: L2.1(-c,-d),
I-1, I-2, P-1..P-3, N-1, `ViProp` (route in design10 §2.4). -/
def OrbitCoherenceProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
    ∃ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, GoodOn C (orbitKey C ν) f

/-- **BG Coherence Theorem 2.3** (p. 206), (i), (ii), (iii), (vi) and `ν̃^s = ν̃`. -/
def Coherence23CoreProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∃ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ,
    ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
      GoodOn C (orbitKey C ν) f

/-- **BG Coherence Theorem 2.3**, all six clauses. (iv) and (v) follow from (ii) by I-2 and
by Lemma 1.3 (value form) + Remark 1.4. -/
def Coherence23Prop (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∃ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ,
    (∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν → GoodOn C (orbitKey C ν) f) ∧
    -- (iv)
    (∀ μ₁ ν₁ μ₂ ν₂ : ClassFunction ↥C.P.H0 ℂ,
      IsIrreducibleCharacter μ₁ → IsIrreducibleCharacter ν₁ →
      IsIrreducibleCharacter μ₂ → IsIrreducibleCharacter ν₂ →
      LamEquiv C μ₁ ν₁ → LamEquiv C μ₂ ν₂ →
      ¬ LamEquiv C μ₁ μ₂ → ¬ LamEquiv C (sconj C μ₁) μ₂ →
      ClassFunction.inner (f μ₁ - f ν₁) (f μ₂ - f ν₂) = 0) ∧
    -- (v)
    (∀ μ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
      LamEquiv C μ ν → ∀ g : ↥C.P.H0, (g : G) ∉ C.P.U →
        (f μ - f ν) (g : G) =
          (μ - ν) g + (μ - ν) (conjMulEquiv C.P C.s g))

/-- A-1. Assembly of the core from the per-orbit lemma.  Proof: `f ν := gOf (orbitKey C ν) ν`
with `gOf E := if h : ∃ f, GoodOn C E f then Classical.choose h else 0`, plus
`orbitKey C μ = orbitKey C ν` for `μ ~ ν` or `μ = ν^s` (uses `SconjLamProp`, `s² = 1`). -/
def AssemblyCoreProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  SconjLamProp C → OrbitCoherenceProp C → Coherence23CoreProp C

/-- A-2. (iv) from the core by I-2 (all four `cH` cross terms vanish), (v) from the core
by I-3'. -/
def AssemblyFullProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  GramProp C → BSValueTProp C → Coherence23CoreProp C → Coherence23Prop C

end Coherence

end Work.BG
