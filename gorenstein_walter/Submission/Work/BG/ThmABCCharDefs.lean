/-
Design pass 16 (lead), area BG: the character-theoretic leaves behind `KeyBigProp`,
`KeySmallProp`, `ThmCBigProp`, `ThmCSmallProp` of `Core16.lean` (BG §2.2, 2.4, 2.5, §3, §4).
Statements only; routes, sizes and dispatch order in `NOTES_LEAD_gw_design16.md`.
Vocabulary: area BG's `S02.lean` (`Sec2Ctx`, `lamCF`, `LamEquiv`, `lamOrbit`, `sconj`, `ind`,
`IsPmIrr`, `DisjointCF`, `GoodOn`, `Coherence23Prop`).
-/
import Mathlib
import Submission.Work.BG.S02

namespace Work.GW2.C16

open OddOrder.RepresentationTheory Work.GW2 Work.BG Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Bridge `BGData → Sec2Ctx`, the coherent map, `𝒮(χ)` -/

/-- A §2 context compatible with the BG data `D` (`s := t₁`). -/
structure Compat (D : BGData G) (C : Sec2Ctx G) : Prop where
  H_eq : C.P.H = D.H
  U_eq : C.P.U = D.U
  H0_eq : C.P.H0 = H1 D
  t_eq : (C.t : G) = D.t
  s_eq : (C.s : G) = D.t1

/-- **G1.** Every `BGData` has a compatible `Sec2Ctx` (from `hyp12OfBGData`, needs the contract
`CentralizerSplitProp`). -/
def BridgeProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G), ∃ C : Sec2Ctx G, Compat D C

/-- The §3 standing hypothesis (BG p. 208): `S' = ⟨x² | x ∈ S₀⟩` centralizes `U`. -/
def Sec3Hyp (D : BGData G) : Prop := ∀ x ∈ D.S0, ∀ u ∈ D.U, x ^ 2 * u = u * x ^ 2

section Coh

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `f` is a coherent map in the sense of BG 2.3 (the body of `Coherence23Prop`). -/
def IsCoherent (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) : Prop :=
  (∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν → GoodOn C (orbitKey C ν) f) ∧
  (∀ μ₁ ν₁ μ₂ ν₂ : ClassFunction ↥C.P.H0 ℂ,
    IsIrreducibleCharacter μ₁ → IsIrreducibleCharacter ν₁ →
    IsIrreducibleCharacter μ₂ → IsIrreducibleCharacter ν₂ →
    LamEquiv C μ₁ ν₁ → LamEquiv C μ₂ ν₂ →
    ¬ LamEquiv C μ₁ μ₂ → ¬ LamEquiv C (sconj C μ₁) μ₂ →
    ClassFunction.inner (f μ₁ - f ν₁) (f μ₂ - f ν₂) = 0) ∧
  (∀ μ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
    LamEquiv C μ ν → ∀ g : ↥C.P.H0, (g : G) ∉ C.P.U →
      (f μ - f ν) (g : G) = (μ - ν) g + (μ - ν) (conjMulEquiv C.P C.s g))

theorem coherence23_iff (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Coherence23Prop C ↔ ∃ f, IsCoherent C f := Iff.rfl

/-- `𝒮(χ)` (BG p. 207): the `ν ∈ Irr(H₀)` with `(χ, ν̃) ≠ 0`. -/
def bset (C : Sec2Ctx G) (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ)
    (χ : ClassFunction G ℂ) : Set (ClassFunction ↥C.P.H0 ℂ) :=
  {ν | IsIrreducibleCharacter ν ∧ ClassFunction.inner χ (f ν) ≠ 0}

end Coh

/-! ## 1. Pure character-theory tools -/

/-- **X1 (pure).** `Σ_{χ ∈ Irr} χ(g)²/χ(1) · (θ, χ) = Σᵢ εᵢ(g)²/εᵢ(1)` for `θ = Σᵢ εᵢ`,
`εᵢ ∈ ±Irr` (linearity + orthonormality; sign-invariant, BG p. 205 "Remark"). -/
def ConstituentSumProp : Prop :=
  ∀ {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    [Fintype (IrreducibleCharacter K)] {ι : Type} [Fintype ι]
    (ε : ι → ClassFunction K ℂ), (∀ i, IsPmIrr (ε i)) → ∀ g : K,
      ∑ χ : IrreducibleCharacter K, (χ : ClassFunction K ℂ) g ^ 2 / (χ : ClassFunction K ℂ) 1 *
          ClassFunction.inner (∑ i, ε i) (χ : ClassFunction K ℂ) =
        ∑ i, ε i g ^ 2 / ε i 1

/-- **X2 (pure; Gorenstein 4.2.12).** For a conjugacy class `X ∋ x₀` and any class function
`θ`: `Σ_{x,y ∈ X} θ(xy) = |X|² Σ_χ (θ,χ) χ(x₀)²/χ(1)`.  (Expand `θ` in `Irr`; S02's
`ClassSumSquareProp`.) -/
def ClassMultProp : Prop :=
  ∀ {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    [Fintype (IrreducibleCharacter K)] (X : Finset K) (x₀ : K),
    (∀ x : K, x ∈ X ↔ IsConj x x₀) → ∀ θ : ClassFunction K ℂ,
      ∑ x ∈ X, ∑ y ∈ X, θ (x * y) =
        (X.card : ℂ) ^ 2 * ∑ χ : IrreducibleCharacter K,
          ClassFunction.inner θ (χ : ClassFunction K ℂ) *
            ((χ : ClassFunction K ℂ) x₀ ^ 2 / (χ : ClassFunction K ℂ) 1)

/-- **X3 (bridge to `ClassSumCongruence.isIntegral_card_mul_character_div`; Gorenstein
4.2.10).** `|G : C_G(g)| χ(g)/χ(1)` is an algebraic integer. -/
def CentralIntegralProp : Prop :=
  ∀ {K : Type} [Group K] [Finite K] (χ : ClassFunction K ℂ), IsIrreducibleCharacter χ →
    ∀ g : K, IsIntegral ℤ (((centralizer ({g} : Set K)).index : ℂ) * χ g / χ 1)


/-- **X4 (Lemma 1.9, value form; p. 202 "`α ≡ α*` on `B`").** From
`Work.BG.glauberman_general_assembled` (odd-multiplicity form) and Lemma 1.8
(`lemma18LinearIndependent`): the odd-multiplicity constituent `β` satisfies
`α(b) ≡ β(b) (mod 2)` for all `b ∈ C_U(S)`. -/
def GlaubValueProp : Prop :=
  ∀ {S U : Type} [Group S] [Group U] [Finite S] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (_hS : IsPGroup 2 S) (_hU : Odd (Nat.card U))
    (φ : S →* MulAut U) [Fintype ↥(fixedSubgroupS φ)]
    [Invertible (Nat.card ↥(fixedSubgroupS φ) : ℂ)]
    (α : ClassFunction U ℂ), IsIrreducibleCharacter α →
    (∀ (s : S) (u : U), α (φ s u) = α u) →
    ∃ β : ClassFunction ↥(fixedSubgroupS φ) ℂ, IsIrreducibleCharacter β ∧
      ∀ b : ↥(fixedSubgroupS φ), AlgIntModTwo (α (b : U)) (β b)

/-! ## 2. Lemma 2.2 in general (p. 205) -/

section L22

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- The involutions of `H ∖ H₀` (= `t₁^H ⊔ t₂^H`), as a finset of `↥H`. -/
noncomputable def invJ (C : Sec2Ctx G) [Fintype ↥C.P.H] : Finset ↥C.P.H := by
  classical exact Finset.univ.filter (fun x : ↥C.P.H => x ^ 2 = 1 ∧ x ≠ 1 ∧ (x : G) ∉ C.P.H0)

/-- `μ ↦ μ^H` (induction `H₀ → H` along `H0in`). -/
noncomputable def indH (C : Sec2Ctx G) [Fintype ↥C.P.H]
    [Invertible (Nat.card ↥(H0in C.P) : ℂ)] (μ : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction ↥C.P.H ℂ :=
  ClassFunction.induce (H0in C.P) (ClassFunction.compHom (H0inEquiv C.P).toMonoidHom μ)

/-- **L22-G (V = W, p. 205).** For equivalent `μ, ν ∈ Irr(H₀)`:
`|G:H| Σ_χ χ(t)²/χ(1) (χ, (μ-ν)*) = Σ_{θ ∈ Irr H} (Σ_{x ∈ J} θ(x))²/θ(1) (θ, μ^H - ν^H)`.
Route: X2 in `G` with `X = t^G` and in `H` with `X = J` (an `H`-invariant set), the two
pair-count functions agree on `T` (S02 `InvolutionPairProp`), `δ = μ^H - ν^H` vanishes off `T`
and `δ* = δ^G` (Lemma 1.3), Frobenius reciprocity.  `|t^G| = |G:H|`. -/
def Lemma22GenProp (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥C.P.H]
    [Invertible (Nat.card ↥C.P.H : ℂ)] [Invertible (Nat.card ↥(H0in C.P) : ℂ)]
    [Fintype (IrreducibleCharacter G)] [Fintype (IrreducibleCharacter ↥C.P.H)] : Prop :=
  ∀ μ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ → IsIrreducibleCharacter ν →
    LamEquiv C μ ν →
    (C.P.H.index : ℂ) * ∑ χ : IrreducibleCharacter G,
        (χ : ClassFunction G ℂ) (C.t : G) ^ 2 / (χ : ClassFunction G ℂ) 1 *
          ClassFunction.inner (ind C (μ - ν)) (χ : ClassFunction G ℂ) =
      ∑ θ : IrreducibleCharacter ↥C.P.H,
        (∑ x ∈ invJ C, (θ : ClassFunction ↥C.P.H ℂ) x) ^ 2 / (θ : ClassFunction ↥C.P.H ℂ) 1 *
          ClassFunction.inner (indH C μ - indH C ν) (θ : ClassFunction ↥C.P.H ℂ)

/-- **L22-W (evaluation, p. 205 bottom).** `κ` linear, `s`-invariant, `t₁t₂ ∈ ker κ` (stated as:
`κ` is `1` on `S₀`); `ν = λκ` with `λ ∈ Λ`.  Then `W = 2|J|²` if `ν^s ≠ ν`, and also if
`λ = λ₂` is `s`-fixed, `λ ≠ 1`, and `|t₁^H| = |t₂^H|` (stated as `2 * #(J ∩ C.s^H) = |J|`).
Route: `κ^H = τ + τ'` (Remark 1.4), `τ ≡ 1` on `J` after choosing `τ(s) = 1`, `τ' = -τ` off
`H₀`; `ν^H` irreducible vanishes on `J`; in the `λ₂` case `ν^H = τ₂ + τ₂'` with
`Σ_J τ₂ = k₁ - k₂ = 0`. -/
def Lemma22EvalProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥C.P.H] [Invertible (Nat.card ↥C.P.H : ℂ)]
    [Invertible (Nat.card ↥(H0in C.P) : ℂ)] [Fintype (IrreducibleCharacter ↥C.P.H)] : Prop :=
  Compat D C → ∀ (κ : ClassFunction ↥C.P.H0 ℂ) (β : quotGroup C.P →* ℂˣ),
    IsIrreducibleCharacter κ → κ 1 = 1 → sconj C κ = κ →
    (∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1) →
    (sconj C (lamCF C β * κ) ≠ lamCF C β * κ ∨
      (β ≠ 1 ∧ sconj C (lamCF C β) = lamCF C β ∧
        (centralizer ({D.t1} : Set G)).relIndex D.H =
          (centralizer ({D.t2} : Set G)).relIndex D.H)) →
    ∑ θ : IrreducibleCharacter ↥C.P.H,
        (∑ x ∈ invJ C, (θ : ClassFunction ↥C.P.H ℂ) x) ^ 2 / (θ : ClassFunction ↥C.P.H ℂ) 1 *
          ClassFunction.inner (indH C κ - indH C (lamCF C β * κ)) (θ : ClassFunction ↥C.P.H ℂ) =
      2 * ((invJ C).card : ℂ) ^ 2

/-- **G9.** `|J| = k` (`J = t₁^H ⊔ t₂^H`; the two classes are distinct: for `|S| ≥ 8` their
images in `H/U ≅ S` are the two non-central `S`-classes, for `|S| = 4` an `H`-element swapping
`t₁, t₂` would normalize `S` with even order modulo `C_G(S)`). -/
def InvJCardProp (D : BGData G) (C : Sec2Ctx G) [Fintype ↥C.P.H] : Prop :=
  Compat D C → (invJ C).card = D.k

/-- **L22-K** = L22-G + L22-W + G9 + `C.P.H.index = D.H.index`: the form consumed below. -/
def Lemma22KappaProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (IrreducibleCharacter G)] : Prop :=
  Compat D C → ∀ (κ : ClassFunction ↥C.P.H0 ℂ) (β : quotGroup C.P →* ℂˣ),
    IsIrreducibleCharacter κ → κ 1 = 1 → sconj C κ = κ →
    (∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1) →
    (sconj C (lamCF C β * κ) ≠ lamCF C β * κ ∨
      (β ≠ 1 ∧ sconj C (lamCF C β) = lamCF C β ∧
        (centralizer ({D.t1} : Set G)).relIndex D.H =
          (centralizer ({D.t2} : Set G)).relIndex D.H)) →
    (D.H.index : ℂ) * ∑ χ : IrreducibleCharacter G,
        (χ : ClassFunction G ℂ) (C.t : G) ^ 2 / (χ : ClassFunction G ℂ) 1 *
          ClassFunction.inner (ind C (κ - lamCF C β * κ)) (χ : ClassFunction G ℂ) =
      2 * (D.k : ℂ) ^ 2

end L22

/-! ## 3. Lemma 2.4, Lemma 2.5 (front half) -/

section L24

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **L24 (p. 207).** For `χ ∈ ±Irr(G)`: `𝒮(χ)` is finite, `χ = Σ_{ν ∈ 𝒮(χ)} (χ, ν̃) ν` on `T`,
and `χ ≡ Σ_{ν ∈ 𝒮(χ)} ν` (mod 2) on `U`.  Route: S02 `Lemma17TProp` with representatives
chosen orthogonal to `χ`, then Lemma 1.6 (`lemma16_mod_two`) twice through `tu ∈ T`. -/
def Lemma24Prop (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  ∀ f, IsCoherent C f → ∀ χ : ClassFunction G ℂ, IsPmIrr χ →
    (bset C f χ).Finite ∧
    (∀ g : ↥C.P.H0, (g : G) ∉ C.P.U →
      χ (g : G) = ∑ᶠ ν ∈ bset C f χ, ClassFunction.inner χ (f ν) * ν g) ∧
    (∀ u : ↥C.P.H0, (u : G) ∈ C.P.U →
      AlgIntModTwo (χ (u : G)) (∑ᶠ ν ∈ bset C f χ, ν u))

/-- **DEC-BIG (Lemma 2.5, first lines).** `|S| ≥ 8`: there is `λ₃ = λ_β` with `λ₃(t) = -1`,
`λ̃₃ ∈ ±Irr`, `λ̃₃(t) = -2`, and `λ̃₁ = 1_G + φ` with `φ ∈ ±Irr`, `φ ⊥ 1_G`, `φ(t) = 1`.
Route: `β` faithful on the cyclic `H₀/U` of order `n`; `|Λλ₃| = n`; `λ̃₃(t) = 2λ₃(t)` by
`GoodOn` (vi) when `n ≥ 8`, by Lemma 3.4 when `n = 4` (§3 holds: `S' = ⟨t⟩ ≤ Z(H)`);
`(1_G, λ̃₁ - λ̃₃) = 1` (Frobenius) and disjointness (iii) give `λ̃₁ = 1_G + φ`;
`λ̃₁(t) - λ̃₃(t) = 2(1 - λ₃(t)) = 4` (S02 `BSValueProp`) gives `φ(t) = 1`. -/
def DecompBigProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → 4 ≤ D.n → ∀ f, IsCoherent C f →
    ∃ β : quotGroup C.P →* ℂˣ, lamCF C β C.t = -1 ∧ sconj C (lamCF C β) ≠ lamCF C β ∧
      IsPmIrr (f (lamCF C β)) ∧ f (lamCF C β) (C.t : G) = -2 ∧
      ∃ φ : ClassFunction G ℂ, IsPmIrr φ ∧
        ClassFunction.inner φ (trivialClassFunction G) = 0 ∧
        ClassFunction.inner φ (f (lamCF C β)) = 0 ∧
        f (lamCF C 1) = trivialClassFunction G + φ ∧ φ (C.t : G) = 1

/-- **KEYBIG-ASM** (assembly leaf, pure manipulation): DEC-BIG + L22-K (`κ = λ₁`) + X1 + S02
`IndDiffProp` (`(λ₁ - λ₃)*(1) = 0`) give `KeyBigProp` with `x := φ(1) ∈ ℤ`:
`N(1 + 1/x - 4/(x+1)) = 2k²`, i.e. `N(x-1)² = 2k²x(x+1)`. -/
def KeyBigAsmProp : Prop :=
  BridgeProp → ConstituentSumProp →
  (∀ (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)],
      Coherence23Prop C ∧ IndDiffProp C ∧ DecompBigProp D C ∧ Lemma22KappaProp D C) →
  -- `= Work.GW2.C16.KeyBigProp` of `Core16.lean` (inlined: design files do not import each other)
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G), 4 ≤ D.n →
    ∃ x : ℤ, x ≠ 0 ∧ x ≠ -1 ∧
      (D.H.index : ℤ) * (x - 1) ^ 2 = 2 * (D.k : ℤ) ^ 2 * x * (x + 1)

end L24

/-! ## 4. §3 (`S'` centralizes `U`): Remark 3.1, Theorem 3.2, Lemmas 3.3, 3.4, 3.6 -/

section Sec3

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `U` inside `H₀`. -/
abbrev Uin (C : Sec2Ctx G) : Subgroup ↥C.P.H0 := C.P.U.subgroupOf C.P.H0

/-- **R31-O (Remark 3.1, general Gallagher form; used in 3.2).**
`(μ|_U, ν|_U)_U = m/|Λν|` if `μ ~ ν`, else `0` (`m = |H₀ : U| = n`).  Route: Frobenius,
`(ν|_U)^{H₀} = ν · r(Λ)`, `#{λ : λν = μ} = |Λ_ν| = m/|Λν|`. -/
def Rem31OrthProp (D : BGData G) (C : Sec2Ctx G) [Fintype ↥(Uin C)]
    [Invertible (Nat.card ↥(Uin C) : ℂ)] : Prop :=
  Compat D C → ∀ μ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ →
    IsIrreducibleCharacter ν →
    (LamEquiv C μ ν →
      ClassFunction.inner (ClassFunction.restrict (Uin C) μ) (ClassFunction.restrict (Uin C) ν) =
        (D.n : ℂ) / ((lamOrbit C ν).ncard : ℂ)) ∧
    (¬ LamEquiv C μ ν →
      ClassFunction.inner (ClassFunction.restrict (Uin C) μ) (ClassFunction.restrict (Uin C) ν) =
        0)

/-- **R31-S (Remark 3.1, shape; needs §3).** `ν|_U = a` with `|Λν| = m`, `a` `S₀`-invariant, or
`ν|_U = a₁ + a₂` (distinct, same degree) with `|Λν| = m/2`; and `Λν` is `s`-invariant iff
`S_a ⊄ S₀`.  Recorded in degree form (what 3.4, 3.6 and (3) use). -/
def Rem31ShapeProp (D : BGData G) (C : Sec2Ctx G) : Prop :=
  Compat D C → Sec3Hyp D → ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
    ∃ a : ClassFunction ↥(Uin C) ℂ, IsIrreducibleCharacter a ∧
      ((ClassFunction.restrict (Uin C) ν = a ∧ (lamOrbit C ν).ncard = D.n) ∨
       (∃ a₂ : ClassFunction ↥(Uin C) ℂ, IsIrreducibleCharacter a₂ ∧ a₂ ≠ a ∧ a₂ 1 = a 1 ∧
          ClassFunction.restrict (Uin C) ν = a + a₂ ∧ 2 * (lamOrbit C ν).ncard = D.n))

/-- **T32 (Theorem 3.2).** `|𝒮(χ)| ≤ 3` (needs §3).  Route p. 208: `2 = 2(χ,χ) > ...` using
L24 on `T`, the TI-set `T` with `N(T) = H`, R31-O, and `|𝒮(χ) ∩ Λᵢ| ≤ 2 ≤ |Λᵢ|`. -/
def Thm32Prop (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → Sec3Hyp D → ∀ f, IsCoherent C f → ∀ χ : ClassFunction G ℂ, IsPmIrr χ →
    (bset C f χ).ncard ≤ 3

/-- **L33 (Lemma 3.3).** Two `s`-fixed `ν ∈ 𝒮(χ)` with `|Λν| = m` force `|S| = 4` and
`𝒮(χ)` = three such characters.  Route p. 209: L24 mod 2 on `B`, Lemma 1.9 (value form, X4),
Lemma 1.8, X3 with `|G : C_G(g)|` odd on `B`; for `|S| ≥ 8`, Lemma 2.1 + the three
pairwise-orthogonal `δᵢ` give `χ(1) = 0`. -/
def Lemma33Prop (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → Sec3Hyp D → ∀ f, IsCoherent C f → ∀ χ : ClassFunction G ℂ, IsPmIrr χ →
    ∀ ν₁ ∈ bset C f χ, ∀ ν₂ ∈ bset C f χ, ν₁ ≠ ν₂ →
      sconj C ν₁ = ν₁ → sconj C ν₂ = ν₂ →
      (lamOrbit C ν₁).ncard = D.n → (lamOrbit C ν₂).ncard = D.n →
      D.n = 2 ∧ (bset C f χ).ncard = 3 ∧
        ∀ ν ∈ bset C f χ, sconj C ν = ν ∧ (lamOrbit C ν).ncard = D.n

/-- **L34 (Lemma 3.4).** Route p. 209: T32, 2.3(vi), L33, R31-S, Lemma 1.7, X3 with
`4 ∤ |G : C_G(u)|` on `B₁`, Lemmas 1.8, 1.9. -/
def Lemma34Prop (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → Sec3Hyp D → ∀ f, IsCoherent C f → ∀ χ : ClassFunction G ℂ, IsPmIrr χ →
    ∀ ν ∈ bset C f χ, sconj C ν ≠ ν →
      (sconj C ν ∉ lamOrbit C ν ∨ (lamOrbit C ν).ncard = D.n) →
      bset C f χ = {ν, sconj C ν} ∧ f ν (C.t : G) = 2 * ν C.t

/-- **L36 (Lemma 3.6).** `χ ∈ Irr(G)`, `𝒮(χ) ≠ ∅`, `K ⊄ ker χ`, `ν^s ∈ Λν` for all
`ν ∈ 𝒮(χ)` ⇒ some `a ∈ Irr(U)` with `K ⊄ ker a` and `χ(1) > 2m a(1)`.  Route p. 210:
R31-S; `K` inverted by `S ∖ S₀` moves `a`; `Λμ ∩ 𝒮(χ) = ∅`; equal multiplicities on
`Λμ ∪ Λμ^s`. -/
def Lemma36Prop (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (K : Subgroup G) : Prop :=
  Compat D C → Sec3Hyp D → K ≤ D.U → ∀ f, IsCoherent C f → ∀ χ : ClassFunction G ℂ,
    IsIrreducibleCharacter χ → (bset C f χ).Nonempty → (∃ x ∈ K, χ x ≠ χ 1) →
    (∀ ν ∈ bset C f χ, sconj C ν ∈ lamOrbit C ν) →
    ∃ a : ClassFunction ↥(Uin C) ℂ, IsIrreducibleCharacter a ∧
      (∃ u : ↥(Uin C), ((u : ↥C.P.H0) : G) ∈ K ∧ a u ≠ a 1) ∧
      ∃ dχ da : ℕ, χ 1 = dχ ∧ a 1 = da ∧ 2 * D.n * da < dχ

end Sec3

/-! ## 5. Theorem C, `|S| ≥ 8` (pp. 210–211): the chain -/

section C3

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- The hypotheses of Theorem C, bundled. -/
def ThmCHyps (D : BGData G) (K1 K2 : Subgroup G) : Prop :=
  IsMaxInverted D.H D.t1 K1 ∧ IsMaxInverted D.H D.t2 K2 ∧
  IsInternalDirect D.U (D.B1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2)) ∧
  Nat.Coprime (Nat.card (K1 ⊓ K2 : Subgroup G)) D.H.index ∧ ⁅D.B, D.B⁆ ≠ D.B ∧
  (D.U ≠ D.B ⊔ (K1 ⊓ K2) → IsFrobeniusWith (D.B ⊔ (K1 ⊓ K2)) (K1 ⊓ K2) D.B)

/-- `κ` is an admissible `κ₁ ≠ 1_{H₀}` (p. 204: linear, `S₀[S,U] ≤ ker κ`, hence `s`-fixed). -/
def IsKappa (D : BGData G) (C : Sec2Ctx G) (κ : ClassFunction ↥C.P.H0 ℂ) : Prop :=
  IsIrreducibleCharacter κ ∧ κ 1 = 1 ∧ sconj C κ = κ ∧
  (∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1) ∧ κ ≠ lamCF C 1

/-- **C3-0 (κ exists).** `B ⊄ U'` (G6) gives a linear `κ ≠ 1` of `H₀` trivial on
`S₀ [S, U] U'` (`H₀/(S₀[S,U]U') ≅ B/(B ∩ U')`-quotient is non-trivial). -/
def KappaExistsProp (D : BGData G) (C : Sec2Ctx G) : Prop :=
  Compat D C → ¬ D.B ≤ ⁅D.U, D.U⁆ → ∃ κ, IsKappa D C κ

/-- **C3-1 (identity (6) and (1)).** With `κ̃₁ = χ₁ + χ₂`, `κ̃₃ = χ₃` (`κ₃ = λ₃κ₁`,
`λ₃(t) = -1`): `χ₃(t)² = 4`, `χ₁(t) + χ₂(t) = 2`, and
`2k²/N = χ₁(t)²/χ₁(1) + χ₂(t)²/χ₂(1) - 4/χ₃(1)`.  Route: L34 for `κ₃` (`|Λκ₃| = m`),
BSValue, L22-K (`ν = κ₃`, not `s`-fixed), X1. -/
def C3IdentityProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (IrreducibleCharacter G)] : Prop :=
  Compat D C → 4 ≤ D.n → Sec3Hyp D → ∀ f, IsCoherent C f → ∀ κ, IsKappa D C κ →
    ∀ β : quotGroup C.P →* ℂˣ, lamCF C β C.t = -1 →
    ∃ χ₁ χ₂ : ClassFunction G ℂ, IsPmIrr χ₁ ∧ IsPmIrr χ₂ ∧ ClassFunction.inner χ₁ χ₂ = 0 ∧
      f κ = χ₁ + χ₂ ∧ IsPmIrr (f (lamCF C β * κ)) ∧
      f (lamCF C β * κ) (C.t : G) ^ 2 = 4 ∧ χ₁ (C.t : G) + χ₂ (C.t : G) = 2 ∧
      (D.H.index : ℂ) * (χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 -
          4 / f (lamCF C β * κ) 1) = 2 * (D.k : ℂ) ^ 2

/-- **C3-2 ((2)–(5) and the Frobenius trigger).** For a constituent `χ₁` of `κ̃` with
`χ₁(t) = 1 + x`: `x ∈ ℤ`, `|x| ≤ (|𝒮(χ₁)| - 1)|B|`, `|𝒮(χ₁)| ≤ 2 ⇒ x² ≤ 2|B|`, and
`𝒮(χ₁) ≠ {κ} ⇒ U ≠ BK`.  Route: L33, L34 give (2); R31-S + "`t₁`- or `t₂`-fixed `a ∈ Irr U`
has `K` in its kernel" give (3) `|ν(t)| = ν(1) ≤ |B|`; L24 at `t` gives (4); (5) from (3);
the trigger from R31-S (`n = 2` for `ν ≠ κ` moves `a` under `S₀`, so `[S₀, U] ≠ 1`). -/
def C3BoundsProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (K1 K2 : Subgroup G) : Prop :=
  Compat D C → ThmCHyps D K1 K2 → 4 ≤ D.n → Sec3Hyp D → ∀ f, IsCoherent C f →
    ∀ κ, IsKappa D C κ → ∀ χ₁ : ClassFunction G ℂ, IsPmIrr χ₁ →
    ClassFunction.inner χ₁ (f κ) = 1 →
    ∃ x : ℤ, χ₁ (C.t : G) = 1 + x ∧
      |x| ≤ ((bset C f χ₁).ncard - 1 : ℤ) * Nat.card D.B ∧
      ((bset C f χ₁).ncard ≤ 2 → x ^ 2 ≤ 2 * (Nat.card D.B : ℤ)) ∧
      (bset C f χ₁ ≠ {κ} → D.U ≠ D.B ⊔ (K1 ⊓ K2))

/-- **C3-3 (`|𝒮(χ₁)| ≠ 3`, p. 211).** Route: the two `δᵢ = ν̃ᵢ - μ̃ᵢ` force
`χ₁(1) = χ₂(1)`, `χ₃(1) = 2χ₁(1)`, (6) becomes `k²χ₁(1) = x²N`; `2|K| ∣ k` and
`(|K|, N) = 1` give `2|K| ≤ |x| ≤ 2|B|`, contradicting `|K| ≡ 1 (mod |B|)`, `|K| > |B|`
(Frobenius kernel). -/
def C3NotThreeProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (K1 K2 : Subgroup G) : Prop :=
  Compat D C → ThmCHyps D K1 K2 → IsSimpleGroup G → 4 ≤ D.n → ∀ f, IsCoherent C f →
    ∀ κ, IsKappa D C κ → ∀ χ₁ : ClassFunction G ℂ, IsPmIrr χ₁ →
    ClassFunction.inner χ₁ (f κ) = 1 → (bset C f χ₁).ncard ≠ 3

/-- **C3-4 (degrees, p. 211 via L36 and Frobenius).** One `A ≥ 1` with `|χ(1)| ≥ 8A + 1` for
`χ ∈ {χ₁, χ₂, χ₃, φ}` (any `±Irr` `χ ≠ ±1_G` whose `𝒮(χ)` contains an `s`-fixed or a
`Λ`-self-conjugate character; `G` simple so `K ⊄ ker χ`), and `U ≠ BK ⇒ A ≥ |B|`
(`a ∈ Irr U` non-trivial on the Frobenius kernel `K` has `|B| ∣ a(1)`).  Stated per
character; the assembly takes the minimum. -/
def C3DegreeProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (K1 K2 : Subgroup G) : Prop :=
  Compat D C → ThmCHyps D K1 K2 → IsSimpleGroup G → 4 ≤ D.n → ∀ f, IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, IsPmIrr χ →
    ClassFunction.inner χ (trivialClassFunction G) = 0 →
    (∃ ν ∈ bset C f χ, sconj C ν = ν) ∨ (∀ ν ∈ bset C f χ, sconj C ν ∈ lamOrbit C ν) →
    (bset C f χ).Nonempty →
    ∃ A : ℕ, 1 ≤ A ∧ (D.U ≠ D.B ⊔ (K1 ⊓ K2) → Nat.card D.B ≤ A) ∧
      ∃ d : ℤ, χ 1 = d ∧ 8 * (A : ℤ) + 1 ≤ |d|

end C3

/-! ## 6. §4 (`|S| = 4`) -/

section Sec4

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `δ_ν := (ν - λ₂ν)*` for the non-trivial `β₂ : H₀/U → ℂˣ` (`m = 2`). -/
noncomputable def delta (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (β₂ : quotGroup C.P →* ℂˣ) (ν : ClassFunction ↥C.P.H0 ℂ) : ClassFunction G ℂ :=
  ind C (ν - lamCF C β₂ * ν)

/-- The index set of §4: `ν = ν^s`, `ν(t) = ν(1)`. -/
def S4Index (C : Sec2Ctx G) : Set (ClassFunction ↥C.P.H0 ℂ) :=
  {ν | IsIrreducibleCharacter ν ∧ sconj C ν = ν ∧ ν C.t = ν 1}

/-- `𝒮'(χ)`. -/
def bset' (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] (β₂ : quotGroup C.P →* ℂˣ)
    (χ : ClassFunction G ℂ) : Set (ClassFunction ↥C.P.H0 ℂ) :=
  {ν | ν ∈ S4Index C ∧ ClassFunction.inner χ (delta C β₂ ν) ≠ 0}

/-- **L41 (Lemma 4.1 (i), (ii), (iv)).** Route p. 212: `ν ∈ 𝒮'(χ)` iff `𝒮(χ)` contains `ν` or
`λ₂ν`; then L24, L33, L34 (§3 holds trivially: `S' = 1`). -/
def Lemma41Prop (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 →
    ∀ χ : ClassFunction G ℂ, IsPmIrr χ → (bset' C β₂ χ).Nonempty →
      ((bset' C β₂ χ).ncard = 1 ∨ (bset' C β₂ χ).ncard = 3) ∧
      χ (C.t : G) = ∑ᶠ ν ∈ bset' C β₂ χ, ClassFunction.inner χ (delta C β₂ ν) * ν 1 ∧
      ∃ d : ℤ, Odd d ∧ χ 1 = d

/-- **T43 (Theorem 4.3), consumed form.** Every `δ_ν` is either disjoint from all other `δ_μ`,
or lies in a component `{δ₁, δ₂, δ₃}` of the sign pattern `(+,+,+,+), (+,-,+,-), (+,+,-,-)`.
Route pp. 212–213: L41 (iii), (v) (needs X4 = Lemma 1.9 value form and Lemma 1.8), Lemma 4.2
(`μ' := μ̂*` on `S × B`, parity), then the three-case analysis; the `ν̂`-conjugacy clause
is the extra output used by C4. -/
def Thm43Prop (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 → ∀ ν ∈ S4Index C,
    (∀ μ ∈ S4Index C, delta C β₂ μ ≠ delta C β₂ ν →
        DisjointCF (delta C β₂ ν) (delta C β₂ μ)) ∨
    ∃ μ₂ ∈ S4Index C, ∃ μ₃ ∈ S4Index C, ∃ χ₁ χ₂ χ₃ χ₄ : ClassFunction G ℂ,
      IsPmIrr χ₁ ∧ IsPmIrr χ₂ ∧ IsPmIrr χ₃ ∧ IsPmIrr χ₄ ∧
      delta C β₂ ν = χ₁ + χ₂ + χ₃ + χ₄ ∧ delta C β₂ μ₂ = χ₁ - χ₂ + χ₃ - χ₄ ∧
      delta C β₂ μ₃ = χ₁ + χ₂ - χ₃ - χ₄ ∧ μ₂ 1 = ν 1 ∧ μ₃ 1 = ν 1

/-- **S4-DEC (p. 214).** `(1 - λ₂)* = 1_G + φ₁ + φ₂ + φ₃` with `φᵢ ∈ ±Irr`, `φᵢ(t) = 1`,
odd integer degrees.  Route: `(1_G, δ₁) = 1` (Frobenius), T43 (the triple pattern puts `1_G`
in three `δ`'s, impossible), so `δ₁` is isolated, `𝒮'(φᵢ) = {1}`, L41 (ii), (iv). -/
def S4DecompProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 →
    ∃ φ₁ φ₂ φ₃ : ClassFunction G ℂ, IsPmIrr φ₁ ∧ IsPmIrr φ₂ ∧ IsPmIrr φ₃ ∧
      delta C β₂ (lamCF C 1) = trivialClassFunction G + φ₁ + φ₂ + φ₃ ∧
      φ₁ (C.t : G) = 1 ∧ φ₂ (C.t : G) = 1 ∧ φ₃ (C.t : G) = 1 ∧
      ∃ a b c : ℤ, Odd a ∧ Odd b ∧ Odd c ∧ φ₁ 1 = a ∧ φ₂ 1 = b ∧ φ₃ 1 = c

/-- **G10.** `t ∈ G'` (`t = t₁t₂` with `t₂ = t₁^g`), so a `±`linear character takes the value
`φ(1)` at `t`; with S4-DEC this turns `|a| = 1` into `a = 1`. -/
def TDerivedProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G), D.t ∈ commutator G

/-- **C4-ID ((2), p. 214).** `δ_κ = χ₁ + χ₂ + χ₃ + χ₄` with
`2k²/N = Σ χᵢ(t)²/χᵢ(1)` (L22-K with `ν = λ₂κ`, `k₁ = k₂` by G5; X1). -/
def C4IdentityProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (IrreducibleCharacter G)] : Prop :=
  Compat D C → D.n = 2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 → ∀ κ, IsKappa D C κ →
    ∃ χ₁ χ₂ χ₃ χ₄ : ClassFunction G ℂ, IsPmIrr χ₁ ∧ IsPmIrr χ₂ ∧ IsPmIrr χ₃ ∧ IsPmIrr χ₄ ∧
      delta C β₂ κ = χ₁ + χ₂ + χ₃ + χ₄ ∧
      (D.H.index : ℂ) * (χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 +
        χ₃ (C.t : G) ^ 2 / χ₃ 1 + χ₄ (C.t : G) ^ 2 / χ₄ 1) = 2 * (D.k : ℂ) ^ 2


/-- **C4-VAL (pp. 214–215).** Under `U = BK` (G7): either every constituent of `δ_κ` has
value `1` at `t` (`δ_κ` isolated, L41 (ii)), or `δ_κ` is in a T43 triple, the three `ν` are
linear (`ν̂ = ν|_B`), `χ-values (3, 1, 1, -1)`, degrees `(d, -d, -d, d)` (`δᵢ(1) = 0`), and (2)
gives `2k² d = 8N`. -/
def C4ValuesProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (K1 K2 : Subgroup G) : Prop :=
  Compat D C → D.n = 2 → ThmCHyps D K1 K2 → ∀ β₂ : quotGroup C.P →* ℂˣ, β₂ ≠ 1 →
    ∀ κ, IsKappa D C κ → ∀ χ₁ χ₂ χ₃ χ₄ : ClassFunction G ℂ,
    IsPmIrr χ₁ → IsPmIrr χ₂ → IsPmIrr χ₃ → IsPmIrr χ₄ →
    delta C β₂ κ = χ₁ + χ₂ + χ₃ + χ₄ →
    (D.H.index : ℂ) * (χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 +
        χ₃ (C.t : G) ^ 2 / χ₃ 1 + χ₄ (C.t : G) ^ 2 / χ₄ 1) = 2 * (D.k : ℂ) ^ 2 →
    (χ₁ (C.t : G) = 1 ∧ χ₂ (C.t : G) = 1 ∧ χ₃ (C.t : G) = 1 ∧ χ₄ (C.t : G) = 1) ∨
      ∃ d : ℤ, 2 * (D.k : ℤ) ^ 2 * d = 8 * (D.H.index : ℤ)

/-- **C4-DEG (Lemma 3.6 with `m = 2`, p. 215).** `G` simple: every `χ ∈ ±Irr`, `χ ⊥ 1_G`, with
an `s`-fixed member of `𝒮(χ)` has `|χ(1)| ≥ 5` (`χ(1) > 4a(1)`). -/
def C4DegreeProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (K1 K2 : Subgroup G) : Prop :=
  Compat D C → ThmCHyps D K1 K2 → IsSimpleGroup G → D.n = 2 → ∀ f, IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, IsPmIrr χ →
    ClassFunction.inner χ (trivialClassFunction G) = 0 →
    (∃ ν ∈ bset C f χ, sconj C ν = ν) →
    ∃ d : ℤ, χ 1 = d ∧ 5 ≤ |d|

end Sec4

end Work.GW2.C16
