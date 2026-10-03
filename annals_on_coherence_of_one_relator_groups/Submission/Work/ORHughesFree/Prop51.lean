/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# [JZLA20, Proposition 5.1]: the key lemma

The key step in the proof of [JZLA20, Theorem 6.1] is the following auxiliary result, proved by
induction on the `H`-complexity of an element of the division closure `D_{H,P}` of `E ∗ H` in a
ring `P` containing `A((t;τ))`.

The carrier of the statement is `Prop51Data`.  Compared with the abstract interface
`RatComplexity` of `JZLA20.lean`, the rational `E × H`-semiring `Rat(E × H)` is here realized by
the **concrete** model `RatU Γ` of `Rat/RTerm.lean`, and the complexity `Tree` by
`Rat.treeOfRat Γ` (`Rat/ratComplexity_model.lean`).  This is what makes the lemma *provable*: the
induction of [JZLA20, Proposition 5.1] is an induction on the construction of an element of
`Rat(E × H)`, hence needs the term structure `RTerm Γ` and its evaluation, not merely the
universal property.

## The shape of the data

`Γ = E^× H` is the group of units of the crossed product, `N = E^× N₀` the subgroup corresponding
to the normal subgroup `N₀ ⊴ H` with `H/N₀ ≅ ℤ`, and `t ∈ Γ` a preimage of a generator of
`Γ/N`.  The morphism `Φ : Rat(Γ) → D_{H,P}` of rational `Γ`-semirings is the restriction of the
universal morphism `Φ_{H,P} : Rat(E^× H) ∪ {0} → D_{H,P}`, and the induction runs on the
following two facts, which are *not* consequences of the pure rational-semiring structure and
must therefore be part of the data:

* `Φ_N` and `Φ_t`: the restriction of `Φ` to `N · ⟨t⟩` is the composite
  `N · ⟨t⟩ → E^× N₀[t^{±1};τ] → D_{N,P}((t;τ)) ⊆ P`, i.e. `Φ(N) ⊆ D_{N,P}` and `Φ(t)` is the
  variable `t` of `D_{N,P}((t;τ))`.  This is the *base case* of the induction.
* `DH_inv_closed`: `D_{H,P}` is the division closure of `E ∗ H` in `P`, so the inverse (in `P`) of
  an element of `D_{H,P}` which is a unit of `P` again lies in `D_{H,P}`.

Universe: everything here is at universe `0`, because the skew Laurent series ring
`A((t;τ))` and its API (`SkewLaurentSeries`) are formalised at universe `0`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.Rat.RTerm
import Submission.Work.ORHughesFree.Rat.Source
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.ratComplexity_model
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.RootedTreesConcrete

set_option autoImplicit false

namespace Work.ORHughesFree

/-- The data in which [JZLA20, Proposition 5.1] takes place.  `H` is a finitely generated group
with `N₀ ⊴ H` and `H/N₀ ≅ ℤ`, `E ∗ H` a crossed product, which enters only through the rational
`E × H`-semiring `Rat(E × H)` (here `Γ = E^× H` and `RatU Γ` the concrete model) and `P` is a
ring containing `A((t;τ))` (conditions (i)–(iii) of the proposition).  Thus `D_{N,P} = DN` and
`D_{H,P} = DH` are division closures inside `P`, `Φ : Rat(E × H) →+* P` is the universal morphism
of rational `Γ`-semirings and `treeH : P → Tree` is the `H`-complexity of [JZLA20, §4.3] — the
minimum of `Tree α` over the `α : RatU Γ` with `Φ α = a`, which is `treeH_spec`.

The element `b` of `D_{H,P}` is decomposed by the skew Laurent series ring `D_{N,P}((t;τ))`
(`SkewLaurentSeries ↥DN`, with `τ` given by conjugation by `t`); `laurentEmbed` is the embedding
`D_{N,P}((t;τ)) →+* P` of condition (iii) and the `k`-th coefficient of `b` is `f.1 k` for the
unique `f : SkewLaurentSeries ↥DN` with `laurentEmbed f = b` (uniqueness is
`laurentEmbed_injective`, and `laurentEmbed (SkewLaurentSeries.coeff d) = d` by
`laurentEmbed_coeff`). -/
structure Prop51Data (Γ : Type) [Group Γ] (P : Type) [Ring P] (DN : Subring P)
    [MulSemiringAction (Multiplicative ℤ) ↥DN] where
  /-- `D_{N,P}` is non-trivial. -/
  nontrivialDN : Nontrivial ↥DN
  /-- `D_{N,P}` is a **division closure** in `P`: every element of `D_{N,P}` which is invertible
  in `P` has its inverse in `D_{N,P}`.  This is the only property of `D_{N,P}` that [JZLA20,
  Proposition 5.1] uses; in the intended instantiation `D_{N,P} = D_{N,A}` with `A` von Neumann
  regular it follows from [JZLA20, Lemma 4.5] and `DivisionClosure.inverse_mem_divisionClosure`.
  It replaces the stronger hypothesis `IsDivisionRing ↥DN`, which is *false* in the intended
  instantiation (see the README, gap item 10). -/
  DN_inv_closed : ∀ x ∈ DN, IsUnit x → ∃ y ∈ DN, x * y = 1 ∧ y * x = 1
  /-- the division closure `D_{H,P}` of `E ∗ H` inside `P` -/
  DH : Subring P
  /-- `D_{N,P} ⊆ D_{H,P}` -/
  le_DN_DH : DN ≤ DH
  /-- `D_{H,P}` is a division closure: an element of `D_{H,P}` which is a unit of `P` has its
  inverse in `D_{H,P}`. -/
  DH_inv_closed : ∀ x ∈ DH, IsUnit x → ∃ y ∈ DH, x * y = 1
  /-- the universal morphism `Rat(E × H) → P` of rational `Γ`-semirings -/
  Φ : RatU Γ →+* P
  /-- `Φ` takes values in `D_{H,P}` -/
  map_mem : ∀ α : RatU Γ, Φ α ∈ DH
  /-- the `H`-complexity -/
  treeH : P → Tree
  /-- on `D_{H,P}`, `treeH a` is the minimum of `Tree α` over the `α` with `Φ α = a` -/
  treeH_spec : ∀ a ∈ DH, (∃ α : RatU Γ, Φ α = a ∧ Rat.treeOfRat Γ α = treeH a) ∧
    ∀ β : RatU Γ, Φ β = a → Tree.le (treeH a) (Rat.treeOfRat Γ β)
  /-- the rational `Γ`-semiring structure of `D_{H,P}` ([JZLA20, §4.3]: `a⋄` is the inverse of `a`
  inside `D_{H,P}` when it exists, and `0` otherwise) -/
  rDH : RationalUSemiring Γ ↥DH
  /-- `Φ` is the universal morphism of rational `Γ`-semirings `Rat(E × H) →+* D_{H,P}`
  ([JZLA20, §4.3], Lemma 4.2): it commutes with `⋄` and with the two `Γ`-actions.  This is what the
  induction of Proposition 5.1 runs on. -/
  Φ_rat : IsRationalUSemiringHom (RatU.rational) rDH (Φ.codRestrict DH map_mem)
  /-- `⋄0 = 0` in `D_{H,P}` (`0` is not invertible) -/
  ratOp_zero : rDH.ratOp 0 = 0
  /-- `⋄` is inversion on the units of `D_{H,P}` ([JZLA20, §4.3]: `a⋄ = a⁻¹` for invertible `a`) -/
  ratOp_of_isUnit : ∀ x : ↥DH, IsUnit x → x * rDH.ratOp x = 1
  /-- the embedding `D_{N,P}((t;τ)) →+* P` of [JZLA20, Proposition 5.1](iii) -/
  laurentEmbed : SkewLaurentSeries ↥DN →+* P
  /-- that embedding is injective -/
  laurentEmbed_injective : Function.Injective laurentEmbed
  /-- `laurentEmbed` extends the inclusion `D_{N,P} ⊆ P` on constant series -/
  laurentEmbed_coeff : ∀ d : ↥DN,
    laurentEmbed (skewLaurentCoeff ↥DN d) = (d : P)
  /-- the subgroup `E^× N₀ ≤ Γ` -/
  N : Subgroup Γ
  /-- a preimage in `Γ` of a generator of `Γ/N` -/
  t : Γ
  /-- `Γ = N · ⟨t⟩` -/
  decomp : ∀ u : Γ, ∃ (n : Γ) (k : ℤ), n ∈ N ∧ u = n * t ^ k
  /-- `Φ` maps `N` into `D_{N,P}`: this is the `E^× N₀`-part of condition (iii) -/
  Φ_N : ∀ u : Γ, u ∈ N → Φ (RatU.ofGroup u) ∈ DN
  /-- `Φ` maps `t` to the variable of `D_{N,P}((t;τ))` — the `t`-part of condition (iii) -/
  Φ_t : Φ (RatU.ofGroup t) = laurentEmbed (skewLaurentSeriesT ↥DN : SkewLaurentSeries ↥DN)
  /-- `-1` is the image of an element of `Γ`.  In the paper `Γ = E^×H` is the group of units of
  the crossed product and `-1 ∈ E^×`, so that `Φ(-1) = Φ(ofGroup u)` for some `u ∈ Γ`.  This is
  what makes `Tree_H(-1) = 1`, the missing ingredient of the `⋄`-case of [JZLA20, Proposition 5.1]
  (the coefficients of an inverse series are obtained from the coefficients of the series and the
  coefficients of `-1` by sums and products, so their complexity is controlled by that of `-1`). -/
  Phi_neg_one : ∃ u : Γ, Φ (RatU.ofGroup u) = -1
  /-- The subgroup `E^× N₀ ≤ Γ` is normalised by `t` (in the paper `N₀ ⊴ H` and
  `H = N₀ ⋊ ⟨t⟩`, so that `H/N₀ ≅ ℤ`).  This is what makes conjugation by `Φ(t)^k` an
  automorphism of `D_{N,P}` and lets one move the factor `t^k` of a monomial `Rat(E^×N)·t^k`
  across an element of `Rat(E^×N)`. -/
  N_conj : ∀ (k : ℤ) (n : Γ), n ∈ N → t ^ k * n * t ^ (-k) ∈ N
  /-- In the intended model of [JZLA20, §4.3] the rational operation of `D_{H,P}` is *inversion
  on the units and `0` everywhere else*, so that `x⋄ ≠ 0` forces `x` to be a unit.  (The paper
  only defines `⋄` on `Rat(U) ∖ {0}`, so this is not an axiom of `RationalUSemiring`; it is a
  property of the division-closure model.)  It is what lets one pass from `b = c⋄ ≠ 0` to
  `b = c⁻¹` in the `⋄`-case of [JZLA20, Proposition 5.1]. -/
  ratOp_ne_zero : ∀ x : ↥DH, rDH.ratOp x ≠ 0 → IsUnit x

namespace Prop51Data

variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

/-- The coefficient `d ∈ D_{N,P}` of a Laurent series, viewed in `P`. -/
def coeffToP (d : Prop51Data Γ P DN) (x : ↥DN) : P := (x : P)

theorem coeffToP_mem (d : Prop51Data Γ P DN) (x : ↥DN) : d.coeffToP x ∈ d.DH :=
  d.le_DN_DH x.2

/-- The `H`-complexity of an element of `D_{H,P}` is realised by some `α ∈ Rat(E × H)`. -/
theorem exists_realizing (d : Prop51Data Γ P DN) {a : P} (ha : a ∈ d.DH) :
    ∃ α : RatU Γ, d.Φ α = a ∧ Rat.treeOfRat Γ α = d.treeH a :=
  (d.treeH_spec a ha).1

/-- The `H`-complexity is a minimum: `treeH (Φ α) ≤ Tree α`. -/
theorem treeH_le_treeOfRat (d : Prop51Data Γ P DN) (α : RatU Γ) :
    Tree.le (d.treeH (d.Φ α)) (Rat.treeOfRat Γ α) :=
  (d.treeH_spec (d.Φ α) (d.map_mem α)).2 α rfl

/-- `treeH a = 0` for `a ∈ D_{H,P}` if and only if `a = 0`. -/
theorem treeH_eq_zero_iff (d : Prop51Data Γ P DN) {a : P} (ha : a ∈ d.DH) :
    d.treeH a = 0 ↔ a = 0 := by
  constructor
  · intro h
    obtain ⟨α, hα, htree⟩ := d.exists_realizing ha
    rw [h] at htree
    rw [← hα, (Rat.treeOfRat_eq_zero_iff Γ α).mp htree, map_zero]
  · rintro rfl
    have hle := (d.treeH_spec (0 : P) d.DH.zero_mem).2 (0 : RatU Γ) (map_zero d.Φ)
    rw [Rat.treeOfRat_zero] at hle
    exact Tree.le_antisymm hle (Tree.le_zero _)

/-- A non-zero element of `D_{H,P}` has non-zero complexity. -/
theorem treeH_ne_zero (d : Prop51Data Γ P DN) {a : P} (ha : a ∈ d.DH) (ha0 : a ≠ 0) :
    d.treeH a ≠ 0 :=
  fun h => ha0 ((d.treeH_eq_zero_iff ha).mp h)

end Prop51Data

/-- The **conclusion** of [JZLA20, Proposition 5.1] for a fixed element `b ∈ D_{H,P}`: `b` lies in
the skew Laurent series ring `D_{N,P}((t;τ)) ⊆ P`, every non-zero coefficient of `b` satisfies
`Tree_H(f.1 k) ≤ Tree_H(b)`, and `Tree_H(f.1 k) = Tree_H(b)` can hold for at most one `k` (in which
case all the other coefficients vanish, i.e. `b = f.1 k · t^k` lies in `D_{N,P} t^k`). -/
def Prop51Concl {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Prop51Data Γ P DN) (b : P) : Prop :=
  ∃ f : SkewLaurentSeries ↥DN, d.laurentEmbed f = b ∧
    (∀ k : ℤ, f.1 k ≠ 0 → Tree.le (d.treeH (d.coeffToP (f.1 k))) (d.treeH b)) ∧
    (∀ k : ℤ, d.treeH (d.coeffToP (f.1 k)) = d.treeH b → ∀ j : ℤ, j ≠ k → f.1 j = 0)

/-- The **third clause of [JZLA20, Proposition 5.1(2)]**: whenever `b` has its (unique) coefficient
of maximal complexity at the index `k`, every `β ∈ Rat(E × H)` which realises `b` with the minimal
complexity `Tree_H(b)` lies in `Rat(E × N) · t^k`. -/
def Prop51Mono {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Prop51Data Γ P DN) (b : P) (k : ℤ) : Prop :=
  ∀ β : RatU Γ, d.Φ β = b → Rat.treeOfRat Γ β = d.treeH b →
    ∃ β' : RatU ↥d.N, RatU.ofSubgroup d.N β' * RatU.ofGroup (d.t ^ k) = β

/-- The **full second clause of [JZLA20, Proposition 5.1(2)]**: the `H`-complexities of the
coefficients are bounded by `Tree_H(b)`, the bound is attained at most once, and in that case every
minimal realiser of `b` lies in `Rat(E × N)·t^k` (`Prop51Mono`).

The bound clause is stated for *every* index (a zero coefficient has complexity `0 ≤ Tree_H(b)`);
this is the form in which the sum, product and `⋄` steps of [JZLA20, Proposition 5.1] compose
(`ConclB`). -/
def Prop51ConclP {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Prop51Data Γ P DN) (b : P) : Prop :=
  ∃ f : SkewLaurentSeries ↥DN, d.laurentEmbed f = b ∧
    (∀ k : ℤ, Tree.le (d.treeH (d.coeffToP (f.1 k))) (d.treeH b)) ∧
    (∀ k : ℤ, d.treeH (d.coeffToP (f.1 k)) = d.treeH b → ∀ j : ℤ, j ≠ k → f.1 j = 0) ∧
    (∀ k : ℤ, d.treeH (d.coeffToP (f.1 k)) = d.treeH b → Prop51Mono d b k)

/-- `Prop51ConclP` implies `Prop51Concl`. -/
theorem Prop51ConclP.toConcl {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] {d : Prop51Data Γ P DN} {b : P}
    (h : Prop51ConclP d b) : Prop51Concl d b := by
  obtain ⟨f, h1, h2, h3, -⟩ := h
  exact ⟨f, h1, fun k hk => h2 k, h3⟩

/-- The **induction hypothesis** of [JZLA20, Proposition 5.1] at `a`: every non-zero
`c ∈ D_{H,P}` with `Tree_H(c) < Tree_H(a)` is invertible in `D_{H,P}`. -/
def Prop51Inv {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Prop51Data Γ P DN) (a : P) : Prop :=
  ∀ (c : P) (_ : c ∈ d.DH), c ≠ 0 → Tree.le (d.treeH c) (d.treeH a) → d.treeH c ≠ d.treeH a →
    ∃ y ∈ d.DH, c * y = 1 ∧ y * c = 1

/-- **[JZLA20, Proposition 5.1]** (the key lemma).  Assume every non-zero element `c ∈ D_{H,P}`
with `Tree_H(c) < Tree_H(a)` is invertible in `D_{H,P}` (`Prop51Inv`).  Then for every
`b ∈ D_{H,P}` with `Tree_H(b) ≤ Tree_H(a)`, the conclusion `Prop51Concl` holds.

The last clause of `Prop51Concl` is the "only if" half of [JZLA20, Proposition 5.1(2)] (the
equality `Tree_H(b_n) = Tree_H(b)` holds for some `n` if and only if `b = b_n t^n`); the "if" half
is immediate.  The remaining clause of the proposition — that every `β ∈ Rat(E × H)` realising the
complexity of `b` lies in `Rat(E × N)t^n` — is *not* formalised here: it needs the level structure
of `Rat(Γ)` and the injectivity `Rat(V) ↪ Rat(U)` for `V ≤ U` of [DHS04, Theorem 5.7] (partially
available now through `RatU.ofSubgroup` in `Rat/Source.lean`).  It *is* needed for
[JZLA20, Theorem 6.1]: it is what excludes the single-monomial case `a = a_n t^n` of the proof of
Theorem 6.1, and the exclusion is not supplied by `Prop51Concl` — see `README.md` gap item 10 and
`Rat/Geo/NOTES.md` §4. -/
def Prop51 {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Prop51Data Γ P DN) (a : P) : Prop :=
  Prop51Inv d a →
  ∀ (b : P) (hb : b ∈ d.DH), Tree.le (d.treeH b) (d.treeH a) → Prop51Concl d b

theorem prop51_iff {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Prop51Data Γ P DN) (a : P) :
    Prop51 d a ↔
      (Prop51Inv d a →
        ∀ (b : P) (hb : b ∈ d.DH), Tree.le (d.treeH b) (d.treeH a) → Prop51Concl d b) :=
  Iff.rfl

end Work.ORHughesFree
