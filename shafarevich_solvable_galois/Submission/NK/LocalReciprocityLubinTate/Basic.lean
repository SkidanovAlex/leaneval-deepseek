import Mathlib
import Submission.NK.LocalCFT.All
import Submission.NK.LocalArtin.Basic
import Submission.NK.LocalReciprocity.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Lubin–Tate chapter of local class field theory: vocabulary

This is the entry file of `Submission/Work/LocalReciprocityLubinTate/`, the chapter that builds the
**Lubin–Tate construction of local class field theory** for a `p`-adic field.

The chapter speaks the vocabulary of the two sibling chapters it consumes and extends:

* `Submission/Work/LocalCFT/` — the *target datum* `NK.LocalCFT.ArtinReciprocity F F'`: the
  canonical Artin map `Fˣ →* Gal(F^{ab}/F)` together with the reciprocity isomorphisms at all finite
  abelian levels and the existence theorem;
* `Submission/Work/LocalArtin/` — the *reduction* of that datum to
  `KernelCondition + NormIndex + ExistenceTheoremAbstract`.

## What this file contains

1. **The higher unit filtration** of a nonarchimedean local field: for `n : ℕ`,
   `principalUnits F n = 1 + 𝔪[F]^n ≤ 𝒪[F]ˣ` and `higherUnits F n ≤ Fˣ`, the two forms of the
   classical filtration `U^n` of Serre, *Local Fields*, Ch. I §1 and Ch. IV §1.  These are the
   subgroups occurring in the Lubin–Tate norm-group description
   `N_{F(π_n)/F} F(π_n)ˣ = ⟨π⟩ · U^n`, i.e. they are the *input side* of the local reciprocity
   isomorphism.
2. **The Lubin–Tate tower** `LubinTateTower F F' π U q`: the classical output of Lubin–Tate theory
   for a uniformiser `π` and residue cardinality `q`, phrased entirely in terms of the norm groups
   of the finite abelian levels of `F^{ab}` — see the docstring of the structure for the exact
   classical statements (Serre, *Local Fields*, Ch. XV §3–§5; Milne, *Class Field Theory*, §I.1–I.4;
   Neukirch, *Algebraic Number Theory*, Ch. V §4–§5).

The tower is *data*, not an axiom: it is a `structure` whose fields are classical theorems about
Lubin–Tate formal groups and the norm residue symbol.  The *consequences* derived from it in the
rest of the chapter (`ExistenceTheorem`, the reciprocity isomorphism at every finite abelian level,
and finally `NK.LocalCFT.ArtinReciprocity`) are proved theorems.

## Main definitions

* `NK.LocalReciprocityLubinTate.principalUnits`, `NK.LocalReciprocityLubinTate.higherUnits`;
* `NK.LocalReciprocityLubinTate.residueCard`;
* `NK.LocalReciprocityLubinTate.LubinTateTower`.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate

universe u v

noncomputable section

/-! ## The higher unit filtration -/

/-- The cardinality `q = #𝓀[F]` of the residue field of a nonarchimedean local field. -/
def residueCard (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : ℕ := Nat.card 𝓀[F]

/-- The maximal ideal of the ring of integers of a nonarchimedean local field. -/
abbrev maximalIdealOfIntegers (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Ideal ↥𝒪[F] := IsLocalRing.maximalIdeal ↥𝒪[F]

/-- **The higher principal units** `U^n = 1 + 𝔪[F]^n ≤ 𝒪[F]ˣ`, for `n : ℕ`, where `𝔪[F]` is the
maximal ideal of the ring of integers.  (`U^0` is the whole group of units and `U^1 = 1 + 𝔪[F]` is
the group of principal units; the filtration is the one used in the Lubin–Tate norm-group
description `N_{F(π_n)/F} F(π_n)ˣ = ⟨π⟩ · U^n`.)

In the notation of Serre, *Local Fields*, Ch. IV §1, `U^n = 1 + 𝔭^n`. -/
def principalUnits (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) : Subgroup (↥𝒪[F])ˣ where
  carrier := {u : (↥𝒪[F])ˣ | ((u : ↥𝒪[F]) - 1) ∈ (maximalIdealOfIntegers F) ^ n}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ((a : ↥𝒪[F]) - 1) ∈ (maximalIdealOfIntegers F) ^ n at ha
    change ((b : ↥𝒪[F]) - 1) ∈ (maximalIdealOfIntegers F) ^ n at hb
    change ((a * b : (↥𝒪[F])ˣ) : ↥𝒪[F]) - 1 ∈ (maximalIdealOfIntegers F) ^ n
    have h : ((a * b : (↥𝒪[F])ˣ) : ↥𝒪[F]) - 1
        = ((a : ↥𝒪[F]) - 1) + ((b : ↥𝒪[F]) - 1)
          + ((a : ↥𝒪[F]) - 1) * ((b : ↥𝒪[F]) - 1) := by
      rw [Units.val_mul]; ring
    rw [h]
    refine add_mem (add_mem ha hb) ?_
    have hmem : ((a : ↥𝒪[F]) - 1) * ((b : ↥𝒪[F]) - 1)
        ∈ (maximalIdealOfIntegers F) ^ n * (maximalIdealOfIntegers F) ^ n :=
      Ideal.mul_mem_mul ha hb
    have hle : (maximalIdealOfIntegers F) ^ n * (maximalIdealOfIntegers F) ^ n
        ≤ (maximalIdealOfIntegers F) ^ n := by
      rw [← pow_two, ← pow_mul, Nat.mul_two]
      exact Ideal.pow_le_pow_right (by omega)
    exact hle hmem
  inv_mem' := by
    intro a ha
    change ((a : ↥𝒪[F]) - 1) ∈ (maximalIdealOfIntegers F) ^ n at ha
    change ((a⁻¹ : (↥𝒪[F])ˣ) : ↥𝒪[F]) - 1 ∈ (maximalIdealOfIntegers F) ^ n
    have h1 : ((a⁻¹ : (↥𝒪[F])ˣ) : ↥𝒪[F]) * (a : ↥𝒪[F]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : -(((a⁻¹ : (↥𝒪[F])ˣ) : ↥𝒪[F])) * ((a : ↥𝒪[F]) - 1)
        = -(((a⁻¹ : (↥𝒪[F])ˣ) : ↥𝒪[F]) * (a : ↥𝒪[F]))
          + ((a⁻¹ : (↥𝒪[F])ˣ) : ↥𝒪[F]) := by ring
    have h : ((a⁻¹ : (↥𝒪[F])ˣ) : ↥𝒪[F]) - 1
        = -(((a⁻¹ : (↥𝒪[F])ˣ) : ↥𝒪[F])) * ((a : ↥𝒪[F]) - 1) := by
      rw [h2, h1]; ring
    rw [h]
    exact Ideal.mul_mem_left _ _ ha

/-- A **uniformiser** of a nonarchimedean local field: an element `π` whose valuation generates the
value group and is `< 1`, i.e. an element generating the maximal ideal of the ring of integers.
This is Mathlib's `Valuation.IsUniformizer` for the canonical valuation of `F` (Mathlib has the
instance `Valuation.IsRankOneDiscrete (ValuativeRel.valuation F)` for a nonarchimedean local field,
because the value group is cyclic); the local `abbrev` merely fixes the valuation, so that all of
Mathlib's API for uniformisers (`Valuation.IsUniformizer.val_lt_one`,
`Valuation.associated_of_isUniformizer`, ...) is available under the chapter's name. -/
abbrev IsUniformizer (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : F) : Prop :=
  Valuation.IsUniformizer (ValuativeRel.valuation F) π

/-- **The higher unit groups of the field**: `U^n` regarded as a subgroup of `Fˣ` via
`𝒪[F]ˣ ↪ Fˣ`.  This is the subgroup occurring in the Lubin–Tate norm-group description. -/
def higherUnits (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) : Subgroup Fˣ :=
  (principalUnits F n).map (Units.map (Subring.subtype 𝒪[F]).toMonoidHom)

theorem mem_principalUnits_iff {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} {u : (↥𝒪[F])ˣ} :
    u ∈ principalUnits F n ↔ ((u : ↥𝒪[F]) - 1) ∈ (maximalIdealOfIntegers F) ^ n := Iff.rfl

theorem principalUnits_zero (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : principalUnits F 0 = ⊤ := by
  ext u
  simp [mem_principalUnits_iff]

theorem principalUnits_antitone (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Antitone (principalUnits F) := by
  intro m n hmn u hu
  exact Ideal.pow_le_pow_right hmn hu

theorem higherUnits_antitone (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Antitone (higherUnits F) := by
  intro m n hmn
  exact Subgroup.map_mono (principalUnits_antitone F hmn)

/-! ## The Lubin–Tate tower -/

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The Lubin–Tate tower of a uniformiser.**

Let `F` be a `p`-adic field with ring of integers `𝒪[F]`, residue cardinality `q = #𝓀[F]` and
uniformiser `π`, let `F'` be a Galois extension of `F` (in the application a separable closure) and
let `U : ℕ → Subgroup Fˣ` be a filtration of `Fˣ` by neighbourhoods of `1` (in the application the
higher unit filtration `NK.LocalReciprocityLubinTate.higherUnits`, so that `U n = 1 + 𝔪^n`).

A `LubinTateTower F F' π U q` is the classical output of Lubin–Tate theory for `(F, π)`, in the form
in which local class field theory consumes it: a two-parameter family of finite abelian levels of
`F^{ab}` whose norm groups are the groups `⟨π^{m+1}⟩ · U^{n+1}`, and which exhaust `F^{ab}`.

The classical content, and where it is proved in the literature:

* **existence of the levels.**  The Lubin–Tate formal group `F_Π` of a uniformiser `Π` of the base
  field and the field `K_n = F(π_n)` generated by the `Π^n`-division points of the Lubin–Tate
  group; `[K_n : F] = (q-1)q^{n-1}`, `K_n/F` totally ramified abelian, and
  `Gal(K_n/F) ≅ (𝒪[F]/π^n)ˣ`.  (Serre, *Local Fields*, Ch. XV §3, Thms. 3.1–3.4; Milne, *Class
  Field Theory*, §I.1.)
* **the explicit reciprocity law / norm groups.** `N_{K_n/F} K_nˣ = ⟨π⟩ · U^n`, and for the
  unramified extension `F_m/F` of degree `m` the norm group is `⟨π^m⟩ · U^0`; the compositum of an
  unramified and a Lubin–Tate level has the intersection of the two norm groups as norm group.
  (Serre, *Local Fields*, Ch. XV §5.2; Neukirch, *Algebraic Number Theory*, V §5.5.)
As `m` and `n` grow, the norm groups `⟨π^{m+1}⟩ · U^{n+1}` are cofinal among the finite-index
subgroups of `Fˣ`, which is what produces the existence theorem
(`NK.LocalReciprocityLubinTate.ExistenceTheorem`) below. -/
structure LubinTateTower (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (π : Fˣ) (U : ℕ → Subgroup Fˣ) (q : ℕ) where
  /-- The finite abelian level `E_{m,n}`: the compositum of the unramified extension of degree
  `m + 1` with the `(n+1)`-st Lubin–Tate level. -/
  level : ℕ → ℕ → IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')
  /-- each level is finite over `F`. -/
  finiteDimensional : ∀ m n, FiniteDimensional F ↥(level m n)
  /-- each level is normal over `F`. -/
  normal : ∀ m n, Normal F ↥(level m n)
  /-- each level is abelian over `F` (it is a quotient of `Gal(F^{ab}/F)`, but we ask for it
  explicitly so that the levels can be consumed by `NK.LocalArtin`). -/
  commutative : ∀ m n, ∀ σ τ : ↥(level m n) ≃ₐ[F] ↥(level m n), σ * τ = τ * σ
  /-- **the norm-group description of the Lubin–Tate levels**: the norm group of `E_{m,n}` is the
  group generated by the `(m+1)`-st power of the uniformiser and the `(n+1)`-st higher unit group.
  This is the explicit reciprocity law of Lubin–Tate theory in the form
  `N_{F(f_n)/F} F(f_n)ˣ = ⟨π⟩ · U^n`, together with the norm group `⟨π^m⟩ · U^0` of the unramified
  extension of degree `m` and the intersection formula for the norm group of a compositum. -/
  normGroup_eq : ∀ m n,
    NK.LocalReciprocity.normGroup F ↥(level m n)
      = Subgroup.zpowers (π ^ (m + 1)) ⊔ U (n + 1)

end

end NK.LocalReciprocityLubinTate
