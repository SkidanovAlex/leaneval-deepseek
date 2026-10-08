import Mathlib
import Submission.OddOrder.GroupTheory.TISubset
import Submission.Work.GLUE.Defs

/-!
# Area BG: Bender–Glauberman 1981 §1 — definitions

This module is the definition layer of area `BG` of the `gorenstein_walter` drive
(route: Bender 1981 + Bender–Glauberman 1981, with Feit–Thompson available as
`OddOrder.feitThompson`).

## The shared vocabulary

The group-theoretic vocabulary of the design contract
`Submission/Work/_design_gw/Contracts2.lean` (namespace `GW2`) is **not** re-declared here:
area GLUE (`Submission.Work.GLUE.Defs`) owns the canonical verbatim copy under the namespace
`Work.GW2`, and this module imports it.  Consequently every declaration of area BG that
mentions the vocabulary — `BGData`, `BGThmAProp`, `BGThmBProp`, `BGThmCProp`,
`CentralizerSplitProp`, `IsMaxInverted`, `IsInternalDirect`, `IsFrobeniusWith`, `oddCore`,
`fittingIn`, `primesOf`, `invSet`, `IsFourGroup`, … — speaks the contract's notation
directly, and the lead's assembly can consume it without any bridge.

A caller of area BG therefore only needs

```
import Submission.Work.BG.Defs
open Work.GW2
```

## What area BG adds to the vocabulary

* `Work.BG.Tset H0 U` — the subset `T = H₀ ∖ U` of Bender–Glauberman 1981, Hypothesis 1.2;
* `Work.BG.Hyp12` — **Bender–Glauberman 1981, Hypothesis 1.2** (p. 202): `U ≤ H₀ ⊴ H`,
  `[H : H₀] = 2`, `T = H₀ ∖ U` a TI-subset of `G` whose normalizer is `H`;
* `Work.BG.AlgIntModTwo a b` — the congruence `a ≡ b (mod 2)` for algebraic integers
  (`a - b = 2c` with `c` integral).  This is the form in which Bender–Glauberman state
  Lemma 1.6 and the characterisation of Lemma 1.9 (p. 202: "for algebraic integers a and b,
  `a = b` means `a = b` modulo 2"), with its elementary calculus.
-/

open scoped MatrixGroups

namespace Work.BG

open Subgroup
open OddOrder.GroupTheory (IsTISubset)

/-! ## 0. The congruence `≡ (mod 2)` of Bender–Glauberman 1981 -/

/-- `a ≡ b (mod 2)` for algebraic integers `a`, `b`: their difference is twice an
algebraic integer.  (Bender–Glauberman 1981, p. 202.) -/
def AlgIntModTwo (a b : ℂ) : Prop := ∃ c : ℂ, IsIntegral ℤ c ∧ a - b = 2 * c

namespace AlgIntModTwo

theorem refl (a : ℂ) (_ : IsIntegral ℤ a) : AlgIntModTwo a a :=
  ⟨0, isIntegral_zero, by ring⟩

theorem symm {a b : ℂ} (h : AlgIntModTwo a b) : AlgIntModTwo b a := by
  obtain ⟨c, hc, hcab⟩ := h
  exact ⟨-c, hc.neg, by linear_combination -hcab⟩

theorem trans {a b c : ℂ} (hab : AlgIntModTwo a b) (hbc : AlgIntModTwo b c) :
    AlgIntModTwo a c := by
  obtain ⟨x, hx, hxab⟩ := hab
  obtain ⟨y, hy, hybc⟩ := hbc
  exact ⟨x + y, hx.add hy, by linear_combination hxab + hybc⟩

theorem add {a b c d : ℂ} (hab : AlgIntModTwo a b) (hcd : AlgIntModTwo c d) :
    AlgIntModTwo (a + c) (b + d) := by
  obtain ⟨x, hx, hxab⟩ := hab
  obtain ⟨y, hy, hybc⟩ := hcd
  exact ⟨x + y, hx.add hy, by linear_combination hxab + hybc⟩

theorem neg {a b : ℂ} (h : AlgIntModTwo a b) : AlgIntModTwo (-a) (-b) := by
  obtain ⟨c, hc, hcab⟩ := h
  exact ⟨-c, hc.neg, by linear_combination -hcab⟩

theorem sub {a b c d : ℂ} (hab : AlgIntModTwo a b) (hcd : AlgIntModTwo c d) :
    AlgIntModTwo (a - c) (b - d) := by
  simpa [sub_eq_add_neg] using hab.add hcd.neg

/-- `2c ≡ 0 (mod 2)` for an algebraic integer `c`. -/
theorem mul_two {c : ℂ} (hc : IsIntegral ℤ c) : AlgIntModTwo (2 * c) 0 :=
  ⟨c, hc, by ring⟩

end AlgIntModTwo

/-! ## 1. Hypothesis 1.2 of Bender–Glauberman 1981 -/

/-- The set `T = H₀ ∖ U` of Bender–Glauberman 1981, Hypothesis 1.2. -/
def Tset {G : Type*} [Group G] (H0 U : Subgroup G) : Set G := {x | x ∈ H0 ∧ x ∉ U}

section Fixed

/-- The fixed-point subgroup `C_U(σ)` of an automorphism `σ` of `U`: for a 2-group `S`
acting on a 2'-group `U` through `φ : S →* MulAut U` this is `C_U(S)` once `σ` is a
generator, and for `S = ZMod 2` (written `Multiplicative (ZMod 2)`, or as a single
involution) it is `C_U(S)` itself.  Bender–Glauberman's Lemma 1.9 attaches to every
`S`-invariant `α ∈ Irr(U)` a unique `β ∈ Irr(C_U(S))`. -/
def fixedSubgroup {U : Type*} [Group U] (σ : MulAut U) : Subgroup U where
  carrier := {u | σ u = u}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; show σ (a * b) = a * b; rw [map_mul, ha, hb]
  inv_mem' := by intro a ha; show σ a⁻¹ = a⁻¹; rw [map_inv, ha]

@[simp] theorem mem_fixedSubgroup {U : Type*} [Group U] {σ : MulAut U} {u : U} :
    u ∈ fixedSubgroup σ ↔ σ u = u := Iff.rfl

/-- The fixed-point subgroup `C_U(S)` of a 2-group `S` acting by automorphisms on `U`
(Bender–Glauberman's `B` in Lemma 1.9, for the general case). -/
def fixedSubgroupS {S : Type*} [Group S] {U : Type*} [Group U] (φ : S →* MulAut U) :
    Subgroup U where
  carrier := {u | ∀ s : S, φ s u = u}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb s
    show φ s (a * b) = a * b
    rw [map_mul, ha s, hb s]
  inv_mem' := by
    intro a ha s
    show φ s a⁻¹ = a⁻¹
    rw [map_inv, ha s]

@[simp] theorem mem_fixedSubgroupS {S : Type*} [Group S] {U : Type*} [Group U]
    {φ : S →* MulAut U} {u : U} : u ∈ fixedSubgroupS φ ↔ ∀ s : S, φ s u = u := Iff.rfl

/-- **Bender–Glauberman 1981, Lemma 1.9, general case** (the statement; the `|S| = 2` case is
proved as `Work.BG.glauberman_two`).  `S` is a 2-group acting by automorphisms `φ` on a group
`U` of odd order; for every `S`-invariant irreducible character `α` of `U` there is a unique
irreducible character `β` of `C_U(S) = fixedSubgroupS φ` whose multiplicity in `α|_{C_U(S)}`
is odd.  The bijection form of Lemma 1.9 (every `β` arises) is the companion statement. -/
def glaubermanGeneralProp : Prop :=
  ∀ {S U : Type} [Group S] [Group U] [Finite S] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hS : IsPGroup 2 S) (hU : Odd (Nat.card U))
    (φ : S →* MulAut U) [Fintype ↥(fixedSubgroupS φ)]
    [Invertible (Nat.card ↥(fixedSubgroupS φ) : ℂ)]
    (α : OddOrder.RepresentationTheory.IrreducibleCharacter U)
    (hα : ∀ (s : S) (u : U),
      (α : OddOrder.RepresentationTheory.ClassFunction U ℂ)
        (φ s u) = (α : OddOrder.RepresentationTheory.ClassFunction U ℂ) u),
    ∃! β : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(fixedSubgroupS φ),
      ∃ k : ℤ, OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (fixedSubgroupS φ)
          (α : OddOrder.RepresentationTheory.ClassFunction U ℂ))
        (β : OddOrder.RepresentationTheory.ClassFunction ↥(fixedSubgroupS φ) ℂ)
        = (2 * k + 1 : ℂ)

theorem fixedSubgroup_eq_top_iff {U : Type*} [Group U] {σ : MulAut U} :
    fixedSubgroup σ = ⊤ ↔ σ = 1 := by
  constructor
  · intro h
    ext u
    have : u ∈ fixedSubgroup σ := by rw [h]; trivial
    simpa using this
  · rintro rfl
    ext u
    simp

end Fixed

/-- `H₁ = U S₀`, the `H₀` of Bender–Glauberman's Hypothesis 1.2 in the situation of
Hypothesis 1.1 (with `U = O(H)`, `H = C_G(t)` and `S₀` the cyclic maximal subgroup of `S`
containing the central involution `t`). -/
def H1 {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) : Subgroup G :=
  Work.GW2.BGData.U D ⊔ D.S0

/-- **Bender–Glauberman 1981, Hypothesis 1.2** (p. 202), without the `Λ`-notation:
`U ≤ H₀ ⊴ H ≤ G` with `[H : H₀] = 2`, and `T = H₀ ∖ U` is a TI-subset of `G` whose
normalizer is `H`.

The set `Λ` of linear characters of `H₀/U` and the orbit theory of §2 are not part of this
structure: the §1 items stated on Hypothesis 1.2 (Lemma 1.3, the Brauer–Suzuki isometry;
Remark 1.4, Clifford for index 2; Lemma 1.7) only need the data recorded here. -/
structure Hyp12 (G : Type*) [Group G] [Finite G] where
  H0 : Subgroup G
  H : Subgroup G
  U : Subgroup G
  U_le_H0 : U ≤ H0
  H0_le_H : H0 ≤ H
  H0_normal : (H0.subgroupOf H).Normal
  H0_relIndex : H0.relIndex H = 2
  TI : IsTISubset (Tset H0 U) H
  normalizer_T : normalizer (Tset H0 U) = H

namespace Hyp12

variable {G : Type*} [Group G] [Finite G]

/-- `T ⊆ H₀`. -/
theorem Tset_subset (P : Hyp12 G) : Tset P.H0 P.U ⊆ P.H0 := fun _ hx => hx.1

/-- `T ⊆ H`. -/
theorem Tset_subset_H (P : Hyp12 G) : Tset P.H0 P.U ⊆ P.H :=
  fun _ hx => P.H0_le_H hx.1

/-- `T` avoids `U`. -/
theorem not_mem_U (P : Hyp12 G) {x : G} (hx : x ∈ Tset P.H0 P.U) : x ∉ P.U := hx.2

/-- Membership in `T`, unfolded. -/
theorem mem_H0 (P : Hyp12 G) {x : G} (hx : x ∈ Tset P.H0 P.U) : x ∈ P.H0 := hx.1

/-- Membership in `T`, unfolded. -/
theorem mem_H (P : Hyp12 G) {x : G} (hx : x ∈ Tset P.H0 P.U) : x ∈ P.H := P.H0_le_H hx.1

/-- `H` normalizes `T` (the normalizer is *equal* to `H` by hypothesis). -/
theorem le_normalizer_T (P : Hyp12 G) : P.H ≤ normalizer (Tset P.H0 P.U) := by
  rw [P.normalizer_T]

/-- The TI condition in the form used in §2: an element of `G` mapping a point of `T` into
`T` already lies in `H`. -/
theorem mem_H_of_conj_mem (P : Hyp12 G) {g x : G} (hx : x ∈ Tset P.H0 P.U)
    (hgx : g * x * g⁻¹ ∈ Tset P.H0 P.U) : g ∈ P.H :=
  P.TI g ⟨x, hx, hgx⟩

end Hyp12

end Work.BG
