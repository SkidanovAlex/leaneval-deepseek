/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.SignatureBordism.Signature
import Submission.Work.SignatureBordism.BilinearQuadratic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Integral bilinear forms: the basic vocabulary

This file starts the chapter **unimodular forms over `ℤ`** (`Submission/NOTES.md` §3, §8.4, §15).

A *form* here is a `ℤ`-bilinear form `B : M →ₗ[ℤ] M →ₗ[ℤ] ℤ` on a `ℤ`-module `M`
(`Work.UnimodularForms.ZForm`).  The notions defined are

* `IsUnimodular B` : `m ↦ B m _` is a bijection `M ≃ M*` (`Function.Bijective ⇑B`).  For a free
  `ℤ`-module of finite rank this is equivalent to `det (Gram matrix) = ±1`; it is the condition that
  the lattice is *self-dual*, i.e. the condition satisfied by the intersection form of a closed
  oriented manifold;
* `IsSymm B` : `B x y = B y x`;
* `IsEven B` : every norm `B x x` is even (`IsOdd B` is its negation);
* `IsPosDef B`, `IsNegDef B`, `IsDefinite B`, `IsIndefinite B` : the sign conditions on the norms;
* `orthSum B B'` : the orthogonal direct sum on `M × M'`;
* `IsIsometric B B'` : the two forms are identified by a linear equivalence (a change of basis);
* `SplitsOff B B'` : `B` is isometric to `B'` orthogonal-summed with some other form —
  "`B'` is an orthogonal summand of `B`".

The signature `sig` and the rank `rank` live in `Work.UnimodularForms.Signature`; the concrete
matrix model (`gramBilin`, `ℍ`, `⟨1⟩`, `E₈`) in `Work.UnimodularForms.Matrix`.

## References

* J. Milnor, D. Husemoller, *Symmetric Bilinear Forms*, Ergebnisse 73, Springer 1973.
* J.-P. Serre, *A Course in Arithmetic*, GTM 7, Chapter V.
* M. Kneser, *Klassenzahlen indefiniter quadratischer Formen*, Arch. Math. 7 (1956).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

-- Make the product module structure resolve to `Prod.instModule` (rather than
-- `AddCommGroup.toIntModule`), so that it is the instance used by Mathlib's `TensorProduct.prodRight`.
-- This is a *global* attribute: it is inherited by every module importing this one, which is what
-- makes statements about `orthSum` unambiguous for callers (see the `README.md`).
attribute [instance 5000] Prod.instModule

namespace Work.UnimodularForms

noncomputable section

open LinearMap (BilinForm)

/-- A `ℤ`-bilinear form on a `ℤ`-module, i.e. an integral bilinear form (an integral lattice, once a
nondegeneracy condition is imposed). -/
abbrev ZForm (M : Type*) [AddCommGroup M] [Module ℤ M] := BilinForm ℤ M

variable {M : Type*} [AddCommGroup M] [Module ℤ M]
variable {M' : Type*} [AddCommGroup M'] [Module ℤ M']
variable {M'' : Type*} [AddCommGroup M''] [Module ℤ M'']

/-! ## Symmetry and unimodularity -/

/-- A bilinear form is **symmetric** if `B x y = B y x` for all `x`, `y`.

This is `LinearMap.IsSymm` for `B : BilinForm ℤ M`; see
`Work.UnimodularForms.isSymm_iff_linearMap_isSymm`. -/
def IsSymm (B : ZForm M) : Prop := ∀ x y : M, B x y = B y x

theorem isSymm_iff_forall (B : ZForm M) : IsSymm B ↔ ∀ x y : M, B x y = B y x := Iff.rfl

/-- **Unimodularity**: the linear map `M → M*`, `m ↦ B m _`, is bijective (equivalently, for a free
`ℤ`-module of finite rank, the Gram matrix in any basis has determinant `±1`; this is the condition
that the lattice is *self-dual*). -/
def IsUnimodular (B : ZForm M) : Prop := Function.Bijective ⇑B

theorem isUnimodular_iff (B : ZForm M) : IsUnimodular B ↔ Function.Bijective ⇑B := Iff.rfl

namespace IsUnimodular

variable {B : ZForm M}

theorem injective (h : IsUnimodular B) : Function.Injective ⇑B := h.1

theorem surjective (h : IsUnimodular B) : Function.Surjective ⇑B := h.2

/-- A unimodular form has no radical: an element orthogonal to everything is `0`. -/
theorem eq_zero_of (h : IsUnimodular B) {x : M} (hx : ∀ y : M, B x y = 0) : x = 0 := by
  refine h.injective ?_
  rw [show (⇑B) x = 0 from ?_, map_zero]
  ext y
  simpa using hx y

/-- **Unimodularity is surjectivity onto the dual.**  This is the form in which it is used to
*solve* for vectors: e.g. to find a hyperbolic partner `y` with `B x y = 1` of a vector `x`
whose functional `B x _` is nonzero. -/
theorem exists_eq (h : IsUnimodular B) (φ : M →ₗ[ℤ] ℤ) : ∃ x : M, B x = φ :=
  h.surjective φ

/-- The negation of a unimodular form is unimodular. -/
theorem neg (h : IsUnimodular B) : IsUnimodular (-B) := by
  constructor
  · intro x y hxy
    refine h.injective ?_
    have h' : -(B x) = -(B y) := hxy
    simpa using h'
  · intro φ
    obtain ⟨x, hx⟩ := h.surjective (-φ)
    exact ⟨x, by ext y; simpa [hx] using congr_fun (congr_arg DFunLike.coe hx) y⟩

end IsUnimodular

/-! ## Parity -/

/-- A form is **even** if every norm `B x x` is even.  (For a symmetric form this is equivalent to
the diagonal entries of the Gram matrix in some — equivalently every — basis being even; see
`Work.UnimodularForms.isEven_iff_diagonal_even`.) -/
def IsEven (B : ZForm M) : Prop := ∀ x : M, Even (B x x)

/-- A form is **odd** if some norm is odd.  For symmetric forms this is the negation of `IsEven`
(`Work.UnimodularForms.not_isEven_iff_isOdd`). -/
def IsOdd (B : ZForm M) : Prop := ∃ x : M, Odd (B x x)

theorem not_isEven_iff_isOdd (B : ZForm M) : ¬ IsEven B ↔ IsOdd B := by
  simp only [IsEven, IsOdd, not_forall]
  exact exists_congr fun x => Int.not_even_iff_odd

/-! ## Sign conditions -/

/-- A form is **positive definite** if every nonzero norm is positive. -/
def IsPosDef (B : ZForm M) : Prop := ∀ x : M, x ≠ 0 → 0 < B x x

/-- A form is **negative definite** if every nonzero norm is negative. -/
def IsNegDef (B : ZForm M) : Prop := ∀ x : M, x ≠ 0 → B x x < 0

/-- A form is **definite** if it is positive or negative definite. -/
def IsDefinite (B : ZForm M) : Prop := IsPosDef B ∨ IsNegDef B

/-- A form is **indefinite** if it takes both strictly positive and strictly negative values
(equivalently, if its real signature has both a positive and a negative part). -/
def IsIndefinite (B : ZForm M) : Prop := (∃ x : M, 0 < B x x) ∧ ∃ y : M, B y y < 0

theorem IsIndefinite.not_isDefinite {B : ZForm M} (h : IsIndefinite B) : ¬ IsDefinite B := by
  rintro (hp | hn)
  · obtain ⟨y, hy⟩ := h.2
    rcases eq_or_ne y 0 with rfl | hy0
    · simp at hy
    · exact absurd (hp y hy0) (not_lt.mpr (le_of_lt hy))
  · obtain ⟨x, hx⟩ := h.1
    rcases eq_or_ne x 0 with rfl | hx0
    · simp at hx
    · exact absurd (hn x hx0) (not_lt.mpr (le_of_lt hx))

theorem isPosDef_neg_iff (B : ZForm M) : IsPosDef (-B) ↔ IsNegDef B := by
  simp only [IsPosDef, IsNegDef, LinearMap.neg_apply]
  constructor <;> intro h x hx <;> have := h x hx <;> linarith

theorem isNegDef_neg_iff (B : ZForm M) : IsNegDef (-B) ↔ IsPosDef B := by
  have := isPosDef_neg_iff (-B)
  rw [neg_neg] at this
  exact this.symm

theorem isDefinite_neg (B : ZForm M) : IsDefinite (-B) ↔ IsDefinite B := by
  simp only [IsDefinite, isPosDef_neg_iff, isNegDef_neg_iff]
  tauto

/-! ## The orthogonal direct sum -/

/-- The **orthogonal direct sum** `B ⊥ B'` of two integral forms, on `OrthSum M M'` (a synonym for
`M × M'`, see `Work.UnimodularForms.OrthSum`). -/
def orthSum (B : ZForm M) (B' : ZForm M') : ZForm (M × M') :=
  LinearMap.mk₂ ℤ (fun x y : M × M' => B x.1 y.1 + B' x.2 y.2)
    (fun x y z => by
      obtain ⟨x₁, x₂⟩ := x; obtain ⟨y₁, y₂⟩ := y; obtain ⟨z₁, z₂⟩ := z
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      abel)
    (fun a x y => by
      obtain ⟨x₁, x₂⟩ := x; obtain ⟨y₁, y₂⟩ := y
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, Int.zsmul_eq_mul,
        mul_add])
    (fun x y z => by
      obtain ⟨x₁, x₂⟩ := x; obtain ⟨y₁, y₂⟩ := y; obtain ⟨z₁, z₂⟩ := z
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      abel)
    (fun a x y => by
      obtain ⟨x₁, x₂⟩ := x; obtain ⟨y₁, y₂⟩ := y
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, Int.zsmul_eq_mul,
        mul_add])

@[simp]
theorem orthSum_apply (B : ZForm M) (B' : ZForm M') (x y : M × M') :
    orthSum B B' x y = B x.1 y.1 + B' x.2 y.2 := rfl

@[simp]
theorem orthSum_apply_fst (B : ZForm M) (B' : ZForm M') (x y : M) :
    orthSum B B' (x, 0) (y, 0) = B x y := by simp

@[simp]
theorem orthSum_apply_snd (B : ZForm M) (B' : ZForm M') (x y : M') :
    orthSum B B' (0, x) (0, y) = B' x y := by simp

theorem neg_orthSum (B : ZForm M) (B' : ZForm M') :
    -orthSum B B' = orthSum (-B) (-B') := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  show - ((B x.1) y.1 + (B' x.2) y.2) = -((B x.1) y.1) + -((B' x.2) y.2)
  ring

theorem isSymm_orthSum {B : ZForm M} {B' : ZForm M'}
    (h : IsSymm B) (h' : IsSymm B') : IsSymm (orthSum B B') := by
  intro x y
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  simp only [orthSum_apply, h x₁ y₁, h' x₂ y₂]

theorem isPosDef_orthSum (B : ZForm M) (B' : ZForm M') :
    IsPosDef (orthSum B B') ↔ IsPosDef B ∧ IsPosDef B' := by
  constructor
  · intro h
    have hne : ∀ x : M, x ≠ 0 → (x, (0 : M')) ≠ 0 := fun x hx h => hx (by simpa using congrArg Prod.fst h)
    have hne' : ∀ x : M', x ≠ 0 → ((0 : M), x) ≠ 0 := fun x hx h => hx (by simpa using congrArg Prod.snd h)
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have := h (x, 0) (hne x hx); simpa using this
    · have := h (0, x) (hne' x hx); simpa using this
  · rintro ⟨h, h'⟩ x hx
    obtain ⟨x₁, x₂⟩ := x
    rw [orthSum_apply]
    by_cases hx1 : x₁ = 0
    · have hx2 : x₂ ≠ 0 := fun h2 => hx (by rw [hx1, h2]; rfl)
      have h2 : 0 < B' x₂ x₂ := h' x₂ hx2
      have h1 : 0 ≤ B x₁ x₁ := by subst hx1; simp
      linarith
    · have h1 : 0 < B x₁ x₁ := h x₁ hx1
      have h2 : 0 ≤ B' x₂ x₂ := by
        by_cases hx2 : x₂ = 0
        · subst hx2; simp
        · exact le_of_lt (h' x₂ hx2)
      linarith

theorem isNegDef_orthSum (B : ZForm M) (B' : ZForm M') :
    IsNegDef (orthSum B B') ↔ IsNegDef B ∧ IsNegDef B' := by
  rw [← isPosDef_neg_iff, neg_orthSum, isPosDef_orthSum, isPosDef_neg_iff, isPosDef_neg_iff]

theorem isEven_orthSum (B : ZForm M) (B' : ZForm M') :
    IsEven (orthSum B B') ↔ IsEven B ∧ IsEven B' := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have := h (x, 0); simpa using this
    · have := h (0, x); simpa using this
  · rintro ⟨h, h'⟩ x
    obtain ⟨a, ha⟩ := h x.1
    obtain ⟨b, hb⟩ := h' x.2
    refine ⟨a + b, ?_⟩
    simp only [orthSum_apply, ha, hb]
    ring

/-! ## Isometries -/

/-- **Isometry** of integral forms: a linear equivalence of the underlying lattices carrying one
form to the other (i.e. a change of `ℤ`-basis). -/
def IsIsometric (B : ZForm M) (B' : ZForm M') : Prop :=
  ∃ e : M ≃ₗ[ℤ] M', ∀ x y : M, B' (e x) (e y) = B x y

theorem IsIsometric.refl (B : ZForm M) : IsIsometric B B :=
  ⟨LinearEquiv.refl ℤ M, fun _ _ => rfl⟩

theorem IsIsometric.symm {B : ZForm M} {B' : ZForm M'} (h : IsIsometric B B') :
    IsIsometric B' B := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun x y => ?_⟩
  have := he (e.symm x) (e.symm y)
  simpa using this.symm

theorem IsIsometric.trans {B : ZForm M} {B' : ZForm M'} {B'' : ZForm M''}
    (h : IsIsometric B B') (h' : IsIsometric B' B'') : IsIsometric B B'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := h'
  refine ⟨e.trans f, fun x y => ?_⟩
  simp only [LinearEquiv.trans_apply]
  rw [hf, he]

theorem IsIsometric.isSymm {B : ZForm M} {B' : ZForm M'} (h : IsIsometric B B')
    (hB : IsSymm B) : IsSymm B' := by
  obtain ⟨e, he⟩ := h
  intro x y
  have h1 := he (e.symm x) (e.symm y)
  have h2 := he (e.symm y) (e.symm x)
  simp only [LinearEquiv.apply_symm_apply] at h1 h2
  rw [h1, h2, hB]

theorem IsIsometric.isEven {B : ZForm M} {B' : ZForm M'} (h : IsIsometric B B')
    (hB : IsEven B) : IsEven B' := by
  obtain ⟨e, he⟩ := h
  intro x
  have hthis : B' x x = B (e.symm x) (e.symm x) := by
    have := he (e.symm x) (e.symm x)
    simpa using this
  rw [hthis]
  exact hB _

theorem IsIsometric.isPosDef {B : ZForm M} {B' : ZForm M'} (h : IsIsometric B B')
    (hB : IsPosDef B) : IsPosDef B' := by
  obtain ⟨e, he⟩ := h
  intro x hx
  have hxs : e.symm x ≠ 0 := fun h0 => hx (by rw [← e.apply_symm_apply x, h0]; simp)
  have hthis : B' x x = B (e.symm x) (e.symm x) := by
    have := he (e.symm x) (e.symm x)
    simpa using this
  rw [hthis]
  exact hB _ hxs

theorem IsIsometric.isNegDef {B : ZForm M} {B' : ZForm M'} (h : IsIsometric B B')
    (hB : IsNegDef B) : IsNegDef B' := by
  obtain ⟨e, he⟩ := h
  intro x hx
  have hxs : e.symm x ≠ 0 := fun h0 => hx (by rw [← e.apply_symm_apply x, h0]; simp)
  have hthis : B' x x = B (e.symm x) (e.symm x) := by
    have := he (e.symm x) (e.symm x)
    simpa using this
  rw [hthis]
  exact hB _ hxs

theorem IsIsometric.isUnimodular {B : ZForm M} {B' : ZForm M'} (h : IsIsometric B B')
    (hB : IsUnimodular B) : IsUnimodular B' := by
  obtain ⟨e, he⟩ := h
  -- `x ↦ B' x` is `ψ ↦ ψ ∘ₗ e.symm` applied to `x ↦ B (e.symm x)`
  have hequiv : Function.Bijective
      (fun ψ : M →ₗ[ℤ] ℤ => ψ ∘ₗ (e.symm : M' →ₗ[ℤ] M)) := by
    refine ⟨fun ψ χ hψχ => ?_, fun χ => ⟨χ ∘ₗ (e : M →ₗ[ℤ] M'), ?_⟩⟩
    · refine LinearMap.ext fun m => ?_
      have := congrFun (congrArg DFunLike.coe hψχ) (e m)
      simpa using this
    · refine LinearMap.ext fun m' => ?_
      simp
  have hcomp : (⇑B' : M' → M' →ₗ[ℤ] ℤ)
      = (fun ψ : M →ₗ[ℤ] ℤ => ψ ∘ₗ (e.symm : M' →ₗ[ℤ] M)) ∘ (⇑B) ∘ (e.symm : M' →ₗ[ℤ] M) := by
    funext x
    refine LinearMap.ext fun y => ?_
    simp only [Function.comp_apply, LinearMap.comp_apply]
    simpa using he (e.symm x) (e.symm y)
  show Function.Bijective (⇑B')
  rw [hcomp]
  exact (hequiv.comp hB).comp e.symm.bijective

theorem IsIsometric.isUnimodular_iff {B : ZForm M} {B' : ZForm M'} (h : IsIsometric B B') :
    IsUnimodular B ↔ IsUnimodular B' :=
  ⟨fun hB => h.isUnimodular hB, fun hB' => h.symm.isUnimodular hB'⟩

theorem IsIsometric.isIndefinite {B : ZForm M} {B' : ZForm M'} (h : IsIsometric B B')
    (hB : IsIndefinite B) : IsIndefinite B' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hB
  refine ⟨⟨e x, ?_⟩, e y, ?_⟩
  · have := he x x; rw [this]; exact hx
  · have := he y y; rw [this]; exact hy

/-! ## Splitting off an orthogonal summand -/

/-- `SplitsOff B B'` : the form `B'` is an orthogonal summand of `B`, i.e. `B` is isometric to
`B' ⊥ B''` for some form `B''`.  In the applications, "`B` splits off a hyperbolic plane" is
`SplitsOff B hyp` (`Work.UnimodularForms.hyp`). -/
def SplitsOff.{u, v} {M : Type u} [AddCommGroup M] [Module ℤ M]
    {M' : Type v} [AddCommGroup M'] [Module ℤ M'] (B : ZForm M) (B' : ZForm M') : Prop :=
  ∃ (M'' : Type u) (_ : AddCommGroup M'') (_ : Module ℤ M'') (B'' : ZForm M''),
    IsIsometric B (orthSum B' B'')

@[inherit_doc] scoped infix:70 " ⊕ₒ " => orthSum

end

end Work.UnimodularForms
