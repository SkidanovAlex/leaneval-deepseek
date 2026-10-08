import Mathlib
import Submission.Work.CharLib.Defs
import Submission.Work.CharLib.CFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.Basic`: Clifford theory — definitions and conventions

This is the base module of the Clifford-theory area (Area A7 of the Feit–Thompson drive).
It fixes the vocabulary in which Clifford's theorem, the Clifford correspondence,
Gallagher's theorem, Brauer's permutation lemma and the Galois action on characters are
stated.

## Main definitions

* `Work.Clifford.Irr G` — the set of irreducible complex characters of `G`.
* `Work.Clifford.resFun H f`, `Work.Clifford.resFunOfLe h f` — restriction of a function
  `G → ℂ` to a subgroup.
* `Work.Clifford.conjFun N g θ` — the conjugate `θ^g` of a function on a normal subgroup `N`,
  `θ^g(x) = θ (g x g⁻¹)` (so that `(θ^g)^h = θ^{g h}`, `conjFun_mul`).
* `Work.Clifford.inertia N θ` — the inertia group `I_G(θ) = {g : G | θ^g = θ}`.
* `Work.Clifford.charOrbit N θ`, `Work.Clifford.orbitSum N θ` — the `G`-orbit of `θ` and the
  sum of that orbit, the function on `N` that appears in Clifford's theorem.
* `Work.Clifford.inflateFun N f` — pullback of a function on `G ⧸ N` to `G`.
* `Work.Clifford.powChar k χ`, `Work.Clifford.autChar e χ` — the Frobenius twists
  `g ↦ χ (g ^ k)` and `χ ∘ e.symm`.
* `Work.Clifford.IsConstituentOf θ f` — `⟪f, θ⟫ ≠ 0` (`θ` is a constituent of `f`).
* `Work.Clifford.Extends N χ θ`, `Work.Clifford.LiesOver h θ ψ` — extension of a character
  from a subgroup, and `θ` occurring in the restriction of `ψ`.

## Conventions and compatibility

`Work.CharLib` (the seed module of the character-theory areas) fixes its inner product
`Work.CharLib.cfInner` for groups in the universe `Type 0` (`variable {G : Type}`).
The present development must be universe polymorphic (the final theorem is), so we copy the
three primitives `cfInner`, `IsClassFun`, `indFun` *verbatim* here, with the same formulas, at an
arbitrary universe `u`; `Work.Clifford.cfInner_eq_charLib` and friends record that on groups in
`Type 0` the two coincide definitionally.  Everything else in this area is phrased in terms of
the copies defined here.

Note the convention on conjugation, which matches `Work.Induction.conjFun`
(where it is defined for elements of the normalizer): `conjFun N g θ = θ ∘ conjMem N g`, i.e.
`θ^g(x) = θ (g * x * g⁻¹)`, so that `(θ^g)^h = θ^{g * h}`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Clifford

universe u v w

variable {G : Type u} [Group G]

/-! ### Irreducible characters, restriction -/

/-- The set of irreducible complex characters of `G`: the characters of the simple
finite-dimensional complex representations of `G`. -/
def Irr (G : Type*) [Group G] : Set (G → ℂ) :=
  {χ | ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ V.character = χ}

@[simp] theorem mem_Irr {χ : G → ℂ} :
    χ ∈ Irr G ↔ ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ V.character = χ := Iff.rfl

/-- The principal (trivial) character of `G`. -/
def principalChar (G : Type*) [Group G] : G → ℂ := fun _ => 1

@[simp] theorem principalChar_apply (x : G) : principalChar G x = 1 := rfl

/-- Restriction of a complex function on `G` to a subgroup `H ≤ G`. -/
def resFun (H : Subgroup G) (f : G → ℂ) : H → ℂ := fun h => f h

@[simp] theorem resFun_apply (H : Subgroup G) (f : G → ℂ) (h : H) : resFun H f h = f h := rfl

theorem resFun_zero (H : Subgroup G) : resFun H (0 : G → ℂ) = 0 := rfl

theorem resFun_add (H : Subgroup G) (f g : G → ℂ) : resFun H (f + g) = resFun H f + resFun H g :=
  rfl

theorem resFun_smul (H : Subgroup G) (c : ℂ) (f : G → ℂ) :
    resFun H (c • f) = c • resFun H f := rfl

theorem resFun_neg (H : Subgroup G) (f : G → ℂ) : resFun H (-f) = -resFun H f := rfl

theorem resFun_sub (H : Subgroup G) (f g : G → ℂ) :
    resFun H (f - g) = resFun H f - resFun H g := rfl

/-- Restriction of a complex function on `K` to a subgroup `H ≤ K`. -/
def resFunOfLe {H K : Subgroup G} (h : H ≤ K) (f : K → ℂ) : H → ℂ := fun x => f ⟨x, h x.2⟩

@[simp] theorem resFunOfLe_apply {H K : Subgroup G} (h : H ≤ K) (f : K → ℂ) (x : H) :
    resFunOfLe h f x = f ⟨x, h x.2⟩ := rfl

/-! ### Conjugation, inertia, orbits -/

/-- The conjugate of a function on a normal subgroup: `θ^g(x) = θ (g * x * g⁻¹)`. -/
def conjFun (N : Subgroup G) [hN : N.Normal] (g : G) (f : N → ℂ) : N → ℂ :=
  fun n => f ⟨g * (n : G) * g⁻¹, hN.conj_mem (n : G) n.2 g⟩

theorem conjFun_apply (N : Subgroup G) [hN : N.Normal] (g : G) (f : N → ℂ) (n : N) :
    conjFun N g f n = f ⟨g * (n : G) * g⁻¹, hN.conj_mem (n : G) n.2 g⟩ := rfl

@[simp] theorem conjFun_one (N : Subgroup G) [N.Normal] (f : N → ℂ) : conjFun N 1 f = f := by
  ext n
  simp only [conjFun]
  congr 1
  exact Subtype.ext (by group)

theorem conjFun_mul (N : Subgroup G) [N.Normal] (g h : G) (f : N → ℂ) :
    conjFun N (g * h) f = conjFun N h (conjFun N g f) := by
  ext n
  simp only [conjFun]
  congr 1
  exact Subtype.ext (by group)

@[simp] theorem conjFun_inv_left (N : Subgroup G) [N.Normal] (g : G) (f : N → ℂ) :
    conjFun N g⁻¹ (conjFun N g f) = f := by
  rw [← conjFun_mul, mul_inv_cancel, conjFun_one]

@[simp] theorem conjFun_inv_right (N : Subgroup G) [N.Normal] (g : G) (f : N → ℂ) :
    conjFun N g (conjFun N g⁻¹ f) = f := by
  rw [← conjFun_mul, inv_mul_cancel, conjFun_one]

/-- The inertia group `I_G(θ) = {g : G | θ^g = θ}` of a function `θ` on a normal subgroup. -/
def inertia (N : Subgroup G) [N.Normal] (θ : N → ℂ) : Subgroup G where
  carrier := {g : G | conjFun N g θ = θ}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [conjFun_mul, hg, hh]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h1 : conjFun N g⁻¹ (conjFun N g θ) = conjFun N g⁻¹ θ := by rw [hg]
    rw [← conjFun_mul, mul_inv_cancel, conjFun_one] at h1
    exact h1.symm

@[simp] theorem mem_inertia (N : Subgroup G) [N.Normal] (θ : N → ℂ) (g : G) :
    g ∈ inertia N θ ↔ conjFun N g θ = θ := Iff.rfl

/-! ### The inner product, induction, and the orbit sum -/

section Fintype

variable [Fintype G]

/-- The normalised inner product `⟪f, g⟫ = |G|⁻¹ ∑_x f x * conj (g x)` of two complex functions
on a finite group; it is linear in the first argument and conjugate linear in the second. -/
def cfInner (f g : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ x, f x * starRingEnd ℂ (g x)

/-- `f` is a class function on `G`: `f (h * g * h⁻¹) = f g` for all `g`, `h`. -/
def IsClassFun (f : G → ℂ) : Prop := ∀ g h : G, f (h * g * h⁻¹) = f g

/-- The induced class function of a function on a subgroup `H ≤ G`, in the classical trace form
`Ind_H^G f g = |H|⁻¹ ∑_{x : x * g * x⁻¹ ∈ H} f ⟨x * g * x⁻¹, _⟩`. -/
def indFun (H : Subgroup G) (f : H → ℂ) : G → ℂ :=
  fun g => (Nat.card H : ℂ)⁻¹ *
    ∑ x : G, if hx : x * g * x⁻¹ ∈ H then f ⟨x * g * x⁻¹, hx⟩ else 0

@[simp] theorem cfInner_apply (f g : G → ℂ) :
    cfInner f g = (Fintype.card G : ℂ)⁻¹ * ∑ x, f x * starRingEnd ℂ (g x) := rfl

theorem isClassFun_iff {f : G → ℂ} :
    IsClassFun f ↔ ∀ g h : G, f (h * g * h⁻¹) = f g := Iff.rfl

/-- The `G`-orbit of `θ` in the set of functions `N → ℂ` (for `N ⊴ G`). -/
def charOrbit (N : Subgroup G) [N.Normal] (θ : N → ℂ) : Finset (N → ℂ) :=
  Finset.univ.image (fun g : G => conjFun N g θ)

/-- The sum of the `G`-orbit of `θ`: the function on `N` appearing in Clifford's theorem. -/
def orbitSum (N : Subgroup G) [N.Normal] (θ : N → ℂ) : N → ℂ :=
  fun n => ∑ φ ∈ charOrbit N θ, φ n

@[simp] theorem orbitSum_apply (N : Subgroup G) [N.Normal] (θ : N → ℂ) (n : N) :
    orbitSum N θ n = ∑ φ ∈ charOrbit N θ, φ n := rfl

/-- `θ` is a constituent of `f`: `⟪f, θ⟫ ≠ 0`. -/
def IsConstituentOf {H : Type*} [Group H] [Fintype H] (θ f : H → ℂ) : Prop := cfInner f θ ≠ 0

/-- `ψ` (a function on `T`) lies over `θ` (a function on `N ≤ T`): `θ` is a constituent of the
restriction of `ψ` to `N`. -/
def LiesOver (N T : Subgroup G) (h : N ≤ T) (θ : N → ℂ) (ψ : T → ℂ) : Prop :=
  IsConstituentOf θ (resFunOfLe h ψ)

end Fintype

/-! ### Inflation, twists, extensions -/

/-- Pullback of a function on `G ⧸ N` to `G` (for `N ⊴ G`). -/
def inflateFun (N : Subgroup G) [N.Normal] (f : G ⧸ N → ℂ) : G → ℂ :=
  fun g => f (QuotientGroup.mk (s := N) g)

/-- The "Frobenius twist" `g ↦ χ (g ^ k)` of a complex function. -/
def powChar (k : ℕ) (χ : G → ℂ) : G → ℂ := fun g => χ (g ^ k)

/-- Composition of a complex function on `G` with an automorphism of `G`. -/
def autChar (e : G ≃* G) (χ : G → ℂ) : G → ℂ := fun g => χ (e.symm g)

/-- `χ` extends `θ`, where `θ` is a function on a subgroup `N`: the restriction of `χ` to `N`
is `θ`. -/
def Extends (N : Subgroup G) (χ : G → ℂ) (θ : N → ℂ) : Prop := resFun N χ = θ

/-! ### Compatibility with `Work.CharLib` (groups in `Type 0`) -/

section CharLibBridge

variable {G₀ : Type} [Group G₀] [Fintype G₀]

theorem cfInner_eq_charLib (f g : G₀ → ℂ) :
    cfInner f g = CharLib.cfInner (G := G₀) f g := rfl

theorem isClassFun_eq_charLib (f : G₀ → ℂ) :
    IsClassFun f ↔ CharLib.IsClassFun f := Iff.rfl

theorem indFun_eq_charLib (H : Subgroup G₀) (f : H → ℂ) :
    indFun H f = CharLib.indFun H f := rfl

end CharLibBridge

end Work.Clifford
