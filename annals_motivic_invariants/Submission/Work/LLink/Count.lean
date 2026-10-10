import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.cInv_add_defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.LLink.Count` — the counting layer of the L-link computation

Part A (`Submission/Work/Motivic/Defs.lean`) defines, for a birational map `φ : X ⤏ Y` over a
field `𝕜` and a point `z` of a `𝕜`-scheme `Z`,

* `exDiv φ = {x : X | coheight x = 1 ∧ ¬ IsIsoAt φ x}` — the exceptional divisors of `φ`,
* `excCount 𝕜 z φ = #{x ∈ exDiv φ | ResEquiv 𝕜 x z}` — how many of them have the birational
  (= function field) class of `z`,
* `cInv 𝕜 z φ = excCount 𝕜 z φ⁻¹ - excCount 𝕜 z φ` — the `[κ(z)]`-coefficient of the
  Lin–Shinder invariant.

This file computes those numbers in the situation of the paper's L-links (Lemma 3.14
`lemma:L-link`, item 2): the birational map has exactly **one** exceptional divisor in each
direction, and the two are distinguished by the residue field of the base point `z`.

The results here are hypothesis-level: the *geometry* ("`exDiv φ` is this singleton") is the
output of the Crauder–Katz construction (see `Submission/Work/LLink/QuadroCubic.lean`), while the
*counting* is what this file does.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.LLink

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

variable {𝕜 : Type} [Field 𝕜]
variable {X Y Z Z' : Scheme.{0}}

section Count

variable [IrreducibleSpace X] [IrreducibleSpace Y]
variable [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
variable [Z.Over (Spec (.of 𝕜))]

/-- `excCount` is the cardinality of the set of exceptional divisors matching the base point. -/
theorem excCount_eq_ncard (z : Z) (φ : X.BirationalMap Y) :
    excCount 𝕜 z φ = (exDiv φ ∩ {x | ResEquiv 𝕜 x z}).ncard := rfl

/-- If the only exceptional divisor of `φ` is `x`, and `x` has the birational class of the base
point, then `φ` contributes exactly `1` to the coefficient. -/
theorem excCount_eq_one_of_exDiv_eq_singleton (z : Z) (φ : X.BirationalMap Y) {x : X}
    (h : exDiv φ = {x}) (hx : ResEquiv 𝕜 x z) : excCount 𝕜 z φ = 1 := by
  have hset : {x' : X | x' ∈ exDiv φ ∧ ResEquiv 𝕜 x' z} = {x} := by
    ext y
    simp only [Set.mem_ofPred_eq, h, Set.mem_singleton_iff]
    exact ⟨fun hy => hy.1, fun hy => ⟨hy, by rw [hy]; exact hx⟩⟩
  show (Set.ncard {x' : X | x' ∈ exDiv φ ∧ ResEquiv 𝕜 x' z} : ℕ) = 1
  rw [hset, Set.ncard_singleton]

/-- If the only exceptional divisor of `φ` is `x`, and `x` does *not* have the birational class of
the base point, then `φ` contributes exactly `0`. -/
theorem excCount_eq_zero_of_exDiv_eq_singleton (z : Z) (φ : X.BirationalMap Y) {x : X}
    (h : exDiv φ = {x}) (hx : ¬ ResEquiv 𝕜 x z) : excCount 𝕜 z φ = 0 := by
  have hset : {x' : X | x' ∈ exDiv φ ∧ ResEquiv 𝕜 x' z} = ∅ := by
    ext y
    simp only [Set.mem_ofPred_eq, h, Set.mem_singleton_iff, Set.mem_empty_iff_false]
    exact ⟨fun hy => hx (by rw [← hy.1]; exact hy.2), fun hy => hy.elim⟩
  show (Set.ncard {x' : X | x' ∈ exDiv φ ∧ ResEquiv 𝕜 x' z} : ℕ) = 0
  rw [hset, Set.ncard_empty]

/-- If `φ` has no exceptional divisors at all, it contributes `0`. -/
theorem excCount_eq_zero_of_exDiv_eq_empty (z : Z) (φ : X.BirationalMap Y)
    (h : exDiv φ = ∅) : excCount 𝕜 z φ = 0 := by
  have hset : {x' : X | x' ∈ exDiv φ ∧ ResEquiv 𝕜 x' z} = ∅ := by
    ext y
    simp only [Set.mem_ofPred_eq, h, Set.mem_empty_iff_false, false_and]
  show (Set.ncard {x' : X | x' ∈ exDiv φ ∧ ResEquiv 𝕜 x' z} : ℕ) = 0
  rw [hset, Set.ncard_empty]

end Count

section Main

variable [IrreducibleSpace X] [IrreducibleSpace Y]
variable [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
variable [Z.Over (Spec (.of 𝕜))]

/-- **The L-link computation of the invariant coefficient** (paper Lemma 3.14, item 2, in the
per-coefficient vocabulary of Part A).

Let `φ : X ⤏ Y` be a birational map over `𝕜` with exactly one exceptional divisor `x` on the
source and exactly one exceptional divisor `y` on the target, and let `z` be a base point whose
birational class is that of `y` but not that of `x`.  Then the `[κ(z)]`-coefficient of the
Lin–Shinder invariant of `φ` is exactly `1`.

Concretely, for the Crauder–Katz link `ψ : Q³ ⤏ ℙ³` we take `x` to be the divisor birational to
`ℙ¹ × C'` and `y` the one birational to `ℙ¹ × C`; then `cInv 𝕜 z ψ = [ℙ¹ × C] - [ℙ¹ × C']`
evaluated at the class `[κ(z)] = [κ(C)(t)]`. -/
theorem cInv_eq_one_of_exDiv_eq_singletons (z : Z) (φ : X.BirationalMap Y) {x : X} {y : Y}
    (hx : exDiv φ = {x}) (hy : exDiv φ.symm = {y})
    (hxz : ¬ ResEquiv 𝕜 x z) (hyz : ResEquiv 𝕜 y z) : cInv 𝕜 z φ = 1 := by
  have h1 : excCount 𝕜 z φ.symm = 1 :=
    excCount_eq_one_of_exDiv_eq_singleton (X := Y) (Y := X) z φ.symm hy hyz
  have h2 : excCount 𝕜 z φ = 0 :=
    excCount_eq_zero_of_exDiv_eq_singleton z φ hx hxz
  show (excCount 𝕜 z φ.symm : ℤ) - (excCount 𝕜 z φ : ℤ) = 1
  rw [h1, h2]
  norm_num

/-- The same computation, recorded as the pair of `excCount`s: "the two exceptional divisors
contribute `1` and `0` respectively". -/
theorem excCount_pair_of_exDiv_eq_singletons (z : Z) (φ : X.BirationalMap Y) {x : X} {y : Y}
    (hx : exDiv φ = {x}) (hy : exDiv φ.symm = {y})
    (hxz : ¬ ResEquiv 𝕜 x z) (hyz : ResEquiv 𝕜 y z) :
    excCount 𝕜 z φ.symm = 1 ∧ excCount 𝕜 z φ = 0 :=
  ⟨excCount_eq_one_of_exDiv_eq_singleton (X := Y) (Y := X) z φ.symm hy hyz,
    excCount_eq_zero_of_exDiv_eq_singleton z φ hx hxz⟩

/-- **Sharpness of the L-link computation.**  If the two exceptional divisors of the link *both*
have the birational class of the base point — in particular if the two centres `C`, `C'` of the
link are stably birational — then the coefficient vanishes.  So the non-triviality of the link is
*exactly* the inequality `κ(C)(t) ≇ κ(C')(t)`; the hypothesis `¬ ResEquiv 𝕜 x z` of
`cInv_eq_one_of_exDiv_eq_singletons` cannot be dropped. -/
theorem cInv_eq_zero_of_exDiv_eq_singletons_of_resEquiv (z : Z) (φ : X.BirationalMap Y) {x : X}
    {y : Y} (hx : exDiv φ = {x}) (hy : exDiv φ.symm = {y}) (hxz : ResEquiv 𝕜 x z)
    (hyz : ResEquiv 𝕜 y z) : cInv 𝕜 z φ = 0 := by
  have h1 : excCount 𝕜 z φ.symm = 1 :=
    excCount_eq_one_of_exDiv_eq_singleton (X := Y) (Y := X) z φ.symm hy hyz
  have h2 : excCount 𝕜 z φ = 1 :=
    excCount_eq_one_of_exDiv_eq_singleton z φ hx hxz
  show (excCount 𝕜 z φ.symm : ℤ) - (excCount 𝕜 z φ : ℤ) = 0
  rw [h1, h2]
  norm_num

/-- **The L-link is motivically non-trivial.**  Same hypotheses as
`cInv_eq_one_of_exDiv_eq_singletons`. -/
theorem cInv_ne_zero_of_exDiv_eq_singletons (z : Z) (φ : X.BirationalMap Y) {x : X} {y : Y}
    (hx : exDiv φ = {x}) (hy : exDiv φ.symm = {y})
    (hxz : ¬ ResEquiv 𝕜 x z) (hyz : ResEquiv 𝕜 y z) : cInv 𝕜 z φ ≠ 0 := by
  rw [cInv_eq_one_of_exDiv_eq_singletons z φ hx hy hxz hyz]
  norm_num

end Main

section BaseChange

variable [IrreducibleSpace X] [IrreducibleSpace Y]
variable [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
variable [Z.Over (Spec (.of 𝕜))] [Z'.Over (Spec (.of 𝕜))]

/-- `excCount` depends on the base point only through its residue field. -/
theorem excCount_congr_of_resEquiv (z : Z) {z' : Z'} (h : ResEquiv 𝕜 z z')
    (φ : X.BirationalMap Y) : excCount 𝕜 z φ = excCount 𝕜 z' φ := by
  have hset : {x' : X | x' ∈ exDiv φ ∧ ResEquiv 𝕜 x' z} =
      {x' : X | x' ∈ exDiv φ ∧ ResEquiv 𝕜 x' z'} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hw, hwz⟩
      exact ⟨hw, Work.Motivic.ResEquiv.trans hwz h⟩
    · rintro ⟨hw, hwz⟩
      exact ⟨hw, Work.Motivic.ResEquiv.trans hwz (Work.Motivic.ResEquiv.symm h)⟩
  show (Set.ncard {x' : X | x' ∈ exDiv φ ∧ ResEquiv 𝕜 x' z} : ℕ) =
    (Set.ncard {x' : X | x' ∈ exDiv φ ∧ ResEquiv 𝕜 x' z'} : ℕ)
  rw [hset]

/-- **The base point of the invariant is only its residue field.**  If `ResEquiv 𝕜 z z'` then the
whole coefficient `cInv` agrees at `z` and `z'`.  This is what lets one instantiate the paper's
`z₀` (the generic point of `C × ℙ¹`) by *any* point with function field `κ(C)(t)`. -/
theorem cInv_congr_of_resEquiv (z : Z) {z' : Z'} (h : ResEquiv 𝕜 z z')
    (φ : X.BirationalMap Y) : cInv 𝕜 z φ = cInv 𝕜 z' φ := by
  show (excCount 𝕜 z φ.symm : ℤ) - (excCount 𝕜 z φ : ℤ) =
    (excCount 𝕜 z' φ.symm : ℤ) - (excCount 𝕜 z' φ : ℤ)
  rw [excCount_congr_of_resEquiv z h φ.symm, excCount_congr_of_resEquiv z h φ]

end BaseChange


section AbstractLink

variable [IrreducibleSpace X] [IrreducibleSpace Y]
variable [X.Over (Spec (.of 𝕜))]

/-- If the two exceptional counts of the L-link are `1` and `0`, the coefficient is `1`. -/
theorem cInv_eq_one_of_excCount_eq [Y.Over (Spec (.of 𝕜))] {Z : Scheme.{0}}
    [Z.Over (Spec (.of 𝕜))] (z : Z) (φ : X.BirationalMap Y)
    (h1 : excCount 𝕜 z φ.symm = 1) (h2 : excCount 𝕜 z φ = 0) : cInv 𝕜 z φ = 1 := by
  show (excCount 𝕜 z φ.symm : ℤ) - (excCount 𝕜 z φ : ℤ) = 1
  rw [h1, h2]
  norm_num

/-- **The L-link lemma, non-vanishing form, with no base point to choose.**  Let `ψ : X ⤏ Y` be a
birational map over `𝕜` whose only exceptional divisor on the source is `x`, whose only exceptional
divisor on the target is `y`, and suppose that the two do not have the same birational class.
Then there is a base point `z₀` at which the invariant coefficient of `ψ` does not vanish. -/
theorem exists_cInv_ne_zero_of_link [hY : Y.Over (Spec (.of 𝕜))]
    (ψ : X.BirationalMap Y) (x : X) (y : Y)
    (hx : exDiv ψ = {x}) (hy : exDiv ψ.symm = {y}) (hxy : ¬ ResEquiv 𝕜 x y) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z),
      cInv 𝕜 z₀ ψ ≠ 0 := by
  refine ⟨Y, hY, y, ?_⟩
  have h : cInv 𝕜 y ψ = 1 :=
    cInv_eq_one_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := X) (Y := Y) y ψ hx hy hxy
      (Work.Motivic.ResEquiv.refl 𝕜 y)
  rw [h]
  norm_num

end AbstractLink


section ResAlgEquiv

variable [IrreducibleSpace X] [X.Over (Spec (.of 𝕜))]

/-- **`κ(x)` presented by an abstract field.**  `ResAlgEquiv 𝕜 x A φ` says that the residue field
of `x` is `𝕜`-isomorphic to the field `A`, the structure map `𝕜 → κ(x)` corresponding to
`φ : 𝕜 →+* A`.

This is the form in which the field-theoretic input of the Crauder–Katz link is stated: with
`A` the function field `κ(C)(t)` of `ℙ¹ × C` this is the assertion `κ(η) ≅_𝕜 κ(C)(t)`. -/
def ResAlgEquiv (𝕜 : Type) [Field 𝕜] {X : Scheme.{0}} [X.Over (Spec (.of 𝕜))] (x : X)
    (A : Type) [Field A] (φ : 𝕜 →+* A) : Prop :=
  ∃ e : X.residueField x ≃+* A, e.toRingHom.comp (resMap 𝕜 X x) = φ

/-- `ResEquiv` between two points is the special case of `ResAlgEquiv` in which the abstract field
is the other residue field. -/
theorem resEquiv_iff_resAlgEquiv {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] {x : X} {z : Z} :
    ResEquiv 𝕜 x z ↔ ResAlgEquiv 𝕜 x (Z.residueField z) (resMap 𝕜 Z z) := Iff.rfl

end ResAlgEquiv

end Work.LLink
