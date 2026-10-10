/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.Assembly
import Submission.Work.LLink.cInv_eq_neg_symm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.Affine` — the affine form of the Crauder–Katz link, and the identity transport

The Cremona group of the challenge is `Cr 𝕜 3 = Bir(𝔸³/𝕜)` (`ChallengeDeps.lean`), so a link
`ψ : Q ⤏ P` between projective threefolds has to be *transported* to `𝔸³` before it can be used:
`φ = ε ∘ ψ ∘ δ` with `ε : 𝔸³ ⤏ Q`, `δ : P ⤏ 𝔸³` birational identifications over `𝕜`
(`Work.LLink.transport`; the paper's strong rationality of `Q³` and `ℙ³`).

This file contains

* the **identity-transport lemmas** — `exDiv (BirationalMap.refl X) = ∅`,
  `cInv 𝕜 z (BirationalMap.refl X) = 0` — which make the transport data `TRA` of
  `CrauderKatzLink` *free* whenever the link already lives on `𝔸³`;
* the **affine form** `AffineKatzLink 𝕜 X` of the link (`Q = P = 𝔸³`), together with
  `AffineKatzLink.toCrauderKatzLink`, which converts it into a `CrauderKatzLink` and thereby
  removes the `TRA` input entirely, and the invariant computations
  `AffineKatzLink.cInv_eq_one` / `cInv_ne_zero` for the affine composite.

*Caveat, recorded deliberately.*  `AffineKatzLink` is a *sufficient*, but not literally the
paper's, form of the input: the affine composite `ε ∘ ψ ∘ δ` of the paper's projective link need
not have singleton exceptional sets, because `ε` and `δ` have exceptional divisors of their own
(e.g. the hyperplane at infinity for `ℙ³ ⤏ 𝔸³`).  It is the form in which the final argument for
`Cr 𝕜 3` is carried out (compare the paper's proof of `thm:bir-generation`), and a producer who
realises the link directly on affine charts can use it and forget about (TRA).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order
open Work.Arithmetic (GenOneCurve)

namespace Work.CrauderKatz

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## The identity transport -/

/-- A partial isomorphism realises its own rational map, hence every point of its source is an
isomorphism point of the associated birational map. -/
theorem isIsoAt_toBirationalMap_of_mem_source {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (i : X.PartialIso Y) {x : X} (hx : x ∈ i.source) :
    IsIsoAt i.toBirationalMap x :=
  ⟨i, hx, rfl⟩

/-- **The identity is an isomorphism at every point.** -/
theorem isIsoAt_refl {X : Scheme.{0}} [IrreducibleSpace X] (x : X) :
    IsIsoAt (BirationalMap.refl X) x :=
  ⟨PartialIso.refl X, by simp, rfl⟩

/-- **The identity has no exceptional divisors.** -/
theorem exDiv_refl {X : Scheme.{0}} [IrreducibleSpace X] :
    exDiv (BirationalMap.refl X) = (∅ : Set X) := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨-, h⟩
  exact h (isIsoAt_refl x)

/-- The inverse of the identity birational map is the identity. -/
@[simp]
theorem symm_refl {X : Scheme.{0}} [IrreducibleSpace X] :
    (BirationalMap.refl X).symm = BirationalMap.refl X := by
  apply BirationalMap.ext
  simp

/-- **The identity transport contributes nothing to the invariant.** -/
theorem cInv_refl (𝕜 : Type) [Field 𝕜] {X : Scheme.{0}} [IrreducibleSpace X]
    [X.Over (Spec (.of 𝕜))] {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z) :
    cInv 𝕜 z (BirationalMap.refl X) = 0 := by
  have h2 := Work.LLink.cInv_eq_neg_symm 𝕜 z (BirationalMap.refl X)
  rw [symm_refl] at h2
  linarith

/-- A `𝕜`-scheme structure makes the identity birational map a map over `𝕜`. -/
instance instIsOver_refl (S : Scheme.{0}) {X : Scheme.{0}} [IrreducibleSpace X] [X.Over S] :
    (BirationalMap.refl X).IsOver S :=
  inferInstanceAs ((RationalMap.id X).IsOver S)

/-- The transport along two identity identifications is the map itself, so no invariant is
created: this is what makes the affine form `AffineKatzLink` free of transport hypotheses. -/
theorem transport_refl (φ : (Work.LLink.Affine3 𝕜).BirationalMap (Work.LLink.Affine3 𝕜)) :
    Work.LLink.transport (BirationalMap.refl (Work.LLink.Affine3 𝕜)) φ
      (BirationalMap.refl (Work.LLink.Affine3 𝕜)) = φ := by
  rw [Work.LLink.transport_def, BirationalMap.trans_refl, BirationalMap.refl_trans]

/-! ## The affine form of the link -/

/-- **The affine form of the Crauder–Katz link**: the same geometric and function-field data as
`CrauderKatzLink`, but with `Q = P = 𝔸³`, so the transports `ε`, `δ` of `CrauderKatzLink` are the
identities and (TRA) is discharged by `cInv_refl`.

`ψ : 𝔸³ ⤏ 𝔸³` is a birational self-map over `𝕜` with exactly one exceptional divisor `x` on the
source (birational to `ℙ¹ × C'`) and exactly one on the target `y` (birational to `ℙ¹ × C`),
presented by (F1) as the cylinder fields `κ(C')(t)`, `κ(C)(t)`; the base point of the invariant is
`y` itself. -/
structure AffineKatzLink (𝕜 : Type) [Field 𝕜] (X : GenOneCurve 𝕜) where
  /-- A scheme model of `C' = Jac²C`. -/
  M : JacSqModel 𝕜 X
  /-- The affine form of the Crauder–Katz transformation. -/
  ψ : (Work.LLink.Affine3 𝕜).BirationalMap (Work.LLink.Affine3 𝕜)
  /-- `ψ` is defined over `𝕜`, i.e. it lies in `Cr 𝕜 3`. -/
  isOverψ : ψ.IsOver (Spec (.of 𝕜))
  /-- The exceptional divisor of `ψ` on the source (birational to `ℙ¹ × C'`). -/
  x : Work.LLink.Affine3 𝕜
  /-- The exceptional divisor of `ψ⁻¹` on the target (birational to `ℙ¹ × C`). -/
  y : Work.LLink.Affine3 𝕜
  exDiv_ψ : exDiv ψ = {x}
  exDiv_ψ_symm : exDiv ψ.symm = {y}
  /-- **(F1)** `κ(y) ≅_𝕜 κ(C)(t)`. -/
  resY : Work.LLink.ResAlgEquiv 𝕜 y (cylinderField 𝕜 X) (cylResMap 𝕜 X)
  /-- **(F1)** `κ(x) ≅_𝕜 κ(C')(t)`. -/
  resX : Work.LLink.ResAlgEquiv 𝕜 x (cylinderField 𝕜 M.C') (cylResMap 𝕜 M.C')

namespace AffineKatzLink

variable {X : GenOneCurve 𝕜} (A : AffineKatzLink 𝕜 X)

/-- The affine form of the link seen as a `CrauderKatzLink`: the two transports are the
identities, and they contribute nothing (`cInv_refl`), so no transport input is needed. -/
noncomputable def toCrauderKatzLink :
    CrauderKatzLink 𝕜 X :=
  { M := A.M
    Q := Work.LLink.Affine3 𝕜
    P := Work.LLink.Affine3 𝕜
    ψ := A.ψ
    isOverψ := A.isOverψ
    x := A.x
    y := A.y
    exDiv_ψ := A.exDiv_ψ
    exDiv_ψ_symm := A.exDiv_ψ_symm
    resY := A.resY
    resX := A.resX
    ε := BirationalMap.refl _
    δ := BirationalMap.refl _
    cInv_ε := cInv_refl 𝕜 A.y
    cInv_δ := cInv_refl 𝕜 A.y }

/-- **The affine link computes the invariant `1`** at the exceptional divisor `y`, with no
transport input at all. -/
theorem cInv_eq_one (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) :
    cInv 𝕜 A.y A.ψ = 1 :=
  Work.LLink.cInv_eq_one_of_exDiv_eq_singletons A.y A.ψ A.exDiv_ψ A.exDiv_ψ_symm
    (fun h => not_resEquiv_of_presentations A.M A.resY A.resX hF hni
      (Work.Motivic.ResEquiv.symm h))
    (Work.Motivic.ResEquiv.refl 𝕜 A.y)

/-- The invariant coefficient of the affine link does not vanish. -/
theorem cInv_ne_zero (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) :
    cInv 𝕜 A.y A.ψ ≠ 0 := by
  rw [A.cInv_eq_one hF hni]
  norm_num

/-- **The affine-form assembly**: from an affine link over `𝕜` at `X` (and the function-field
input) one gets the existential consumed by `Work.Motivic.not_gen_of_cInv_ne_zero`, with no
transport hypothesis to discharge. -/
theorem exists_cInv_ne_zero (A : AffineKatzLink 𝕜 X) (hF : FunctionFieldInput 𝕜)
    (hni : X.NotIsoJacSq) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 3),
      cInv 𝕜 z₀ (φ : (Work.LLink.Affine3 𝕜).BirationalMap
        (Work.LLink.Affine3 𝕜)) ≠ 0 :=
  Work.LLink.QuadroCubicLink.exists_cInv_ne_zero
    ⟨toQuadroCubicLink A.toCrauderKatzLink hni hF⟩

end AffineKatzLink

end

end Work.CrauderKatz
