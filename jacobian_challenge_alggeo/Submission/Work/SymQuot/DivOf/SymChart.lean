/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The chart of a point of `Symⁿ C`: coordinate pullbacks and characteristic polynomials (area SY)

Fix an affine open `V ⊆ C` and put `U = piOpen C.toOver V n = Vⁿ ⊆ Cⁿ`, so that the chart of
`Symⁿ C` over `U` is `Spec A` with `A = Γ(Cⁿ, U)^{S_n}` (`Work.SymQuot.DivOf.chartInvariants`)
and the ring of the curve is `B = Γ(C, V)`.

This file provides the elementary algebra of the construction of `divOf` (see
`Submission/Work/SymQuot/NOTES.md`):

* `coordPullbackAt C n V m : Γ(C,V) →+* Γ(Cⁿ, Vⁿ)`, the pullback of a regular function on `V`
  along the `m`-th projection `Cⁿ ⟶ C`, and `sectionHom_coordPullbackAt`: the `S_n`-action
  permutes the coordinate pullbacks;
* `charpoly C n V b = ∏_m (T - b^(m))`, whose coefficients are `S_n`-invariant
  (`charpoly_coeff_mem_chartInvariants`), i.e. regular functions on the chart `Spec A`;
* `ChartPt` — a point `p` of `Symⁿ C` together with the data of an affine open `V ⊆ C` whose
  chart contains it (`ChartPt.φ` is the induced map `A →+* F` on the chart ring);
* `ChartPt.evalMap` — the evaluation of a regular function on `Vⁿ` at an `F'`-point `x` of `Vⁿ`;
* `ChartPt.charpolyValue` — the characteristic polynomial `χ_b ∈ F[T]` of `b ∈ Γ(C,V)` at the
  point, i.e. `charpoly` with its coefficients evaluated through `φ`.

The main input proved downstream is the *key lemma* (`ChartPt.φ_eq_evalMap`): the value of an
invariant function at a point of `Symⁿ C` equals its value at any lift.
-/
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.DivOf.Setup
import Submission.Work.SymQuot.Prod.isAffineOpen_piOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

namespace DivOf

variable {K : Type u} [Field K]

/-! ### The coordinate pullbacks -/

variable (C : Work.CurveBasics.Curve K) (n : ℕ)

/-- **The `m`-th coordinate pullback**: the pullback of a regular function on `V ⊆ C` to the
product open `Vⁿ ⊆ Cⁿ` along the `m`-th projection. -/
noncomputable def coordPullbackAt (V : C.left.Opens) (m : Fin n) :
    Γ(C.left, V) →+* Γ((prod C.toOver n).left, piOpen C.toOver V n) :=
  (((proj C.toOver n m).left.appLE V (piOpen C.toOver V n)
    (by intro x hx; rw [mem_piOpen] at hx; exact hx m))).hom

variable {C n}

@[simp]
theorem coordPullbackAt_apply (V : C.left.Opens) (m : Fin n) (b : Γ(C.left, V)) :
    coordPullbackAt C n V m b =
      Scheme.Hom.appLE (proj C.toOver n m).left V (piOpen C.toOver V n)
        (by intro x hx; rw [mem_piOpen] at hx; exact hx m) b := rfl

variable (C n) in
/-- The product open `Vⁿ` is contained in the preimage of `V` under the `m`-th projection
(the defining property of the product open). -/
theorem piOpen_le_preimage_proj (V : C.left.Opens) (m : Fin n) :
    piOpen C.toOver V n ≤ (proj C.toOver n m).left ⁻¹ᵁ V :=
  fun _ hx => by rw [mem_piOpen] at hx; exact hx m

variable (C n) in
/-- **The action of `S_n` on the sections permutes the coordinate pullbacks.** -/
theorem sectionHom_coordPullbackAt (V : C.left.Opens)
    (hU : (symAction C n).IsInvariantOpen (piOpen C.toOver V n))
    (σ : ULift.{u} (Equiv.Perm (Fin n))) (m : Fin n) :
    ((symAction C n).sectionHom (piOpen C.toOver V n) hU σ).comp
        (coordPullbackAt C n V m) =
      coordPullbackAt C n V (σ.down.symm m) := by
  have hproj : (symAction C n).hom σ ≫ (proj C.toOver n m).left =
      (proj C.toOver n (σ.down.symm m)).left :=
    (comp_hom_proj C.toOver n σ.down m)
  have hmem : piOpen C.toOver V n ≤ (symAction C n).hom σ ⁻¹ᵁ (piOpen C.toOver V n) :=
    le_of_eq (hU σ).symm
  have key : Scheme.Hom.appLE ((proj C.toOver n m).left) V (piOpen C.toOver V n)
        (piOpen_le_preimage_proj C n V m) ≫
      Scheme.Hom.appLE ((symAction C n).hom σ) (piOpen C.toOver V n) (piOpen C.toOver V n) hmem =
      Scheme.Hom.appLE ((proj C.toOver n (σ.down.symm m)).left) V (piOpen C.toOver V n)
        (piOpen_le_preimage_proj C n V (σ.down.symm m)) := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_hom hproj _ _
  ext b
  simp only [RingHom.comp_apply, GAction.sectionHom_apply, coordPullbackAt_apply]
  exact congrArg (fun f : Γ(C.left, V) →+* Γ((prod C.toOver n).left, piOpen C.toOver V n) =>
    f b) (congrArg CommRingCat.Hom.hom key)

variable (C n) in
/-- **The product open `Vⁿ ⊆ Cⁿ` is invariant under the `S_n`-action** (the `ULift`ed form of
`Work.SymQuot.piOpen_invariant`). -/
theorem symPiOpen_invariant (V : C.left.Opens) :
    (symAction C n).IsInvariantOpen (piOpen C.toOver V n) :=
  fun σ => piOpen_invariant C.toOver V n σ.down

variable (C n) in
/-- **The characteristic polynomial** `∏_m (T - b^(m))` of `b ∈ Γ(C,V)`: a monic polynomial of
degree `n` over `Γ(Cⁿ, Vⁿ)`. -/
noncomputable def charpoly (V : C.left.Opens) (b : Γ(C.left, V)) :
    Polynomial Γ((prod C.toOver n).left, piOpen C.toOver V n) :=
  ∏ m, (Polynomial.X - Polynomial.C (coordPullbackAt C n V m b))

variable (C n) in
/-- The `S_n`-action fixes the characteristic polynomial. -/
theorem charpoly_perm (V : C.left.Opens)
    (hU : (symAction C n).IsInvariantOpen (piOpen C.toOver V n))
    (σ : ULift.{u} (Equiv.Perm (Fin n))) (b : Γ(C.left, V)) :
    Polynomial.map ((symAction C n).sectionHom (piOpen C.toOver V n) hU σ)
      (charpoly C n V b) = charpoly C n V b := by
  have key : ∀ m : Fin n,
      Polynomial.map ((symAction C n).sectionHom (piOpen C.toOver V n) hU σ)
        (Polynomial.X - Polynomial.C (coordPullbackAt C n V m b)) =
      Polynomial.X - Polynomial.C (coordPullbackAt C n V (σ.down.symm m) b) := by
    intro m
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 2
    exact congrArg (fun f : Γ(C.left, V) →+* Γ((prod C.toOver n).left,
        piOpen C.toOver V n) => f b) (sectionHom_coordPullbackAt C n V hU σ m)
  have h1 : Polynomial.map ((symAction C n).sectionHom (piOpen C.toOver V n) hU σ)
      (charpoly C n V b) =
      ∏ m : Fin n, Polynomial.map ((symAction C n).sectionHom (piOpen C.toOver V n) hU σ)
        (Polynomial.X - Polynomial.C (coordPullbackAt C n V m b)) := by
    rw [charpoly, Polynomial.map_prod]
  rw [h1, Finset.prod_congr rfl (fun m _ => key m),
    Equiv.prod_comp σ.down.symm (fun m => Polynomial.X - Polynomial.C (coordPullbackAt C n V m b)),
    ← charpoly]

variable (C n) [NeZero n] in
/-- **The coefficients of the characteristic polynomial are invariant**, i.e. they are regular
functions on the chart `Spec A` of `Symⁿ C` (with `A = Γ(Cⁿ,Vⁿ)^{S_n}`). -/
theorem charpoly_coeff_mem_chartInvariants [CurveAffineCover C] (V : C.left.Opens)
    (hU : (symAction C n).IsInvariantOpen (piOpen C.toOver V n)) (b : Γ(C.left, V)) (i : ℕ) :
    (charpoly C n V b).coeff i ∈ chartInvariants (C := C) (n := n) (piOpen C.toOver V n) hU := by
  rw [GAction.mem_invariants_iff]
  intro σ
  rw [← Polynomial.coeff_map, charpoly_perm C n V hU σ⁻¹ b]

end DivOf

end Work.SymQuot
