/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2
-/
import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotC2.TransAux.NoRoot
import Submission.Work.MotC2.TransAux.CoordExt
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open Polynomial WeierstrassCurve.Affine
open scoped IntermediateField

variable {L : Type*} [Field L] [DecidableEq L]

noncomputable local instance instDecEqFuncTr (E : WeierstrassCurve L) : DecidableEq (Func E) :=
  Classical.decEq _

section Translation

variable (E : WeierstrassCurve L) [E.IsElliptic]

/-! ## The translated coordinates are not constant -/

/-- If `(U, V)` satisfies the Weierstrass equation and `U` is transcendental, then `V` is not in the
field `L(U)`: the Weierstrass quadratic has no root there. -/
lemma notMem_adjoin_of_equation {U V : Func E} (h : Equation (baseE E) U V)
    (hU : Transcendental L U) : V ∉ L⟮U⟯ := by
  intro hmem
  rw [IntermediateField.mem_adjoin_simple_iff] at hmem
  obtain ⟨r, s, hs⟩ := hmem
  have key : ∀ r s : L[X], s ≠ 0 → V ≠ Polynomial.aeval U r / Polynomial.aeval U s := by
    intro r s hs' heq
    have hUinj := transcendental_iff_injective.mp hU
    have hsU : Polynomial.aeval U s ≠ 0 := fun hz => hs' (hUinj (by simpa using hz))
    have hmul : V * Polynomial.aeval U s = Polynomial.aeval U r := by
      rw [heq, div_mul_cancel₀ _ hsU]
    have hrel := h
    rw [equation_iff, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hrel
    have hRU : Polynomial.aeval U (r ^ 2 + (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃)
        * r * s - (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2
          + Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆) * s ^ 2) = 0 := by
      simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [← hmul]
      linear_combination (norm := first | refl_ring1 | ring1) (Polynomial.aeval U s ^ 2) * hrel
    have hR0 : r ^ 2 + (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) * r * s
        - (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 + Polynomial.C E.a₄
            * Polynomial.X + Polynomial.C E.a₆) * s ^ 2 = 0 :=
      hUinj (by simpa using hRU)
    exact TransAux.NoRoot E.a₁ E.a₃ E.a₂ E.a₄ E.a₆ r s hs' hR0
  by_cases hs0 : s = 0
  · have hV0 : V = Polynomial.aeval U (0 : L[X]) / Polynomial.aeval U (1 : L[X]) := by
      rw [hs, hs0]
      simp
    exact key 0 1 one_ne_zero hV0
  · exact key r s hs0 hs

/-! ## The evaluation homomorphism at the translated point -/

/-- The `L`-algebra homomorphism `L[E] → L(E)` evaluating at the coordinates of the sum of the
generic point with `T`. -/
noncomputable def phiT (T : E.toAffine.Point) : Coord E →ₐ[L] Func E :=
  plugHom E (transX E T) (transY E T) (equation_transX_transY E T)

@[simp]
lemma phiT_coordX (T : E.toAffine.Point) : phiT E T (coordX E) = transX E T :=
  plugHom_coordX E (transX E T) (transY E T) (equation_transX_transY E T)

@[simp]
lemma phiT_coordY (T : E.toAffine.Point) : phiT E T (coordY E) = transY E T :=
  plugHom_coordY E (transX E T) (transY E T) (equation_transX_transY E T)

lemma phiT_algebraMap (T : E.toAffine.Point) (p : L[X]) :
    phiT E T (algebraMap (L[X]) (Coord E) p) = Polynomial.aeval (transX E T) p := by
  have hcomp : (phiT E T).comp (IsScalarTower.toAlgHom L (L[X]) (Coord E))
      = Polynomial.aeval (transX E T) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_X_eq_coordX,
      phiT_coordX, Polynomial.aeval_X]
  exact AlgHom.congr_fun hcomp p

lemma phiT_eq_zero {T : E.toAffine.Point} {r : Coord E} (hr : phiT E T r = 0) : r = 0 := by
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq (W' := E.toAffine) r
  have hr' : r = algebraMap (L[X]) (Coord E) p + algebraMap (L[X]) (Coord E) q * coordY E := by
    rw [← hpq, CoordinateRing.smul, CoordinateRing.smul, mul_one, AdjoinRoot.mk_C, AdjoinRoot.mk_C,
      ← coordY_eq_mk, ← AdjoinRoot.algebraMap_eq]
  have h2 : Polynomial.aeval (transX E T) p + Polynomial.aeval (transX E T) q * transY E T = 0 := by
    rw [← hr, hr', map_add, map_mul, phiT_algebraMap E T p, phiT_algebraMap E T q, phiT_coordY]
  by_cases hq : q = 0
  · have hp : p = 0 := by
      refine (transcendental_iff_injective.mp (transcendental_transX E T)) ?_
      simpa [hq] using h2
    rw [hr', hp, hq]
    simp
  · have hUtr : Transcendental L (transX E T) := transcendental_transX E T
    have hV : transY E T ∉ L⟮transX E T⟯ := by
      cases T with
      | zero =>
          simpa only [transX_zero, transY_zero] using
            notMem_adjoin_of_equation E (equation_genX_genY E) (transcendental_genX E)
      | some a b hh =>
          simpa only [tU_def, tV_def] using
            notMem_adjoin_of_equation E (transNonsingular E (Point.some a b hh)).1 hUtr
    exfalso
    apply hV
    rw [IntermediateField.mem_adjoin_simple_iff]
    refine ⟨-p, q, ?_⟩
    have hqne : Polynomial.aeval (transX E T) q ≠ 0 := fun hz =>
      hq ((transcendental_iff_injective.mp hUtr) (by simpa using hz))
    rw [map_neg, eq_div_iff hqne]
    linear_combination (norm := first | refl_ring1 | ring1) h2

/-- The evaluation homomorphism at the coordinates of the translated generic point is injective. -/
lemma phiT_injective (T : E.toAffine.Point) : Function.Injective (phiT E T) := by
  intro r r' hrr
  have h0 : phiT E T (r - r') = 0 := by rw [map_sub, hrr, sub_self]
  exact sub_eq_zero.mp (phiT_eq_zero E h0)

/-! ## The induced algebra homomorphism of the function field -/

/-- The `L`-algebra endomorphism of the function field induced by translation by `T`. -/
noncomputable def phi (T : E.toAffine.Point) : Func E →ₐ[L] Func E :=
  IsFractionRing.liftAlgHom (phiT_injective E T)

lemma phi_genX (T : E.toAffine.Point) : phi E T (genX E) = transX E T := by
  rw [phi, genX, IsFractionRing.coe_liftAlgHom, IsFractionRing.lift_algebraMap]
  exact phiT_coordX E T

lemma phi_genY (T : E.toAffine.Point) : phi E T (genY E) = transY E T := by
  rw [phi, genY, IsFractionRing.coe_liftAlgHom, IsFractionRing.lift_algebraMap]
  exact phiT_coordY E T

lemma phi_zero : phi E (0 : E.toAffine.Point) = 1 := by
  have hcomp : (phi E (0 : E.toAffine.Point)).comp (IsScalarTower.toAlgHom L (Coord E) (Func E))
      = IsScalarTower.toAlgHom L (Coord E) (Func E) := by
    refine TransAux.CoordExt E _ _ ?_ ?_
    · change phi E (0 : E.toAffine.Point) (genX E) = genX E
      rw [phi_genX]
      exact transX_zero E
    · change phi E (0 : E.toAffine.Point) (genY E) = genY E
      rw [phi_genY]
      exact transY_zero E
  apply AlgHom.coe_ringHom_injective
  refine IsFractionRing.ringHom_ext (A := Coord E) (fun r => ?_)
  exact AlgHom.congr_fun hcomp r


/-! ## The commutation of `phi T` with the addition formulae -/

lemma map_baseE_phi (P : E.toAffine.Point) :
    (baseE E).map (phi E P).toRingHom = baseE E := by
  rw [baseE, WeierstrassCurve.map_map]
  congr 1
  ext x
  exact (phi E P).commutes x

/-- `phi P` commutes with the `addX` formula. -/
lemma phi_addX_formula (P : E.toAffine.Point) (x₁ x₂ ℓ : Func E) :
    phi E P (addX (baseE E) x₁ x₂ ℓ)
      = addX (baseE E) (phi E P x₁) (phi E P x₂) (phi E P ℓ) := by
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    map_sub, map_add, map_mul, map_pow]
  rw [AlgHom.commutes, AlgHom.commutes]

/-- `phi P` commutes with the `addY` formula. -/
lemma phi_addY_formula (P : E.toAffine.Point) (x₁ x₂ y₁ ℓ : Func E) :
    phi E P (addY (baseE E) x₁ x₂ y₁ ℓ)
      = addY (baseE E) (phi E P x₁) (phi E P x₂) (phi E P y₁) (phi E P ℓ) := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, map_sub, map_add, map_mul, map_pow, map_neg]
  rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]

/-- `phi P` commutes with the slope formula. -/
lemma phi_slope_formula (P : E.toAffine.Point) {a b : L} (h : Nonsingular E a b) :
    phi E P (WeierstrassCurve.Affine.slope (baseE E) (genX E) (algebraMap L (Func E) a)
        (genY E) (algebraMap L (Func E) b))
      = WeierstrassCurve.Affine.slope (baseE E) (phi E P (genX E))
          (phi E P (algebraMap L (Func E) a)) (phi E P (genY E))
          (phi E P (algebraMap L (Func E) b)) := by
  have hne : phi E P (genX E) ≠ phi E P (algebraMap L (Func E) a) := by
    rw [phi_genX, AlgHom.commutes]
    exact transX_ne_algebraMap E P a b h
  rw [slope_of_X_ne (genX_ne_algebraMap E a), slope_of_X_ne hne]
  rw [map_div₀, map_sub, map_sub]

/-- Translation by `P` commutes with the `X`-coordinate formula. -/
lemma phi_transX_some (P : E.toAffine.Point) {a b : L} (h : Nonsingular E a b) :
    phi E P (transX E (Point.some a b h)) = transX E (P + Point.some a b h) := by
  have hne : transX E P ≠ algebraMap L (Func E) a := transX_ne_algebraMap E P a b h
  have hpt : ((genPoint E + pt E P) + pt E (Point.some a b h))
      = genPoint E + pt E (P + Point.some a b h) := by
    rw [add_assoc, pt_add]
  have hleft : ((genPoint E + pt E P) + pt E (Point.some a b h))
      = Point.some (addX (baseE E) (transX E P) (algebraMap L (Func E) a)
          (slope (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
            (algebraMap L (Func E) b)))
        (addY (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
          (slope (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
            (algebraMap L (Func E) b)))
        (nonsingular_add (transNonsingular E P) (ptNonsingular E a b h)
          (fun hxy => hne hxy.1)) := by
    rw [genPoint_add_pt E P, pt_some, Point.add_of_X_ne hne]
  have h2 : Point.some (addX (baseE E) (transX E P) (algebraMap L (Func E) a)
        (slope (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
          (algebraMap L (Func E) b)))
        (addY (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
          (slope (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
            (algebraMap L (Func E) b)))
        (nonsingular_add (transNonsingular E P) (ptNonsingular E a b h)
          (fun hxy => hne hxy.1)) = genPoint E + pt E (P + Point.some a b h) :=
    hleft.symm.trans hpt
  rw [genPoint_add_pt E (P + Point.some a b h), Point.some.injEq] at h2
  rw [transX_some E a b h, phi_addX_formula E P, phi_slope_formula E P h, phi_genX, phi_genY,
    (phi E P).commutes a, (phi E P).commutes b]
  exact h2.1

/-- Translation by `P` commutes with the `Y`-coordinate formula. -/
lemma phi_transY_some (P : E.toAffine.Point) {a b : L} (h : Nonsingular E a b) :
    phi E P (transY E (Point.some a b h)) = transY E (P + Point.some a b h) := by
  have hne : transX E P ≠ algebraMap L (Func E) a := transX_ne_algebraMap E P a b h
  have hpt : ((genPoint E + pt E P) + pt E (Point.some a b h))
      = genPoint E + pt E (P + Point.some a b h) := by
    rw [add_assoc, pt_add]
  have hleft : ((genPoint E + pt E P) + pt E (Point.some a b h))
      = Point.some (addX (baseE E) (transX E P) (algebraMap L (Func E) a)
          (slope (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
            (algebraMap L (Func E) b)))
        (addY (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
          (slope (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
            (algebraMap L (Func E) b)))
        (nonsingular_add (transNonsingular E P) (ptNonsingular E a b h)
          (fun hxy => hne hxy.1)) := by
    rw [genPoint_add_pt E P, pt_some, Point.add_of_X_ne hne]
  have h2 : Point.some (addX (baseE E) (transX E P) (algebraMap L (Func E) a)
        (slope (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
          (algebraMap L (Func E) b)))
        (addY (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
          (slope (baseE E) (transX E P) (algebraMap L (Func E) a) (transY E P)
            (algebraMap L (Func E) b)))
        (nonsingular_add (transNonsingular E P) (ptNonsingular E a b h)
          (fun hxy => hne hxy.1)) = genPoint E + pt E (P + Point.some a b h) :=
    hleft.symm.trans hpt
  rw [genPoint_add_pt E (P + Point.some a b h), Point.some.injEq] at h2
  rw [transY_some E a b h, phi_addY_formula E P, phi_slope_formula E P h, phi_genX, phi_genY,
    (phi E P).commutes a, (phi E P).commutes b]
  exact h2.2

lemma phi_transX (P Q : E.toAffine.Point) : phi E P (transX E Q) = transX E (P + Q) := by
  cases Q with
  | zero =>
      rw [transX_zero, phi_genX, show P + Point.zero = P from add_zero P]
  | some a b h => exact phi_transX_some E P h

lemma phi_transY (P Q : E.toAffine.Point) : phi E P (transY E Q) = transY E (P + Q) := by
  cases Q with
  | zero =>
      rw [transY_zero, phi_genY, show P + Point.zero = P from add_zero P]
  | some a b h => exact phi_transY_some E P h

/-- Translation is multiplicative on the function field. -/
lemma phi_mul (P Q : E.toAffine.Point) : phi E P * phi E Q = phi E (P + Q) := by
  have hcomp : ((phi E P * phi E Q).comp (IsScalarTower.toAlgHom L (Coord E) (Func E)))
      = ((phi E (P + Q)).comp (IsScalarTower.toAlgHom L (Coord E) (Func E))) := by
    refine TransAux.CoordExt E _ _ ?_ ?_
    · change (phi E P * phi E Q) (genX E) = phi E (P + Q) (genX E)
      rw [show (phi E P * phi E Q) (genX E) = phi E P (phi E Q (genX E)) from rfl, phi_genX,
        phi_transX, phi_genX]
    · change (phi E P * phi E Q) (genY E) = phi E (P + Q) (genY E)
      rw [show (phi E P * phi E Q) (genY E) = phi E P (phi E Q (genY E)) from rfl, phi_genY,
        phi_transY, phi_genY]
  apply AlgHom.coe_ringHom_injective
  refine IsFractionRing.ringHom_ext (A := Coord E) (fun r => ?_)
  exact AlgHom.congr_fun hcomp r

/-! ## The translation automorphism -/

/-- The `L`-algebra automorphism of the function field `L(E)` induced by translation by the
point `Q`: the pullback of the translation `P ↦ P + Q`. -/
noncomputable def transAlgEquiv (Q : E.toAffine.Point) : Func E ≃ₐ[L] Func E :=
  AlgEquiv.ofAlgHom (phi E Q) (phi E (-Q))
    (by
      change phi E Q * phi E (-Q) = 1
      rw [phi_mul, add_neg_cancel, phi_zero])
    (by
      change phi E (-Q) * phi E Q = 1
      rw [phi_mul, neg_add_cancel, phi_zero])

@[simp]
lemma transAlgEquiv_apply (Q : E.toAffine.Point) (z : Func E) :
    transAlgEquiv E Q z = phi E Q z := rfl

lemma transAlgEquiv_zero : transAlgEquiv E (0 : E.toAffine.Point) = 1 := by
  apply AlgEquiv.ext
  intro z
  change phi E (0 : E.toAffine.Point) z = z
  rw [phi_zero]
  rfl

lemma transAlgEquiv_add (P Q : E.toAffine.Point) :
    transAlgEquiv E (P + Q) = transAlgEquiv E P * transAlgEquiv E Q := by
  apply AlgEquiv.ext
  intro z
  change phi E (P + Q) z = phi E P (phi E Q z)
  rw [← phi_mul E P Q]
  rfl

lemma transAlgEquiv_genX {a b : L} (h : Nonsingular E a b) :
    transAlgEquiv E (Point.some a b h) (genX E) =
      addX (baseE E) (genX E) (algebraMap L (Func E) a)
        (slope (baseE E) (genX E) (algebraMap L (Func E) a) (genY E)
          (algebraMap L (Func E) b)) := by
  rw [transAlgEquiv_apply, phi_genX, transX_some]

lemma transAlgEquiv_genY {a b : L} (h : Nonsingular E a b) :
    transAlgEquiv E (Point.some a b h) (genY E) =
      addY (baseE E) (genX E) (algebraMap L (Func E) a) (genY E)
        (slope (baseE E) (genX E) (algebraMap L (Func E) a) (genY E)
          (algebraMap L (Func E) b)) := by
  rw [transAlgEquiv_apply, phi_genY, transY_some]

end Translation

theorem Translation (L : Type*) [Field L] [DecidableEq L] (E : WeierstrassCurve L) [E.IsElliptic] :
    ∃ τ : E.toAffine.Point → (Work.MotC2.Func E ≃ₐ[L] Work.MotC2.Func E),
      (τ 0 = 1) ∧
      (∀ P Q : E.toAffine.Point, τ (P + Q) = τ P * τ Q) ∧
      (∀ (a b : L) (h : WeierstrassCurve.Affine.Nonsingular E a b),
        (τ (WeierstrassCurve.Affine.Point.some a b h)) (Work.MotC2.genX E) =
          WeierstrassCurve.Affine.addX (Work.MotC2.baseE E) (Work.MotC2.genX E)
            (algebraMap L (Work.MotC2.Func E) a)
            (@WeierstrassCurve.Affine.slope (Work.MotC2.Func E) _ (Work.MotC2.baseE E)
              (Classical.decEq (Work.MotC2.Func E)) (Work.MotC2.genX E)
              (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
              (algebraMap L (Work.MotC2.Func E) b))) ∧
      (∀ (a b : L) (h : WeierstrassCurve.Affine.Nonsingular E a b),
        (τ (WeierstrassCurve.Affine.Point.some a b h)) (Work.MotC2.genY E) =
          WeierstrassCurve.Affine.addY (Work.MotC2.baseE E) (Work.MotC2.genX E)
            (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
            (@WeierstrassCurve.Affine.slope (Work.MotC2.Func E) _ (Work.MotC2.baseE E)
              (Classical.decEq (Work.MotC2.Func E)) (Work.MotC2.genX E)
              (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
              (algebraMap L (Work.MotC2.Func E) b))) := by
  refine ⟨fun Q => transAlgEquiv E Q, ?_, ?_, ?_, ?_⟩
  · exact transAlgEquiv_zero E
  · intro P Q
    exact transAlgEquiv_add E P Q
  · intro a b h
    exact transAlgEquiv_genX E h
  · intro a b h
    exact transAlgEquiv_genY E h

end Work.MotC2
