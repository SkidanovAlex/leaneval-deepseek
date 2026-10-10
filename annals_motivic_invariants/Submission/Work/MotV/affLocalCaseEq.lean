import Mathlib
import Submission.Work.MotC2.AffPlaceSetup
import Submission.Work.MotC2.AffPlaceMaxIdealPrincipal
import Submission.Work.MotV.affLocalDerivUnit
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotV

theorem affLocalCaseEq {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (a b : N) (h : WeierstrassCurve.Affine.Nonsingular E a b)
    (hw : 2 * b + E.a₁ * a + E.a₃ = 0) :
    Irreducible (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
        (WeierstrassCurve.Affine.CoordinateRing.YClass E (Polynomial.C b))) ∧
    (∃ u : (↥(Work.MotC2.affPlaceAt E a b))ˣ,
        algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
            (WeierstrassCurve.Affine.CoordinateRing.XClass E a)
          = (u : ↥(Work.MotC2.affPlaceAt E a b)) *
            (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
              (WeierstrassCurve.Affine.CoordinateRing.YClass E (Polynomial.C b)))^2) ∧
    IsUnit (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
        (3 * (Work.MotC2.coordX E)^2 + algebraMap N (Work.MotC2.Coord E) (2 * E.a₂) * Work.MotC2.coordX E
          + algebraMap N (Work.MotC2.Coord E) E.a₄
          - algebraMap N (Work.MotC2.Coord E) E.a₁ * Work.MotC2.coordY E)) := by
  haveI hns : Work.MotC2.IsNonsingularPoint E a b := ⟨h⟩
  -- Nonsingularity, rewritten in terms of the partial derivatives; the hypothesis `hw` kills
  -- the `y`-partial, so the `x`-partial must be nonzero.
  have hns' : E.a₁ * b - (3 * a ^ 2 + 2 * E.a₂ * a + E.a₄) ≠ 0 ∨
      2 * b + E.a₁ * a + E.a₃ ≠ 0 := by
    have hh := h.2
    rwa [WeierstrassCurve.Affine.evalEval_polynomialX,
      WeierstrassCurve.Affine.evalEval_polynomialY] at hh
  have hx' : 3 * a ^ 2 + 2 * E.a₂ * a + E.a₄ - E.a₁ * b ≠ 0 := by
    rcases hns' with hx | hy
    · intro h0
      exact hx (by linear_combination -h0)
    · exact absurd hw hy
  -- Shorthand for the two coordinate classes and the structure constants in the local ring.
  set X' : ↥(Work.MotC2.affPlaceAt E a b) :=
    algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
      (WeierstrassCurve.Affine.CoordinateRing.XClass E a)
  set Y' : ↥(Work.MotC2.affPlaceAt E a b) :=
    algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
      (WeierstrassCurve.Affine.CoordinateRing.YClass E (Polynomial.C b))
  set α : ↥(Work.MotC2.affPlaceAt E a b) := algebraMap N ↥(Work.MotC2.affPlaceAt E a b) a
  set β : ↥(Work.MotC2.affPlaceAt E a b) := algebraMap N ↥(Work.MotC2.affPlaceAt E a b) b
  set A₁ : ↥(Work.MotC2.affPlaceAt E a b) := algebraMap N ↥(Work.MotC2.affPlaceAt E a b) E.a₁
  set A₂ : ↥(Work.MotC2.affPlaceAt E a b) := algebraMap N ↥(Work.MotC2.affPlaceAt E a b) E.a₂
  set A₃ : ↥(Work.MotC2.affPlaceAt E a b) := algebraMap N ↥(Work.MotC2.affPlaceAt E a b) E.a₃
  set A₄ : ↥(Work.MotC2.affPlaceAt E a b) := algebraMap N ↥(Work.MotC2.affPlaceAt E a b) E.a₄
  set A₆ : ↥(Work.MotC2.affPlaceAt E a b) := algebraMap N ↥(Work.MotC2.affPlaceAt E a b) E.a₆
  set V : ↥(Work.MotC2.affPlaceAt E a b) :=
    (3 * α + A₂) * X' + X' ^ 2 + (3 * α ^ 2 + 2 * A₂ * α + A₄ - A₁ * β)
  have hX'eq : X' = algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
      (Work.MotC2.coordX E) - α := Work.MotC2.affPlaceAt_algebraMap_XClass E a b
  have hY'eq : Y' = algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
      (Work.MotC2.coordY E) - β := Work.MotC2.affPlaceAt_algebraMap_YClass E a b
  -- Taylor expansion of the Weierstrass relation around the point.
  have htay : Y' * (Y' + A₁ * X' + (2 * β + A₁ * α + A₃)) = X' * V := by
    have h1 := Work.MotC2.affPlaceAt_coordY_sq_relation E a b
    have h2 := Work.MotC2.affPlaceAt_equation E a b
    have ht := Work.MotC2.taylor_identity
      (x := algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b) (Work.MotC2.coordX E))
      (y := algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b) (Work.MotC2.coordY E))
      (a := α) (b := β) (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) (A₄ := A₄) (A₆ := A₆) h1 h2
    rw [← hX'eq, ← hY'eq] at ht
    exact ht
  -- the `y`-partial vanishes at `(a, b)`.
  have hz : 2 * β + A₁ * α + A₃ = 0 := by
    have hWy : algebraMap N ↥(Work.MotC2.affPlaceAt E a b) (2 * b + E.a₁ * a + E.a₃) =
        2 * β + A₁ * α + A₃ := by
      simp only [map_add, map_mul, map_ofNat]
      rfl
    rw [← hWy, hw, map_zero]
  have htay' : Y' * (Y' + A₁ * X') = X' * V := by
    rw [hz, add_zero] at htay
    exact htay
  have hX'mem : X' ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E a b) :=
    Work.MotC2.affPlaceAt_XClass_mem_maximalIdeal E a b
  have hY'mem : Y' ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E a b) :=
    Work.MotC2.affPlaceAt_YClass_mem_maximalIdeal E a b
  -- the coefficient of `x - a` on the right-hand side is a unit.
  have hVunit : IsUnit V := by
    have hmem : (3 * α + A₂) * X' + X' ^ 2 ∈
        IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E a b) :=
      add_mem (Ideal.mul_mem_left _ _ hX'mem)
        (Ideal.pow_mem_of_mem _ hX'mem 2 (by norm_num))
    have hWx : algebraMap N ↥(Work.MotC2.affPlaceAt E a b)
          (3 * a ^ 2 + 2 * E.a₂ * a + E.a₄ - E.a₁ * b) =
        3 * α ^ 2 + 2 * A₂ * α + A₄ - A₁ * β := by
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
      rfl
    have h3 := Work.MotC2.isUnit_add_mem_maximalIdeal
      (Work.MotC2.isUnit_algebraMap_affPlaceAt_of_ne_zero E a b hx') hmem
    rw [hWx, add_comm] at h3
    exact h3
  have hWunit : IsUnit (V - A₁ * Y') := by
    have hmem : A₁ * Y' ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E a b) :=
      Ideal.mul_mem_left _ _ hY'mem
    have h := Work.MotC2.isUnit_add_mem_maximalIdeal hVunit (neg_mem hmem)
    simpa only [sub_eq_add_neg] using h
  -- with the `y`-partial gone, the Taylor expansion collapses to `x - a = u * (y - b)^2`.
  have hrel : X' * (V - A₁ * Y') = Y' ^ 2 := by
    calc X' * (V - A₁ * Y') = X' * V - X' * (A₁ * Y') := by ring
      _ = Y' * (Y' + A₁ * X') - X' * (A₁ * Y') := by rw [← htay']
      _ = Y' ^ 2 := by ring
  have hXu : ∃ u : (↥(Work.MotC2.affPlaceAt E a b))ˣ,
      X' = (u : ↥(Work.MotC2.affPlaceAt E a b)) * Y' ^ 2 := by
    obtain ⟨w, hw_eq⟩ := hWunit
    rw [← hw_eq] at hrel
    refine ⟨w⁻¹, ?_⟩
    have h2 : X' = Y' ^ 2 * (((w⁻¹ : (↥(Work.MotC2.affPlaceAt E a b))ˣ) :
        ↥(Work.MotC2.affPlaceAt E a b))) := by
      calc X' = X' * 1 := (mul_one X').symm
        _ = X' * ((w : ↥(Work.MotC2.affPlaceAt E a b)) *
              ((w⁻¹ : (↥(Work.MotC2.affPlaceAt E a b))ˣ) : ↥(Work.MotC2.affPlaceAt E a b))) := by
              rw [Units.mul_inv]
        _ = (X' * (w : ↥(Work.MotC2.affPlaceAt E a b))) *
              ((w⁻¹ : (↥(Work.MotC2.affPlaceAt E a b))ˣ) : ↥(Work.MotC2.affPlaceAt E a b)) := by
              first | refl_ring1 | ring
        _ = Y' ^ 2 * (((w⁻¹ : (↥(Work.MotC2.affPlaceAt E a b))ˣ) :
              ↥(Work.MotC2.affPlaceAt E a b))) := by rw [hrel]
    rw [h2, mul_comm]
  have hX'ne : X' ≠ 0 := by
    intro h0
    have h0' : algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
        (WeierstrassCurve.Affine.CoordinateRing.XClass E a) = 0 := h0
    have h1 : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E)
        (WeierstrassCurve.Affine.CoordinateRing.XClass E a) = 0 := by
      rw [← Work.MotC2.affPlaceAt_algebraMap_val E a b
        (WeierstrassCurve.Affine.CoordinateRing.XClass E a), h0']
      rfl
    exact WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero (W' := E) a
      (IsFractionRing.injective (Work.MotC2.Coord E) (Work.MotC2.Func E)
        (by simpa using h1))
  have hspan : Ideal.span ({X', Y'} : Set ↥(Work.MotC2.affPlaceAt E a b)) =
      Ideal.span ({Y'} : Set ↥(Work.MotC2.affPlaceAt E a b)) := by
    rw [show ({X', Y'} : Set ↥(Work.MotC2.affPlaceAt E a b)) = insert X' {Y'} from rfl,
      Ideal.span_insert, sup_eq_right]
    rw [Ideal.span_singleton_le_span_singleton]
    obtain ⟨u, hu⟩ := hXu
    exact ⟨(u : ↥(Work.MotC2.affPlaceAt E a b)) * Y', by rw [hu, pow_two]; ring⟩
  have hmaxY : (Ideal.span ({Y'} : Set ↥(Work.MotC2.affPlaceAt E a b))).IsMaximal := by
    have h := IsLocalRing.maximalIdeal.isMaximal (↥(Work.MotC2.affPlaceAt E a b))
    rw [Work.MotC2.affPlaceAt_maximalIdeal_eq, hspan] at h
    exact h
  have hY'ne : Y' ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hXu
    have hX0 : X' = 0 := by
      rw [hu, h0]
      first | refl_ring1 | ring
    exact hX'ne hX0
  refine ⟨Ideal.irreducible_of_isMaximal_span_singleton hY'ne hmaxY, hXu, ?_⟩
  exact Work.MotV.affLocalDerivUnit E a b h hw

end Work.MotV
