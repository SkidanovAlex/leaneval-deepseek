import Mathlib
import Submission.Work.MotC2.AffPlaceSetup
import Submission.Work.MotC2.AffPlaceMaxIdealPrincipal

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

theorem affLocalDerivUnit {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (a b : N) (h : WeierstrassCurve.Affine.Nonsingular E a b)
    (hw : 2 * b + E.a₁ * a + E.a₃ = 0) :
    IsUnit (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
        (3 * (Work.MotC2.coordX E)^2 + algebraMap N (Work.MotC2.Coord E) (2 * E.a₂) * Work.MotC2.coordX E
          + algebraMap N (Work.MotC2.Coord E) E.a₄
          - algebraMap N (Work.MotC2.Coord E) E.a₁ * Work.MotC2.coordY E)) := by
  -- `(a, b)` is a nonsingular point at which the `y`-derivative `2b + a₁a + a₃` vanishes, so the
  -- `x`-derivative `3a² + 2a₂a + a₄ - a₁b` does not vanish.
  have : Work.MotC2.IsNonsingularPoint E a b := ⟨h⟩
  have hns : E.a₁ * b - (3 * a ^ 2 + 2 * E.a₂ * a + E.a₄) ≠ 0 ∨
      2 * b + E.a₁ * a + E.a₃ ≠ 0 := by
    have hh := h.2
    rwa [WeierstrassCurve.Affine.evalEval_polynomialX,
      WeierstrassCurve.Affine.evalEval_polynomialY] at hh
  have hc : 3 * a ^ 2 + 2 * E.a₂ * a + E.a₄ - E.a₁ * b ≠ 0 := by
    rcases hns with hx | hy
    · intro h0
      exact hx (by linear_combination -h0)
    · exact absurd hw hy
  -- The element of the coordinate ring is the constant `c` plus an element of the maximal ideal
  -- `⟨x - a, y - b⟩` of the local ring at `(a, b)`.
  set X' : ↥(Work.MotC2.affPlaceAt E a b) := algebraMap (Work.MotC2.Coord E)
    ↥(Work.MotC2.affPlaceAt E a b) (WeierstrassCurve.Affine.CoordinateRing.XClass E a) with hX'def
  set Y' : ↥(Work.MotC2.affPlaceAt E a b) := algebraMap (Work.MotC2.Coord E)
    ↥(Work.MotC2.affPlaceAt E a b) (WeierstrassCurve.Affine.CoordinateRing.YClass E (Polynomial.C b))
    with hY'def
  set T : ↥(Work.MotC2.affPlaceAt E a b) :=
    (3 : ↥(Work.MotC2.affPlaceAt E a b)) *
      (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b) (Work.MotC2.coordX E)
        + algebraMap N ↥(Work.MotC2.affPlaceAt E a b) a)
    + 2 * algebraMap N ↥(Work.MotC2.affPlaceAt E a b) E.a₂ with hTdef
  have hdecomp :
      algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b)
        (3 * (Work.MotC2.coordX E)^2 + algebraMap N (Work.MotC2.Coord E) (2 * E.a₂) * Work.MotC2.coordX E
          + algebraMap N (Work.MotC2.Coord E) E.a₄
          - algebraMap N (Work.MotC2.Coord E) E.a₁ * Work.MotC2.coordY E)
      = algebraMap N ↥(Work.MotC2.affPlaceAt E a b) (3 * a ^ 2 + 2 * E.a₂ * a + E.a₄ - E.a₁ * b)
        + (X' * T - algebraMap N ↥(Work.MotC2.affPlaceAt E a b) E.a₁ * Y') := by
    rw [hX'def, hY'def, hTdef]
    rw [Work.MotC2.affPlaceAt_algebraMap_XClass, Work.MotC2.affPlaceAt_algebraMap_YClass]
    simp only [map_add, map_sub, map_mul, map_pow, Work.MotC2.affPlaceAt_algebraMap_algebraMap,
      map_ofNat]
    ring_nf
  have hmem : X' * T - algebraMap N ↥(Work.MotC2.affPlaceAt E a b) E.a₁ * Y' ∈
      IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E a b) := by
    have hX : X' ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E a b) :=
      Work.MotC2.affPlaceAt_XClass_mem_maximalIdeal E a b
    have hY : Y' ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E a b) :=
      Work.MotC2.affPlaceAt_YClass_mem_maximalIdeal E a b
    exact sub_mem (Ideal.mul_mem_right T _ hX)
      (Ideal.mul_mem_left _ (algebraMap N ↥(Work.MotC2.affPlaceAt E a b) E.a₁) hY)
  -- A nonzero scalar of the residue field is a unit, and a unit plus a maximal-ideal element is a
  -- unit.
  have hu : IsUnit (algebraMap N ↥(Work.MotC2.affPlaceAt E a b)
      (3 * a ^ 2 + 2 * E.a₂ * a + E.a₄ - E.a₁ * b)) :=
    Work.MotC2.isUnit_algebraMap_affPlaceAt_of_ne_zero E a b hc
  have hmain : IsUnit (algebraMap N ↥(Work.MotC2.affPlaceAt E a b)
      (3 * a ^ 2 + 2 * E.a₂ * a + E.a₄ - E.a₁ * b)
      + (X' * T - algebraMap N ↥(Work.MotC2.affPlaceAt E a b) E.a₁ * Y')) :=
    Work.MotC2.isUnit_add_mem_maximalIdeal hu hmem
  rw [hdecomp]
  exact hmain

end Work.MotV
