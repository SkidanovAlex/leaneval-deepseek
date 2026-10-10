import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.InfAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The invariant derivation preserves the chart-at-infinity coordinate ring

For an elliptic Weierstrass curve `E` over a field `N` and the derivation `D` of `N(E)` with
`D x = 2y + a₁x + a₃`, `D y = 3x² + 2a₂x + a₄ - a₁y`, the chart-at-infinity coordinate ring
`infCoordRing E = N[1/x, y/x²]` is preserved by `D`.

In the chart coordinates `u = 1/x`, `w = y/x²` one has

* `D u = -(2w + a₁u + a₃u²)`,
* `D w = -1 - 2a₂u - 3a₄u² - 4a₆u³ + a₁w + 2a₃uw`,

and since `infCoordRing E = N[u, w]` the statement follows by closure under sums, products and
scalars.  The second identity uses the chart relation `w² = u·(1 + a₂u + a₄u² + a₆u³ - a₁w - a₃uw)`,
i.e. `y²/x³ = 1 + a₂u + a₄u² + a₆u³ - a₁w - a₃uw`, which is isolated as `hY` below.
-/

namespace Work.MotV5

open WeierstrassCurve WeierstrassCurve.Affine

/-- **The invariant derivation preserves the chart-at-infinity coordinate ring `N[1/x, y/x²]`.** -/
theorem chart_deriv_aux {N : Type*} [Field N] [CharP N 5] (E : WeierstrassCurve N)
    [E.IsElliptic] (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hx : D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃)
    (hy : D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E) :
    ∀ r : Work.MotC2.Func E, r ∈ Work.MotC2.infCoordRing E →
      D r ∈ Work.MotC2.infCoordRing E := by
  have hx0 : Work.MotC2.genX E ≠ 0 := Work.MotC2.genX_ne_zero E
  have hu := Work.MotC2.InfAux.infU_mem_infCoordRing E
  have hw := Work.MotC2.InfAux.infW_mem_infCoordRing E
  -- ## the first chart coordinate `u = 1/x`
  have hu_mul : Work.MotC2.infU E * Work.MotC2.genX E = 1 := Work.MotC2.infU_mul_genX E
  have h1 : (Work.MotC2.infU E) ^ 2 * Work.MotC2.genY E = Work.MotC2.infW E := by
    rw [Work.MotC2.genY_eq_infW_mul]
    rw [show (Work.MotC2.infU E) ^ 2 *
          (Work.MotC2.infW E * (Work.MotC2.genX E) ^ 2) =
        Work.MotC2.infW E * (Work.MotC2.infU E * Work.MotC2.genX E) ^ 2 from by ring]
    rw [hu_mul]
    first | refl_ring1 | ring
  have h2 : (Work.MotC2.infU E) ^ 2 * Work.MotC2.genX E = Work.MotC2.infU E := by
    rw [show (Work.MotC2.infU E) ^ 2 * Work.MotC2.genX E =
        Work.MotC2.infU E * (Work.MotC2.infU E * Work.MotC2.genX E) from by ring]
    rw [hu_mul]
    first | refl_ring1 | ring
  have hX : (Work.MotC2.infU E) ^ 2 *
      (2 * Work.MotC2.genY E + algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃) =
      2 * Work.MotC2.infW E + algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infU E +
        algebraMap N (Work.MotC2.Func E) E.a₃ * (Work.MotC2.infU E) ^ 2 := by
    rw [show (Work.MotC2.infU E) ^ 2 *
          (2 * Work.MotC2.genY E + algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
            algebraMap N (Work.MotC2.Func E) E.a₃) =
        2 * ((Work.MotC2.infU E) ^ 2 * Work.MotC2.genY E) +
          algebraMap N (Work.MotC2.Func E) E.a₁ *
            ((Work.MotC2.infU E) ^ 2 * Work.MotC2.genX E) +
          algebraMap N (Work.MotC2.Func E) E.a₃ * (Work.MotC2.infU E) ^ 2 from by ring]
    rw [h1, h2]
  have hDu_eq : D (Work.MotC2.infU E) = -(2 * Work.MotC2.infW E +
      algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infU E +
      algebraMap N (Work.MotC2.Func E) E.a₃ * (Work.MotC2.infU E) ^ 2) := by
    calc D (Work.MotC2.infU E) =
          -(Work.MotC2.infU E) ^ 2 * D (Work.MotC2.genX E) := by
          rw [Work.MotC2.infU, Derivation.leibniz_inv, smul_eq_mul]
      _ = -(Work.MotC2.infU E) ^ 2 *
            (2 * Work.MotC2.genY E + algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
              algebraMap N (Work.MotC2.Func E) E.a₃) := by rw [hx]
      _ = -(2 * Work.MotC2.infW E + algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infU E +
            algebraMap N (Work.MotC2.Func E) E.a₃ * (Work.MotC2.infU E) ^ 2) := by
          rw [neg_mul, hX]
  have hDu : D (Work.MotC2.infU E) ∈ Work.MotC2.infCoordRing E := by
    rw [hDu_eq]
    have ha1 : algebraMap N (Work.MotC2.Func E) E.a₁ ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.algebraMap_mem _ E.a₁
    have ha3 : algebraMap N (Work.MotC2.Func E) E.a₃ ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.algebraMap_mem _ E.a₃
    have h2c : (2 : Work.MotC2.Func E) ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.natCast_mem _ 2
    exact Subalgebra.neg_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
      (Subalgebra.mul_mem _ h2c hw)
      (Subalgebra.mul_mem _ ha1 hu))
      (Subalgebra.mul_mem _ ha3 (Subalgebra.pow_mem _ hu 2)))
  -- ## the second chart coordinate `w = y/x²`
  have hw_rel : Work.MotC2.infU E *
      (1 + algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.infU E +
        algebraMap N (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 2 +
        algebraMap N (Work.MotC2.Func E) E.a₆ * (Work.MotC2.infU E) ^ 3 -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infW E -
        algebraMap N (Work.MotC2.Func E) E.a₃ * Work.MotC2.infU E * Work.MotC2.infW E) =
      (Work.MotC2.infW E) ^ 2 := by
    calc Work.MotC2.infU E *
          (1 + algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.infU E +
            algebraMap N (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 2 +
            algebraMap N (Work.MotC2.Func E) E.a₆ * (Work.MotC2.infU E) ^ 3 -
            algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infW E -
            algebraMap N (Work.MotC2.Func E) E.a₃ * Work.MotC2.infU E * Work.MotC2.infW E)
        = Work.MotC2.infU E + algebraMap N (Work.MotC2.Func E) E.a₂ * (Work.MotC2.infU E) ^ 2 +
            algebraMap N (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 3 +
            algebraMap N (Work.MotC2.Func E) E.a₆ * (Work.MotC2.infU E) ^ 4 -
            algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infU E * Work.MotC2.infW E -
            algebraMap N (Work.MotC2.Func E) E.a₃ * (Work.MotC2.infU E) ^ 2 *
              Work.MotC2.infW E := by ring
      _ = ((Work.MotC2.infW E) ^ 2 + algebraMap N (Work.MotC2.Func E) E.a₁ *
              Work.MotC2.infU E * Work.MotC2.infW E +
            algebraMap N (Work.MotC2.Func E) E.a₃ * (Work.MotC2.infU E) ^ 2 *
              Work.MotC2.infW E) -
            algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infU E * Work.MotC2.infW E -
            algebraMap N (Work.MotC2.Func E) E.a₃ * (Work.MotC2.infU E) ^ 2 *
              Work.MotC2.infW E := by rw [Work.MotC2.infW_sq_relation E]
      _ = (Work.MotC2.infW E) ^ 2 := by ring
  have hY : (Work.MotC2.infW E) ^ 2 * (Work.MotC2.infU E)⁻¹ =
      1 + algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.infU E +
        algebraMap N (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 2 +
        algebraMap N (Work.MotC2.Func E) E.a₆ * (Work.MotC2.infU E) ^ 3 -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infW E -
        algebraMap N (Work.MotC2.Func E) E.a₃ * Work.MotC2.infU E * Work.MotC2.infW E := by
    have hu0 : Work.MotC2.infU E ≠ 0 := by
      rw [Work.MotC2.infU]
      exact inv_ne_zero hx0
    calc (Work.MotC2.infW E) ^ 2 * (Work.MotC2.infU E)⁻¹
        = (Work.MotC2.infU E *
            (1 + algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.infU E +
              algebraMap N (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 2 +
              algebraMap N (Work.MotC2.Func E) E.a₆ * (Work.MotC2.infU E) ^ 3 -
              algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infW E -
              algebraMap N (Work.MotC2.Func E) E.a₃ * Work.MotC2.infU E *
                Work.MotC2.infW E)) * (Work.MotC2.infU E)⁻¹ := by rw [hw_rel]
      _ = (1 + algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.infU E +
            algebraMap N (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 2 +
            algebraMap N (Work.MotC2.Func E) E.a₆ * (Work.MotC2.infU E) ^ 3 -
            algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infW E -
            algebraMap N (Work.MotC2.Func E) E.a₃ * Work.MotC2.infU E * Work.MotC2.infW E) *
          (Work.MotC2.infU E * (Work.MotC2.infU E)⁻¹) := by ring
      _ = 1 + algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.infU E +
            algebraMap N (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 2 +
            algebraMap N (Work.MotC2.Func E) E.a₆ * (Work.MotC2.infU E) ^ 3 -
            algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infW E -
            algebraMap N (Work.MotC2.Func E) E.a₃ * Work.MotC2.infU E * Work.MotC2.infW E := by
          rw [mul_inv_cancel₀ hu0, mul_one]
  have hDx2 : D ((Work.MotC2.genX E) ^ 2) =
      2 * Work.MotC2.genX E * D (Work.MotC2.genX E) := by
    rw [Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one]
    first | refl_ring1 | ring
  have hstep : D (Work.MotC2.infW E) =
      3 + 2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.infU E +
        algebraMap N (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 2 -
        3 * algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infW E -
        4 * ((Work.MotC2.infW E) ^ 2 * (Work.MotC2.infU E)⁻¹) -
        2 * algebraMap N (Work.MotC2.Func E) E.a₃ * Work.MotC2.infU E * Work.MotC2.infW E := by
    rw [Work.MotC2.infW, Derivation.leibniz_div, hDx2, hx, hy, Work.MotC2.infU]
    simp only [smul_eq_mul]
    field_simp
    first | refl_ring1 | ring
  have hDw_eq : D (Work.MotC2.infW E) = -((1 : Work.MotC2.Func E) +
      2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.infU E +
      3 * algebraMap N (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 2 +
      4 * algebraMap N (Work.MotC2.Func E) E.a₆ * (Work.MotC2.infU E) ^ 3 -
      algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infW E -
      2 * algebraMap N (Work.MotC2.Func E) E.a₃ * Work.MotC2.infU E * Work.MotC2.infW E) := by
    rw [hstep, hY]
    first | refl_ring1 | ring
  have hDw : D (Work.MotC2.infW E) ∈ Work.MotC2.infCoordRing E := by
    rw [hDw_eq]
    have ha1 : algebraMap N (Work.MotC2.Func E) E.a₁ ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.algebraMap_mem _ E.a₁
    have ha2 : algebraMap N (Work.MotC2.Func E) E.a₂ ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.algebraMap_mem _ E.a₂
    have ha3 : algebraMap N (Work.MotC2.Func E) E.a₃ ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.algebraMap_mem _ E.a₃
    have ha4 : algebraMap N (Work.MotC2.Func E) E.a₄ ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.algebraMap_mem _ E.a₄
    have ha6 : algebraMap N (Work.MotC2.Func E) E.a₆ ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.algebraMap_mem _ E.a₆
    have h2c : (2 : Work.MotC2.Func E) ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.natCast_mem _ 2
    have h3c : (3 : Work.MotC2.Func E) ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.natCast_mem _ 3
    have h4c : (4 : Work.MotC2.Func E) ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.natCast_mem _ 4
    have h1c : (1 : Work.MotC2.Func E) ∈ Work.MotC2.infCoordRing E := Subalgebra.one_mem _
    have t1 : 2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.infU E ∈
        Work.MotC2.infCoordRing E := Subalgebra.mul_mem _ (Subalgebra.mul_mem _ h2c ha2) hu
    have t2 : 3 * algebraMap N (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 2 ∈
        Work.MotC2.infCoordRing E :=
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ h3c ha4) (Subalgebra.pow_mem _ hu 2)
    have t3 : 4 * algebraMap N (Work.MotC2.Func E) E.a₆ * (Work.MotC2.infU E) ^ 3 ∈
        Work.MotC2.infCoordRing E :=
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ h4c ha6) (Subalgebra.pow_mem _ hu 3)
    have t4 : algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.infW E ∈
        Work.MotC2.infCoordRing E := Subalgebra.mul_mem _ ha1 hw
    have t5 : 2 * algebraMap N (Work.MotC2.Func E) E.a₃ * Work.MotC2.infU E *
        Work.MotC2.infW E ∈ Work.MotC2.infCoordRing E :=
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ h2c ha3) hu) hw
    exact Subalgebra.neg_mem _ (Subalgebra.sub_mem _
      (Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _ h1c t1) t2) t3) t4) t5)
  -- ## closure under the algebra operations
  have key : ∀ x ∈ Algebra.adjoin N
      ({Work.MotC2.infU E, Work.MotC2.infW E} : Set (Work.MotC2.Func E)),
      D x ∈ Work.MotC2.infCoordRing E := by
    intro x hx'
    induction hx' using Algebra.adjoin_induction with
    | mem y hy' =>
        rcases hy' with h | h
        · rw [h]; exact hDu
        · rw [h]; exact hDw
    | algebraMap c =>
        rw [Derivation.map_algebraMap]
        exact Subalgebra.zero_mem _
    | add x y hx hy ihx ihy =>
        rw [map_add]
        exact Subalgebra.add_mem _ ihx ihy
    | mul x y hx hy ihx ihy =>
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx ihy) (Subalgebra.mul_mem _ hy ihx)
  intro r hr
  exact key r hr

end Work.MotV5
