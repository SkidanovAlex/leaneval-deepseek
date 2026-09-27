import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Homotopy.Lifting

open scoped Multiplicative

namespace Commons.AlgebraicTopology.FundamentalGroup

open AddSubgroup

/-- The map `n ↦ n • a` as an additive group homomorphism `ℤ →+ zmultiples a`. -/
def zmultiplesAddMonoidHom (a : ℝ) : ℤ →+ AddSubgroup.zmultiples a where
  toFun n := ⟨n • a, AddSubgroup.zsmul_mem_zmultiples a n⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' m n := by
    apply Subtype.ext
    change (m + n) • a = m • a + n • a
    exact add_zsmul a m n

/-- For a nonzero real `a`, the additive group of integer multiples of `a` is
isomorphic to `ℤ`, via `n ↦ n • a`. -/
noncomputable def intEquivZmultiples (a : ℝ) (ha : a ≠ 0) : ℤ ≃+ AddSubgroup.zmultiples a := by
  refine AddEquiv.ofBijective (zmultiplesAddMonoidHom a) ?_
  constructor
  · intro n m h
    have hv := congrArg Subtype.val h
    change (n • a : ℝ) = m • a at hv
    rw [zsmul_eq_mul, zsmul_eq_mul] at hv
    have hcast : (n : ℝ) = (m : ℝ) := mul_right_cancel₀ ha hv
    exact_mod_cast hcast
  · intro y
    rcases y with ⟨x, hx⟩
    rcases (mem_zmultiples_iff.mp hx) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    exact Subtype.ext hn

/-- The fundamental group of the circle is the infinite cyclic group:
`π₁(S¹) ≅ ℤ`.  (Classical result; Mathlib gap.  Recommended route: the
covering `ℝ → Circle`, `t ↦ exp(2πi t)` / `AddCircle.homeomorphCircle`, with
path-lifting from `Mathlib.Topology.Covering`.) -/
theorem pi1_circle_eq_int :
    Nonempty (FundamentalGroup (Circle) (1 : Circle) ≃* Multiplicative ℤ) := by
  refine ⟨?_⟩
  /- `Circle.exp : ℝ → Circle` is the universal (simply connected) covering map
  of the circle with deck group `zmultiples (2 * π) ≅ ℤ`, so monodromy gives
  `π₁(S¹) ≅ ℤ`. -/
  let e₀ : (⇑Circle.exp) ⁻¹' ({(1 : Circle)} : Set Circle) := ⟨0, by simp⟩
  let F := (Circle.isAddQuotientCoveringMap_exp).fundamentalGroupEquiv e₀
  let hG : (Multiplicative (AddSubgroup.zmultiples (2 * Real.pi)))ᵐᵒᵖ ≃*
      Multiplicative ℤ :=
    (MulEquiv.op (AddEquiv.toMultiplicative
      (intEquivZmultiples (2 * Real.pi) (mul_ne_zero two_ne_zero Real.pi_ne_zero)).symm)).trans
      (MulOpposite.opMulEquiv (M := Multiplicative ℤ)).symm
  exact F.trans hG

end Commons.AlgebraicTopology.FundamentalGroup