import Mathlib
import Submission.Work.MotC.C6.Defs
import Submission.Work.MotC.C6.genX_genY_nonsingular
import Submission.Work.MotC.constantsOnly_all

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The image of the generic point under a coefficient map is constant

Let `L` be a field, `W⁄L` a Weierstrass curve with `Δ ≠ 0` (so `W` is not singular, and its
function field `K = L(W)` is the function field of an elliptic curve), and let
`Ψ : K →ₐ[L] RatFunc N` be an `L`-algebra homomorphism into the rational function field of a field
`N` with `L → N`.

Then both coordinates of the generic point of `W` (`Work.MotC.C6.genX W`, `Work.MotC.C6.genY W`)
are sent by `Ψ` into the constants `N ⊆ N(t) = RatFunc N`.

The point is that `(Ψ (genX W), Ψ (genY W))` is a solution of the Weierstrass equation of
`W` base changed to `N`, in the field `RatFunc N = N(t)`; and the one-variable Weierstrass
rigidity `Work.MotC.exists_algebraMap_of_weierstrass_ratFunc_all` (proved in the chapter as the
unconditional form of `E(N(t)) = E(N)`, in every characteristic) says that every such solution has
constant coordinates.
-/

namespace Work.MotC

open WeierstrassCurve WeierstrassCurve.Affine

theorem exists_algebraMap_genXY_of_algHom_ratFunc {L : Type} [Field L] [DecidableEq L]
    (W : WeierstrassCurve L) (hΔ : W.Δ ≠ 0) (N : Type) [Field N] [Algebra L N]
    (Ψ : WeierstrassCurve.Affine.FunctionField W →ₐ[L] RatFunc N) :
    (∃ n : N, Ψ (Work.MotC.C6.genX W) = algebraMap N (RatFunc N) n) ∧
      (∃ n : N, Ψ (Work.MotC.C6.genY W) = algebraMap N (RatFunc N) n) := by
  -- The generic point of `W` is nonsingular, hence satisfies the Weierstrass equation over the
  -- function field `K = L(W)`.
  have hns := Work.MotC.C6.genX_genY_nonsingular W hΔ
  have hΔK : (W.baseChange (WeierstrassCurve.Affine.FunctionField W)).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact fun h => hΔ (RingHom.injective
      (algebraMap L (WeierstrassCurve.Affine.FunctionField W)) (by rw [h, map_zero]))
  have hEq : WeierstrassCurve.Affine.Equation
      (W.baseChange (WeierstrassCurve.Affine.FunctionField W))
      (Work.MotC.C6.genX W) (Work.MotC.C6.genY W) :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔK).mpr hns
  rw [WeierstrassCurve.Affine.equation_iff,
    WeierstrassCurve.Affine.baseChange_a₁, WeierstrassCurve.Affine.baseChange_a₂,
    WeierstrassCurve.Affine.baseChange_a₃, WeierstrassCurve.Affine.baseChange_a₄,
    WeierstrassCurve.Affine.baseChange_a₆] at hEq
  -- Push the equation forward along `Ψ`.
  have hpush : (Ψ (Work.MotC.C6.genY W)) ^ 2
        + algebraMap L (RatFunc N) W.a₁ * Ψ (Work.MotC.C6.genX W) * Ψ (Work.MotC.C6.genY W)
        + algebraMap L (RatFunc N) W.a₃ * Ψ (Work.MotC.C6.genY W)
      = (Ψ (Work.MotC.C6.genX W)) ^ 3
        + algebraMap L (RatFunc N) W.a₂ * (Ψ (Work.MotC.C6.genX W)) ^ 2
        + algebraMap L (RatFunc N) W.a₄ * Ψ (Work.MotC.C6.genX W)
        + algebraMap L (RatFunc N) W.a₆ := by
    have h := congrArg (fun z => Ψ z) hEq
    simpa only [map_add, map_mul, map_pow, AlgHom.commutes] using h
  -- Nonsingularity of `W` base changed to `N`.
  have hΔN : (W.baseChange N).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact fun h => hΔ ((algebraMap L N).injective (by rw [h, map_zero]))
  -- One-variable Weierstrass rigidity, applied to `E := W ⁄ N` over the field `N`.
  refine Work.MotC.exists_algebraMap_of_weierstrass_ratFunc_all (W.baseChange N) hΔN ?_
  simpa only [WeierstrassCurve.Affine.baseChange_a₁, WeierstrassCurve.Affine.baseChange_a₂,
    WeierstrassCurve.Affine.baseChange_a₃, WeierstrassCurve.Affine.baseChange_a₄,
    WeierstrassCurve.Affine.baseChange_a₆, IsScalarTower.algebraMap_apply L N (RatFunc N)]
    using hpush

end Work.MotC
