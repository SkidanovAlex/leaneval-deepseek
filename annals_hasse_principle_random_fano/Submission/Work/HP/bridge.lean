import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.BridgeEval
import Submission.Work.HP.BridgeSol
import Submission.Work.HP.BridgeAdelic
import Submission.Work.HP.BridgeThm

/-!
# N02: the bridge from the challenge's projective objects to primitive coefficient vectors

The projective points of height at most `A` correspond two-to-one to the primitive integer
coefficient vectors of norm at most `A` (`BridgeThm`), solubility over `ℚ` corresponds to
`HasRatZero` (`hasSolutionsIn_rat`), adelic solubility is the predicate `AdelicSol`, and an
adelic solution induces a real solution and primitive zeros modulo every prime power
(`BridgeAdelic`).
-/

set_option autoImplicit false

noncomputable section

open Filter MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace Work.HP

open HassePrincipleRandomFano (HasSolutionsIn)

/-- The `2`-factors cancel in the ratios. -/
private lemma ratio_cancel (X Y : ℕ) :
    ((X : ℝ) / (Y : ℝ)) = ((2 * X : ℕ) : ℝ) / ((2 * Y : ℕ) : ℝ) := by
  push_cast
  by_cases hY : (Y : ℝ) = 0
  · rw [hY, mul_zero, div_zero, div_zero]
  · have h2Y : (2 : ℝ) * (Y : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hY
    rw [div_eq_div_iff hY h2Y]
    ring

/-- N02. Bridge from the challenge's projective objects to primitive coefficient vectors. -/
theorem bridge (d n : ℕ) (hd : 2 ≤ d) :
    (∀ A : ℝ, HassePrincipleRandomFano.ρ d n A = ratio d n A (HasRatZero d n)) ∧
    (∀ A : ℝ, ((HassePrincipleRandomFano.𝕍Loc d n ∩ HassePrincipleRandomFano.heightLE d n A).ncard : ℝ)
        / ((HassePrincipleRandomFano.heightLE d n A).ncard : ℝ) = ratio d n A (AdelicSol d n)) ∧
    (∀ a, HasRatZero d n a → AdelicSol d n a) ∧
    (∀ a, AdelicSol d n a → RealSol d n a ∧ ∀ p r : ℕ, p.Prime → PrimModZero d n a p r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A
    have hS := ncard_primSet_hasRatZero d n A
    have hT := ncard_primSet_true d n A
    rw [HassePrincipleRandomFano.ρ, ratio, primCount, primCount, hS, hT]
    exact ratio_cancel _ _
  · intro A
    have hset : (HassePrincipleRandomFano.𝕍Loc d n ∩
          HassePrincipleRandomFano.heightLE d n A)
        = {V : HassePrincipleRandomFano.𝕍 d n |
            V ∈ HassePrincipleRandomFano.heightLE d n A ∧
              HasSolutionsIn V.rep.1 HassePrincipleRandomFano.𝔸} := by
      ext V
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have hS := ncard_primSet_adelic d n A
    have hT := ncard_primSet_true d n A
    rw [hset, ratio, primCount, primCount, hS, hT]
    exact ratio_cancel _ _
  · intro a ha
    exact hasSolutionsIn_of_rat (formOf d n a) HassePrincipleRandomFano.𝔸
      ((hasSolutionsIn_rat d n a).mpr ha)
  · intro a ha
    refine ⟨adelic_real d n a ha, fun p r hp => ?_⟩
    haveI : Fact p.Prime := ⟨hp⟩
    exact padic_point_primModZero d n a p r (adelic_padic d n a p ha)

end Work.HP
