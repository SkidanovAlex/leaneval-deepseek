import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotT.coeffAlgEquiv
import Submission.Work.MotT.exists_twistAut

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- The coefficient action of a `𝕜`-linear automorphism `τ` of `Kb 𝕜` on the function field
`Om D = K̄(E)`: it acts on the constants `K̄` by `τ`, fixes the generic point `genX, genY` (the
coefficients of the Weierstrass equation of `D.E` lie in `𝕜`), hence fixes every Klein coordinate
`κ_i` (a `𝕜`-linear combination of `1, x, y, x², xy`), and therefore acts on the twisted
coordinates by `twCoord D h i = w^{-i} κ_i/κ_0 ↦ (g w)^{-i} κ_i/κ_0`.

The existence and the `K̄`-action are `Work.MotT.coeffAlgEquiv 𝕜 D.E (Kb 𝕜) τ` (module
`Submission.Work.MotT.coeffAlgEquiv`, which also gives `g genX = genX`, `g genY = genY`); the
Klein computations are the `𝕜`-linear analogues of `Work.MotV5.coeffAction_kleinBas`,
`coeffAction_kleinCoord`, `coeffAction_kleinRatio`, `coeffAction_twCoordK` in
`Submission/Work/MotT/exists_twistAut.lean`.  No `D.Good` is needed. -/
theorem coeffAutSemilinear {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (τ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜) :
    ∃ g : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D,
      (∀ y : Work.MotV.Kb 𝕜, g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) y)
          = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (τ y)) ∧
      (∀ i : Fin 5, g (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
            / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
          = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
            / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) ∧
      (∀ (h : RatFunc 𝕜) (i : Fin 5), g (Work.MotV.twCoord D h i)
          = (g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV.root5 h)))⁻¹ ^ (i : ℕ)
            * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
              / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)) := by
  obtain ⟨g, hgconst, hgX, hgY⟩ := Work.MotT.coeffAlgEquiv 𝕜 D.E (Work.MotV.Kb 𝕜) τ
  -- The coefficient action fixes the Klein basis `1, x, y, x², xy`, since it fixes `x` and `y`.
  have hbas : ∀ m : Fin 5, g (Work.MotV.kleinBas D (Work.MotV.Kb 𝕜) m)
      = Work.MotV.kleinBas D (Work.MotV.Kb 𝕜) m := by
    intro m
    fin_cases m <;> simp [Work.MotV.kleinBas, hgX, hgY]
  -- It therefore fixes the Klein coordinates `κ_i` (a `𝕜`-linear combination of the basis).
  have hcoord : ∀ i : Fin 5, g (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i := by
    intro i
    simp only [Work.MotV.kleinCoord_eq_sum, map_sum, map_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    · rw [hgconst, AlgEquiv.commutes τ (D.coord i m)]
    · exact hbas m
  refine ⟨g, hgconst, ?_, ?_⟩
  · -- the Klein ratios are fixed
    intro i
    rw [map_div₀, hcoord i, hcoord 0]
  · -- the twisted coordinates: `twCoord D h i = w^{-i}·κ_i/κ_0`
    intro h i
    rw [Work.MotV.twCoord, map_mul, map_pow, map_inv₀, map_div₀, hcoord i, hcoord 0]

end Work.MotV
