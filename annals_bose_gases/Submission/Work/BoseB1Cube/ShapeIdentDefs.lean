import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Submission.Work.ConvQuadDev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.ShapeIdentDefs` — the vocabulary of the shape identity

Definitions and elementary rewriting lemmas used by the proof of
`Work.BoseB1Cube.shapeIdentity`, the identity

    ∫ ‖∇(γ·χ)‖² = ∫ χ²‖∇γ‖² − (47/48)∫ γ²‖∇χ‖² + 144π²∫ γ²χ²      (`χ = chiSmall48`)

for an arbitrary Lipschitz `γ`.  The identity is proved by
* expanding `‖∇f z‖²` as the sum of the squares of the coordinate derivatives (`norm_sq_eq_sum_e3`),
* an integration by parts in each coordinate direction (the Lipschitz IBP
  `LipschitzWith.integral_lineDeriv_mul_eq`), and
* the pointwise "cosine-power" identity `(47/48)‖∇χ‖² − χ·Δχ = 144π²χ²`
  (`Work.BoseB1Cube.chiSmallBase_pde`).

Nothing here is specific to the bump; `e3`, `secondDir` and the two norm lemmas are the common
vocabulary.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The `k`-th standard unit vector of `ℝ³` (`= EuclideanSpace.single k 1`). -/
noncomputable def e3 (k : Fin 3) : E3 := EuclideanSpace.single k (1 : ℝ)

lemma e3_eq_basisFun (k : Fin 3) : e3 k = EuclideanSpace.basisFun (Fin 3) ℝ k := by
  rw [EuclideanSpace.basisFun_apply, e3]

@[simp] lemma e3_ofLp (k : Fin 3) : (e3 k).ofLp = Pi.single k (1 : ℝ) := rfl

@[simp] lemma e3_ofLp_apply (k j : Fin 3) : (e3 k).ofLp j = if j = k then 1 else 0 := by
  rw [e3_ofLp]
  simp [Pi.single_apply]

/-- **The norm of a linear functional is the square sum of its values on the standard basis.** -/
lemma norm_sq_eq_sum_e3 (L : E3 →L[ℝ] ℝ) : ‖L‖ ^ 2 = ∑ k : Fin 3, (L (e3 k)) ^ 2 := by
  rw [OrthonormalBasis.norm_dual (EuclideanSpace.basisFun (Fin 3) ℝ) L]
  exact Finset.sum_congr rfl fun k _ => by rw [e3_eq_basisFun]

/-- **The squared operator norm of the Fréchet derivative is the sum of the squares of the
coordinate derivatives.** -/
lemma norm_fderiv_sq_eq_sum (f : E3 → ℝ) (z : E3) :
    ‖fderiv ℝ f z‖ ^ 2 = ∑ k : Fin 3, (fderiv ℝ f z (e3 k)) ^ 2 :=
  norm_sq_eq_sum_e3 (fderiv ℝ f z)

/-- The second coordinate derivative `∂_k ∂_k f`. -/
noncomputable def secondDir (f : E3 → ℝ) (k : Fin 3) (z : E3) : ℝ :=
  (fderiv ℝ (fun w : E3 => fderiv ℝ f w (e3 k)) z) (e3 k)

/-- The "coordinate Laplacian" `∑_k ∂_k² f`. -/
noncomputable def coordLaplacian (f : E3 → ℝ) (z : E3) : ℝ :=
  ∑ k : Fin 3, secondDir f k z

end Work.BoseB1Cube
