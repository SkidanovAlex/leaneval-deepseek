/-
Area AV: the chart ring `Away (gr k) (X i)` of `P¹` is a polynomial ring over `k`.
-/
import Mathlib
import Submission.Work.AbVar.P1Chart.Basic
import Submission.Work.AbVar.ProjectiveLine.chart
import Submission.Work.AbVar.ProjectiveLine.awaySurjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open HomogeneousLocalization MvPolynomial

noncomputable section

universe u

namespace Work.AbVar.P1Chart

/-- The chart ring `AX k i` is a polynomial ring in one variable over `k`; the variable is
`X_j/X_i` for `j ≠ i`. -/
noncomputable def awayXAlgEquiv (k : Type u) [Field k] (i : Fin 2) :
    AX k i ≃ₐ[k] Polynomial k :=
  (AlgEquiv.ofBijective (ProjectiveLine.polyToAway (R := k) i (other i))
    ⟨ProjectiveLine.polyToAway_injective (other_ne i),
      ProjectiveLine.awaySurjective (R := k) (other_ne i)⟩).symm

/-- After tensoring with a field extension `K/k`, the chart ring becomes `K[T]`, a domain. -/
theorem isDomain_tensor_k (k : Type u) [Field k] (i : Fin 2) (K : Type u) [Field K]
    [Algebra k K] : IsDomain (TensorProduct k (AX k i) K) := by
  have hpoly : IsDomain (TensorProduct k (Polynomial k) K) :=
    MulEquiv.isDomain (Polynomial K)
      ((Algebra.TensorProduct.comm k (Polynomial k) K).trans (polyEquivTensor k K).symm).toMulEquiv
  exact MulEquiv.isDomain _
    (Algebra.TensorProduct.congr (awayXAlgEquiv k i).symm
      (AlgEquiv.refl : K ≃ₐ[k] K)).toMulEquiv.symm

end Work.AbVar.P1Chart
