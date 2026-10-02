import Mathlib
import Submission.Work.LerayHirsch.Naturality
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.zetaPow_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type} {m : ℕ}

/-! ## Naturality of the Leray–Hirsch map -/

/-- **Naturality of the Leray–Hirsch map**: the decomposition
`(x_i) ↦ Σ_i π^*(x_i) ⌣ ζ^i` pulls back along `P(f) : P(f^*E) → P(E)` to the decomposition for
`f^*E` (with `x_i` replaced by `f^*(x_i)`).  This is the compatibility that the Mayer–Vietoris step
of `Work.LerayHirsch.LerayHirschGlue` restricts along. -/
theorem lhMap_comap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (f : C(B', B)) (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    (CohMap (projMapComap Z f) ℤ (2 * k)).hom (lhMap Z k xf)
      = lhMap (bundleComap Z f) k (fun i => (CohMap f ℤ (2 * (k - (i : ℕ)))).hom (xf i)) := by
  rw [lhMap_apply, lhMap_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [lhTerm_def, lhTerm_def, Work.Whitney.cohTransport_CohMap, Work.Whitney.cupChern_CohMap]
  have hX : (CohMap (projMapComap Z f) ℤ (2 * (k - (i : ℕ)))).hom
        ((CohMap (projMap Z) ℤ (2 * (k - (i : ℕ)))).hom (xf i))
      = (CohMap (projMap (bundleComap Z f)) ℤ (2 * (k - (i : ℕ)))).hom
        ((CohMap f ℤ (2 * (k - (i : ℕ)))).hom (xf i)) := by
    rw [Work.Thom.CohMap_comp_apply (projMapComap Z f) (projMap Z) ℤ (2 * (k - (i : ℕ)))
        (xf i)]
    rw [show (projMap Z).comp (projMapComap Z f) = f.comp (projMap (bundleComap Z f)) from
      ContinuousMap.ext (fun x => projMap_projMapComap Z f x)]
    rw [← Work.Thom.CohMap_comp_apply (projMap (bundleComap Z f)) f ℤ (2 * (k - (i : ℕ)))
        (xf i)]
  rw [hX, zetaPow_comap Z f i]

end

end Work.LerayHirsch
