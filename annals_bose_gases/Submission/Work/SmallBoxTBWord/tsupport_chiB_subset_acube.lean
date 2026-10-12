import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

/-- **The topological support of the sliding cutoff lies in the big box.**

`χ_B = chiB ℓ d u` is the product `χ(x/ℓ)·χ(x/(ℓd) − u)`; if it is nonzero then
its first factor is nonzero, so `x` lies in the (closed) small/double box
`dlBox ℓ d u ⊆ acube ℓ` (`chiB_support_mem`). The support of `chiB ℓ d u` is
therefore contained in the closed cube `acube ℓ`, and so is its closure. -/
theorem tsupport_chiB_subset_acube {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) :
    tsupport (Submission.BoseGases.chiB ℓ d u) ⊆ Submission.BoseGases.acube ℓ := by
  refine closure_minimal (fun x hx => ?_) ?_
  · rw [Function.mem_support] at hx
    exact (Submission.BoseGases.chiB_support_mem hℓ hd u x hx).1
  · rw [show Submission.BoseGases.acube ℓ = ⋂ m : Fin 3, (fun y : EuclideanSpace ℝ (Fin 3) => y m) ⁻¹' (Set.Icc (-ℓ/2) (ℓ/2)) from by
      ext y; simp [Submission.BoseGases.mem_acube_iff]]
    exact isClosed_iInter (fun m => IsClosed.preimage (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y m) isClosed_Icc)

end Work.SmallBoxTBWord
