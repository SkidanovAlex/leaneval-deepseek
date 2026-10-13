import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.EllipticEst.InteriorRegularity.Strip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.EllipticEst.InteriorRegularity

open Set Filter

/-- **Multiplication of a smooth function by a function smooth on a neighbourhood of its
support.**  If `g` is `C^n` on an open set `U` and `f` is `C^∞` on the whole space with
`tsupport f ⊆ U`, then `f * g` is `C^n` on the whole space.

The proof is a two-open-set argument: `f` is `C^n` on the open set `U` (it is `C^m` for every
`m : ℕ`, so `contDiffWithinAt_iff_forall_nat_le` upgrades this to the order `n`, which may be
`∞`), while on the complement of the (closed) topological support of `f` the function `f`
vanishes identically on a neighbourhood of every point, so `f * g` agrees there with the zero
function.  The two open sets cover the space because `tsupport f ⊆ U`, so
`contDiff_of_contDiffOn_union_of_isOpen` applies. -/
theorem contDiff_mul_of_tsupport_subset {U : Set E2} {f g : E2 → ℂ} {n : ℕ∞}
    (hg : ContDiffOn ℝ (n : WithTop ℕ∞) g U) (hU : IsOpen U) (hf : ∀ m : ℕ, ContDiff ℝ m f)
    (hfs : tsupport f ⊆ U) : ContDiff ℝ (n : WithTop ℕ∞) (fun x => f x * g x) := by
  -- `f` is `C^m` for every `m`, hence `C^n` on the open set `U`
  have hfU : ContDiffOn ℝ (n : WithTop ℕ∞) f U := by
    intro x hx
    rw [contDiffWithinAt_iff_forall_nat_le]
    exact fun m _ => (hf m).contDiffOn x hx
  -- off the topological support of `f`, the product vanishes on a neighbourhood of every point
  have hcompl : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x => f x * g x) (tsupport f)ᶜ := by
    intro x hx
    have hev : (fun y => f y * g y) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact ((contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev).contDiffWithinAt
  -- `U` and `(tsupport f)ᶜ` are open and cover the whole space
  refine contDiff_of_contDiffOn_union_of_isOpen (hfU.mul hg) hcompl ?_ hU
    (isClosed_tsupport f).isOpen_compl
  rw [eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact Or.inl (hfs hx)
  · exact Or.inr hx

end Work.EllipticEst.InteriorRegularity
