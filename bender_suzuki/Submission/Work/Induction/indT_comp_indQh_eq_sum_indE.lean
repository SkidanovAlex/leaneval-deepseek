import Mathlib
import Submission.Work.Induction.IndRepModel

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical

/-- The pointwise identity `indT V g ∘ indQh V h = ∑_{y : G} indE V h g y`: the two matrices of
linear maps on `G → V` agree.  Evaluating the right-hand side at `f` and `x`, the sum has the
single non-zero term `y = h⁻¹ * x * g`. -/
theorem indT_comp_indQh_eq_sum_indE {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (V : FDRep ℂ H) (g : G) (h : H) :
    (Work.Induction.indT V g).comp (Work.Induction.indQh V h)
      = ∑ y : G, Work.Induction.indE V h g y := by
  apply LinearMap.ext; intro f
  funext x
  simp only [LinearMap.comp_apply, indQh_apply, indT_apply, indE_apply, LinearMap.sum_apply,
    Finset.sum_apply]
  have hcoe : ((h⁻¹ : H) : G) = ((h : G))⁻¹ := map_inv H.subtype h
  rw [Finset.sum_eq_single ((h : G)⁻¹ * x * g)]
  · rw [ite_eq_left (by group)]
    congr 1
    rw [hcoe, mul_assoc]
  · intro b _ hb
    rw [ite_eq_right]
    intro hxb
    exact hb (by rw [hxb]; group)
  · intro hm; exact absurd (Finset.mem_univ _) hm

end Work.Induction
