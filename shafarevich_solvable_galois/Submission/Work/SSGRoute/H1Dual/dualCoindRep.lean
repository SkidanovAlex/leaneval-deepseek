import Mathlib
import Submission.Work.SSGRoute.H1Dual.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

namespace Work.SSGRoute.H1Dual

/-- The action of the coinduced representation `coindRepRep k G V = (G → V)`,
`h • φ = (x ↦ φ (x * h))`, on the function `δ_x v : G → V` supported at `x` with value `v`:
it is `δ_{x * h⁻¹} v`. -/
theorem coindRepRep_piSingle (k : Type) [CommRing k] (G : Type) [Group G] [DecidableEq G]
    (V : Type) [AddCommGroup V] [Module k V] (h x : G) (v : V) :
    (Work.SSGRoute.coindRepRep k G V) h (Pi.single x v) = Pi.single (x * h⁻¹) v := by
  funext y
  simp only [Work.SSGRoute.coindRepRep_apply, Pi.single_apply]
  by_cases hy : y * h = x
  · have hy' : y = x * h⁻¹ := by rw [← hy]; group
    rw [if_pos hy, if_pos hy']
  · have hy' : ¬ (y = x * h⁻¹) := fun hh => hy (by rw [hh]; group)
    rw [if_neg hy, if_neg hy']

/-- The `k`-linear dual of the coinduced representation `coindRep k G V = (G → V)` is the
coinduced representation on the dual `V^∨`, via `f ↦ (x ↦ (v ↦ f (δ_x v)))` where `δ_x v` is the
function `G → V` supported at `x` with value `v`. -/
theorem dualCoindRep (k : Type) [CommRing k] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module k V] :
    Nonempty (Work.SSGRoute.dualRep (Work.SSGRoute.coindRep k G V) ≅
      Work.SSGRoute.coindRep k G (Module.Dual k V)) := by
  classical
  -- The dual of the finite product `G → V` is the product of the duals,
  -- `(LinearMap.lsum k (fun _ : G => V) k).symm : ((G → V) →ₗ[k] k) ≃ₗ[k] (G → V →ₗ[k] k)`.
  refine ⟨Rep.mkIso (Representation.Equiv.mk
    (ρ := Representation.dual (Work.SSGRoute.coindRepRep k G V))
    (σ := Work.SSGRoute.coindRepRep k G (Module.Dual k V))
    ((LinearMap.lsum k (fun _ : G => V) k).symm) ?_)⟩
  -- Equivariance: `e ((ρ.dual g) f) x v = (σ g (e f)) x v`.
  intro g
  apply LinearMap.ext
  intro f
  apply funext
  intro x
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply,
    Work.SSGRoute.coindRepRep_apply]
  change (LinearMap.lsum k (fun _ : G => V) k).symm
      (f ∘ₗ (Work.SSGRoute.coindRepRep k G V) g⁻¹) x v =
    (LinearMap.lsum k (fun _ : G => V) k).symm f (x * g) v
  rw [LinearMap.lsum_symm_apply, LinearMap.lsum_symm_apply]
  simp only [LinearMap.comp_apply, LinearMap.single_apply]
  rw [Work.SSGRoute.H1Dual.coindRepRep_piSingle, inv_inv]

end Work.SSGRoute.H1Dual
