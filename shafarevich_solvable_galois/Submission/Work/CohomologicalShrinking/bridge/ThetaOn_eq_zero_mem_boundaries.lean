import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Submission.Work.CohomologicalShrinking.Bridge.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.bridge

open Work.Bridge

/-- If `thetaFun` kills a finitely supported function, that function is concentrated at `1`. -/
theorem eq_single_one_of_thetaFun_eq_zero {G : Type} [Group G] [Fintype G] [DecidableEq G]
    {M : Type} [AddCommGroup M] [DistribMulAction G M] {x : G →₀ M}
    (h : thetaFun (G:=G) x = 0) : x = Finsupp.single 1 (x 1) := by
  have hx : ∀ g : G, x g = d1 (G:=G) (coeffSum x) g := by
    intro g
    have := congrFun h g
    simp only [Pi.zero_apply, thetaFun_apply] at this
    exact sub_eq_zero.mp this
  ext g
  by_cases hg : g = 1
  · subst hg; simp
  · rw [show x g = 0 by rw [hx g, d1_apply, if_neg hg], Finsupp.single_eq_of_ne hg]

theorem ThetaOn_eq_zero_mem_boundaries (k : Type) [CommRing k] (G : Type) [Group G]
    [Fintype G] [DecidableEq G] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction G M]
    [SMulCommClass G k M] (z : ↥(Work.Bridge.Z k G M))
    (hz : Work.Bridge.ThetaOn k G M z = 0) :
    (z : G →₀ M) ∈ Work.Bridge.B k G M := by
  have hθ : thetaFun (G:=G) (z : G →₀ M) = 0 := by
    have h := congrArg (fun w : ↥(K (G:=G) (M:=M)) => ((w : A (G:=G) (M:=M)) : G → M)) hz
    simpa [ThetaOn_coe] using h
  rw [eq_single_one_of_thetaFun_eq_zero hθ]
  exact LinearMap.mem_range.mpr ⟨Finsupp.single (1, 1) ((z : G →₀ M) 1), by
    rw [groupHomology.d₂₁_single_one_fst]⟩

end Work.CohomologicalShrinking.bridge
