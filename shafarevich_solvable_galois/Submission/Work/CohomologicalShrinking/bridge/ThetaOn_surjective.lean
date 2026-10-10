import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Submission.Work.CohomologicalShrinking.Bridge.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators

namespace Work.CohomologicalShrinking.bridge

/-- The dimension-shift map `Θ : Z₁(G,M) → ker(N_{M^♯})`, `x ↦ x - single 1 (∑ x)`, is
surjective.

Indeed, if `y ∈ ker(N : M^♯ → M^♯)` then, viewing `y` as a function `G → M`, the two
defining relations `∑_g g⁻¹ • y g = 0` (membership in `M^♯`) and `∑_g y g = 0` (vanishing of
the norm, `Work.Bridge.coe_norm_A_eq_const`) say exactly that `y` is a `1`-cycle and that its
coefficient sum vanishes; hence `Θ y = y - single 1 (∑ y) = y`. -/
theorem ThetaOn_surjective (k : Type) [CommRing k] (G : Type) [Group G] [Fintype G]
    [DecidableEq G] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction G M]
    [SMulCommClass G k M] : Function.Surjective (Work.Bridge.ThetaOn k G M) := by
  classical
  intro y
  let yf : G → M := (((y : Work.Bridge.K (G:=G) (M:=M)) : Work.Bridge.A (G:=G) (M:=M)) : G → M)
  have hyf_mem : yf ∈ Work.Tate.coindUp G M := by
    have h := ((y : Work.Bridge.K (G:=G) (M:=M)) : Work.Bridge.A (G:=G) (M:=M)).2
    simpa [yf] using h
  have hsum : (∑ g, yf g) = 0 := by
    have hnorm : Work.Tate.norm G (Work.Bridge.A (G:=G) (M:=M))
        (y : Work.Bridge.A (G:=G) (M:=M)) = 0 := y.2
    have hconst := Work.Bridge.coe_norm_A_eq_const (G:=G) (M:=M)
        (y := (y : Work.Bridge.A (G:=G) (M:=M)))
    have h1 : Function.const G (∑ g, (((y : Work.Bridge.K (G:=G) (M:=M)) :
        Work.Bridge.A (G:=G) (M:=M)) : G → M) g) = 0 := by
      rw [← hconst, hnorm]
      simp
    have h2 := congrFun h1 1
    simpa [yf, Function.const_apply] using h2
  let x : G →₀ M := Finsupp.onFinset Finset.univ yf (fun g _ => Finset.mem_univ g)
  have hxg : ∀ g, x g = yf g := by
    intro g; simp [x]
  have hx : x ∈ Work.Bridge.Z k G M := by
    rw [Work.Bridge.Z, groupHomology.mem_cycles₁_iff]
    change x.sum (fun g a => g⁻¹ • a) = x.sum (fun _ a => a)
    rw [Finsupp.sum_fintype x (fun g a => g⁻¹ • a) (by intro i; simp),
        Finsupp.sum_fintype x (fun _ a => a) (by intro i; simp)]
    have e1 : (∑ g, g⁻¹ • x g) = ∑ g, g⁻¹ • yf g :=
      Finset.sum_congr rfl (fun g _ => by rw [hxg g])
    have e2 : (∑ g, x g) = ∑ g, yf g := Finset.sum_congr rfl (fun g _ => hxg g)
    rw [e1, e2, Work.Tate.mem_coindUp_iff.mp hyf_mem, hsum]
  refine ⟨⟨x, hx⟩, ?_⟩
  have hfun : ((((Work.Bridge.ThetaOn k G M) ⟨x, hx⟩ : Work.Bridge.K (G:=G) (M:=M)) :
      Work.Bridge.A (G:=G) (M:=M)) : G → M) = yf := by
    funext g
    rw [Work.Bridge.ThetaOn_coe, Work.Bridge.thetaFun_apply]
    have hcoeff : Work.Bridge.coeffSum x = 0 := by
      rw [Work.Bridge.coeffSum_eq_sum]
      rw [show (∑ g, x g) = ∑ g, yf g from Finset.sum_congr rfl (fun g _ => hxg g)]
      exact hsum
    rw [hcoeff, hxg g]
    simp [Work.Bridge.d1]
  exact Subtype.ext (Subtype.ext hfun)

end Work.CohomologicalShrinking.bridge
