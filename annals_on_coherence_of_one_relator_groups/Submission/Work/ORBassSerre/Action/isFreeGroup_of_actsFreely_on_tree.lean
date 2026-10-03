import Mathlib
import Submission.Work.ORBassSerre.Action.Cocompact
import Submission.Work.ORBassSerre.Action.QuotientReverse
import Submission.Work.ORBassSerre.Action.FreeActionWord
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

namespace Work.ORBassSerre.Action

open Quiver

/-- A group acting freely and without inversions on a non-empty tree is a free group
(Nielsen--Schreier / Bass--Serre). -/
theorem isFreeGroup_of_actsFreely_on_tree {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    [Nonempty V] (hT : Work.ORBassSerre.IsTree V) (hfree : Work.ORBassSerre.ActsFreely G V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V) :
    IsFreeGroup G := by
  classical
  let v₀ : V := Classical.arbitrary V
  let f : G → FreeGroup (HalfEdge (G := G) (V := V)) :=
    fun g => pathWordFree (G := G) (V := V) (hT.geodesic v₀ (g • v₀))
  have hf : ∀ g h : G, f (g * h) = f g * f h := by
    intro g h
    simp only [f]
    rw [mul_smul,
      pathWordFree_eq_of_same_endpoints hT hninv (hT.geodesic v₀ (g • (h • v₀)))
        ((hT.geodesic v₀ (g • v₀)).comp (hT.geodesic (g • v₀) (g • (h • v₀)))),
      pathWordFree_comp]
    congr 1
    rw [pathWordFree_eq_of_same_endpoints hT hninv (hT.geodesic (g • v₀) (g • (h • v₀)))
      (smulPath g (hT.geodesic v₀ (h • v₀))), pathWordFree_smul]
  let ψ : G →* FreeGroup (HalfEdge (G := G) (V := V)) := MonoidHom.mk' f hf
  have hker : ∀ g : G, ψ g = 1 → g = 1 := by
    intro g hg
    have hp : pathWord (G := G) (V := V) (hT.geodesic v₀ (g • v₀)) = [] := by
      have h1 : FreeGroup.mk (pathWord (G := G) (V := V) (hT.geodesic v₀ (g • v₀))) = 1 := hg
      obtain ⟨c, hc, hc'⟩ := FreeGroup.Red.exact.1 (h1.trans FreeGroup.one_eq_mk)
      rw [FreeGroup.Red.nil_iff] at hc'
      have hred : FreeGroup.Red (pathWord (G := G) (V := V) (hT.geodesic v₀ (g • v₀))) [] := by
        rwa [hc'] at hc
      exact ((isReduced_pathWord hninv hfree (hT.geodesic v₀ (g • v₀))
        (hT.geodesic_isReduced v₀ (g • v₀))).red_iff_eq.1 hred).symm
    exact hfree g v₀
      (Quiver.Path.eq_of_length_zero _ (length_eq_zero_of_pathWord_eq_nil hp)).symm
  have hinj : Function.Injective ψ := by
    intro a b hab
    exact inv_mul_eq_one.mp
      (hker (a⁻¹ * b) (by rw [map_mul, map_inv, hab, inv_mul_cancel]))
  haveI : IsFreeGroup ↥ψ.range := subgroupIsFreeOfIsFree ψ.range
  have hbij : Function.Bijective ψ.rangeRestrict :=
    ⟨fun x y hxy => hinj (by simpa using Subtype.ext_iff.mp hxy),
      fun y => by obtain ⟨x, hx⟩ := y.2; exact ⟨x, Subtype.ext hx⟩⟩
  exact IsFreeGroup.ofMulEquiv (MulEquiv.ofBijective ψ.rangeRestrict hbij).symm

end Work.ORBassSerre.Action
