import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB.ZJBasic
import Submission.Work.GLUE.ThompsonJ
import Submission.OddOrder.GroupTheory.ThompsonSubgroupAbelian

/-!
# `ZJB2`, leaf `zjMap`: the characteristic-functor property of `Z(J(·))`

Glauberman 1968, p. 1116 (property (c) of the characteristic functor `K(P) = Z(J(P))`), used
on p. 1121 to move `K` along `S ↦ SM/M` (where `M ⊴ SM` and `S ⊓ M = 1`).

`ZJ P = thompsonJ P ⊓ C_G(thompsonJ P) = Z(J(P))` is the centre of `J(P)`, and `f : G →* H` is
injective on `S` exactly when `S ⊓ f.ker = ⊥`.  Under that hypothesis `f` restricts to an
isomorphism `S ≃* f(S)` carrying `J(S)` to `J(f(S))`, and the centre travels with it.  The two
formal ingredients are

* `Subgroup.thompsonJAbelian_map_of_disjoint_ker` (odd-order library), transported across the
  bridge `Work.GW2.thompsonJ_eq_thompsonJAbelian`: `J(S^f) = J(S)^f`;
* `map_inf_centralizer_of_disjoint_ker` below: for `T ≤ S` and `f` injective on `S`,
  `(T ⊓ C_G(T))^f = T^f ⊓ C_H(T^f)`.  (This is *not* the general `map`-commutativity of the
  centralizer, which is false for non-surjective `f`; the intersection with `T^f` is what makes
  it true.)
-/

namespace Work.ZJB2

open Subgroup

/-- **A subgroup and its centralizer commute with `map` along a homomorphism that is injective
on a common overgroup.**  If `T ≤ S` and `S ⊓ f.ker = ⊥` then the image of the centre of `T` is
the centre of the image:

  `(T ⊓ C_G(T)).map f = T.map f ⊓ C_H(T.map f)`.

Injectivity of `f` on `S` is used to move commutativity *back* along `f`: for `x = f t` in the
right-hand side and `s ∈ T`, the commutator `s t s⁻¹ t⁻¹` lies in `S` and in `f.ker`. -/
theorem map_inf_centralizer_of_disjoint_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    {S T : Subgroup G} (hTS : T ≤ S) (hker : Disjoint S f.ker) :
    (T ⊓ Subgroup.centralizer (T : Set G)).map f
      = T.map f ⊓ Subgroup.centralizer (T.map f : Set H) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨t, ⟨htT, htC⟩, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨Subgroup.mem_map_of_mem f htT, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro z hz
    obtain ⟨w, hwT, rfl⟩ := Subgroup.mem_map.mp hz
    have hcomm : w * t = t * w := Subgroup.mem_centralizer_iff.mp htC w hwT
    rw [← map_mul, ← map_mul, hcomm]
  · rintro x ⟨hxT, hxC⟩
    obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp hxT
    refine Subgroup.mem_map.mpr ⟨t, ⟨htT, Subgroup.mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro s hsT
    refine Subgroup.eq_of_map_eq_of_disjoint_ker hker (S.mul_mem (hTS hsT) (hTS htT))
      (S.mul_mem (hTS htT) (hTS hsT)) ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hxC (f s) (Subgroup.mem_map_of_mem f hsT)

/-- **`ZJB2` leaf `zjMap`.**  `Z(J(·))` is a characteristic functor: for every homomorphism
`f : G →* H` that is injective on the subgroup `S` (`f.ker ⊓ S = ⊥`),

  `Z(J(S.map f)) = (Z(J(S))).map f`.

Both inclusions are the restriction of the two sides (`J`, and the centralizer) to
`S ≃* S.map f`. -/
theorem zjMap (G : Type) [Group G] [Finite G] : Work.ZJB.ZJMapProp G := by
  intro H _ _ f S hker
  have hdisj : Disjoint S f.ker := by
    rw [disjoint_iff, inf_comm]
    exact hker
  have hJ : Work.GW2.thompsonJ (S.map f) = (Work.GW2.thompsonJ S).map f := by
    simp only [Work.GW2.thompsonJ_eq_thompsonJAbelian]
    exact Subgroup.thompsonJAbelian_map_of_disjoint_ker hdisj
  unfold Work.GW2.ZJ
  simp only [hJ]
  exact (map_inf_centralizer_of_disjoint_ker f (Work.GW2.thompsonJ_le S) hdisj).symm

end Work.ZJB2
