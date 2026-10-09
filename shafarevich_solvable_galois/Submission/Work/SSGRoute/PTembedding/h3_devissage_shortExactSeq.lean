import Mathlib
import Submission.Work.SSGRoute.range_mapH3_eq_ker_mapH3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Dévissage of `H³` along a short exact sequence

If `0 → A →^{ι} B →^{π} C → 0` is a short exact sequence of (discrete) `Γ`-modules and both
`H³(Γ,A)` and `H³(Γ,C)` are trivial, then `H³(Γ,B)` is trivial.

This is the "dévissage" step for the third cohomology: the long exact sequence in continuous
cohomology gives exactness at the middle term,

  `H³(Γ,A) →^{ι_*} H³(Γ,B) →^{π_*} H³(Γ,C)`,

i.e. `range H³(ι) = ker H³(π)`
(`Work.SSGRoute.range_mapH3_eq_ker_mapH3`).  As `H³(Γ,A) = 0` the range of `H³(ι)` is trivial,
and as `H³(Γ,C) = 0` the kernel of `H³(π)` is everything; hence `H³(Γ,B) = 0`.
-/

namespace Work.SSGRoute.PTembedding

theorem h3_devissage_shortExactSeq {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C]
    (S : Work.AbsoluteKummer.ShortExactSeq Γ A B C)
    (hA : Subsingleton (Work.SSGRoute.H3 (M := A) Γ))
    (hC : Subsingleton (Work.SSGRoute.H3 (M := C) Γ)) :
    Subsingleton (Work.SSGRoute.H3 (M := B) Γ) := by
  refine ⟨fun x y => ?_⟩
  -- `x - y` lies in the kernel of `π_*`, which by exactness is the range of `ι_*`
  have hmem : x - y ∈ (Work.SSGRoute.H3Map.mapH3 S.iota S.iota_equivariant).range := by
    rw [Work.SSGRoute.range_mapH3_eq_ker_mapH3 S, AddMonoidHom.mem_ker]
    have h1 : Work.SSGRoute.H3Map.mapH3 S.pi S.pi_equivariant x
        = Work.SSGRoute.H3Map.mapH3 S.pi S.pi_equivariant y :=
      Subsingleton.elim (h := hC) _ _
    rw [map_sub, h1, sub_self]
  -- the range of `ι_*` is trivial, so `x - y = 0`
  obtain ⟨z, hz⟩ := hmem
  have hz0 : z = 0 := Subsingleton.elim (h := hA) z 0
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

end Work.SSGRoute.PTembedding
