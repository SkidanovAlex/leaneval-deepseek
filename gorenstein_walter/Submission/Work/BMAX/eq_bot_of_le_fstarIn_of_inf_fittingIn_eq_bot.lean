import Mathlib
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.LayerCentralizesFitting

set_option linter.style.haveILetI false

namespace Work.BMAX

/-- A normal nilpotent subgroup of `X` lies in the Fitting subgroup `F(X)`.

`Work.GW2.fitting X` is the normal core of the join of the normal nilpotent subgroups; since
that join is normal, its normal core is itself, so any member of the join lies in it. -/
private theorem normal_nilpotent_le_fitting_aux {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    [Group.IsNilpotent ↥N] : N ≤ Work.GW2.fitting X := by
  rw [Work.GW2.fitting]
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, inferInstance⟩)

/-- **The centre of `F*(X)` lies in `F(X)`**: if `z ∈ F*(X)` centralizes `F*(X)`, then
`z ∈ F(X)`.

This is the group-theoretic core of the target lemma.  `F*(X) = F(X)·E(X)` is normal in `X`
(join of the normal subgroups `F(X)` and `E(X)`), so `Z(F*(X)) = F*(X) ⊓ C_X(F*(X))` is normal
in `X`.  For `z ∈ Z(F*(X))` the whole normal closure `N = ⟨z^X⟩` therefore lies in
`Z(F*(X))`, which is abelian; hence `N` is an abelian, in particular nilpotent, normal
subgroup of `X`, so `N ≤ F(X)` and `z ∈ N ≤ F(X)`.

Note that no finiteness is used. -/
private theorem mem_fitting_of_mem_fstar_of_mem_centralizer_aux {X : Type*} [Group X]
    {z : X} (hz : z ∈ Work.GW2.fstar X)
    (hzc : z ∈ Subgroup.centralizer (Work.GW2.fstar X : Set X)) :
    z ∈ Work.GW2.fitting X := by
  have hFn : (Work.GW2.fitting X).Normal := by
    rw [Work.GW2.fitting]; exact Subgroup.normalCore_normal _
  have hLn : (Work.GW2.layer X).Normal :=
    Subgroup.sSup_normal _ (fun _ hH => hH.1)
  have hfsn : (Work.GW2.fstar X).Normal := by
    rw [Work.GW2.fstar]; exact inferInstance
  have hcn : (Subgroup.centralizer (Work.GW2.fstar X : Set X)).Normal := inferInstance
  have hin : (Work.GW2.fstar X ⊓ Subgroup.centralizer (Work.GW2.fstar X : Set X)).Normal :=
    inferInstance
  let N : Subgroup X := Subgroup.normalClosure ({z} : Set X)
  -- `N = ⟨z^X⟩` lies in the (abelian) centre `Z(F*(X)) = F*(X) ⊓ C_X(F*(X))`
  have hNle : N ≤ Work.GW2.fstar X ⊓ Subgroup.centralizer (Work.GW2.fstar X : Set X) :=
    Subgroup.normalClosure_le_normal (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hz, hzc⟩)
  have hNn : N.Normal := Subgroup.normalClosure_normal
  -- hence `N` is abelian, and therefore nilpotent
  have hNcomm : IsMulCommutative ↥N := isMulCommutative_iff.mpr (fun (a b : ↥N) => by
    apply Subtype.ext
    show (a : X) * (b : X) = (b : X) * (a : X)
    exact (Subgroup.mem_centralizer_iff.mp (hNle a.2).2 _ (hNle b.2).1).symm)
  haveI : IsMulCommutative ↥N := hNcomm
  haveI : Group.IsNilpotent ↥N := inferInstance
  exact normal_nilpotent_le_fitting_aux (N := N) (Subgroup.subset_normalClosure (Set.mem_singleton z))

theorem eq_bot_of_le_fstarIn_of_inf_fittingIn_eq_bot {G : Type} [Group G] [Finite G]
    (A Q : Subgroup G)
    (hQf : Q ≤ Work.GW2.fstarIn A) (hQF : Q ⊓ Work.GW2.fittingIn A = ⊥)
    (hQc : Q ≤ Subgroup.centralizer (Work.GW2.fstarIn A : Set G)) : Q = ⊥ := by
  have hQle : Q ≤ Work.GW2.fittingIn A := by
    intro q hq
    -- `q ∈ F*(A)`; lift to a preimage `z` inside the group `↥A`
    have hqf : q ∈ (Work.GW2.fstar ↥A).map A.subtype := hQf hq
    rw [Subgroup.mem_map] at hqf
    obtain ⟨z, hz, hzq⟩ := hqf
    -- `z` centralizes `F*(↥A)` because `q` centralizes `F*(A)`
    have hzc : z ∈ Subgroup.centralizer (Work.GW2.fstar ↥A : Set ↥A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : A.subtype w ∈ Work.GW2.fstarIn A := by
        rw [Work.GW2.fstarIn, Subgroup.mem_map]
        exact ⟨w, hw, rfl⟩
      have hcomm : A.subtype w * q = q * A.subtype w :=
        Subgroup.mem_centralizer_iff.mp (hQc hq) (A.subtype w) hw'
      refine A.subtype_injective ?_
      rw [map_mul, map_mul, hzq]
      exact hcomm
    -- the centre of `F*` is contained in `F`
    have hzf : z ∈ Work.GW2.fitting ↥A :=
      mem_fitting_of_mem_fstar_of_mem_centralizer_aux hz hzc
    show q ∈ Work.GW2.fittingIn A
    rw [Work.GW2.fittingIn, Subgroup.mem_map]
    exact ⟨z, hzf, hzq⟩
  have hbot : Q ≤ ⊥ := by
    rw [← hQF]
    exact le_inf le_rfl hQle
  exact le_bot_iff.mp hbot

end Work.BMAX
