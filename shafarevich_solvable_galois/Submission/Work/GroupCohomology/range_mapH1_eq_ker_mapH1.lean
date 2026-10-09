import Mathlib
import Submission.Work.GroupCohomology.ShortExact
import Submission.Work.GroupCohomology.H1pi_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

theorem range_mapH1_eq_ker_mapH1 {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : Work.GroupCohomology.ShortExactSeq G A B C) :
    (Work.GroupCohomology.mapH1 G S.iota S.iota_equivariant).range =
      (Work.GroupCohomology.mapH1 G S.pi S.pi_equivariant).ker := by
  apply le_antisymm
  · -- image `⊆` kernel: the composite of the two maps is `mapH1` of `pi ∘ iota = 0`.
    intro y hy
    rw [AddMonoidHom.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [AddMonoidHom.mem_ker]
    induction x using H1_induction_on with
    | h f =>
      rw [mapH1_H1π, mapH1_H1π, H1pi_eq_zero_iff, mem_B1_iff]
      refine ⟨0, ?_⟩
      funext g
      simp [S.pi_iota]
  · -- kernel `⊆` image: kill the class of `F` by subtracting the coboundary of a lift of the
    -- coboundary witnessing that `pi ∘ F` is a coboundary in `C`.
    intro x hx
    rw [AddMonoidHom.mem_range]
    revert hx
    induction x using H1_induction_on with
    | h F =>
      intro hx
      rw [AddMonoidHom.mem_ker] at hx
      rw [mapH1_H1π, H1pi_eq_zero_iff, mem_B1_iff] at hx
      obtain ⟨c, hc⟩ := hx
      -- `hc : d⁰ c = pi ∘ F`, i.e. `pi (F g) = g • c - c` for all `g`.
      have hcval : ∀ g : G, g • c - c = S.pi ((F : G → B) g) := by
        intro g
        have h := congrFun hc g
        simpa using h
      -- lift `c` to `B`
      obtain ⟨b, hb⟩ := S.exists_lift c
      -- the `B`-valued cocycle `F - d⁰ b`, which lies in the kernel of `pi`
      let D : Z1 G B := ⟨d0 G B b, d0_mem_Z1 G B b⟩
      let zB : Z1 G B := F - D
      have hzB_val : ∀ g : G, (zB : G → B) g = (F : G → B) g - (g • b - b) := fun _ => rfl
      have hzB_ker : ∀ g : G, (zB : G → B) g ∈ S.pi.ker := by
        intro g
        have h1 : S.pi ((zB : G → B) g) = S.pi ((F : G → B) g) - (g • c - c) := by
          rw [hzB_val g, map_sub, map_sub, S.pi_equivariant g b, hb]
        rw [AddMonoidHom.mem_ker, h1, hcval g, sub_self]
      -- lift each value of `zB` back to `A`; this transports the cocycle structure
      let fA : G → A := fun g => Classical.choose (S.exists_preimage (hzB_ker g))
      have hfA : ∀ g : G, S.iota (fA g) = (zB : G → B) g :=
        fun g => Classical.choose_spec (S.exists_preimage (hzB_ker g))
      have hfA_cross : IsCrossedHom G A fA := by
        intro g h
        apply S.iota_injective
        rw [map_add, S.iota_equivariant, hfA (g * h), hfA h, hfA g]
        exact zB.2 g h
      let fAZ : Z1 G A := ⟨fA, hfA_cross⟩
      refine ⟨H1π G A fAZ, ?_⟩
      rw [mapH1_H1π]
      have hzm : mapZ1 G S.iota S.iota_equivariant fAZ = zB := by
        apply Subtype.ext
        funext g
        simp only [mapZ1_coe, mapCochain1_apply]
        exact hfA g
      rw [hzm]
      -- `zB = F - D` with `D` a coboundary, so `zB` and `F` have the same class
      have hDmem : ((D : Z1 G B) : G → B) ∈ B1 G B := ⟨b, rfl⟩
      have hDz : H1π G B D = 0 :=
        (H1pi_eq_zero_iff (G := G) (A := B) D).mpr hDmem
      have hzBeq : zB = F - D := rfl
      rw [hzBeq, map_sub, hDz, sub_zero]

end Work.GroupCohomology
