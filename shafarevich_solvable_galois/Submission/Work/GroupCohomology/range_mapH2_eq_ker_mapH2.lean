import Mathlib
import Submission.Work.GroupCohomology.ShortExact
import Submission.Work.GroupCohomology.H2pi_eq_iff
import Submission.Work.GroupCohomology.H2pi_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

theorem range_mapH2_eq_ker_mapH2 {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : Work.GroupCohomology.ShortExactSeq G A B C) :
    (Work.GroupCohomology.mapH2 G S.iota S.iota_equivariant).range =
      (Work.GroupCohomology.mapH2 G S.pi S.pi_equivariant).ker := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    rw [AddMonoidHom.mem_ker]
    refine H2_induction_on x (C := fun y =>
      mapH2 G S.pi S.pi_equivariant (mapH2 G S.iota S.iota_equivariant y) = 0) ?_
    intro c
    rw [mapH2_H2π, mapH2_H2π]
    rw [H2pi_eq_zero_iff, mem_B2_iff]
    refine ⟨0, ?_⟩
    funext p
    simp only [map_zero, Pi.zero_apply, mapCochain2_apply, mapZ2_coe, S.pi_iota]
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    refine (H2_induction_on x (C := fun y =>
      mapH2 G S.pi S.pi_equivariant y = 0 →
      y ∈ (mapH2 G S.iota S.iota_equivariant).range) ?_) hx
    intro b hb
    rw [mapH2_H2π] at hb
    have hmem : ((mapZ2 G S.pi S.pi_equivariant b : Z2 G C) : G × G → C) ∈ B2 G C :=
      (H2pi_eq_zero_iff (mapZ2 G S.pi S.pi_equivariant b)).mp hb
    rw [mem_B2_iff] at hmem
    obtain ⟨f, hf⟩ := hmem
    choose g_ hg_ using fun g => S.pi_surjective (f g)
    let bk : Z2 G B :=
      ⟨fun p => (b : G × G → B) p - d1 G B g_ p, by
        exact sub_mem b.2 (d1_mem_Z2 G B g_)⟩
    have hbk_ker : ∀ p, (bk : G × G → B) p ∈ S.pi.ker := by
      intro p
      rw [AddMonoidHom.mem_ker]
      have hg : mapCochain1 G S.pi g_ = f := by
        funext g
        exact hg_ g
      have hd1 : ∀ q, S.pi (d1 G B g_ q) = mapCochain2 G S.pi (b : G × G → B) q := by
        intro q
        have h := congrFun (mapCochain2_d1 G S.pi S.pi_equivariant g_) q
        rw [hg, congrFun hf q, mapZ2_coe, mapCochain2_apply] at h
        exact h
      show S.pi ((b : G × G → B) p - d1 G B g_ p) = 0
      rw [map_sub, show S.pi ((b : G × G → B) p) = mapCochain2 G S.pi (b : G × G → B) p from rfl,
        hd1 p, sub_self]
    have ha_ex : ∀ p : G × G, ∃ a : A, S.iota a = (bk : G × G → B) p :=
      fun p => S.exists_preimage (hbk_ker p)
    let aCoch : G × G → A := fun p => Classical.choose (ha_ex p)
    have haCoch : ∀ p, S.iota (aCoch p) = (bk : G × G → B) p :=
      fun p => Classical.choose_spec (ha_ex p)
    have ha_mem : aCoch ∈ Z2 G A := by
      rw [mem_Z2_iff]
      intro g h k
      apply S.iota_injective
      simp only [map_add]
      rw [haCoch (g * h, k), haCoch (g, h), S.iota_equivariant g (aCoch (h, k)),
        haCoch (h, k), haCoch (g, h * k)]
      exact bk.2 g h k
    refine ⟨H2π G A ⟨aCoch, ha_mem⟩, ?_⟩
    rw [mapH2_H2π]
    have hmapZ : mapZ2 G S.iota S.iota_equivariant (⟨aCoch, ha_mem⟩ : Z2 G A) = bk := by
      ext p
      simp only [mapZ2_coe, mapCochain2_apply]
      exact haCoch p
    rw [hmapZ]
    have hbk_eq : H2π G B bk = H2π G B b := by
      rw [H2pi_eq_iff, mem_B2_iff]
      refine ⟨fun g => - g_ g, ?_⟩
      have hbk_sub : (↑(bk - b) : G × G → B) = - d1 G B g_ := by
        funext p
        obtain ⟨p1, p2⟩ := p
        rw [show (↑(bk - b) : G × G → B) (p1, p2) =
            ((b : G × G → B) (p1, p2) - d1 G B g_ (p1, p2)) - (b : G × G → B) (p1, p2) from rfl]
        show ((b : G × G → B) (p1, p2) - d1 G B g_ (p1, p2)) - (b : G × G → B) (p1, p2) =
            - (d1 G B g_ (p1, p2))
        abel
      have hd1neg : d1 G B (fun g => - g_ g) = - d1 G B g_ := by
        rw [show (fun g => - g_ g) = - g_ from rfl, map_neg]
      rw [hd1neg, hbk_sub]
    exact hbk_eq

end Work.GroupCohomology
