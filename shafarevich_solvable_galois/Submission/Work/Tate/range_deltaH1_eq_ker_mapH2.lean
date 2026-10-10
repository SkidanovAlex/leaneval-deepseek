import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.GroupCohomology.ConnectingMap
import Submission.Work.GroupCohomology.H2pi_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

open Work.GroupCohomology

theorem range_deltaH1_eq_ker_mapH2 {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : Work.GroupCohomology.ShortExactSeq G A B C) :
    S.deltaH1.range = (Work.GroupCohomology.mapH2 G S.iota S.iota_equivariant).ker := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine H1_induction_on x (C := fun y => mapH2 G S.iota S.iota_equivariant (S.deltaH1 y) = 0) ?_
    intro c
    rw [S.deltaH1_H1π, mapH2_H2π, H2pi_eq_zero_iff, mem_B2_iff]
    refine ⟨S.liftCochain (c : G → C), ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    simp only [mapZ2_coe, mapCochain2_apply]
    exact (S.iota_deltaCocycle c g h).symm
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    refine H2_induction_on x (C := fun y =>
      mapH2 G S.iota S.iota_equivariant y = 0 → y ∈ S.deltaH1.range) ?_ hx
    intro a ha
    rw [mapH2_H2π] at ha
    have hmem : ((mapZ2 G S.iota S.iota_equivariant a : Z2 G B) : G × G → B) ∈ B2 G B :=
      (H2pi_eq_zero_iff _).mp ha
    rw [mem_B2_iff] at hmem
    obtain ⟨f, hf⟩ := hmem
    have h1 : ∀ g h, d1 G B f (g, h) = S.iota ((a : G × G → A) (g, h)) := by
      intro g h
      have := congrFun hf (g, h)
      simpa only [mapZ2_coe, mapCochain2_apply] using this
    let γcoe : G → C := fun g => S.pi (f g)
    have hγcoc : IsCrossedHom G C γcoe := by
      intro g h
      have h2 := congrArg S.pi (h1 g h)
      rw [d1_apply] at h2
      rw [map_add, map_sub, S.pi_equivariant g (f h), S.pi_iota] at h2
      show γcoe (g * h) = g • γcoe h + γcoe g
      show S.pi (f (g * h)) = g • S.pi (f h) + S.pi (f g)
      have hh : g • S.pi (f h) + S.pi (f g) - S.pi (f (g * h)) = 0 := by
        rw [← h2]; abel
      exact (sub_eq_zero.mp hh).symm
    let γ : Z1 G C := ⟨γcoe, hγcoc⟩
    have hfinal : H2π G A (S.deltaCocycle γ) = H2π G A a := by
      rw [H2pi_eq_iff]
      rw [mem_B2_iff]
      have hm : ∀ g, S.liftCochain (γ : G → C) g - f g ∈ S.pi.ker := by
        intro g
        rw [AddMonoidHom.mem_ker]
        show S.pi (S.liftCochain (γ : G → C) g - f g) = 0
        rw [map_sub, S.pi_liftCochain (γ : G → C) g]
        show γcoe g - S.pi (f g) = 0
        rw [show S.pi (f g) = γcoe g from rfl]
        abel
      let k : G → A := fun g =>
        S.preimage (S.liftCochain (γ : G → C) g - f g) (hm g)
      have hk : ∀ g, S.iota (k g) =
          S.liftCochain (γ : G → C) g - f g := by
        intro g
        dsimp only [k]
        exact S.iota_preimage _ (hm g)
      have hd1 : ∀ g h, d1 G A k (g, h) =
          (S.deltaCocycle γ : G × G → A) (g, h) - (a : G × G → A) (g, h) := by
        intro g h
        apply S.iota_injective
        have step1 : S.iota (d1 G A k (g, h)) =
            d1 G B (fun x => S.iota (k x)) (g, h) := by
          have hmap1 : mapCochain1 G S.iota k = fun x => S.iota (k x) := by
            funext x; rw [mapCochain1_apply]
          have := congrFun (mapCochain2_d1 G S.iota S.iota_equivariant k) (g, h)
          rwa [mapCochain2_apply, hmap1] at this
        have step2 : d1 G B (fun x => S.iota (k x)) (g, h) =
            d1 G B (S.liftCochain (γ : G → C)) (g, h) - d1 G B f (g, h) := by
          have hLf : (fun x => S.iota (k x)) =
              S.liftCochain (γ : G → C) - f := by
            funext x
            rw [hk x]
            rfl
          rw [hLf, map_sub, Pi.sub_apply]
        have step3 : d1 G B (S.liftCochain (γ : G → C)) (g, h) - d1 G B f (g, h) =
            S.iota ((S.deltaCocycle γ : G × G → A) (g, h)) -
              S.iota ((a : G × G → A) (g, h)) := by
          rw [← S.iota_deltaCocycle γ g h, h1 g h]
        calc S.iota (d1 G A k (g, h))
            = d1 G B (fun x => S.iota (k x)) (g, h) := step1
          _ = d1 G B (S.liftCochain (γ : G → C)) (g, h) - d1 G B f (g, h) := step2
          _ = S.iota ((S.deltaCocycle γ : G × G → A) (g, h)) -
                S.iota ((a : G × G → A) (g, h)) := step3
          _ = S.iota ((S.deltaCocycle γ : G × G → A) (g, h) -
                (a : G × G → A) (g, h)) := by rw [map_sub]
      refine ⟨k, ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      rw [hd1 g h]
      simp only [AddSubgroup.coe_sub, Pi.sub_apply]
    refine ⟨H1π G C γ, ?_⟩
    rw [S.deltaH1_H1π, hfinal]

end Work.Tate
