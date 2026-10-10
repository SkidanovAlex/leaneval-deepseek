import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.GroupCohomology.Connecting
import Submission.Work.GroupCohomology.H1pi_eq_iff
import Submission.Work.GroupCohomology.H2pi_eq_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

theorem deltaCocycle_eq_class {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : Work.GroupCohomology.ShortExactSeq G A B C)
    (c c' : Work.GroupCohomology.Z1 G C)
    (h : Work.GroupCohomology.H1π G C c = Work.GroupCohomology.H1π G C c') :
    Work.GroupCohomology.H2π G A (S.deltaCocycle c) =
      Work.GroupCohomology.H2π G A (S.deltaCocycle c') := by
  rw [Work.GroupCohomology.H2pi_eq_iff]
  -- `c - c'` is a coboundary
  have hmem : ((c - c' : Work.GroupCohomology.Z1 G C) : G → C) ∈ Work.GroupCohomology.B1 G C :=
    (Work.GroupCohomology.H1pi_eq_iff c c').mp h
  obtain ⟨a, ha⟩ := (Work.GroupCohomology.mem_B1_iff G C
    ((c - c' : Work.GroupCohomology.Z1 G C) : G → C)).mp hmem
  have ha' : ∀ g : G, g • a - a = (c : G → C) g - (c' : G → C) g := by
    intro g
    have hg := congrFun ha g
    simpa using hg
  -- a lift of `a` along `pi`
  obtain ⟨b, hb⟩ := S.exists_lift a
  -- the cochain `m = L - L' - d⁰ b` takes values in `ker pi`
  let m : G → B := fun g => S.liftCochain (c : G → C) g - S.liftCochain (c' : G → C) g - (g • b - b)
  have hm_ker : ∀ g : G, m g ∈ S.pi.ker := by
    intro g
    rw [AddMonoidHom.mem_ker]
    show S.pi (m g) = 0
    dsimp only [m]
    rw [map_sub, map_sub, map_sub, S.pi_equivariant g b, hb,
      S.pi_liftCochain (c : G → C) g, S.pi_liftCochain (c' : G → C) g, ← ha' g]
    abel
  -- hence `m = iota ∘ k`
  let k : G → A := fun g => S.preimage (m g) (hm_ker g)
  have hk : ∀ g : G, S.iota (k g) = m g := by
    intro g
    dsimp only [k]
    exact S.iota_preimage (m g) (hm_ker g)
  -- and `δc - δc' = d¹ k`
  have hd1 : ∀ g h : G, Work.GroupCohomology.d1 G A k (g, h) =
      (S.deltaCocycle c : G × G → A) (g, h) - (S.deltaCocycle c' : G × G → A) (g, h) := by
    intro g h
    apply S.iota_injective
    have step1 : S.iota (Work.GroupCohomology.d1 G A k (g, h)) =
        Work.GroupCohomology.d1 G B m (g, h) := by
      have hmd := congrFun (Work.GroupCohomology.mapCochain2_d1 G S.iota S.iota_equivariant k) (g, h)
      rw [Work.GroupCohomology.mapCochain2_apply] at hmd
      rw [hmd, show Work.GroupCohomology.mapCochain1 G S.iota k = m from funext hk]
    have hm_eq : m = S.liftCochain (c : G → C) - S.liftCochain (c' : G → C) -
        Work.GroupCohomology.d0 G B b := by
      funext g'
      simp only [Pi.sub_apply, m, Work.GroupCohomology.d0_apply]
    have step2 : Work.GroupCohomology.d1 G B m (g, h) =
        Work.GroupCohomology.d1 G B (S.liftCochain (c : G → C)) (g, h) -
          Work.GroupCohomology.d1 G B (S.liftCochain (c' : G → C)) (g, h) := by
      rw [hm_eq, map_sub, map_sub, Work.GroupCohomology.d1_d0, sub_zero, Pi.sub_apply]
    have step3 : Work.GroupCohomology.d1 G B (S.liftCochain (c : G → C)) (g, h) -
          Work.GroupCohomology.d1 G B (S.liftCochain (c' : G → C)) (g, h) =
        S.iota ((S.deltaCocycle c : G × G → A) (g, h)) -
          S.iota ((S.deltaCocycle c' : G × G → A) (g, h)) := by
      rw [← S.iota_deltaCocycle c g h, ← S.iota_deltaCocycle c' g h]
    calc S.iota (Work.GroupCohomology.d1 G A k (g, h)) = Work.GroupCohomology.d1 G B m (g, h) := step1
      _ = Work.GroupCohomology.d1 G B (S.liftCochain (c : G → C)) (g, h) -
            Work.GroupCohomology.d1 G B (S.liftCochain (c' : G → C)) (g, h) := step2
      _ = S.iota ((S.deltaCocycle c : G × G → A) (g, h)) -
            S.iota ((S.deltaCocycle c' : G × G → A) (g, h)) := step3
      _ = S.iota ((S.deltaCocycle c : G × G → A) (g, h) -
            (S.deltaCocycle c' : G × G → A) (g, h)) := by rw [map_sub]
  -- conclude that `δc - δc' ∈ B²(G, A)`
  rw [Work.GroupCohomology.mem_B2_iff]
  exact ⟨k, funext fun p => by
    obtain ⟨g, h⟩ := p
    rw [hd1 g h, AddSubgroup.coe_sub, Pi.sub_apply]⟩

end Work.GroupCohomology
