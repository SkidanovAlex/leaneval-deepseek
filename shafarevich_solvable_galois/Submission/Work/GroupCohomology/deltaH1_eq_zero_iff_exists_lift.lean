import Mathlib
import Submission.Work.GroupCohomology.range_mapH1_eq_ker_deltaH1
import Submission.Work.GroupCohomology.ConnectingLift
import Submission.Work.Tate.ker_deltaH1_eq_range_mapH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- **The connecting map as the obstruction to lifting.**  For a short exact sequence of `G`-modules `0 → A --iota--> B --pi--> C → 0`, a `1`-cocycle `c` of `C` has vanishing connecting image in `H²(G, A)` if and only if it lifts to a `1`-cocycle of `B` along `π`. -/
theorem deltaH1_eq_zero_iff_exists_lift {G : Type*} {A B C : Type*} [Group G]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A]
    [DistribMulAction G B] [DistribMulAction G C]
    (S : Work.GroupCohomology.ShortExactSeq G A B C) (c : Work.GroupCohomology.Z1 G C) :
    S.deltaH1 (Work.GroupCohomology.H1π G C c) = 0 ↔
      ∃ b : Work.GroupCohomology.Z1 G B,
        Work.GroupCohomology.mapZ1 G S.pi S.pi_equivariant b = c := by
  constructor
  · -- If the connecting image vanishes, the class of `c` lies in the kernel of `δ¹`, which by
    -- exactness is the range of `mapH1 π`; the Tate construction then produces an honest lift.
    intro h
    rw [S.deltaH1_H1π] at h
    exact Work.Tate.exists_mapZ1_pi_eq_of_deltaCocycle_eq_zero S c h
  · -- Conversely a cocycle that is the image under `π` of a cocycle of `B` has vanishing
    -- connecting image, since it lies in the range of `mapH1 π = ker δ¹`.
    rintro ⟨b, hb⟩
    have hx : Work.GroupCohomology.H1π G C c =
        Work.GroupCohomology.mapH1 G S.pi S.pi_equivariant (Work.GroupCohomology.H1π G B b) := by
      rw [Work.GroupCohomology.mapH1_H1π, hb]
    have hmem : Work.GroupCohomology.mapH1 G S.pi S.pi_equivariant
        (Work.GroupCohomology.H1π G B b) ∈ S.deltaH1.ker := by
      rw [← range_mapH1_eq_ker_deltaH1 S]
      exact AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hx]
    exact AddMonoidHom.mem_ker.mp hmem

end Work.GroupCohomology
