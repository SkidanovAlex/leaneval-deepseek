import Mathlib
import Submission.Work.GroupCohomology.Connecting
import Submission.Work.GroupCohomology.ShortExact
import Submission.Work.GroupCohomology.H2pi_eq_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- The connecting map `H¹(G, C) → H²(G, A)` of a short exact sequence is additive: since
`deltaCocycle` is defined by choosing arbitrary lifts of `1`-cocycles along the surjection
`pi`, the difference `deltaCocycle (c + c') - deltaCocycle c - deltaCocycle c'` need not vanish
on the nose, but it *is* a coboundary: the difference of the chosen lifts
`liftCochain (c + c') - liftCochain c - liftCochain c'` takes values in `ker pi = im iota`,
so pulling back along `iota` exhibits the difference as `d¹ w` for a `1`-cochain `w`, and
`simp [H2pi_eq_iff]`-style reasoning then gives additivity in `H²`. -/
theorem deltaCocycle_add {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : Work.GroupCohomology.ShortExactSeq G A B C)
    (c c' : Work.GroupCohomology.Z1 G C) :
    Work.GroupCohomology.H2π G A (S.deltaCocycle (c + c')) =
      Work.GroupCohomology.H2π G A (S.deltaCocycle c) +
        Work.GroupCohomology.H2π G A (S.deltaCocycle c') := by
  rw [← AddMonoidHom.map_add]
  rw [H2pi_eq_iff]
  -- Choose lifts of `c`, `c'` and `c + c'` along the surjection `pi`.
  set b'' : G → B := S.liftCochain ((c + c' : Z1 G C) : G → C) with hb''
  set b : G → B := S.liftCochain (c : G → C) with hb
  set b' : G → B := S.liftCochain (c' : G → C) with hb'
  -- The difference of the lifts lands in `ker pi`.
  have hker : ∀ g : G, b'' g - b g - b' g ∈ S.pi.ker := by
    intro g
    rw [AddMonoidHom.mem_ker, map_sub, map_sub, hb'', hb, hb',
      S.pi_liftCochain, S.pi_liftCochain, S.pi_liftCochain, AddSubgroup.coe_add, Pi.add_apply]
    abel
  -- Pull it back along the inclusion `iota`.
  set w : G → A := fun g => S.preimage (b'' g - b g - b' g) (hker g) with hw
  have hwi : ∀ g : G, S.iota (w g) = b'' g - b g - b' g := by
    intro g
    simp only [hw]
    exact S.iota_preimage _ (hker g)
  refine (mem_B2_iff G A _).mpr ⟨w, ?_⟩
  -- It remains to show `d¹ w = deltaCocycle (c + c') - (deltaCocycle c + deltaCocycle c')`.
  funext p
  obtain ⟨g, h⟩ := p
  apply S.iota_injective
  have hL : S.iota (d1 G A w (g, h))
      = d1 G B b'' (g, h) - (d1 G B b (g, h) + d1 G B b' (g, h)) := by
    rw [d1_apply, map_add, map_sub, S.iota_equivariant]
    simp only [hwi, smul_sub, d1_apply]
    abel
  have hR : S.iota ((↑(S.deltaCocycle (c + c') - (S.deltaCocycle c + S.deltaCocycle c')
        : Z2 G A) : G × G → A) (g, h))
      = d1 G B b'' (g, h) - (d1 G B b (g, h) + d1 G B b' (g, h)) := by
    have hce : ((↑(S.deltaCocycle (c + c') - (S.deltaCocycle c + S.deltaCocycle c')
        : Z2 G A) : G × G → A) (g, h))
        = (↑(S.deltaCocycle (c + c')) : G × G → A) (g, h)
          - ((↑(S.deltaCocycle c) : G × G → A) (g, h)
              + (↑(S.deltaCocycle c') : G × G → A) (g, h)) := by
      simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, Pi.sub_apply, Pi.add_apply]
    rw [hce, map_sub, map_add, S.iota_deltaCocycle (c + c') g h, S.iota_deltaCocycle c g h,
      S.iota_deltaCocycle c' g h]
  exact hL.trans hR.symm

end Work.GroupCohomology
