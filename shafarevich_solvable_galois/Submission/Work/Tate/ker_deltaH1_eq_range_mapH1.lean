import Mathlib
import Submission.Work.GroupCohomology.ConnectingMap
import Submission.Work.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exactness of `H¹(G, B) → H¹(G, C) → H²(G, A)`

For a short exact sequence of `G`-modules `0 → A --iota--> B --pi--> C → 0` with connecting map
`δ¹ : H¹(G, C) → H²(G, A)` (`Work.GroupCohomology.ShortExactSeq.deltaH1`), the connecting map
kills exactly the classes coming from `H¹(G, B)`:

`S.deltaH1.ker = (mapH1 G S.pi S.pi_equivariant).range`.

Both inclusions are computed on representatives.

* A cocycle of `C` of the form `pi ∘ b` with `b` a cocycle of `B` has vanishing connecting
  image: if `L` lifts `pi ∘ b` along `pi`, then `L - b` takes values in `ker pi = im iota`, say
  `L - b = iota ∘ a`; since `d¹ b = 0` one gets `iota (δ c) = d¹ L = d¹ (iota ∘ a) = iota (d¹ a)`,
  so `δ c = d¹ a` is a coboundary (`deltaCocycle_mapZ1_pi_eq_zero`).

* Conversely, if `δ c ∈ B²`, say `δ c = d¹ a`, then `b := L - iota ∘ a` is a `1`-cocycle of `B`
  (because `d¹ b = d¹ L - iota (d¹ a) = iota (δ c) - iota (δ c) = 0`) projecting onto `c`
  (`exists_mapZ1_pi_eq_of_deltaCocycle_eq_zero`).

Consequently the class of `c` lies in the image of `mapH1 G S.pi S.pi_equivariant`.
-/

namespace Work.Tate

variable {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
  [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
  [DistribMulAction G C]

/-- **`range mapH1(π) ⊆ ker δ¹`.**  The connecting image of a cocycle of `C` that is the image
under `π` of a cocycle of `B` is a `2`-coboundary. -/
theorem deltaCocycle_mapZ1_pi_eq_zero (S : Work.GroupCohomology.ShortExactSeq G A B C)
    (b : Work.GroupCohomology.Z1 G B) :
    Work.GroupCohomology.H2π G A
      (S.deltaCocycle (Work.GroupCohomology.mapZ1 G S.pi S.pi_equivariant b)) = 0 := by
  set c : Work.GroupCohomology.Z1 G C :=
    Work.GroupCohomology.mapZ1 G S.pi S.pi_equivariant b with hc
  have hmem : ((S.deltaCocycle c : Work.GroupCohomology.Z2 G A) : G × G → A) ∈
      Work.GroupCohomology.B2 G A := by
    rw [Work.GroupCohomology.mem_B2_iff]
    set L : G → B := S.liftCochain (c : G → C) with hL
    have hcval : ∀ g : G, (c : G → C) g = S.pi ((b : G → B) g) := by
      intro g
      rw [hc]
      rfl
    have hker : ∀ g : G, L g - (b : G → B) g ∈ S.pi.ker := by
      intro g
      rw [hL, AddMonoidHom.mem_ker, map_sub, S.pi_liftCochain, hcval g, sub_self]
    refine ⟨fun g => S.preimage (L g - (b : G → B) g) (hker g), ?_⟩
    have hw : Work.GroupCohomology.mapCochain1 G S.iota
        (fun g => S.preimage (L g - (b : G → B) g) (hker g)) = L - (b : G → B) := by
      funext g
      rw [Work.GroupCohomology.mapCochain1_apply]
      exact S.iota_preimage _ (hker g)
    have hstep : ∀ g h : G, S.iota ((Work.GroupCohomology.d1 G A
        (fun g => S.preimage (L g - (b : G → B) g) (hker g))) (g, h)) =
        (Work.GroupCohomology.d1 G B) (L - (b : G → B)) (g, h) := by
      intro g h
      rw [← Work.GroupCohomology.mapCochain2_apply,
        Work.GroupCohomology.mapCochain2_d1 G S.iota S.iota_equivariant, hw]
    funext p
    obtain ⟨g, h⟩ := p
    apply S.iota_injective
    rw [S.iota_deltaCocycle c g h, hstep g h]
    have hb1 : (Work.GroupCohomology.d1 G B) (b : G → B) = 0 := by
      rw [← AddMonoidHom.mem_ker, ← Work.GroupCohomology.Z1_eq_ker_d1 (G := G) (A := B)]
      exact b.2
    rw [hL, map_sub, hb1, sub_zero]
  have h0 : Work.GroupCohomology.H2π G A (S.deltaCocycle c) =
      Work.GroupCohomology.H2π G A (0 : Work.GroupCohomology.Z2 G A) :=
    (Work.GroupCohomology.H2pi_eq_iff _ _).mpr (by simpa using hmem)
  rw [h0, map_zero]

/-- **`ker δ¹ ⊆ range mapH1(π)`.**  A cocycle of `C` whose connecting image vanishes is the
image under `π` of a cocycle of `B`. -/
theorem exists_mapZ1_pi_eq_of_deltaCocycle_eq_zero
    (S : Work.GroupCohomology.ShortExactSeq G A B C) (c : Work.GroupCohomology.Z1 G C)
    (hc : Work.GroupCohomology.H2π G A (S.deltaCocycle c) = 0) :
    ∃ b : Work.GroupCohomology.Z1 G B,
      Work.GroupCohomology.mapZ1 G S.pi S.pi_equivariant b = c := by
  have hmem : ((S.deltaCocycle c : Work.GroupCohomology.Z2 G A) : G × G → A) ∈
      Work.GroupCohomology.B2 G A := by
    have h := (Work.GroupCohomology.H2pi_eq_iff (S.deltaCocycle c)
      (0 : Work.GroupCohomology.Z2 G A)).mp (by simpa using hc)
    simpa using h
  obtain ⟨a, ha⟩ := (Work.GroupCohomology.mem_B2_iff G A _).mp hmem
  set L : G → B := S.liftCochain (c : G → C) with hL
  have hcross : (L - Work.GroupCohomology.mapCochain1 G S.iota a) ∈
      Work.GroupCohomology.Z1 G B := by
    rw [Work.GroupCohomology.Z1_eq_ker_d1 (G := G) (A := B), AddMonoidHom.mem_ker, map_sub]
    have h1 : Work.GroupCohomology.mapCochain2 G S.iota (Work.GroupCohomology.d1 G A a)
        = (Work.GroupCohomology.d1 G B) L := by
      funext p
      obtain ⟨g, h⟩ := p
      rw [Work.GroupCohomology.mapCochain2_apply, congrFun ha (g, h), hL]
      exact S.iota_deltaCocycle c g h
    rw [← h1, ← Work.GroupCohomology.mapCochain2_d1 G S.iota S.iota_equivariant a, sub_self]
  refine ⟨⟨L - Work.GroupCohomology.mapCochain1 G S.iota a, hcross⟩, ?_⟩
  apply Subtype.ext
  funext g
  show S.pi ((L - Work.GroupCohomology.mapCochain1 G S.iota a) g) = (c : G → C) g
  rw [Pi.sub_apply, Work.GroupCohomology.mapCochain1_apply, hL, map_sub, S.pi_liftCochain,
    S.pi_iota, sub_zero]

theorem ker_deltaH1_eq_range_mapH1 {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : Work.GroupCohomology.ShortExactSeq G A B C) :
    S.deltaH1.ker = (Work.GroupCohomology.mapH1 G S.pi S.pi_equivariant).range := by
  refine le_antisymm ?_ ?_
  · -- `ker δ¹ ⊆ range mapH1(π)`: a class killed by `δ¹` comes from `H¹(G,B)`
    intro y hy
    have hy' : S.deltaH1 y = 0 := (AddMonoidHom.mem_ker).mp hy
    refine (AddMonoidHom.mem_range).mpr ?_
    revert hy'
    induction y using Work.GroupCohomology.H1_induction_on with
    | h c =>
      intro hy'
      rw [S.deltaH1_H1π] at hy'
      obtain ⟨b, hb⟩ := exists_mapZ1_pi_eq_of_deltaCocycle_eq_zero S c hy'
      exact ⟨Work.GroupCohomology.H1π G B b,
        by rw [Work.GroupCohomology.mapH1_H1π, hb]⟩
  · -- `range mapH1(π) ⊆ ker δ¹`: the connecting image of a class coming from `B` vanishes
    intro y hy
    obtain ⟨x, rfl⟩ := (AddMonoidHom.mem_range).mp hy
    refine (AddMonoidHom.mem_ker).mpr ?_
    induction x using Work.GroupCohomology.H1_induction_on with
    | h b =>
      rw [Work.GroupCohomology.mapH1_H1π, S.deltaH1_H1π]
      exact deltaCocycle_mapZ1_pi_eq_zero S b

end Work.Tate
