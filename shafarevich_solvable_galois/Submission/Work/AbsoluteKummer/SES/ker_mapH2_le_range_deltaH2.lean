import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.SES.ConnectingH2
import Submission.Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.SES

open Work.AbsoluteKummer

/-- **Exactness at `H²(G,M)` (the hard inclusion)**: the kernel of the map `H²(G,M) → H²(G,N)`
induced by `ι` is contained in the image of the connecting map `δ : H¹(G,P) → H²(G,M)`.

Given a continuous `2`-cocycle `c : G × G → M` whose image `ι ∘ c` is a coboundary,
say `ι (c (g,h)) = d¹ b (g,h)` for a locally constant cochain `b : G → N`, the cochain
`π ∘ b : G → P` is a continuous `1`-cocycle of `P`: the chosen lift `S.liftCochainC (π ∘ b)`
differs from `b` by `ι ∘ e` for a locally constant `e : G → M`, whence
`δ(π ∘ b) (g,h) = c (g,h) + d¹ e (g,h)`, so `[c] = δ [π ∘ b]`. -/
theorem ker_mapH2_le_range_deltaH2 {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P] (S : Work.AbsoluteKummer.ShortExactSeq G M N P) : (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker ≤ S.deltaH2.range := by
  intro x hx
  revert hx
  refine H2_induction_on x
    (C := fun y => y ∈ (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker →
      y ∈ S.deltaH2.range) ?_
  intro c hc
  rw [AddMonoidHom.mem_ker] at hc
  rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.H2π_eq_zero_iff,
    Work.AbsoluteKummer.mem_B2_iff] at hc
  obtain ⟨b, hbC, hb⟩ := hc
  -- `b : G → N` is a locally constant cochain with `d¹ b = ι ∘ c`.
  have hblc : IsLocallyConstant b := (mem_C1c_iff b).mp hbC
  have hbpoint : ∀ g h : G, Work.GroupCohomology.d1 G N b (g, h) =
      S.iota ((c : G × G → M) (g, h)) := by
    intro g h
    have h1 := congrFun hb (g, h)
    rwa [mapZ2_apply] at h1
  -- `π ∘ b` is a continuous `1`-cocycle of `P`.
  have hch : Work.GroupCohomology.IsCrossedHom G P (fun g : G => S.pi (b g)) := by
    intro g h
    show S.pi (b (g * h)) = g • S.pi (b h) + S.pi (b g)
    have h1 : g • S.pi (b h) - S.pi (b (g * h)) + S.pi (b g) = 0 := by
      have h0 : S.pi (Work.GroupCohomology.d1 G N b (g, h)) = 0 := by
        rw [hbpoint g h, S.pi_iota]
      rw [Work.GroupCohomology.d1_apply, map_add, map_sub, S.pi_equivariant g] at h0
      exact h0
    have h2 : g • S.pi (b h) + S.pi (b g) - S.pi (b (g * h)) = 0 := by
      rw [show g • S.pi (b h) + S.pi (b g) - S.pi (b (g * h)) =
        g • S.pi (b h) - S.pi (b (g * h)) + S.pi (b g) from by abel]
      exact h1
    exact (sub_eq_zero.mp h2).symm
  have halc : IsLocallyConstant (fun g : G => S.pi (b g)) := IsLocallyConstant.map S.pi hblc
  let a : Z1 G P :=
    ⟨fun g : G => S.pi (b g), mem_Z1_of hch halc⟩
  -- The chosen lift of `a = π ∘ b` differs from `b` by `ι ∘ e` with `e` locally constant.
  have hker : ∀ g : G, S.liftCochainC (a : G → P) g - b g ∈ S.pi.ker := by
    intro g
    rw [AddMonoidHom.mem_ker, map_sub, S.pi_liftCochainC]
    show S.pi (b g) - S.pi (b g) = 0
    rw [sub_self]
  let e : G → M := fun g => S.iotaInv (S.liftCochainC (a : G → P) g - b g)
  have he : ∀ g : G, S.iota (e g) = S.liftCochainC (a : G → P) g - b g := by
    intro g
    exact S.iota_iotaInv (S.mem_range_of_mem_ker (hker g))
  have helc : IsLocallyConstant e := by
    refine IsLocallyConstant.map S.iotaInv ?_
    exact (S.isLocallyConstant_liftCochainC (isLocallyConstant_of_mem_Z1 a.2)).sub hblc
  -- Key pointwise identity: `δ a = c + d¹ e`.
  have hkey : ∀ g h : G, (S.deltaCocycleC a : G × G → M) (g, h) =
      (c : G × G → M) (g, h) + Work.GroupCohomology.d1 G M e (g, h) := by
    intro g h
    apply S.iota_injective
    rw [S.iota_deltaCocycleC, map_add, ← hbpoint g h]
    have hf_eq : S.liftCochainC (a : G → P) = b + fun x : G => S.iota (e x) := by
      funext x
      show S.liftCochainC (a : G → P) x = b x + S.iota (e x)
      rw [he x]
      abel
    have hd1_iota : Work.GroupCohomology.d1 G N (fun x : G => S.iota (e x)) (g, h) =
        S.iota (Work.GroupCohomology.d1 G M e (g, h)) := by
      have hmap := congrFun
        (Work.GroupCohomology.mapCochain2_d1 G S.iota S.iota_equivariant e) (g, h)
      rw [Work.GroupCohomology.mapCochain2_apply] at hmap
      exact hmap.symm
    rw [hf_eq, map_add, Pi.add_apply, hd1_iota]
  -- Hence `δ a - c` is a continuous `2`-coboundary.
  have hmem : ((S.deltaCocycleC a - c : Z2 G M) : G × G → M) ∈ B2 G M := by
    refine (mem_B2_iff _).mpr ⟨e, (mem_C1c_iff e).mpr helc, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    rw [AddSubgroup.coe_sub, Pi.sub_apply, hkey g h]
    abel
  have hclass : H2π G M (S.deltaCocycleC a) = H2π G M c := by
    rw [H2π_eq_iff]
    exact hmem
  exact ⟨H1π G P a, by rw [S.deltaH2_H1π, hclass]⟩

end Work.AbsoluteKummer.SES
