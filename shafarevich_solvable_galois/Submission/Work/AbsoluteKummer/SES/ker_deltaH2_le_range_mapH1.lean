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

/-- **Exactness at `H²(G,M)`**: the kernel of the connecting map `δ¹ : H¹(G,P) → H²(G,M)` is
contained in the image of the map `H¹(G,N) → H¹(G,P)` induced by `π`.

Given a continuous `1`-cocycle `c : G → P` with `δc = 0`, the connecting cocycle
`δc = ι⁻¹ (d¹ b)` (where `b = liftCochainC c` is a lift of `c` along `π`) is a coboundary: there is
a locally constant `k : G → M` with `d¹ k = δc`.  The cochain `f = b - ι ∘ k : G → N` is then a
continuous `1`-cocycle with `π ∘ f = c`, so `[c] = mapH1 π [f]` lies in the image of `mapH1 π`. -/
theorem ker_deltaH2_le_range_mapH1 {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P] (S : Work.AbsoluteKummer.ShortExactSeq G M N P) : S.deltaH2.ker ≤ (Work.AbsoluteKummer.mapH1 S.pi S.pi_equivariant).range := by
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  revert hx
  induction x using H1_induction_on with
  | h c =>
    intro hx
    rw [S.deltaH2_H1π] at hx
    rw [H2π_eq_zero_iff, mem_B2_iff] at hx
    obtain ⟨k, hk_mem, hk_eq⟩ := hx
    set b : G → N := S.liftCochainC (c : G → P) with hb
    set f : G → N := fun g => b g - S.iota (k g) with hf
    have hk_lc : IsLocallyConstant (k : G → M) := (mem_C1c_iff k).mp hk_mem
    have hb_lc : IsLocallyConstant b := by
      rw [hb]; exact S.isLocallyConstant_liftCochainC (isLocallyConstant_of_mem_Z1 c.2)
    have hf_lc : IsLocallyConstant f := by
      rw [hf]; exact hb_lc.sub (IsLocallyConstant.map S.iota hk_lc)
    have hbpi : ∀ g : G, S.pi (b g) = (c : G → P) g := by
      intro g; rw [hb]; exact S.pi_liftCochainC (c : G → P) g
    have hf_eq : f = b - Work.GroupCohomology.mapCochain1 G S.iota (k : G → M) := by
      rw [hf]; funext g; rw [Pi.sub_apply, Work.GroupCohomology.mapCochain1_apply]
    have hb_eq : Work.GroupCohomology.d1 G N b =
        Work.GroupCohomology.mapCochain2 G S.iota (S.deltaCocycleC c : G × G → M) := by
      funext p
      obtain ⟨g, h⟩ := p
      rw [Work.GroupCohomology.mapCochain2_apply, hb]
      exact (S.iota_deltaCocycleC c g h).symm
    have hd1f : Work.GroupCohomology.d1 G N f = 0 := by
      rw [hf_eq, map_sub, hb_eq,
        ← Work.GroupCohomology.mapCochain2_d1 G S.iota S.iota_equivariant (k : G → M), hk_eq]
      abel
    have hf_cross : Work.GroupCohomology.IsCrossedHom G N f := by
      intro g h
      have hh := congrFun hd1f (g, h)
      rw [Work.GroupCohomology.d1_apply, Pi.zero_apply] at hh
      have hh2 : g • f h + f g - f (g * h) = 0 := by rw [← hh]; abel
      exact (sub_eq_zero.mp hh2).symm
    have hf_mem : f ∈ Work.AbsoluteKummer.Z1 G N := mem_Z1_of hf_cross hf_lc
    let F : Work.AbsoluteKummer.Z1 G N := ⟨f, hf_mem⟩
    have hpi_f : ∀ g : G, S.pi (f g) = (c : G → P) g := by
      intro g
      have hfg : f g = b g - S.iota (k g) := by rw [hf]
      rw [hfg, map_sub, S.pi_iota, sub_zero]
      exact hbpi g
    have hmap : Work.AbsoluteKummer.mapZ1 S.pi S.pi_equivariant F = c := by
      apply Subtype.ext
      funext g
      rw [Work.AbsoluteKummer.mapZ1_apply]
      exact hpi_f g
    refine AddMonoidHom.mem_range.mpr ⟨H1π G N F, ?_⟩
    rw [Work.AbsoluteKummer.mapH1_H1π, hmap]

end Work.AbsoluteKummer.SES
