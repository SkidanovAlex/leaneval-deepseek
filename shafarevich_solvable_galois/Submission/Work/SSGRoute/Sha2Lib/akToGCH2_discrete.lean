import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.SSGRoute.PT.e1aBetaCan_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two cohomology models coincide for discrete groups

`Work.AbsoluteKummer.H2 G M` (locally constant `2`-cocycles modulo coboundaries of locally
constant `1`-cochains) and `Work.GroupCohomology.H2 G M` (all `2`-cocycles modulo coboundaries of
arbitrary `1`-cochains) are the two models used throughout the `SSGRoute` development;
`Work.SSGRoute.PT.akToGCH2` is the forgetful map between them.

The E1a/E9 lanes use, implicitly everywhere, that **for a discrete group `G` the two models
coincide**: `C¹_c = C²_c = ⊤` (every function on a discrete space is locally constant), hence
`Z²_c = Z²` and `B²_c = B²`, hence `AbsoluteKummer.H2 = GroupCohomology.H2` and `akToGCH2` is the
identity.  This is what makes the *finite* levels `D_w = Gal(K_w/k_v)`, `Gal(L/k)`, … computable in
whichever model is convenient.  This file proves the four subgroup equalities and the resulting
bijectivity of `akToGCH2`.

(For the profinite `D_A = decomp k A` the map is *not* an isomorphism; its injectivity is the E1a
lane's node `PT.akToGCH2_injective_decompFin`, analysed in
`Submission/Work/SSGRoute/Sha2Lib/NOTE_akToGCH2_injective.md`.)
-/

namespace Work.SSGRoute.Sha2Lib

open Work.AbsoluteKummer

variable {G : Type} [TopologicalSpace G] [Group G] {M : Type} [AddCommGroup M]
  [DistribMulAction G M]

/-- On a discrete space every function is locally constant (in the workspace's sense,
`Work.AbsoluteKummer.IsLocallyConstant`). -/
theorem isLocallyConstant_of_discrete {X : Type} [TopologicalSpace X] [DiscreteTopology X]
    {N : Type} (f : X → N) : AbsoluteKummer.IsLocallyConstant f := by
  intro x
  exact ⟨{x}, isOpen_discrete {x}, by simp, fun y hy => by
    rw [Set.mem_singleton_iff] at hy; rw [hy]⟩

/-- The locally constant `1`-cochains are all the `1`-cochains when `G` is discrete. -/
theorem C1c_eq_top [DiscreteTopology G] : C1c G M = ⊤ := by
  ext f
  simp only [AddSubgroup.mem_top, iff_true]
  exact isLocallyConstant_of_discrete f

/-- The locally constant `2`-cochains are all the `2`-cochains when `G` is discrete. -/
theorem C2c_eq_top [DiscreteTopology G] : C2c G M = ⊤ := by
  ext f
  simp only [AddSubgroup.mem_top, iff_true]
  exact isLocallyConstant_of_discrete f

/-- For a discrete group the continuous and the abstract `2`-cocycles coincide. -/
theorem Z2_eq [DiscreteTopology G] : Z2 G M = Work.GroupCohomology.Z2 G M := by
  rw [Z2, C2c_eq_top, inf_top_eq]

/-- For a discrete group the continuous and the abstract `2`-coboundaries coincide. -/
theorem B2_eq [DiscreteTopology G] : B2 G M = Work.GroupCohomology.B2 G M := by
  rw [B2, C1c_eq_top, Work.GroupCohomology.B2]
  ext f
  constructor
  · rintro ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, trivial, rfl⟩

/-- **For a discrete group the two cohomology models agree**: `akToGCH2` is an isomorphism. -/
theorem akToGCH2_bijective [DiscreteTopology G] :
    Function.Bijective (Work.SSGRoute.PT.akToGCH2 G M) := by
  have hZ : (Z2 G M : AddSubgroup (G × G → M)) = Work.GroupCohomology.Z2 G M := Z2_eq
  have hB : (B2 G M : AddSubgroup (G × G → M)) = Work.GroupCohomology.B2 G M := B2_eq
  have hπc : ∀ z : ↥(Z2 G M), QuotientAddGroup.mk z = H2π G M z := fun z => by
    rw [H2π, QuotientAddGroup.mk'_apply]
  have hπg : ∀ z : ↥(Work.GroupCohomology.Z2 G M),
      QuotientAddGroup.mk z = Work.GroupCohomology.H2π G M z := fun z => by
    rw [Work.GroupCohomology.H2π, QuotientAddGroup.mk'_apply]
  constructor
  · -- injectivity: a locally constant cocycle whose *abstract* class vanishes is a continuous
    -- coboundary, because `B²_c = B²` for discrete `G`
    intro x y hxy
    induction x using QuotientAddGroup.induction_on with
    | H zx =>
      induction y using QuotientAddGroup.induction_on with
      | H zy =>
        rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_comap]
        have h : Work.SSGRoute.PT.akToGCH2 G M (H2π G M zx)
            = Work.SSGRoute.PT.akToGCH2 G M (H2π G M zy) := by
          rw [← hπc zx, ← hπc zy]; exact hxy
        rw [Work.SSGRoute.PT.akToGCH2_H2π, Work.SSGRoute.PT.akToGCH2_H2π,
          Work.GroupCohomology.H2pi_eq_iff] at h
        have h' : ((zx : G × G → M) - (zy : G × G → M)) ∈ Work.GroupCohomology.B2 G M := by
          simpa [Work.SSGRoute.PT.akZ2ToGCZ2_coe] using h
        rw [hB]
        simpa using h'
  · -- surjectivity: every abstract cocycle is locally constant for discrete `G`
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H c =>
      have hmemZ : ((c : G × G → M)) ∈ Z2 G M := hZ.symm ▸ c.2
      refine ⟨H2π G M ⟨(c : G × G → M), hmemZ⟩, ?_⟩
      have h : Work.SSGRoute.PT.akToGCH2 G M (H2π G M ⟨(c : G × G → M), hmemZ⟩)
          = Work.GroupCohomology.H2π G M c := by
        rw [Work.SSGRoute.PT.akToGCH2_H2π, Work.GroupCohomology.H2pi_eq_iff]
        simp [Work.SSGRoute.PT.akZ2ToGCZ2_coe]
      rw [h, hπg c]

end Work.SSGRoute.Sha2Lib
