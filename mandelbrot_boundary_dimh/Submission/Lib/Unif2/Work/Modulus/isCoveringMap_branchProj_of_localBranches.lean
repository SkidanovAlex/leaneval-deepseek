import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusDefs
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.coveringAux
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.isCoveringMap_branchProj

namespace Work.Modulus

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option warn.classDefReducibility false

set_option linter.style.haveILetI false

noncomputable section

open Filter Set

open Work.Modulus.BranchCovering.Aux

/-- **The projection of the modulus bundle is a covering space, as soon as local branches exist.**

This is `Work.Modulus.BranchCovering.isCoveringMap_branchProj` with its only non-local hypothesis
`Submission.HasGreenFunctionE z₀ E` replaced by the *local* input the proof actually uses: on a chart ball
around every point there is a branch `Φ` of the modulus `exp (-E)` whose pair `(Φ, chartDeriv Φ)` never
vanishes.

Verbally: the bundle `Work.SC.ModulusBundle z₀ E → Y` (points: the branches of the multivalued modulus
`exp (-(E + iE*))`, encoded over the pole by the chart derivative) is a covering space.  The proof is the
one in `Submission/Work/Modulus/BranchCovering/isCoveringMap_branchProj.lean`, verbatim: pick the model
branch `Φ₀` on the chart ball `B` around `x` supplied by `hloc x`; every branch near a point of `B` is a
constant multiple `c Φ₀` with `‖c‖ = 1` (off the pole by local constancy of the ratio,
`Aux.exists_ratio_eventually_of_isModulusBranch_of_ne`, at the pole by the identity theorem,
`Aux.exists_ratio_eventually_of_isModulusBranch_at_pole`); the constant `c` is recovered from the pair
`(Φ, Φ')` by `Aux.pointLabel`, giving the trivialization `branchProj ⁻¹' B ≃ₜ B × DiscCircle` with
`DiscCircle` discrete.  The only change needed is that the model branch is now the input `hloc x` rather
than `Aux.exists_isModulusBranch_chartBall (z₀ := z₀) hE x`. -/
theorem isCoveringMap_branchProj_of_localBranches {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [ConnectedSpace Y] [SecondCountableTopology Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y] {z₀ : Y} {E : Y → ℝ}
    (hloc : ∀ x : Y, ∃ (ρ : ℝ) (Φ : Y → ℂ), 0 < ρ ∧
      Work.SC.IsModulusBranch z₀ E (Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ) Φ ∧
      (∀ y ∈ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ,
        Φ y ≠ 0 ∨ Work.SC.chartDeriv Φ y ≠ 0)) :
    @IsCoveringMap (Work.SC.ModulusBundle z₀ E) Y (Work.SC.modulusBundleTopology z₀ E) _
      (Work.SC.branchProj z₀ E) := by
  classical
  letI : TopologicalSpace (Y × ℂ × ℂ) := Work.SC.branchTopology z₀ E
  intro x
  -- a model branch on a chart ball around `x`, supplied by the local hypothesis
  obtain ⟨ρ, Φ₀, hρ, hbr, hnd⟩ := hloc x
  let B : Set Y := Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ
  have hBopen : IsOpen B := Submission.chartBall_isOpen (chartAt ℂ x) ((chartAt ℂ x) x) ρ
  have hxmem : x ∈ B := ⟨mem_chart_source ℂ x, Metric.mem_ball_self hρ⟩
  -- restate the model data in terms of `B`
  have hbrB : Work.SC.IsModulusBranch z₀ E B Φ₀ := hbr
  have hndB : ∀ y ∈ B, Φ₀ y ≠ 0 ∨ Work.SC.chartDeriv Φ₀ y ≠ 0 := hnd
  -- (1) the fibre over `x` is discrete
  have hdisc : DiscreteTopology ↥(Work.SC.branchProj z₀ E ⁻¹' {x}) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro p
    obtain ⟨V, Ψ, hbrΨ, hyV, hval, hder⟩ := (p : Work.SC.ModulusBundle z₀ E).2
    have hset : ({p} : Set ↥(Work.SC.branchProj z₀ E ⁻¹' {x})) =
        (Subtype.val : ↥(Work.SC.branchProj z₀ E ⁻¹' {x}) → Work.SC.ModulusBundle z₀ E) ⁻¹'
          ((Subtype.val : Work.SC.ModulusBundle z₀ E → Y × ℂ × ℂ) ⁻¹'
            Work.SC.branchGraph V Ψ) := by
      ext q
      constructor
      · intro hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        exact ⟨hyV, hval, hder⟩
      · intro hq
        rw [Set.mem_singleton_iff]
        have hqmem : (q : Work.SC.ModulusBundle z₀ E).1.1 = x := Set.mem_singleton_iff.mp q.2
        have hpmem : (p : Work.SC.ModulusBundle z₀ E).1.1 = x := Set.mem_singleton_iff.mp p.2
        apply Subtype.ext
        apply Subtype.ext
        refine Prod.ext (hqmem.trans hpmem.symm) (Prod.ext ?_ ?_)
        · rw [hq.2.1, hval, hqmem, hpmem]
        · rw [hq.2.2, hder, hqmem, hpmem]
    rw [hset]
    exact ((TopologicalSpace.isOpen_generateFrom_of_mem (g := Work.SC.branchFamily z₀ E)
      ⟨V, Ψ, hbrΨ, rfl⟩).preimage continuous_subtype_val).preimage continuous_subtype_val
  -- (2) the projection is continuous
  have hπcont : Continuous (Work.SC.branchProj z₀ E) := by
    rw [continuous_def]
    intro W hW
    rw [isOpen_iff_mem_nhds]
    intro p hp
    rw [show 𝓝 p = Filter.comap (Subtype.val : Work.SC.ModulusBundle z₀ E → Y × ℂ × ℂ)
        (𝓝 ((p : Work.SC.ModulusBundle z₀ E) : Y × ℂ × ℂ)) from nhds_induced _ _]
    rw [Filter.mem_comap]
    obtain ⟨V, Ψ, hbrΨ, hyV, hval, hder⟩ := (p : Work.SC.ModulusBundle z₀ E).2
    refine ⟨Work.SC.branchGraph (V ∩ W) Ψ, ?_, ?_⟩
    · exact (TopologicalSpace.isOpen_generateFrom_of_mem (g := Work.SC.branchFamily z₀ E)
        ⟨V ∩ W, Ψ, hbrΨ.mono (hbrΨ.1.inter hW) inter_subset_left, rfl⟩).mem_nhds
        ⟨⟨hyV, hp⟩, hval, hder⟩
    · intro q hq
      exact hq.1.2
  -- (3) the two halves of the trivialization
  let K : ↥B × DiscCircle → ↥(Work.SC.branchProj z₀ E ⁻¹' B) := fun q =>
    ⟨⟨canonPt Φ₀ q.1.1 q.2.val, canonPt_mem hbrB q.1.2 q.2.norm_val⟩, q.1.2⟩
  let H : ↥(Work.SC.branchProj z₀ E ⁻¹' B) → ↥B × DiscCircle := fun p =>
    (⟨p.1.1.1, p.2⟩, ⟨pointLabel Φ₀ p.1, norm_pointLabel hbrB hndB p.2⟩)
  have hleft : Function.LeftInverse K H := by
    intro p
    have h := canonPt_eq_pointLabel hbrB hndB (p := p.1) p.2
    apply Subtype.ext
    apply Subtype.ext
    show canonPt Φ₀ p.1.1.1 (pointLabel Φ₀ p.1) = p.1.1
    exact h.symm
  have hright : Function.RightInverse K H := by
    rintro ⟨y, c⟩
    refine Prod.ext ?_ ?_
    · exact Subtype.ext rfl
    · refine DiscCircle.ext_iff ?_
      show pointLabel Φ₀ (⟨canonPt Φ₀ y.1 c.val,
        canonPt_mem hbrB y.2 c.norm_val⟩ : Work.SC.ModulusBundle z₀ E) = c.val
      exact pointLabel_canonPt hbrB y.2 (hndB y.1 y.2) c.norm_val
  -- (4) continuity of the trivialization
  have hHcont : Continuous H := by
    refine Continuous.prodMk ?_ ?_
    · exact (hπcont.comp continuous_subtype_val).subtype_mk (fun p => p.2)
    · have hlc : IsLocallyConstant (fun p : ↥(Work.SC.branchProj z₀ E ⁻¹' B) =>
          (⟨pointLabel Φ₀ p.1, norm_pointLabel hbrB hndB p.2⟩ : DiscCircle)) := by
        intro s
        rw [isOpen_iff_mem_nhds]
        intro p hp
        have hnbd : (Subtype.val ⁻¹' sheet (z₀ := z₀) (E := E) Φ₀ B
            (pointLabel Φ₀ p.1)) ∈ 𝓝 p :=
          ((sheet_isOpen hbrB (norm_pointLabel hbrB hndB p.2)).preimage
            continuous_subtype_val).mem_nhds (mem_sheet_pointLabel hbrB hndB p.2)
        refine Filter.mem_of_superset hnbd ?_
        intro q hq
        have hq' : (⟨pointLabel Φ₀ q.1, norm_pointLabel hbrB hndB q.2⟩ : DiscCircle) =
            ⟨pointLabel Φ₀ p.1, norm_pointLabel hbrB hndB p.2⟩ :=
          DiscCircle.ext_iff (pointLabel_eq_of_mem_sheet hbrB hndB hq)
        rw [Set.mem_preimage] at hp
        rw [Set.mem_preimage, hq']
        exact hp
      exact hlc.continuous
  have hKcont : Continuous K := by
    refine continuous_prod_of_forall_snd (f := fun (y : ↥B) (c : DiscCircle) =>
      (⟨⟨canonPt Φ₀ y.1 c.val, canonPt_mem hbrB y.2 c.norm_val⟩,
        (by exact y.2 : Work.SC.branchProj z₀ E _ ∈ B)⟩ :
        ↥(Work.SC.branchProj z₀ E ⁻¹' B))) ?_
    intro c
    exact (continuous_canonPt hbrB hndB c.norm_val).subtype_mk (fun y => y.2)
  -- (5) assemble the even covering and pass to the fibre
  have hcov : IsEvenlyCovered (Work.SC.branchProj z₀ E) x DiscCircle := by
    refine ⟨inferInstance, B, hxmem, hBopen, hπcont.isOpen_preimage B hBopen, ?_, ?_⟩
    · exact ({ toFun := H, invFun := K, left_inv := hleft, right_inv := hright,
               continuous_toFun := hHcont, continuous_invFun := hKcont } :
        ↥(Work.SC.branchProj z₀ E ⁻¹' B) ≃ₜ ↥B × DiscCircle)
    · intro p
      rfl
  exact hcov.to_isEvenlyCovered_preimage

end

end Work.Modulus
