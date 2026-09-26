import Mathlib
import Submission.Work.Drive.strip_cover_defs
import Submission.Work.Drive.trisecant_defs
import Submission.Work.Drive.exists_pathConnected_trace_in_trisecantSet
import Submission.Work.Drive.exists_isOpen_injOn_nhds_stripClass
import Submission.Work.Drive.isOpenMap_stripClass
import Submission.Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds

/-!
# Components of the lifted trisecant locus are path connected

`Work.Drive.isPathConnected_component_liftedTrisecant`: for a smooth knot `r` which is
quadrisecant-free and in transverse general position, every connected component of the lifted
trisecant locus `A = liftedTrisecant r ⊆ ℝ × (0, period)` is path connected.

The argument is Kuperberg's local structure of the trisecant locus transported through the
universal cover `stripClass : ℝ × (0, period) → OpenMobius`, `p ↦ {K p.1, K (p.1 + p.2)}` of
the band of secants:

* `A` is the preimage of Kuperberg's set `O = trisecantSet r` under `stripClass`;
* `O` is locally path connected in the strong (shrinking) form
  `exists_pathConnected_trace_in_trisecantSet`: for every open `V ∋ c` there is an open `W`
  with `c ∈ W ⊆ V` such that the trace `O ∩ W` is path connected.  (Under the hood: the
  interval charts of `O` of `Submission/ComponentChart.lean`; the trace form is what survives
  the passage to the cover, because `O` itself need not be open in the band.)
* the cover is locally injective on the strip (`exists_isOpen_injOn_nhds_stripClass`) and open
  (`isOpenMap_stripClass`), so over a small open `B ∋ p` the cover is a homeomorphism onto the
  open set `stripClass '' B` (`Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`).

Given `z ∈ A`, choose such a `B` and `W` with `c := stripClass z ∈ W ⊆ stripClass '' B` and
`O ∩ W` path connected.  The set `U := {p' ∈ A | p' ∈ B, stripClass p' ∈ W}` is an open
neighbourhood of `z` in `A`, and it is the continuous image of the path-connected `O ∩ W`
(via the inverse of the cover on `B`), hence path connected.  Every point of `A` therefore has
an open path-connected neighbourhood in `A`, and the generic engine
`isPathConnected_of_isConnected_of_open_pathConnected_nhds` (a connected component, every point
of which carries such a neighbourhood, is path connected) finishes.
-/

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

noncomputable section

namespace Work.Drive

set_option maxHeartbeats 1600000

/-! ## The strip and its covering map -/

lemma isOpen_stripSet : IsOpen {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < period} :=
  (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)

lemma continuous_stripClass : Continuous (stripClass : StripPeriod → OpenMobius) :=
  continuous_stripSecantClass

/-! ## Points of `A` have open path-connected neighbourhoods in `A` -/

theorem exists_pathConnected_nhds_in_liftedTrisecant {r : ℝ → Space}
    (hr : IsSmoothKnot r) (hq : QuadrisecantFree r)
    (hg : TorusGeneralPositionTransverse r)
    (z : ℝ × ℝ) (hz : z ∈ liftedTrisecant r) :
    ∃ U : Set (↥(liftedTrisecant r)), IsOpen U ∧
      (⟨z, hz⟩ : ↥(liftedTrisecant r)) ∈ U ∧ IsPathConnected U := by
  classical
  obtain ⟨hz0, hz1, hzc⟩ := mem_liftedTrisecant_iff.mp hz
  let Z : StripPeriod := ⟨z, hz0, hz1⟩
  obtain ⟨B, hBopen, hZB, hBinj⟩ := exists_isOpen_injOn_nhds_stripClass Z
  -- the covering map restricted to `B`
  let g : ↥B → OpenMobius := fun p => stripClass p.1
  have hgc : Continuous g := by
    show Continuous fun p : ↥B => stripSecantClass p.1.1 p.1.2.1 p.1.2.2
    exact continuous_stripSecantClass.comp continuous_subtype_val
  have hginj : Function.Injective g := fun p q hpq => Subtype.ext (hBinj p.2 q.2 hpq)
  have hgopen : IsOpenMap g := by
    have h1 : IsOpenMap (Subtype.val : ↥B → StripPeriod) := hBopen.isOpenEmbedding_subtypeVal.isOpenMap
    exact isOpenMap_stripClass.comp h1
  have hemb : Topology.IsOpenEmbedding g :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hgc hginj hgopen
  have hVopen : IsOpen (Set.range g) := hemb.isOpen_range
  let e : ↥B ≃ₜ ↥(Set.range g) := hemb.isEmbedding.toHomeomorph
  have hcV : stripClass Z ∈ Set.range g := ⟨⟨Z, hZB⟩, rfl⟩
  obtain ⟨W, hWopen, hcW, hWV, hWpc⟩ :=
    exists_pathConnected_trace_in_trisecantSet hr hq hg hzc hVopen hcV
  -- the trace pulls back to a path-connected subset of `↥B`
  let T : Set ↥B := {p | g p ∈ trisecantSet r ∩ W}
  have hWsub : trisecantSet r ∩ W ⊆ Set.range g := (Set.inter_subset_right).trans hWV
  have hTpc : IsPathConnected T := by
    have hpre : IsPathConnected (Subtype.val ⁻¹' (trisecantSet r ∩ W) : Set ↥(Set.range g)) :=
      IsPathConnected.preimage_coe hWpc hWsub
    have himg : IsPathConnected (e.symm '' (Subtype.val ⁻¹' (trisecantSet r ∩ W))) :=
      hpre.image e.symm.continuous
    have heq : e.symm '' (Subtype.val ⁻¹' (trisecantSet r ∩ W)) = T := by
      rw [Homeomorph.image_symm]
      ext p
      exact Iff.rfl
    rwa [heq] at himg
  -- the corresponding subset of `A`
  let ψ : ↥T → ↥(liftedTrisecant r) := fun p =>
    ⟨p.1.1.1, ⟨p.1.1.2.1, p.1.1.2.2, p.2.1⟩⟩
  have hψcont : Continuous ψ := by
    apply Continuous.subtype_mk
    show Continuous fun p : ↥T => (p.1.1.1 : ℝ × ℝ)
    fun_prop
  let U : Set (↥(liftedTrisecant r)) := Set.range ψ
  have hBval_open : IsOpen (Set.range (fun p : ↥B => (p.1.1 : ℝ × ℝ))) := by
    have h1 : Topology.IsOpenEmbedding (fun p : ↥B => (p.1.1 : ℝ × ℝ)) :=
      (isOpen_stripSet.isOpenEmbedding_subtypeVal).comp hBopen.isOpenEmbedding_subtypeVal
    simpa [Set.image_univ] using h1.isOpenMap Set.univ isOpen_univ
  have hWval_open : IsOpen ((Subtype.val : StripPeriod → ℝ × ℝ) '' (stripClass ⁻¹' W)) :=
    isOpen_stripSet.isOpenEmbedding_subtypeVal.isOpenMap _ (hWopen.preimage continuous_stripClass)
  have hUeq : Set.range ψ = Subtype.val ⁻¹' (Set.range (fun p : ↥B => (p.1.1 : ℝ × ℝ)) ∩
      ((Subtype.val : StripPeriod → ℝ × ℝ) '' (stripClass ⁻¹' W))) := by
    ext p
    constructor
    · rintro ⟨⟨b, hbT⟩, rfl⟩
      refine ⟨⟨b, rfl⟩, ?_⟩
      exact ⟨b.1, (show stripClass b.1 ∈ W from (hbT : g b ∈ trisecantSet r ∩ W).2), rfl⟩
    · rintro ⟨⟨b, hb⟩, s, hsW, hsv⟩
      have hbs : b.1 = s := Subtype.ext (hb.trans hsv.symm)
      have hbA : b.1.1 ∈ liftedTrisecant r := by
        rw [show b.1.1 = p.1 from hb]; exact p.2
      have hbT : b ∈ T := by
        show g b ∈ trisecantSet r ∩ W
        obtain ⟨k0, k1, hk⟩ := mem_liftedTrisecant_iff.mp hbA
        refine ⟨?_, ?_⟩
        · show stripSecantClass b.1.1 b.1.2.1 b.1.2.2 ∈ trisecantSet r
          rw [stripSecantClass_congr k0 b.1.2.1 k1 b.1.2.2]
          exact hk
        · show stripClass b.1 ∈ W
          rw [show stripClass b.1 = stripClass s from by rw [hbs]]
          exact hsW
      refine ⟨⟨b, hbT⟩, ?_⟩
      exact Subtype.ext hb
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [show U = Set.range ψ from rfl, hUeq]
    exact (hBval_open.inter hWval_open).preimage continuous_subtype_val
  · refine ⟨⟨⟨Z, hZB⟩, ?_⟩, ?_⟩
    · show g ⟨Z, hZB⟩ ∈ trisecantSet r ∩ W
      exact ⟨hzc, hcW⟩
    · exact Subtype.ext rfl
  · haveI : PathConnectedSpace ↥T := isPathConnected_iff_pathConnectedSpace.mp hTpc
    exact isPathConnected_range hψcont

/-! ## The theorem -/

theorem isPathConnected_component_liftedTrisecant {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hq : LeanEval.KnotTheory.Quadrisecant.QuadrisecantFree r)
    (hg : LeanEval.KnotTheory.Quadrisecant.TorusGeneralPositionTransverse r) :
    ∀ z : ℝ × ℝ, z ∈ LeanEval.KnotTheory.Quadrisecant.liftedTrisecant r →
      IsPathConnected (connectedComponentIn (LeanEval.KnotTheory.Quadrisecant.liftedTrisecant r) z) := by
  intro z hz
  have hs : IsPathConnected
      (connectedComponent (⟨z, hz⟩ : ↥(liftedTrisecant r)) : Set ↥(liftedTrisecant r)) := by
    refine Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds
      (isConnected_connectedComponent) ?_
    intro x hx
    obtain ⟨U, hUopen, hxU, hUpc⟩ := exists_pathConnected_nhds_in_liftedTrisecant hr hq hg x.1 x.2
    refine ⟨U, hUopen, hxU, hUpc, ?_⟩
    intro y hy
    have h1 : y ∈ connectedComponent x :=
      (hUpc.isConnected.isPreconnected).subset_connectedComponent hxU hy
    rwa [← connectedComponent_eq (x := (⟨z, hz⟩ : ↥(liftedTrisecant r))) hx] at h1
  rw [connectedComponentIn_eq_image hz]
  exact hs.image continuous_subtype_val

end Work.Drive
