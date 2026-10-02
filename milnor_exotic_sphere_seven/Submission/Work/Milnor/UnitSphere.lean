import Mathlib
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.mk_to_vk
import Submission.Work.Milnor.Collar
import Submission.Work.Milnor.ScaleDefs
import Submission.Work.Glue.glued_t2space

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The unit sphere bundle `{ν = 1}` of `ξ` and its identification with `Mk k`

The total space `Vk k` of the rank-`4` vector bundle `ξ` over `S⁴` carries the continuous fibre
norm `fibreNormFun k` (`Submission.Work.Milnor.Collar`), and the unit sphere bundle is the closed
subset `{p : Vk k | fibreNormFun k p = 1}`.

`Work.Milnor.mkToVkFun k : Mk k → Vk k` (`Submission.Work.Milnor.mk_to_vk`) includes the unit
sphere bundle of the `S³`-bundle into the unit sphere bundle of the vector bundle; here we prove

* `mem_range_mkToVkFun_iff`: its range is exactly `{ν = 1}`;
* `t2space_Vk`: `Vk k` is Hausdorff (the graph of the clutching map `vMap k` is closed, because
  `vMap k` blows up at the origin of the base);
* `continuous_mkToVkFun`: the inclusion `Mk k → Vk k` is continuous;
* `continuous_unitInv`: the chartwise inverse `unitInv` (normalise the fibre coordinate and read
  off the corresponding point of `Mk k`) is continuous — equivalently, `Mk k` and the unit sphere
  bundle of `ξ` are homeomorphic.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor
open Set

noncomputable section

/-! ## The graph of the clutching map is closed, and `Vk k` is Hausdorff -/

/-- The graph of `vMap k` over `vOpens = {x ≠ 0}` is closed in `MSpace8 × MSpace8`: on the graph
the product `‖z.1.1‖ * ‖z.2.1‖` is identically `1`, so a limit point cannot have `z.1.1 = 0`,
and away from the origin `vMap k` is continuous. -/
theorem graph_closed_vMap (k : ℤ) :
    IsClosed {z : MSpace8 × MSpace8 | z.1 ∈ (vOpens : Set MSpace8) ∧ vMap k z.1 = z.2} := by
  set S : Set (MSpace8 × MSpace8) :=
    {z : MSpace8 × MSpace8 | z.1 ∈ (vOpens : Set MSpace8) ∧ vMap k z.1 = z.2} with hS
  rw [← closure_subset_iff_isClosed]
  intro z hz
  have hcontF : Continuous (fun z : MSpace8 × MSpace8 => ‖z.1.1‖ * ‖z.2.1‖) := by fun_prop
  have hAclosed : IsClosed {z : MSpace8 × MSpace8 | 1 ≤ ‖z.1.1‖ * ‖z.2.1‖} :=
    isClosed_le continuous_const hcontF
  have hSA : S ⊆ {z : MSpace8 × MSpace8 | 1 ≤ ‖z.1.1‖ * ‖z.2.1‖} := by
    intro w hw
    rw [hS] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw1' : w.1.1 ≠ 0 := mem_vOpens.mp hw1
    have hw21 : w.2.1 = invBase w.1.1 := by rw [← hw2]; rfl
    change 1 ≤ ‖w.1.1‖ * ‖w.2.1‖
    rw [hw21, norm_invBase]
    exact le_of_eq (mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw1')).symm
  have hzA : 1 ≤ ‖z.1.1‖ * ‖z.2.1‖ := closure_minimal hSA hAclosed hz
  have hpos : 0 < ‖z.1.1‖ := by
    rcases eq_or_lt_of_le (norm_nonneg z.1.1) with h | h
    · rw [← h, zero_mul] at hzA
      linarith
    · exact h
  have hz1 : z.1.1 ≠ 0 := norm_pos_iff.mp hpos
  have hz1mem : z.1 ∈ (vOpens : Set MSpace8) := mem_vOpens.mpr hz1
  have hcontOn : ContinuousOn (vMap k) (vOpens : Set MSpace8) := (vMap_smooth k).1.continuousOn
  have hcat : ContinuousAt (vMap k) z.1 :=
    (hcontOn.continuousWithinAt hz1mem).continuousAt (vOpens.2.mem_nhds hz1mem)
  have hcont : ContinuousAt (fun w : MSpace8 × MSpace8 => (w.1, vMap k w.1)) z :=
    continuousAt_fst.prodMk (hcat.comp continuousAt_fst)
  have htend1 : Filter.Tendsto id (𝓝[S] z) (𝓝 z) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have htend2 : Filter.Tendsto (fun w : MSpace8 × MSpace8 => (w.1, vMap k w.1)) (𝓝[S] z)
      (𝓝 (z.1, vMap k z.1)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : (fun w : MSpace8 × MSpace8 => (w.1, vMap k w.1)) =ᶠ[𝓝[S] z] id := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hS] at hw
    exact Prod.ext rfl hw.2
  have hz' : z = (z.1, vMap k z.1) := by
    have hneBot : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
    exact tendsto_nhds_unique htend1 (Filter.Tendsto.congr' hev htend2)
  have hz2 : vMap k z.1 = z.2 := by
    have h := congrArg Prod.snd hz'
    simpa using h.symm
  rw [hS]
  exact ⟨hz1mem, hz2⟩

/-- **The total space of the vector bundle `ξ` is Hausdorff.** -/
instance t2space_Vk (k : ℤ) : T2Space (Vk k) :=
  Work.Glue.glued_t2space (vData k) (graph_closed_vMap k)

/-! ## Continuity of the inclusion of sphere bundles -/

/-- The inclusion `mkToVkFun k : Mk k → Vk k` of the sphere bundle of `Mk k` into the total space
of `ξ` is continuous. -/
theorem continuous_mkToVkFun (k : ℤ) : Continuous (mkToVkFun k) := by
  have h : Continuous (mkToVkAux k) := by
    refine Continuous.sumElim ?_ ?_
    · exact (vData k).continuous_ιX.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    · exact (vData k).continuous_ιY.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact h.quotient_lift (fun _ _ hh => mkToVkAux_respects k hh)

/-! ## The range of `mkToVkFun` is the unit sphere bundle -/

/-- A point of `Vk k` lies in the image of `mkToVkFun k` exactly when its fibre norm is `1`. -/
theorem mem_range_mkToVkFun_iff (k : ℤ) (p : Vk k) :
    p ∈ Set.range (mkToVkFun k) ↔ fibreNormFun k p = 1 := by
  constructor
  · rintro ⟨z, rfl⟩
    have hz : z ∈ Set.range (clutchData k).ιX ∪ Set.range (clutchData k).ιY := by
      rw [(clutchData k).range_ιX_union_range_ιY]
      exact Set.mem_univ z
    rcases hz with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [mkToVk_ιX, fibreNormFun_ιX]
      exact norm_eq_of_mem_sphere a.2
    · rw [mkToVk_ιY, fibreNormFun_ιY]
      exact norm_eq_of_mem_sphere a.2
  · intro hp
    have hz : p ∈ Set.range (vData k).ιX ∪ Set.range (vData k).ιY := by
      rw [(vData k).range_ιX_union_range_ιY]
      exact Set.mem_univ p
    rcases hz with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · have h1 : ‖a.2‖ = 1 := by
        rw [← fibreNormFun_ιX k a]
        exact hp
      have h2 : a.2 ∈ Metric.sphere (0 : Quaternion ℝ) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]
        exact h1
      refine ⟨(clutchData k).ιX (a.1, ⟨a.2, h2⟩), ?_⟩
      rw [mkToVk_ιX]
    · have h1 : ‖a.2‖ = 1 := by
        rw [← fibreNormFun_ιY k a]
        exact hp
      have h2 : a.2 ∈ Metric.sphere (0 : Quaternion ℝ) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]
        exact h1
      refine ⟨(clutchData k).ιY (a.1, ⟨a.2, h2⟩), ?_⟩
      rw [mkToVk_ιY]

/-- The unit quaternion in the direction of `y`, as a point of `S³`, from a proof that
`‖y‖ = 1`. -/
def toSphere (y : Quaternion ℝ) (h : ‖y‖ = 1) : QS3 :=
  ⟨y, by rwa [Metric.mem_sphere, dist_zero_right]⟩

@[simp] theorem coe_toSphere (y : Quaternion ℝ) (h : ‖y‖ = 1) :
    ((toSphere y h : QS3) : Quaternion ℝ) = y := rfl

/-! ## The inverse of `mkToVkFun` on the unit sphere bundle -/

/-- **The chartwise inverse of `mkToVkFun k` on the unit sphere bundle**: a point of `{ν = 1}`
determines, and is determined by, a point of `Mk k`. -/
noncomputable def unitInv (k : ℤ) (p : {p : Vk k // fibreNormFun k p = 1}) : Mk k :=
  Classical.choose ((mem_range_mkToVkFun_iff k p.1).mpr p.2)

theorem mkToVkFun_unitInv (k : ℤ) (p : {p : Vk k // fibreNormFun k p = 1}) :
    mkToVkFun k (unitInv k p) = p.1 :=
  Classical.choose_spec ((mem_range_mkToVkFun_iff k p.1).mpr p.2)

/-- The chartwise description of `unitInv` on the first chart. -/
theorem unitInv_eq_ιX (k : ℤ) (p : {p : Vk k // fibreNormFun k p = 1})
    (hp : (p : Vk k) ∈ Set.range (vData k).ιX) (hu : ‖((vData k).homX.symm (p : Vk k)).2‖ = 1) :
    unitInv k p = (clutchData k).ιX
      (((vData k).homX.symm (p : Vk k)).1,
        toSphere ((vData k).homX.symm (p : Vk k)).2 hu) := by
  have hmem : (p : Vk k) ∈ (vData k).homX.target := by
    rw [(vData k).homX_target]
    exact hp
  have h1 : (vData k).ιX ((vData k).homX.symm (p : Vk k)) = (p : Vk k) := by
    rw [← (vData k).homX_apply ((vData k).homX.symm (p : Vk k))]
    exact (vData k).homX.right_inv hmem
  refine mkToVkFun_injective k ?_
  rw [mkToVk_ιX, mkToVkFun_unitInv]
  simpa using h1.symm

/-- The chartwise description of `unitInv` on the second chart. -/
theorem unitInv_eq_ιY (k : ℤ) (p : {p : Vk k // fibreNormFun k p = 1})
    (hp : (p : Vk k) ∈ Set.range (vData k).ιY) (hu : ‖((vData k).homY.symm (p : Vk k)).2‖ = 1) :
    unitInv k p = (clutchData k).ιY
      (((vData k).homY.symm (p : Vk k)).1,
        toSphere ((vData k).homY.symm (p : Vk k)).2 hu) := by
  have hmem : (p : Vk k) ∈ (vData k).homY.target := by
    rw [(vData k).homY_target]
    exact hp
  have h1 : (vData k).ιY ((vData k).homY.symm (p : Vk k)) = (p : Vk k) := by
    rw [← (vData k).homY_apply ((vData k).homY.symm (p : Vk k))]
    exact (vData k).homY.right_inv hmem
  refine mkToVkFun_injective k ?_
  rw [mkToVk_ιY, mkToVkFun_unitInv]
  simpa using h1.symm

/-! ## Continuity of `unitInv` -/

theorem continuousOn_unitInv_range_ιX (k : ℤ) :
    ContinuousOn (unitInv k)
      {p : {p : Vk k // fibreNormFun k p = 1} | (p : Vk k) ∈ Set.range (vData k).ιX} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hu : ∀ p : ↥{p : {p : Vk k // fibreNormFun k p = 1} | (p : Vk k) ∈ Set.range (vData k).ιX},
      ‖((vData k).homX.symm (p.1 : Vk k)).2‖ = 1 := by
    intro p
    have hmem : (p.1 : Vk k) ∈ (vData k).homX.target := by
      rw [(vData k).homX_target]
      exact p.2
    have h1 : (vData k).ιX ((vData k).homX.symm (p.1 : Vk k)) = (p.1 : Vk k) := by
      rw [← (vData k).homX_apply ((vData k).homX.symm (p.1 : Vk k))]
      exact (vData k).homX.right_inv hmem
    rw [← fibreNormFun_ιX k ((vData k).homX.symm (p.1 : Vk k)), h1]
    exact p.1.2
  have hsymm : Continuous (fun p : ↥{p : {p : Vk k // fibreNormFun k p = 1} |
      (p : Vk k) ∈ Set.range (vData k).ιX} => (vData k).homX.symm (p.1 : Vk k)) :=
    ((vData k).homX.continuousOn_symm).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun p => by rw [(vData k).homX_target]; exact p.2)
  have hq : Continuous (fun p : ↥{p : {p : Vk k // fibreNormFun k p = 1} |
      (p : Vk k) ∈ Set.range (vData k).ιX} =>
      toSphere ((vData k).homX.symm (p.1 : Vk k)).2 (hu p)) :=
    (continuous_snd.comp hsymm).subtype_mk (fun p => by
      rw [Metric.mem_sphere, dist_zero_right]
      exact hu p)
  have hcont : Continuous (fun p : ↥{p : {p : Vk k // fibreNormFun k p = 1} |
      (p : Vk k) ∈ Set.range (vData k).ιX} =>
      (clutchData k).ιX (((vData k).homX.symm (p.1 : Vk k)).1,
        toSphere ((vData k).homX.symm (p.1 : Vk k)).2 (hu p))) :=
    (clutchData k).continuous_ιX.comp ((continuous_fst.comp hsymm).prodMk hq)
  refine hcont.congr (fun p => ?_)
  exact (unitInv_eq_ιX k p.1 p.2 (hu p)).symm

theorem continuousOn_unitInv_range_ιY (k : ℤ) :
    ContinuousOn (unitInv k)
      {p : {p : Vk k // fibreNormFun k p = 1} | (p : Vk k) ∈ Set.range (vData k).ιY} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hu : ∀ p : ↥{p : {p : Vk k // fibreNormFun k p = 1} | (p : Vk k) ∈ Set.range (vData k).ιY},
      ‖((vData k).homY.symm (p.1 : Vk k)).2‖ = 1 := by
    intro p
    have hmem : (p.1 : Vk k) ∈ (vData k).homY.target := by
      rw [(vData k).homY_target]
      exact p.2
    have h1 : (vData k).ιY ((vData k).homY.symm (p.1 : Vk k)) = (p.1 : Vk k) := by
      rw [← (vData k).homY_apply ((vData k).homY.symm (p.1 : Vk k))]
      exact (vData k).homY.right_inv hmem
    rw [← fibreNormFun_ιY k ((vData k).homY.symm (p.1 : Vk k)), h1]
    exact p.1.2
  have hsymm : Continuous (fun p : ↥{p : {p : Vk k // fibreNormFun k p = 1} |
      (p : Vk k) ∈ Set.range (vData k).ιY} => (vData k).homY.symm (p.1 : Vk k)) :=
    ((vData k).homY.continuousOn_symm).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun p => by rw [(vData k).homY_target]; exact p.2)
  have hq : Continuous (fun p : ↥{p : {p : Vk k // fibreNormFun k p = 1} |
      (p : Vk k) ∈ Set.range (vData k).ιY} =>
      toSphere ((vData k).homY.symm (p.1 : Vk k)).2 (hu p)) :=
    (continuous_snd.comp hsymm).subtype_mk (fun p => by
      rw [Metric.mem_sphere, dist_zero_right]
      exact hu p)
  have hcont : Continuous (fun p : ↥{p : {p : Vk k // fibreNormFun k p = 1} |
      (p : Vk k) ∈ Set.range (vData k).ιY} =>
      (clutchData k).ιY (((vData k).homY.symm (p.1 : Vk k)).1,
        toSphere ((vData k).homY.symm (p.1 : Vk k)).2 (hu p))) :=
    (clutchData k).continuous_ιY.comp ((continuous_fst.comp hsymm).prodMk hq)
  refine hcont.congr (fun p => ?_)
  exact (unitInv_eq_ιY k p.1 p.2 (hu p)).symm

/-- **The inverse of `mkToVkFun k` on the unit sphere bundle is continuous.** -/
theorem continuous_unitInv (k : ℤ) : Continuous (unitInv k) := by
  refine continuous_of_open_cover
    {p : {p : Vk k // fibreNormFun k p = 1} | (p : Vk k) ∈ Set.range (vData k).ιX}
    {p : {p : Vk k // fibreNormFun k p = 1} | (p : Vk k) ∈ Set.range (vData k).ιY}
    ?_ ?_ ?_ (continuousOn_unitInv_range_ιX k) (continuousOn_unitInv_range_ιY k)
  · exact (vData k).isOpenMap_ιX.isOpen_range.preimage continuous_subtype_val
  · exact (vData k).isOpenMap_ιY.isOpen_range.preimage continuous_subtype_val
  · rw [eq_univ_iff_forall]
    intro p
    rw [Set.mem_union]
    exact (show (p : Vk k) ∈ Set.range (vData k).ιX ∪ Set.range (vData k).ιY from by
      rw [(vData k).range_ιX_union_range_ιY]
      exact Set.mem_univ _)

end

end Work.Milnor
