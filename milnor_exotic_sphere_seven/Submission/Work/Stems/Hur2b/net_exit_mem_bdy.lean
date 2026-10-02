import Mathlib
import Submission.Work.Stems.Hur2b.NetExitGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The exit point of a point outside the interior of the net region lies on `∂D`

`NetBdy = NetRegion \ interior NetRegion` is the inner boundary `∂D` of the T-net
`D = ⋃ k, netCell k`.  The main statement of this file,

`net_exit_mem_bdy`: for **every** point `y` of the square that is not in the interior of the net
region (whether it lies in `D`, on `∂D`, or far outside `D`), the radial exit point
`radialPoint (offOf y)` of the ray from the centre `c` in the direction `y - c` lies on `∂D`.

The two ingredients are:

* `offOf_mem_interior_netOff_of_mem_interior`: on the open box where the clamping `ptOf` is
  inactive, being in the interior of the net region is the same as having the offset in the
  interior of the offset region `netOff` (the offset map is a local homeomorphism there, and
  `net_region_eq` identifies the net region with the preimage of `netOff`);
* `rayOff_notMem_interior_netOff`: the exit point `rayOff z` of the ray in a *nonzero* direction is
  a boundary point of `netOff` — the points `rayOff z + ε z` (`ε > 0`) are outside `netOff`
  (`rayOff_exit`) and converge to `rayOff z`.

Note that the hypothesis is only `y ∉ interior NetRegion`, not `y ∈ NetRegion`: the statement
therefore also covers `y` outside `D`, which is what makes it usable for the collar of the net in
`Submission/Work/Stems/Hur2b/net_model.lean`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-- **The offset point is continuous.** -/
theorem continuous_ptOf : Continuous (ptOf : (Fin 2 → ℝ) → IC 2) := by
  have h : ptOf = fun z => pair2 (clamp (7/16 + z 0)) (clamp (7/16 + z 1)) := rfl
  rw [h]
  exact continuous_pair2 (continuous_clamp.comp (by fun_prop))
    (continuous_clamp.comp (by fun_prop))

/-- On the box where the clamping is inactive, `ptOf` is a right inverse of `offOf`. -/
theorem offOf_ptOf (w : Fin 2 → ℝ) (hw : ∀ i, 7/16 + w i ∈ Set.Icc (0:ℝ) 1) :
    offOf (ptOf w) = w := by
  funext i
  rw [offOf_eq, ptOf_coe, clamp_val _ (hw i)]
  ring

/-- **Interior points of the net region have offsets in the interior of the offset region.** -/
theorem offOf_mem_interior_netOff_of_mem_interior {y : IC 2}
    (hy : y ∈ interior NetRegion) : offOf y ∈ interior netOff := by
  have hyN : y ∈ NetRegion := interior_subset hy
  have hoff : offOf y ∈ netOff := (net_region_eq y).mp hyN
  -- the offsets of a point of the region lie well inside the box on which `ptOf` is unclamped
  have hsafe : ∀ i, 7/16 + offOf y i ∈ Set.Ioo (0:ℝ) 1 := by
    intro i
    rcases hoff with hb | hc
    · simp only [beltOff, Set.mem_ofPred_eq] at hb
      rcases (show i = 0 ∨ i = 1 from by fin_cases i <;> simp) with h | h
      · subst h; exact ⟨by linarith [hb.1], by linarith [hb.2.1]⟩
      · subst h; exact ⟨by linarith [hb.2.2.1], by linarith [hb.2.2.2]⟩
    · simp only [colOff, Set.mem_ofPred_eq] at hc
      rcases (show i = 0 ∨ i = 1 from by fin_cases i <;> simp) with h | h
      · subst h; exact ⟨by linarith [hc.1], by linarith [hc.2.1]⟩
      · subst h; exact ⟨by linarith [hc.2.2.1], by linarith [hc.2.2.2]⟩
  rw [mem_interior_iff_mem_nhds]
  -- pushing the interior of the net region forward along `ptOf`
  have h2 : ∀ᶠ w in 𝓝 (offOf y), ptOf w ∈ interior NetRegion := by
    have hmem : interior NetRegion ∈ 𝓝 (ptOf (offOf y)) := by
      rw [ptOf_offOf]
      exact isOpen_interior.mem_nhds hy
    exact continuous_ptOf.continuousAt.preimage_mem_nhds hmem
  -- and the clamping stays inactive nearby
  have h3 : ∀ᶠ w in 𝓝 (offOf y), ∀ i, 7/16 + w i ∈ Set.Icc (0:ℝ) 1 := by
    rw [Filter.eventually_all]
    intro i
    have hopen : IsOpen {w : Fin 2 → ℝ | 7/16 + w i ∈ Set.Ioo (0:ℝ) 1} :=
      isOpen_Ioo.preimage (continuous_const.add (continuous_apply i))
    have h4 : {w : Fin 2 → ℝ | 7/16 + w i ∈ Set.Ioo (0:ℝ) 1} ∈ 𝓝 (offOf y) :=
      IsOpen.mem_nhds hopen (hsafe i)
    exact Filter.mem_of_superset h4 (fun w hw => ⟨hw.1.le, hw.2.le⟩)
  filter_upwards [h2, h3] with w hw2 hw3
  have hmem : offOf (ptOf w) ∈ netOff := (net_region_eq (ptOf w)).mp (interior_subset hw2)
  rwa [offOf_ptOf w hw3] at hmem

/-- **The exit point of a nonzero direction is a boundary point of the offset region.**

The points `rayOff z + ε z` (`ε > 0`) are outside `netOff` (`rayOff_exit`) and tend to `rayOff z`
as `ε → 0⁺`, so `rayOff z` cannot be an interior point. -/
theorem rayOff_notMem_interior_netOff {z : Fin 2 → ℝ} (hz : z ≠ 0) :
    rayOff z ∉ interior netOff := by
  intro hmem
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hmem)
  set ε : ℝ := ρ / (2 * (‖z‖ + 1)) with hεdef
  have hden : (2:ℝ) * (‖z‖ + 1) ≠ 0 := by positivity
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact div_pos hρ (by positivity)
  have h2 : ε * (2 * (‖z‖ + 1)) = ρ := by
    rw [hεdef]
    exact div_mul_cancel₀ ρ hden
  have hlt : ε * ‖z‖ < ρ := by nlinarith [norm_nonneg z, hρ, h2, hεpos]
  have hballmem : rayOff z + ε • z ∈ Metric.ball (rayOff z) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hεpos]
    exact hlt
  have hnet : rayOff z + ε • z ∈ netOff := interior_subset (hball hballmem)
  exact rayOff_exit hz ε hεpos hnet

/-- **The exit point of any point outside the interior of the net region lies on `∂D`.** -/
theorem net_exit_mem_bdy {y : Work.Stems.Cubical.IC 2} (hy : y ∉ interior Work.Stems.Hur2b.NetRegion) : Work.Stems.Hur2b.radialPoint (Work.Stems.Hur2b.offOf y) ∈ Work.Stems.Hur2b.NetBdy := by
  have hz : offOf y ≠ 0 := by
    intro h
    exact hy (by rw [offOf_eq_zero_iff.mp h]; exact netCentre_mem_interior)
  refine ⟨radialPoint_mem_region hz, fun hmem => ?_⟩
  have h := offOf_mem_interior_netOff_of_mem_interior hmem
  rw [offOf_radialPoint] at h
  exact rayOff_notMem_interior_netOff hz h

end

end Work.Stems.Hur2b
