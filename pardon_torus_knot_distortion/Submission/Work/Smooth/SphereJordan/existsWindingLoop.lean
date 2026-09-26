import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Topology.PlaneCurve.CruxBoundedComponentClean
import Submission.Work.Smooth.SphereJordan.Vendored.frontierCurveOfOpenBallUnionAux

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- **A compact, gap-separated clopen hull of the component of `0`.**

If `F ⊆ ℂ` is closed, `0 ∈ F` and the connected component of `0` in `F` is bounded, then there is a
compact set `U ∋ 0` contained in `F` which is at positive distance from `F \ U`.  (`U` cannot be
taken to be the component itself: for `F = {0} ∪ {1/n}` the component `{0}` is not open in `F`.) -/
theorem compactGapClopen {F : Set ℂ} (hF : IsClosed F) (h0 : (0 : ℂ) ∈ F)
    (hbdd : Bornology.IsBounded (connectedComponentIn F (0 : ℂ))) :
    ∃ (U : Set ℂ) (ρ : ℝ), IsCompact U ∧ (0 : ℂ) ∈ U ∧ U ⊆ F ∧ 0 < ρ ∧
      ∀ u ∈ U, ∀ v ∈ F, v ∉ U → ρ ≤ dist u v := by
  classical
  obtain ⟨R₀, hR₀⟩ := hbdd.exists_norm_le
  set R : ℝ := max R₀ 0 + 1 with hRdef
  have hR0le : R₀ ≤ R := by
    have h1 : R₀ ≤ max R₀ 0 := le_max_left _ _
    rw [hRdef]; linarith
  have hRpos : 0 < R := by
    have h1 : (0:ℝ) ≤ max R₀ 0 := le_max_right _ _
    rw [hRdef]; linarith
  have hCsub : connectedComponentIn F (0 : ℂ) ⊆ Metric.ball (0 : ℂ) R := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (hR₀ z hz) (by rw [hRdef]; linarith [le_max_left R₀ (0:ℝ)])
  -- the compact piece `M := F ∩ closedBall 0 R`
  set M : Set ℂ := F ∩ Metric.closedBall (0 : ℂ) R with hMdef
  have hMclosed : IsClosed M := hF.inter Metric.isClosed_closedBall
  have hMbdd : Bornology.IsBounded M := Metric.isBounded_closedBall.subset inter_subset_right
  have hMcompact : IsCompact M := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hMclosed, hMbdd⟩
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hMcompact
  have h0M : (0 : ℂ) ∈ M := by
    refine ⟨h0, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa using hRpos.le
  have hcompeq : connectedComponentIn M (0 : ℂ) = connectedComponentIn F (0 : ℂ) := by
    refine Subset.antisymm (connectedComponentIn_mono (0 : ℂ) inter_subset_left) ?_
    exact IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn h0)
      (fun z hz => ⟨connectedComponentIn_subset F 0 hz, Metric.ball_subset_closedBall (hCsub hz)⟩)
  -- clopen separation of any point outside the component of `0`
  have hsep : ∀ x : M, (x : ℂ) ∉ connectedComponentIn M (0 : ℂ) →
      ∃ Z : Set M, IsClopen Z ∧ (⟨0, h0M⟩ : M) ∈ Z ∧ x ∉ Z := by
    intro x hx
    have hxnot : x ∉ connectedComponent (⟨0, h0M⟩ : M) := by
      intro hc
      have hmem : (x : ℂ) ∈ connectedComponentIn M (0 : ℂ) := by
        rw [connectedComponentIn_eq_image h0M]
        exact ⟨x, hc, rfl⟩
      exact hx hmem
    rw [connectedComponent_eq_iInter_isClopen] at hxnot
    have h2 : ¬ (∀ s : {s : Set M // IsClopen s ∧ (⟨0, h0M⟩ : M) ∈ s}, x ∈ (s : Set M)) := by
      intro h
      exact hxnot (Set.mem_iInter.mpr h)
    push_neg at h2
    obtain ⟨Z, hxZ⟩ := h2
    exact ⟨Z.1, Z.2.1, Z.2.2, hxZ⟩
  -- the far part of `M`
  set T : Set M := {y : M | (y : ℂ) ∉ Metric.ball (0 : ℂ) R} with hTdef
  have hTclosed : IsClosed T := by
    rw [hTdef]
    exact IsClosed.preimage continuous_subtype_val Metric.isOpen_ball.isClosed_compl
  have hTcompact : IsCompact T := hTclosed.isCompact
  have hchoose : ∀ x : T, ∃ Z : Set M, IsClopen Z ∧ (⟨0, h0M⟩ : M) ∈ Z ∧ (x : M) ∉ Z := by
    intro x
    refine hsep x.1 ?_
    intro hmem
    have hmemF : (x.1 : ℂ) ∈ connectedComponentIn F (0 : ℂ) := by
      rw [← hcompeq]; exact hmem
    exact x.2 (hCsub hmemF)
  choose Z hZcl hZ0 hZx using hchoose
  have hcov : T ⊆ ⋃ x : T, {y : M | y ∉ Z x} := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hZx ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hTcompact.elim_finite_subcover (fun x : T => {y : M | y ∉ Z x})
    (fun x => (hZcl x).isClosed.isOpen_compl) hcov
  set Z₀ : Set M := ⋂ x ∈ t, Z x with hZ₀def
  have hZ₀cl : IsClopen Z₀ := by
    rw [hZ₀def]
    exact Set.Finite.isClopen_biInter t.finite_toSet (fun x _ => hZcl x)
  have hZ₀0 : (⟨0, h0M⟩ : M) ∈ Z₀ := by
    rw [hZ₀def]; exact Set.mem_iInter₂.mpr (fun x _ => hZ0 x)
  have hZ₀T : ∀ y ∈ Z₀, y ∉ T := by
    intro y hy hyT
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hyT)
    exact hyx (Set.mem_iInter₂.mp hy x hxt)
  have hZ₀ball : ∀ y ∈ Z₀, (y : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    intro y hy
    by_contra hcon
    exact hZ₀T y hy hcon
  -- the compact set `U`
  set U : Set ℂ := Subtype.val '' Z₀ with hUdef
  have hUcomp : IsCompact U := (hZ₀cl.isClosed.isCompact).image continuous_subtype_val
  have hU0 : (0 : ℂ) ∈ U := ⟨⟨0, h0M⟩, hZ₀0, rfl⟩
  have hUF : U ⊆ F := by rintro z ⟨y, hy, rfl⟩; exact (y.2).1
  have hUball : U ⊆ Metric.ball (0 : ℂ) R := by rintro z ⟨y, hy, rfl⟩; exact hZ₀ball y hy
  -- the gap between the two clopen pieces of `M`
  have hdist₁ : ∃ ρ₁ > 0, ∀ a ∈ Z₀, ∀ b : M, b ∉ Z₀ → ρ₁ ≤ dist a b := by
    by_cases hne : (Z₀ᶜ : Set M).Nonempty
    · obtain ⟨b₀, hb₀⟩ := hne
      have hcompact : IsCompact (Z₀ ×ˢ (Z₀ᶜ : Set M)) :=
        hZ₀cl.isClosed.isCompact.prod hZ₀cl.compl.isClosed.isCompact
      obtain ⟨p, hp, hpmin⟩ := hcompact.exists_isMinOn
        ⟨(⟨0, h0M⟩, b₀), hZ₀0, hb₀⟩ (continuous_fst.dist continuous_snd).continuousOn
      refine ⟨dist p.1 p.2, ?_, ?_⟩
      · exact dist_pos.mpr (fun h => hp.2 (h ▸ hp.1))
      · rintro a ha b hb
        exact hpmin (show (a, b) ∈ Z₀ ×ˢ (Z₀ᶜ : Set M) from ⟨ha, hb⟩)
    · refine ⟨1, one_pos, fun a ha b hb => ?_⟩
      exact absurd ⟨b, hb⟩ hne
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := hdist₁
  obtain ⟨z₀, hz₀U, hz₀max⟩ := hUcomp.exists_isMaxOn ⟨0, hU0⟩ continuous_norm.continuousOn
  have hz₀lt : ‖z₀‖ < R := by
    have h := hUball hz₀U
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hρ₂ : 0 < R - ‖z₀‖ := by linarith
  refine ⟨U, min ρ₁ (R - ‖z₀‖) / 2, hUcomp, hU0, hUF, ?_, ?_⟩
  · have h2 : (0:ℝ) ≤ min ρ₁ (R - ‖z₀‖) := le_min hρ₁pos.le hρ₂.le
    positivity
  · rintro u ⟨zu, hzu, rfl⟩ v hv hvU
    have hle₁ : min ρ₁ (R - ‖z₀‖) / 2 ≤ ρ₁ := by
      have h1 : min ρ₁ (R - ‖z₀‖) ≤ ρ₁ := min_le_left _ _
      linarith
    have hle₂ : min ρ₁ (R - ‖z₀‖) / 2 ≤ R - ‖z₀‖ := by
      have h1 : min ρ₁ (R - ‖z₀‖) ≤ R - ‖z₀‖ := min_le_right _ _
      linarith
    by_cases hvM : v ∈ M
    · have hv' : (⟨v, hvM⟩ : M) ∉ Z₀ := fun h => hvU ⟨⟨v, hvM⟩, h, rfl⟩
      have h := hρ₁ zu hzu ⟨v, hvM⟩ hv'
      rw [Subtype.dist_eq] at h
      exact le_trans hle₁ h
    · have hvR : R < ‖v‖ := by
        by_contra hcon
        push_neg at hcon
        exact hvM ⟨hv, by rw [Metric.mem_closedBall, dist_zero_right]; exact hcon⟩
      have hzuU : (zu : ℂ) ∈ U := ⟨zu, hzu, rfl⟩
      have hle : ‖(zu : ℂ)‖ ≤ ‖z₀‖ := hz₀max hzuU
      have hge : R - ‖z₀‖ ≤ dist (zu : ℂ) v := by
        rw [dist_comm, dist_eq_norm]
        have h2 : ‖v‖ - ‖(zu : ℂ)‖ ≤ ‖v - (zu : ℂ)‖ :=
          le_trans (le_abs_self _) (abs_norm_sub_norm_le v _)
        linarith
      exact le_trans hle₂ hge

/-- **A finite cover of a compact set by open balls of a fixed radius with centres in the set.** -/
theorem exists_finset_cover_ball {U : Set ℂ} (hU : IsCompact U) {r : ℝ} (hr : 0 < r) :
    ∃ T : Finset ℂ, (∀ p ∈ T, p ∈ U) ∧ U ⊆ ⋃ p ∈ T, Metric.ball p r := by
  have hcov : U ⊆ ⋃ x : U, Metric.ball (x : ℂ) r := by
    intro z hz
    refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    simpa using hr
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U => Metric.ball (x : ℂ) r)
    (fun _ => Metric.isOpen_ball) hcov
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
    exact x.2
  · intro z hz
    obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.mp (ht hz)
    exact Set.mem_iUnion₂.mpr ⟨(x : ℂ), Finset.mem_image.mpr ⟨x, hxt, rfl⟩, hzx⟩

/-- **The planar crux of the chapter.**

Let `F ⊆ ℂ` be closed with `0 ∈ F`, and suppose that the connected component of `0` in `F` is
bounded.  Then there is a closed loop in `ℂ ∖ F`, avoiding `0`, whose index about `0` is non-zero.

The route: `compactGapClopen` supplies a compact `U ∋ 0` inside `F` at positive distance from
`F \ U`; `U` is covered by finitely many balls of radius `r < ρ` with centres in `U`; the frontier
of the union `S` of the corresponding closed balls contains a simple closed curve
(`frontierCurveOfOpenBallUnionAux`), whose complementary component containing `0` is bounded by
`0 ∈ U ⊆ int S`; that curve winds about `0` non-trivially
(`windNumber_ne_zero_of_bounded_component`), and since `∂S` is within `r` of `U` (whence inside
`ℂ ∖ F`) the associated loop avoids `F`. -/
theorem existsWindingLoop {F : Set ℂ} (hF : IsClosed F) (h0 : (0 : ℂ) ∈ F)
    (hbdd : Bornology.IsBounded (connectedComponentIn F (0 : ℂ))) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∉ F) ∧ (∀ t, c t ≠ 0) ∧ c 0 = c 1
      ∧ Work.Smooth.SphereJordan.loopIndex c ≠ 0 := by
  classical
  obtain ⟨U, ρ, hUcomp, hU0, hUF, hρpos, hgap⟩ := compactGapClopen hF h0 hbdd
  set r : ℝ := ρ / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrgap : r < ρ := by rw [hrdef]; linarith
  obtain ⟨T, hTsub, hTcov⟩ := exists_finset_cover_ball hUcomp hrpos
  set S : Set ℂ := ⋃ p ∈ T, Metric.closedBall p r with hSdef
  have hSclosed : IsClosed S := by
    rw [hSdef]; exact isClosed_biUnion_finset fun p _ => Metric.isClosed_closedBall
  -- `0` lies in the open union
  have h0T : (0 : ℂ) ∈ ⋃ p ∈ T, Metric.ball p r := hTcov hU0
  -- the Jordan curve in the frontier
  obtain ⟨γ, hγc, hγper, hγinj, hγrange, hγbdd⟩ :=
    Work.Smooth.SphereJordan.frontierCurveOfOpenBallUnionAux T hrpos h0T
  have hγrangeS : Set.range γ ⊆ frontier S := by
    rw [hSdef]
    exact hγrange
  -- `0` is interior to `S`, hence not on the frontier
  have h0int : (0 : ℂ) ∈ interior S := by
    obtain ⟨p, hpT, h0p⟩ := Set.mem_iUnion₂.mp h0T
    have hsub : Metric.closedBall p r ⊆ S := by
      intro z hz
      rw [hSdef]
      exact Set.mem_iUnion₂.mpr ⟨p, hpT, hz⟩
    exact interior_mono hsub (Metric.ball_subset_interior_closedBall h0p)
  have hzrange : (0 : ℂ) ∉ Set.range γ := by
    rintro ⟨t, ht⟩
    have hmem : (0 : ℂ) ∈ frontier S := by
      rw [← ht]
      exact hγrangeS ⟨t, rfl⟩
    exact hmem.2 h0int
  -- the frontier points are near `U`, where `F` agrees with `U`
  have hrangeU : ∀ t, ∃ u ∈ U, dist (γ t) u ≤ r := by
    intro t
    have hmem : γ t ∈ S :=
      hSclosed.closure_eq ▸ frontier_subset_closure (hγrangeS ⟨t, rfl⟩)
    rw [hSdef] at hmem
    obtain ⟨p, hpT, hpp⟩ := Set.mem_iUnion₂.mp hmem
    exact ⟨p, hTsub p hpT, (Metric.mem_closedBall.mp hpp)⟩
  have havoid : ∀ t, γ t ∉ F := by
    intro t ht
    obtain ⟨u, huU, hdu⟩ := hrangeU t
    have hdist : dist (γ t) u < ρ := lt_of_le_of_lt hdu hrgap
    by_cases hut : γ t ∈ U
    · have hUint : U ⊆ interior S := by
        intro z hz
        obtain ⟨p, hpT, hzp⟩ := Set.mem_iUnion₂.mp (hTcov hz)
        have hsub : Metric.closedBall p r ⊆ S := by
          intro w hw
          rw [hSdef]
          exact Set.mem_iUnion₂.mpr ⟨p, hpT, hw⟩
        exact interior_mono hsub (Metric.ball_subset_interior_closedBall hzp)
      exact (hγrangeS ⟨t, rfl⟩).2 (hUint hut)
    · have hgap' : ρ ≤ dist u (γ t) := hgap u huU (γ t) ht hut
      rw [dist_comm] at hgap'
      linarith
  -- the winding number of the curve about `0` is non-zero
  have hwn : windNumber γ hγc 0 ≠ 0 :=
    windNumber_ne_zero_of_bounded_component hγc hγper hγinj hzrange hγbdd
  set c : C(unitInterval, ℂ) := curveLoop γ hγc with hcdef
  have hcapply : ∀ t : unitInterval, c t = γ (2 * Real.pi * (t : ℝ)) := fun t => rfl
  have hcF : ∀ t, c t ∉ F := by
    intro t
    rw [hcapply t]
    exact havoid _
  have hc0 : ∀ t, c t ≠ 0 := by
    intro t h
    refine hzrange ⟨2 * Real.pi * (t : ℝ), ?_⟩
    rw [← hcapply t, h]
  have hcloop : c 0 = c 1 := by
    have e0 : (((0 : unitInterval) : ℝ)) = 0 := by norm_num
    have e1 : (((1 : unitInterval) : ℝ)) = 1 := by norm_num
    rw [hcapply 0, hcapply 1, e0, e1, mul_zero, mul_one]
    simpa using (hγper 0).symm
  -- transfer the winding number to the index of the loop
  have hidx : loopIndex c ≠ 0 := by
    intro hzero
    apply hwn
    have hcongr : loopIndex (curveLoop (fun t => γ t - 0) (hγc.sub continuous_const))
        = loopIndex c := by
      refine loopIndex_congr (fun t => ?_) ?_ ?_ ?_ ?_
      · show γ (2 * Real.pi * (t : ℝ)) - 0 = c t
        rw [hcapply t, sub_zero]
      · intro t
        show γ (2 * Real.pi * (t : ℝ)) - 0 ≠ 0
        rw [sub_zero]
        exact hc0 t
      · exact hc0
      · show γ (2 * Real.pi * (((0 : unitInterval) : ℝ))) - 0
            = γ (2 * Real.pi * (((1 : unitInterval) : ℝ))) - 0
        have h := hcloop
        rw [hcapply 0, hcapply 1] at h
        have e0 : (((0 : unitInterval) : ℝ)) = 0 := by norm_num
        have e1 : (((1 : unitInterval) : ℝ)) = 1 := by norm_num
        rw [e0, e1, mul_zero, mul_one]
        simpa using h
      · exact hcloop
    rw [windNumber, hcongr, hzero]
  exact ⟨c, hcF, hc0, hcloop, hidx⟩

end

end Work.Smooth.SphereJordan
