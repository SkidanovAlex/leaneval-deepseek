import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Crux.reparam_gen
import Submission.Work.Routing.rootedArcAvoidHalfOpen
import Submission.Work.Routing.junctionHelpers
import Submission.Work.Noncompact.Routing.arcs_removal

/-!
# The step engine of the trail recursion

`Work.Drive.stepSeed` builds the *seed arc* of a routing step: the straight chart germ from `x`
in the direction `v`, extended slightly past its end (so that it leaves the closed segment
`{|s| ≤ e}`).  `Work.Drive.stepArc` is the step engine: in an open preconnected `C` containing the
closed chart ball at `x` and the far point `y`, it produces an arc from `x` to `y` inside `C` whose
initial germ is the straight germ and whose body avoids the closed chart segment
`{c.symm (c x + s • v) : |s| ≤ e}` entirely.

The point of the last row: `C` is a region carved by that segment, so the body of the arc avoids it;
the germ half lies on the positive half of the segment, which meets the negative half only at `x`.
-/

namespace Work.Drive

open Set
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (Work.Noncompact.CompressionTube.MC n)
    Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M]

/-- The straight chart segment through `x` in the direction of `v` with `|s| ≤ e`. -/
def chartSeg (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (x : M)
    (v : EuclideanSpace ℝ (Fin n)) (e : ℝ) : Set M :=
  c.symm '' ((fun s : ℝ => c x + s • v) '' Set.Icc (-e) e)

/-- **The seed arc.**  In an open set `C` containing the image of the closed chart ball of radius
`ρ` at `x`, for a direction `v ≠ 0` and `e ∈ (0,1)` with `(e+1)‖v‖ ≤ ρ`, there is a smooth immersed
arc `A` from `x` whose germ is the straight line `t ↦ c.symm (c x + t • v)` on `[0,e]`, which stays
in `C` and which leaves the closed chart segment `{|s| ≤ e}` as soon as `t > e`. -/
theorem stepSeed {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    {x : M} (hxc : x ∈ c.source) {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    {e ε ρ : ℝ} (he : 0 < e) (he1 : e < 1) (hε : 0 < ε) (hρ : 0 < ρ)
    (hεe : e < ε) (hρe : (e + ε) * ‖v‖ ≤ ρ)
    (hρtgt : Metric.closedBall (c x) ρ ⊆ c.target)
    {C : Set M} (hρC : c.symm '' Metric.closedBall (c x) ρ ⊆ C) :
    ∃ A : ℝ → M, ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder A ∧ A 0 = x ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) A t)) ∧
      Set.InjOn A (Set.Icc (0:ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → A t ∈ C) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → A t = c.symm (c x + t • v)) ∧
      (∀ t : ℝ, e < t → t ≤ 1 → A t ∉ chartSeg c x v e) := by
  classical
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  -- the reparametrisation
  obtain ⟨φ, hφcd, hφpos, hφid, hφrange, hφ1, -⟩ :=
    Work.Noncompact.CompressionTube.exists_smooth_reparam_gen (-ε) (e + ε) e 1
      (by linarith) he he1 le_rfl (by linarith)
  have hφmono : StrictMono φ := strictMono_of_deriv_pos hφpos
  have hφ0 : φ 0 = 0 := hφid 0 ⟨le_refl 0, he.le⟩
  have hφe : φ e = e := hφid e ⟨he.le, le_refl e⟩
  -- the chart-target row on the range window
  have htgt : ∀ u : ℝ, u ∈ Set.Ioo (-ε) (e + ε) → c x + u • v ∈ c.target := by
    intro u hu
    refine hρtgt ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : c x + u • v - c x = u • v := by abel
    rw [hsub]
    have h1 : ‖u • v‖ ≤ (e + ε) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ hvn.le
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    linarith [h1, hρe]
  obtain ⟨hAsm, hAimm⟩ :=
    Work.Routing.reparamChartLine_contMDiff_immersion (n := n) (M := M) hc hxc hv hφcd hφpos
      hφrange htgt
  set A : ℝ → M := fun t => c.symm (c x + φ t • v) with hAdef
  have hA0 : A 0 = x := by
    show c.symm (c x + φ 0 • v) = x
    rw [hφ0, zero_smul, add_zero, c.left_inv hxc]
  have hAseed : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → A t ∈ c.symm '' Metric.closedBall (c x) ρ := by
    intro t _
    refine ⟨c x + φ t • v, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : c x + φ t • v - c x = φ t • v := by abel
    rw [hsub]
    have h1 : ‖φ t • v‖ ≤ (e + ε) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ hvn.le
      rw [abs_le]
      have h := hφrange ⟨t, rfl⟩
      constructor <;> linarith [h.1, h.2]
    linarith [h1, hρe]
  have hgerm : ∀ t : ℝ, 0 ≤ t → t ≤ e → A t = c.symm (c x + t • v) := by
    intro t ht0 hte
    show c.symm (c x + φ t • v) = c.symm (c x + t • v)
    rw [hφid t ⟨ht0, hte⟩]
  have hinj : Set.InjOn A (Set.Icc (0:ℝ) 1) := by
    intro s hs t ht hst
    have hinjsymm : Set.InjOn (⇑c.symm) c.target := by
      simpa [OpenPartialHomeomorph.symm_source] using c.symm.injOn
    have ha : c x + φ s • v ∈ c.target := htgt (φ s) (hφrange ⟨s, rfl⟩)
    have hb : c x + φ t • v ∈ c.target := htgt (φ t) (hφrange ⟨t, rfl⟩)
    have h1 : c x + φ s • v = c x + φ t • v := hinjsymm ha hb hst
    have h2 : (φ s - φ t) • v = 0 := by rw [sub_smul, add_left_cancel h1, sub_self]
    have h3 : φ s = φ t := by
      rcases smul_eq_zero.mp h2 with h | h
      · linarith
      · exact absurd h hv
    exact hφmono.injective h3
  have hinjsymm : Set.InjOn (⇑c.symm) c.target := by
    simpa [OpenPartialHomeomorph.symm_source] using c.symm.injOn
  have hout : ∀ t : ℝ, e < t → t ≤ 1 → A t ∉ chartSeg c x v e := by
    intro t het _ hmem
    rw [chartSeg] at hmem
    obtain ⟨z, ⟨s, hs, hsz⟩, hzA⟩ := hmem
    have hAt : A t = c.symm (c x + φ t • v) := rfl
    have harg_t : c x + φ t • v ∈ c.target := htgt (φ t) (hφrange ⟨t, rfl⟩)
    have hsI : s ∈ Set.Ioo (-ε) (e + ε) := by
      refine ⟨?_, ?_⟩
      · have := hs.1; linarith [hεe]
      · have := hs.2; linarith
    have harg_s : c x + s • v ∈ c.target := htgt s hsI
    have h1 : c.symm (c x + φ t • v) = c.symm z := hAt.symm.trans hzA.symm
    have h2 : c.symm (c x + s • v) = c.symm z := congrArg (⇑c.symm) hsz
    have heq : c x + φ t • v = c x + s • v := hinjsymm harg_t harg_s (h1.trans h2.symm)
    have hφs : φ t = s := by
      have h2 : (φ t - s) • v = 0 := by rw [sub_smul, add_left_cancel heq, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · linarith
      · exact absurd h hv
    have h4 : e < φ t := by
      have h5 : φ e < φ t := hφmono het
      rwa [hφe] at h5
    linarith [hs.2, hφs ▸ h4]
  exact ⟨A, hAsm, hA0, hAimm, hinj,
    (fun t ht => hρC (hAseed t ht)), hgerm, hout⟩


/-- The parameter map of the segment arc `t ↦ e (2 min 1 (max 0 t) - 1)`. -/
noncomputable def segParam (e t : ℝ) : ℝ := e * (2 * min 1 (max 0 t) - 1)

theorem segParam_cont (e : ℝ) : Continuous (segParam e) := by
  unfold segParam; fun_prop

theorem segParam_mem {e : ℝ} (he : 0 ≤ e) (t : ℝ) : segParam e t ∈ Set.Icc (-e) e := by
  unfold segParam
  have h1 : (0:ℝ) ≤ min 1 (max 0 t) := le_min zero_le_one (le_max_left _ _)
  have h2 : min 1 (max 0 t) ≤ 1 := min_le_left _ _
  rw [Set.mem_Icc]
  constructor <;> nlinarith [h1, h2, he]

theorem segParam_id {e t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : segParam e t = e * (2 * t - 1) := by
  unfold segParam
  rw [max_eq_right ht.1, min_eq_right ht.2]

theorem segParam_pre_mem {e s : ℝ} (he : 0 < e) (hs : s ∈ Set.Icc (-e) e) :
    (s / e + 1) / 2 ∈ Set.Icc (0:ℝ) 1 := by
  have h2 : s / e ≤ 1 := by rw [div_le_iff₀ he]; linarith [hs.2]
  have h1 : -1 ≤ s / e := by rw [le_div_iff₀ he]; linarith [hs.1]
  constructor <;> linarith

theorem segParam_surj {e s : ℝ} (he : 0 < e) (hs : s ∈ Set.Icc (-e) e) :
    segParam e ((s / e + 1) / 2) = s := by
  unfold segParam
  have h2 : s / e ≤ 1 := by rw [div_le_iff₀ he]; linarith [hs.2]
  have h1 : -1 ≤ s / e := by rw [le_div_iff₀ he]; linarith [hs.1]
  have h3 : (0:ℝ) ≤ (s / e + 1) / 2 := by linarith
  have h4 : (s / e + 1) / 2 ≤ 1 := by linarith
  rw [max_eq_right h3, min_eq_right h4]
  field_simp
  ring

/-- The `+v` half of the chart segment is contained in it. -/
theorem chartSeg_pos_subset (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (x : M)
    (v : EuclideanSpace ℝ (Fin n)) {e : ℝ} (he : 0 ≤ e) :
    c.symm '' ((fun t : ℝ => c x + t • v) '' Set.Icc (0:ℝ) e) ⊆ chartSeg c x v e := by
  rintro z ⟨y, ⟨t, ht, rfl⟩, rfl⟩
  exact ⟨c x + t • v, ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩, rfl⟩

/-- **The step engine.**  In an open preconnected region `C` containing the image of a chart ball
around `x` (of radius `ρ ≥ 3e‖v‖`, inside the chart target), if the closed chart segment
`{|s| ≤ e}` lies in `C`, then for every `y ∈ C` outside that segment there is an arc `α` from `x` to
`y` inside `C`, immersed, injective on `[0,1]`, whose initial germ is the straight germ and whose
body avoids the closed chart segment.  It ends with a straight terminal germ (with its chart-target
row). -/
theorem stepArc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {C : Set M} (hCo : IsOpen C) (hCpc : IsPreconnected C)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    {x : M} (hxc : x ∈ c.source) {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    {e ρ : ℝ} (he : 0 < e) (he1 : e < 1) (hρ : 0 < ρ) (hρe : (3 * e) * ‖v‖ ≤ ρ)
    (hρtgt : Metric.closedBall (c x) ρ ⊆ c.target)
    (hρC : c.symm '' Metric.closedBall (c x) ρ ⊆ C)
    (hSC : chartSeg c x v e ⊆ C)
    {y : M} (hyC : y ∈ C) (hyS : y ∉ chartSeg c x v e) :
    ∃ (α : ℝ → M) (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w' : EuclideanSpace ℝ (Fin n)) (e' : ℝ),
      α 0 = x ∧ α 1 = y ∧
      ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder α ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) α t)) ∧
      Set.InjOn α (Set.Icc (0:ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → α t ∈ C) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → α t = c.symm (c x + t • v)) ∧
      (∀ t : ℝ, e < t → t ≤ 1 → α t ∉ chartSeg c x v e) ∧
      0 < e' ∧ w' ≠ 0 ∧
      c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧ y ∈ c'.source ∧
      (∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → α t = c'.symm (c' y + (t - 1) • w')) ∧
      (∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → c' y + (t - 1) • w' ∈ c'.target) := by
  classical
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  -- ## the segment, as the image of an arc
  set γ : ℝ → M := fun t => c.symm (c x + segParam e t • v) with hγdef
  have hγtgt : ∀ t : ℝ, c x + segParam e t • v ∈ c.target := by
    intro t
    refine hρtgt ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : c x + segParam e t • v - c x = segParam e t • v := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs]
    have h1 : |segParam e t| ≤ e := by
      rw [abs_le]; exact segParam_mem he.le t
    calc |segParam e t| * ‖v‖ ≤ e * ‖v‖ := mul_le_mul_of_nonneg_right h1 hvn.le
      _ ≤ ρ := by nlinarith [hρe, he, hvn]
  have hγcont : Continuous γ := by
    rw [hγdef]
    exact c.continuousOn_symm.comp_continuous
      (continuous_const.add ((segParam_cont e).smul continuous_const)) hγtgt
  have hγimg : γ '' Set.Icc (0:ℝ) 1 = chartSeg c x v e := by
    rw [hγdef, chartSeg]
    ext z; constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨c x + segParam e t • v, ⟨segParam e t, segParam_mem he.le t, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨(s / e + 1) / 2, segParam_pre_mem he hs, ?_⟩
      show c.symm (c x + segParam e ((s / e + 1) / 2) • v) = c.symm (c x + s • v)
      rw [segParam_surj he hs]
  have hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1) := by
    intro s hs t ht hst
    have hinjsymm : Set.InjOn (⇑c.symm) c.target := by
      simpa [OpenPartialHomeomorph.symm_source] using c.symm.injOn
    have h1 : segParam e s = segParam e t := by
      have h2 : c x + segParam e s • v = c x + segParam e t • v :=
        hinjsymm (hγtgt s) (hγtgt t) (by simpa [hγdef] using hst)
      have h3 : (segParam e s - segParam e t) • v = 0 := by
        rw [sub_smul, add_left_cancel h2, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · linarith
      · exact absurd h hv
    rw [segParam_id hs, segParam_id ht] at h1
    have h4 : e * (2 * s - 1 - (2 * t - 1)) = 0 := by linarith [h1]
    have h5 : 2 * s - 1 - (2 * t - 1) = 0 :=
      (mul_eq_zero.mp h4).resolve_left (ne_of_gt he)
    linarith
  have hSclosed : IsClosed (chartSeg c x v e) := hγimg ▸ (isCompact_Icc.image hγcont).isClosed
  have hγC : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → γ t ∈ C := by
    intro t ht
    exact hSC (hγimg ▸ ⟨t, ht, rfl⟩)
  have hUpc : IsPreconnected (C \ chartSeg c x v e) := by
    rw [← hγimg]
    exact Work.Noncompact.Routing.isPreconnected_sdiff_image_arc hn hCo hCpc hγcont hγinj hγC
  -- ## the seed
  obtain ⟨A, hAcd, hA0, hAimm, hAinj, hAimg, hAgerm, hAavoid⟩ :=
    stepSeed (e := e) (ε := 2 * e) (ρ := ρ) hc hxc hv he he1 (hε := by linarith)
      (hεe := by linarith) hρ (hρe := by nlinarith [hρe]) hρtgt hρC
  -- ## the tool
  have hgerC : ∀ t : ℝ, 0 ≤ t → t ≤ e → c.symm (c x + t • v) ∈ C := by
    intro t ht0 hte
    exact hSC ⟨c x + t • v, ⟨t, ⟨by linarith, hte⟩, rfl⟩, rfl⟩
  have hUdisj : Disjoint (C \ chartSeg c x v e)
      (c.symm '' ((fun t : ℝ => c x + t • v) '' Set.Icc (0:ℝ) e)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hz.2 (chartSeg_pos_subset c x v he.le hz')
  obtain ⟨α, hα0, hα1, hαsm, hαimm, hαinj, hαW, hαgerm, hαav,
    c', w', e₀, he₀, hw', hc', hysrc, hαterm⟩ :=
    Work.Routing.rootedArcAvoidHalfOpen (n := n) (M := M) hn
      (W := C) (U := C \ chartSeg c x v e) (S := chartSeg c x v e)
      hCo (hCo.sdiff hSclosed) hUpc hSclosed (subset_refl _) Set.sdiff_subset
      (by rw [Set.disjoint_left]; intro z hz hzu; exact hzu.2 hz)
      hc hxc hv he hgerC hUdisj he1
      hAcd hA0 hAgerm hAimg hAimm hAinj hAavoid hyC hyS
  -- ## the terminal chart-target row
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp c'.open_target (c' y) (c'.map_source hysrc)
  have hwn : (0 : ℝ) < ‖w'‖ := norm_pos_iff.mpr hw'
  refine ⟨α, c', w', min e₀ (δ / (2 * ‖w'‖)), hα0, hα1, hαsm, hαimm, hαinj, hαW, hαgerm,
    hαav, lt_min he₀ (by positivity), hw', hc', hysrc, ?_, ?_⟩
  · intro t ht1 ht2
    exact hαterm t (by linarith [min_le_left e₀ (δ / (2 * ‖w'‖))]) ht2
  · intro t ht1 ht2
    refine hδsub ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : c' y + (t - 1) • w' - c' y = (t - 1) • w' := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs]
    have h1 : |t - 1| ≤ min e₀ (δ / (2 * ‖w'‖)) := by
      rw [abs_of_nonpos (by linarith)]
      linarith [ht1]
    have h2 : min e₀ (δ / (2 * ‖w'‖)) * ‖w'‖ < δ := by
      have h3 : min e₀ (δ / (2 * ‖w'‖)) ≤ δ / (2 * ‖w'‖) := min_le_right _ _
      have h4 : δ / (2 * ‖w'‖) * ‖w'‖ = δ / 2 := by field_simp
      nlinarith [h3, hδ, hwn]
    nlinarith [mul_le_mul_of_nonneg_right h1 hwn.le]

end Work.Drive
