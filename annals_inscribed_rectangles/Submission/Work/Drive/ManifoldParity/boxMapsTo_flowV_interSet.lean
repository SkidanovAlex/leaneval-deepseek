import Mathlib
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs
import Submission.Work.Drive.ManifoldParity.GraphMap
import Submission.Work.Drive.ManifoldParity.GraphFDeriv
import Submission.Work.Drive.ManifoldParity.GraphFlow
import Submission.Work.Drive.ManifoldParity.flowV_neg

namespace Work.Drive.ManifoldParity

open scoped Manifold ContDiff Topology
open Manifold Set Filter

noncomputable section

/-- **Local data for the flow along the intersection set at a point of the intersection set.**

Given a point `q ∈ K = interSet D N` and an index `i` such that the charted difference map is
surjective on the coordinate hyperplane `{v | v i = 0}` at `q`, and such that all the *other*
coordinates of `q` are strictly inside `(0,1)`, there are a graph `η` over the `i`-th coordinate
through `q` and a radius `ε > 0` such that, near `q`, `graphMap i η` parametrises `K` and the field
`V` is tangent to `K` at the graph points: `V (g u) = fderiv g u ((V (g u)) i)`.

Moreover the graph points whose `i`-th coordinate is in `[0,1]` lie in the unit box, and the
derivative of the graph map is bounded on the interval of parameters.

This is the "static" half of the proof that the flow of a field tangent to `K` preserves `K`: the
local graph structure (`Work.Drive.exists_local_graph`) together with the tangency identity
`eq_fderiv_graphMap_of_fderiv_eq_zero`. -/
theorem exists_local_tangent_data {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (sqPart x) = N (cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (cbPart x)).toLinearMap = ⊤)
    {V : Amb 4 → Amb 4}
    (hVtan : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (sqPart x) = N (cbPart x) → ∀ p : M, x ∈ chartRegion p D N →
      fderiv ℝ (chartDiff p D N) x (V x) = 0)
    {q : Amb 4} (hq : q ∈ interSet D N) {i : Fin 5}
    (hsurj_i : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (chartDiff (D (sqPart q)) D N) q v.1))
    (hother : ∀ j : Fin 5, j ≠ i → q j ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (η : ℝ → Amb 4) (ε : ℝ), 0 < ε ∧ ContDiff ℝ Ctop η ∧ (∀ u, η u i = 0) ∧
      graphMap i η (q i) = q ∧
      (∀ u, |u - q i| < ε → u ∈ Set.Icc (0 : ℝ) 1 →
        graphMap i η u ∈ Submission.Drive.unitBox 4) ∧
      (∀ u, |u - q i| < ε →
        D (sqPart (graphMap i η u)) = N (cbPart (graphMap i η u))) ∧
      (∀ u, |u - q i| < ε → u ∈ Set.Icc (0 : ℝ) 1 →
        V (graphMap i η u) = fderiv ℝ (graphMap i η) u ((V (graphMap i η u)) i)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ u, |u - q i| ≤ ε → ‖fderiv ℝ (graphMap i η) u‖ ≤ C) := by
  classical
  obtain ⟨-, heq⟩ := mem_interSet.mp hq
  have hmemSrc : ∀ y : M, y ∈ (chr y).source := fun y => by
    rw [chr, ← extChartAt_source (I := 𝓡 4) y]
    exact mem_extChartAt_source _
  have hregq : q ∈ chartRegion (D (sqPart q)) D N := by
    rw [mem_chartRegion]
    exact ⟨hmemSrc _, by rw [← heq]; exact hmemSrc _⟩
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hchar⟩ :=
    exists_local_graph (D (sqPart q)) D N hD hN hregq heq i hsurj_i
  have hηdiff : Differentiable ℝ η := hηcd.differentiable (by simp)
  -- the graph points whose `i`-th coordinate is near `q i` have all other coordinates inside
  -- `(0,1)`
  have hgood : ∀ᶠ u in 𝓝 (q i), ∀ j : Fin 5, j ≠ i →
      (graphMap i η u) j ∈ Set.Ioo (0 : ℝ) 1 := by
    refine Filter.eventually_all.mpr (fun j => ?_)
    rcases eq_or_ne j i with rfl | hj
    · exact Filter.Eventually.of_forall (fun u hu => absurd rfl hu)
    · have hqj : η (q i) j = q j := by
        rw [hηx]
        simp [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, hj]
      have hmem' : {x : Work.Drive.Amb 4 | x j ∈ Set.Ioo (0 : ℝ) 1} ∈ 𝓝 (η (q i)) :=
        (isOpen_Ioo.preimage (by fun_prop)).mem_nhds
          (show (η (q i)) j ∈ Set.Ioo (0 : ℝ) 1 by rw [hqj]; exact hother j hj)
      filter_upwards [hηcd.continuous.continuousAt.preimage_mem_nhds hmem'] with u hu
      simpa [graphMap_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hj] using hu
  obtain ⟨ε₁, hε₁, hε₁'⟩ := Metric.eventually_nhds_iff.mp hgood
  -- the local graph characterization at the graph points
  have hchar_at : ∀ t : ℝ, |t - q i| < δ →
      graphMap i η t ∈ chartRegion (D (sqPart q)) D N ∧
        (D (sqPart (graphMap i η t)) = N (cbPart (graphMap i η t)) ↔
          graphMap i η t = (graphMap i η t) i • EuclideanSpace.single i (1 : ℝ) +
            η ((graphMap i η t) i)) := by
    intro t ht
    refine hchar (graphMap i η t) ?_ ?_
    · rwa [graphMap_apply_i hηi]
    · rw [graphMap_apply_i hηi, graphMap_apply]
      simp [hρ]
  have hK_at : ∀ t : ℝ, |t - q i| < δ →
      D (sqPart (graphMap i η t)) = N (cbPart (graphMap i η t)) :=
    fun t ht => ((hchar_at t ht).2).mpr (by rw [graphMap_apply_i hηi]; rfl)
  have hbox_at : ∀ u : ℝ, |u - q i| < min δ ε₁ → u ∈ Set.Icc (0 : ℝ) 1 →
      graphMap i η u ∈ Submission.Drive.unitBox 4 := by
    intro u hu huIcc
    rw [Submission.Drive.unitBox]
    intro j
    rcases eq_or_ne j i with rfl | hj
    · rw [graphMap_apply_i hηi]
      exact huIcc
    · exact Set.Ioo_subset_Icc_self
        (hε₁' (by rw [Real.dist_eq]; exact lt_of_lt_of_le hu (min_le_right _ _)) j hj)
  refine ⟨η, min δ ε₁, lt_min hδ hε₁, hηcd, hηi, ?_, ?_, ?_, ?_, ?_⟩
  · -- the graph passes through `q`
    rw [graphMap_apply, hηx]
    abel
  · -- the graph points with coordinate in `[0,1]` are in the box
    exact hbox_at
  · -- the graph points are in `K`
    intro u hu
    exact hK_at u (lt_of_lt_of_le hu (min_le_left _ _))
  · -- the field is tangent to the graph
    intro u hu huIcc
    have huδ : |u - q i| < δ := lt_of_lt_of_le hu (min_le_left _ _)
    have hreg_gu : graphMap i η u ∈ chartRegion (D (sqPart q)) D N := (hchar_at u huδ).1
    have heq_gu : D (sqPart (graphMap i η u)) = N (cbPart (graphMap i η u)) := hK_at u huδ
    have hbox_gu : graphMap i η u ∈ Submission.Drive.unitBox 4 := hbox_at u hu huIcc
    have hsurj : Function.Surjective
        (fderiv ℝ (chartDiff (D (sqPart q)) D N) (graphMap i η u)) :=
      chartDiff_surjective_of_transverse (D (sqPart q)) D N hD hN hreg_gu heq_gu
        (htrans (graphMap i η u) hbox_gu heq_gu)
    have hker : fderiv ℝ (chartDiff (D (sqPart q)) D N) (graphMap i η u)
        (V (graphMap i η u)) = 0 :=
      hVtan (graphMap i η u) hbox_gu heq_gu (D (sqPart q)) hreg_gu
    have hψd : DifferentiableAt ℝ (chartDiff (D (sqPart q)) D N) (graphMap i η u) :=
      ((contDiffOn_chartDiff (D (sqPart q)) D N hD hN).contDiffAt
        ((isOpen_chartRegion (D (sqPart q)) D N hD.continuous hN.continuous).mem_nhds
          hreg_gu)).differentiableAt (by simp)
    have hψvan : ∀ᶠ t in 𝓝 u, chartDiff (D (sqPart q)) D N (graphMap i η t) = 0 := by
      have hset : {t : ℝ | |t - q i| < δ} ∈ 𝓝 u :=
        (isOpen_lt (by fun_prop : Continuous fun t : ℝ => |t - q i|) continuous_const).mem_nhds
          huδ
      filter_upwards [hset] with t ht
      rw [chartDiff_eq_zero_iff (hchar_at t ht).1]
      exact ((hchar_at t ht).2).mpr (by rw [graphMap_apply_i hηi]; rfl)
    exact eq_fderiv_graphMap_of_fderiv_eq_zero (v := V (graphMap i η u))
      hηdiff.differentiableAt hηi hψd hψvan hsurj hker
  · -- the derivative of the graph map is bounded
    obtain ⟨C, hC⟩ : ∃ C, ∀ u ∈ Set.Icc (q i - min δ ε₁) (q i + min δ ε₁),
        ‖fderiv ℝ (graphMap i η) u‖ ≤ C := by
      refine IsCompact.exists_bound_of_continuousOn isCompact_Icc ?_
      exact ((contDiff_graphMap hηcd).continuous_fderiv (by simp)).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun u hu => ?_⟩
    have hu' : u ∈ Set.Icc (q i - min δ ε₁) (q i + min δ ε₁) := by
      have h := abs_le.mp hu
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    exact (hC u hu').trans (le_max_left _ _)

/-- **The flow line through a point of the intersection set stays on it, for a short forward time.**

If `q ∈ K = interSet D N` and the flow line of `q` stays in the closed box for times in `[0,E]`
(`E > 0`), then there is `ε ∈ (0,E]` such that the flow line of `q` is again in `K` for all times in
`[0,ε]`.

This is the local step: the intersection set is, near `q`, the graph of `η` over a suitable
coordinate `i`, and the field `V` is tangent to that graph, so the graph is invariant under the flow
(`eq_graphMap_of_tangent_flow_right`).  The coordinate `i` is the coordinate of a face of the box
carrying `q` when `q` is on the boundary (`hface` gives it, and the tangency at `q` upgrades it to
one for which the charted difference map is surjective on `{v | v i = 0}`), and an arbitrary
transversal coordinate when `q` is in the interior of the box. -/
theorem flowV_local_interSet_right {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (sqPart x) = N (cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (cbPart x)).toLinearMap = ⊤)
    (V : Amb 4 → Amb 4) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (hVtan : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (sqPart x) = N (cbPart x) → ∀ p : M, x ∈ chartRegion p D N →
      fderiv ℝ (chartDiff p D N) x (V x) = 0)
    (hface : ∀ b : Amb 4, b ∈ interSet D N → b ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
        V b i ≠ 0)
    {q : Amb 4} (hq : q ∈ interSet D N) {E : ℝ} (hE : 0 < E)
    (hbox : ∀ s ∈ Set.Icc (0 : ℝ) E, flowV V hV hVs s q ∈ Submission.Drive.unitBox 4) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ E ∧
      ∀ s ∈ Set.Icc (0 : ℝ) ε, flowV V hV hVs s q ∈ interSet D N := by
  classical
  obtain ⟨hboxq, heq⟩ := mem_interSet.mp hq
  have hmemSrc : ∀ y : M, y ∈ (chr y).source := fun y => by
    rw [chr, ← extChartAt_source (I := 𝓡 4) y]
    exact mem_extChartAt_source _
  have hregq : q ∈ chartRegion (D (sqPart q)) D N := by
    rw [mem_chartRegion]
    exact ⟨hmemSrc _, by rw [← heq]; exact hmemSrc _⟩
  have hsurjq : Function.Surjective (fderiv ℝ (chartDiff (D (sqPart q)) D N) q) :=
    chartDiff_surjective_of_transverse (D (sqPart q)) D N hD hN hregq heq
      (htrans q hboxq heq)
  -- choose the coordinate over which the intersection set is a graph near `q`
  have hkey : ∃ i : Fin 5, (Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
        fderiv ℝ (chartDiff (D (sqPart q)) D N) q v.1)) ∧
      (∀ j : Fin 5, j ≠ i → q j ∈ Set.Ioo (0 : ℝ) 1) := by
    by_cases hint : q ∈ interior (Submission.Drive.unitBox 4)
    · obtain ⟨i, hi⟩ := exists_domRestrict_surjective hsurjq
      refine ⟨i, hi, fun j _ => ?_⟩
      rw [Work.Drive.interior_unitBox] at hint
      exact hint j
    · have hbdry : q ∈ Submission.Drive.unitBoxBdry 4 :=
        ⟨hboxq, exists_coord_eq_zero_or_one_of_not_mem_interior hboxq hint⟩
      obtain ⟨i, -, hother, hVne⟩ := hface q hq hbdry
      refine ⟨i, ?_, hother⟩
      rw [surjective_domRestrict_iff_cofactorVec_ne_zero _ hsurjq i]
      have hker : fderiv ℝ (chartDiff (D (sqPart q)) D N) q (V q) = 0 :=
        hVtan q hboxq heq (D (sqPart q)) hregq
      have hVne0 : V q ≠ 0 := fun h0 => hVne (by simp [h0])
      exact (cofactorVec_apply_ne_zero_iff _ hsurjq hker hVne0 i).mpr hVne
  obtain ⟨i, hsurj_i, hother⟩ := hkey
  -- the local graph data
  obtain ⟨η, εs, hεs, hηcd, hηi, hgq, -, hK_at, htan_at, C, -, hC⟩ :=
    exists_local_tangent_data (V := V) D N hD hN htrans hVtan hq hsurj_i hother
  have hηdiff : Differentiable ℝ η := hηcd.differentiable (by simp)
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport hV hVs
  set γ : ℝ → Amb 4 := fun s => flowV V hV hVs s q with hγdef
  have hγ : ∀ s, HasDerivAt γ (V (γ s)) s := fun s => flowV_deriv V hV hVs q s
  have hγ0 : γ 0 = q := flowV_zero V hV hVs q
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  -- a time interval on which the flow remains close to `q`
  obtain ⟨ε₁, hε₁, hε₁'⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ s : ℝ, |s| < ε₁ → ‖γ s - q‖ < εs := by
    have hball : Metric.ball q εs ∈ 𝓝 (γ 0) := by
      rw [hγ0]
      exact Metric.ball_mem_nhds q hεs
    obtain ⟨ε₁, hε₁, hε₁'⟩ :=
      Metric.eventually_nhds_iff.mp (hγc.continuousAt.preimage_mem_nhds hball)
    exact ⟨ε₁, hε₁, fun s hs => hε₁' (by rwa [Real.dist_eq, sub_zero])⟩
  refine ⟨min (ε₁ / 2) E, lt_min (by linarith) hE, min_le_right _ _, ?_⟩
  intro s hs
  have hsE : s ∈ Set.Icc (0 : ℝ) E := ⟨hs.1, le_trans hs.2 (min_le_right _ _)⟩
  have hsa : |s| < ε₁ := by
    rw [abs_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 (min_lt_of_left_lt (by linarith))
  have hclose : |(γ s) i - q i| < εs := by
    have h1 : |(γ s) i - q i| ≤ ‖γ s - q‖ := by
      have h := PiLp.norm_apply_le (γ s - q) i
      simpa [PiLp.sub_apply, Real.norm_eq_abs] using h
    exact lt_of_le_of_lt h1 (hε₁' s hsa)
  have hubox : (γ s) i ∈ Set.Icc (0 : ℝ) 1 := (hbox s hsE) i
  -- the hypothesis of `eq_graphMap_of_tangent_flow_right` on the whole interval
  have htan : ∀ s' ∈ Set.Icc (0 : ℝ) (min (ε₁ / 2) E),
      V (graphMap i η ((γ s') i)) =
        fderiv ℝ (graphMap i η) ((γ s') i) ((V (graphMap i η ((γ s') i))) i) := by
    intro s' hs'
    have hs'E : s' ∈ Set.Icc (0 : ℝ) E := ⟨hs'.1, le_trans hs'.2 (min_le_right _ _)⟩
    have hsa' : |s'| < ε₁ := by
      rw [abs_of_nonneg hs'.1]
      exact lt_of_le_of_lt hs'.2 (min_lt_of_left_lt (by linarith))
    have hcl' : |(γ s') i - q i| < εs := by
      have h1 : |(γ s') i - q i| ≤ ‖γ s' - q‖ := by
        have h := PiLp.norm_apply_le (γ s' - q) i
        simpa [PiLp.sub_apply, Real.norm_eq_abs] using h
      exact lt_of_le_of_lt h1 (hε₁' s' hsa')
    exact htan_at ((γ s') i) hcl' ((hbox s' hs'E) i)
  have hC' : ∀ s' ∈ Set.Icc (0 : ℝ) (min (ε₁ / 2) E),
      ‖fderiv ℝ (graphMap i η) ((γ s') i)‖ ≤ C := by
    intro s' hs'
    have hs'E : s' ∈ Set.Icc (0 : ℝ) E := ⟨hs'.1, le_trans hs'.2 (min_le_right _ _)⟩
    have hsa' : |s'| < ε₁ := by
      rw [abs_of_nonneg hs'.1]
      exact lt_of_le_of_lt hs'.2 (min_lt_of_left_lt (by linarith))
    have hcl' : |(γ s') i - q i| < εs := by
      have h1 : |(γ s') i - q i| ≤ ‖γ s' - q‖ := by
        have h := PiLp.norm_apply_le (γ s' - q) i
        simpa [PiLp.sub_apply, Real.norm_eq_abs] using h
      exact lt_of_le_of_lt h1 (hε₁' s' hsa')
    exact hC ((γ s') i) hcl'.le
  have hinit : γ 0 = graphMap i η ((γ 0) i) := by
    rw [hγ0]
    exact hgq.symm
  have hgraph : ∀ s' ∈ Set.Icc (0 : ℝ) (min (ε₁ / 2) E),
      γ s' = graphMap i η ((γ s') i) :=
    eq_graphMap_of_tangent_flow_right (i := i) (ε := min (ε₁ / 2) E) hL hγ hηdiff
      (lt_min (by linarith) hE) hC' htan hinit
  have hfinal : flowV V hV hVs s q = graphMap i η ((γ s) i) := by
    change γ s = graphMap i η ((γ s) i)
    exact hgraph s hs
  rw [hfinal]
  exact mem_interSet.mpr
    ⟨by rw [← hfinal]; exact hbox s hsE, hK_at ((γ s) i) hclose⟩

open scoped Manifold ContDiff in
/-- **The intersection set is preserved by the flow while the line stays in the box, under the face
condition.**  `interSet D N = {x ∈ [0,1]⁵ | D (sqPart x) = N (cbPart x)}` for smooth chains
`D : ℝ² → M`, `N : ℝ³ → M` in a smooth 4-manifold `M`; `V` is a compactly supported smooth field,
tangent to `{D (sqPart ·) = N (cbPart ·)}` at every point of the box (`hVtan`), `flowV V hV hVs` is
its global flow (`flowV_zero/deriv/add` available), and `hface` is the face condition: at every point
of `interSet D N` on the boundary of the box, exactly one coordinate is `0` or `1`, all other
coordinates are strictly inside `(0,1)`, and the corresponding component of `V` is non-zero (i.e. the
flow crosses that face transversally).

If the flow line of `x ∈ interSet D N` stays in the closed box on the whole interval between the times
`0` and `t`, then it is again in `interSet D N` at time `t`.

Note this is *not* the naive invariance (`interSet` is not flow-invariant: at a boundary point the
flow line leaves the box, and `hVtan` says nothing about `V` outside the box), and `hface` is
essential: without the transversality at the face, a flow line can leave `{D (sqPart ·) = N (cbPart ·)}`
while staying in the box (tangential contact with a face).

Intended proof: `A := {s ∈ Set.uIcc 0 t | flowV V hV hVs s x ∈ interSet D N}` is closed (the
intersection set is closed) and non-empty (`0 ∈ A`), and is open in `Set.uIcc 0 t`, so `A = Set.uIcc 0 t`.
For the openness at `s₀ ∈ A`, put `γ := flowV V hV hVs · x` and `q := γ s₀ ∈ K`.  If `s₀` is an
interior point of `Set.uIcc 0 t`, then `q` is in the *interior* of the box (otherwise `hface` plus
`Work.Drive.crossing_of_deriv_ne_zero_gen` would put the line outside the box on one side of `s₀`,
contradicting the hypothesis).  In either case the chart at `q`
(`Work.Drive.exists_local_graph`, with an index from `Work.Drive.exists_domRestrict_surjective`
applied to `Work.Drive.chartDiff_surjective_of_transverse`) exhibits
`{y | D (sqPart y) = N (cbPart y)}` near `q` as the graph `u ↦ u • eᵢ + η u`; the graph points
visited near `q` lie in the box (their only possibly-extreme coordinate is the `i`-th, which moves
inward from the face), so `hVtan` applies at them.  Writing `γ s = graph (u s) + n s`,
`u s := (γ s) i`, both `s ↦ (u s, 0)` and `s ↦ (u s, n s)` solve the same ODE
`(u', n') = (V (graph u + n) i, V (graph u + n) - (graph ∘ u)')`, whose right-hand side vanishes at
`n = 0` because `V` is tangent to `K = graph` there; uniqueness of ODE solutions
(`Mathlib.Analysis.ODE.ExistUnique.ODE_solution_unique`) gives `n ≡ 0` on the times where the graph
points lie in the box, which is a relative neighbourhood of `s₀`. -/
theorem boxMapsTo_flowV_interSet {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (htrans : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x)).toLinearMap = ⊤)
    (V : Work.Drive.Amb 4 → Work.Drive.Amb 4) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVs : HasCompactSupport V)
    (hVtan : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) → ∀ p : M,
      x ∈ Work.Drive.chartRegion p D N →
      fderiv ℝ (Work.Drive.chartDiff p D N) x (V x) = 0)
    (hface : ∀ b : Work.Drive.Amb 4, b ∈ Work.Drive.interSet D N →
      b ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
        V b i ≠ 0)
    (x : Work.Drive.Amb 4) (hx : x ∈ Work.Drive.interSet D N) (t : ℝ)
    (hbox : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      Work.Drive.flowV V hV hVs u x ∈ Submission.Drive.unitBox 4) :
    Work.Drive.flowV V hV hVs t x ∈ Work.Drive.interSet D N := by
  classical
  -- the argument for `t ≥ 0`, applicable to any tangent field `V'`
  have hpos : ∀ (V' : Amb 4 → Amb 4) (hV' : ContDiff ℝ Ctop V') (hVs' : HasCompactSupport V')
      (hVtan' : ∀ y : Amb 4, y ∈ Submission.Drive.unitBox 4 →
        D (sqPart y) = N (cbPart y) → ∀ p : M, y ∈ chartRegion p D N →
        fderiv ℝ (chartDiff p D N) y (V' y) = 0)
      (hface' : ∀ b : Amb 4, b ∈ interSet D N → b ∈ Submission.Drive.unitBoxBdry 4 →
        ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧
          (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ V' b i ≠ 0)
      (t' : ℝ), 0 ≤ t' → (∀ u ∈ Set.uIcc (0 : ℝ) t',
          flowV V' hV' hVs' u x ∈ Submission.Drive.unitBox 4) →
        flowV V' hV' hVs' t' x ∈ interSet D N := by
    intro V' hV' hVs' hVtan' hface' t' ht0 htbox
    have htbox' : ∀ u ∈ Set.Icc (0 : ℝ) t',
        flowV V' hV' hVs' u x ∈ Submission.Drive.unitBox 4 := by
      intro u hu
      exact htbox u (by rw [Set.uIcc_of_le ht0]; exact hu)
    have hγc : Continuous (fun s : ℝ => flowV V' hV' hVs' s x) :=
      continuous_iff_continuousAt.mpr fun s => (flowV_deriv V' hV' hVs' x s).continuousAt
    have hKclosed : IsClosed (interSet D N) :=
      (isCompact_interSet D N hD.continuous hN.continuous).isClosed
    set A : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) t' ∧
      flowV V' hV' hVs' s x ∈ interSet D N} with hA
    have hAclosed : IsClosed A := by
      rw [hA]
      exact (isClosed_Icc.preimage continuous_id).inter (hKclosed.preimage hγc)
    have hAne : A.Nonempty := ⟨0, by
      rw [hA]
      exact ⟨⟨le_rfl, ht0⟩, by rw [flowV_zero]; exact hx⟩⟩
    have hAbdd : BddAbove A := ⟨t', fun s hs => hs.1.2⟩
    set T : ℝ := sSup A with hT
    have hTmem : T ∈ A := hAclosed.csSup_mem hAne hAbdd
    have hTE : T = t' := by
      by_contra hne
      have hTlt : T < t' := lt_of_le_of_ne hTmem.1.2 hne
      set q' : Amb 4 := flowV V' hV' hVs' T x with hq'def
      have hq'K : q' ∈ interSet D N := hTmem.2
      have hbox' : ∀ s ∈ Set.Icc (0 : ℝ) (t' - T),
          flowV V' hV' hVs' s q' ∈ Submission.Drive.unitBox 4 := by
        intro s hs
        have h1 : flowV V' hV' hVs' s q' = flowV V' hV' hVs' (s + T) x := by
          rw [hq'def, flowV_add]
        rw [h1]
        exact htbox' (s + T) ⟨by linarith [hs.1, hTmem.1.1, hTlt], by linarith [hs.2]⟩
      obtain ⟨ε, hε, hεE, hloc⟩ :=
        flowV_local_interSet_right D N hD hN htrans V' hV' hVs' hVtan' hface'
          hq'K (by linarith) hbox'
      have hmem : T + ε / 2 ∈ A := by
        refine ⟨⟨by linarith [hTmem.1.1], by linarith [hεE]⟩, ?_⟩
        have hs : ε / 2 ∈ Set.Icc (0 : ℝ) ε := ⟨by linarith, by linarith⟩
        have h2 : flowV V' hV' hVs' (ε / 2) q' ∈ interSet D N := hloc (ε / 2) hs
        have h3 : flowV V' hV' hVs' (ε / 2) q' = flowV V' hV' hVs' (T + ε / 2) x := by
          rw [hq'def, ← flowV_add]
          congr 1
          ring
        rwa [h3] at h2
      have hle := le_csSup hAbdd hmem
      linarith [hε]
    rw [← hTE]
    exact hTmem.2
  by_cases ht : (0 : ℝ) ≤ t
  · exact hpos V hV hVs hVtan hface t ht hbox
  · -- `t < 0`: apply the nonnegative case to the reversed field `-V`
    have htneg : t < 0 := not_le.mp ht
    have hV1 : ContDiff ℝ Ctop (-V) := hV.neg
    have hVs1 : HasCompactSupport (-V) := hVs.neg
    have hVtan1 : ∀ y : Amb 4, y ∈ Submission.Drive.unitBox 4 →
        D (sqPart y) = N (cbPart y) → ∀ p : M, y ∈ chartRegion p D N →
        fderiv ℝ (chartDiff p D N) y ((-V) y) = 0 := by
      intro y hy hyeq p hype
      rw [Pi.neg_apply, map_neg, hVtan y hy hyeq p hype, neg_zero]
    have hface1 : ∀ b : Amb 4, b ∈ interSet D N → b ∈ Submission.Drive.unitBoxBdry 4 →
        ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧
          (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ (-V) b i ≠ 0 := by
      intro b hb hbd
      obtain ⟨i, hi, hoth, hVne⟩ := hface b hb hbd
      exact ⟨i, hi, hoth, by simpa using hVne⟩
    have hbox1 : ∀ u ∈ Set.uIcc (0 : ℝ) (-t),
        flowV (-V) hV1 hVs1 u x ∈ Submission.Drive.unitBox 4 := by
      intro u hu
      have hu1 : u ∈ Set.Icc (0 : ℝ) (-t) := by rwa [Set.uIcc_of_le (by linarith)] at hu
      rw [flowV_neg (V := V) hV hVs hV1 hVs1 u x]
      refine hbox (-u) ?_
      rw [Set.uIcc_comm, Set.uIcc_of_le htneg.le]
      exact ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
    have hfinal := hpos (-V) hV1 hVs1 hVtan1 hface1 (-t) (by linarith) hbox1
    rw [flowV_neg (V := V) hV hVs hV1 hVs1 (-t) x] at hfinal
    simpa using hfinal

end

end Work.Drive.ManifoldParity
