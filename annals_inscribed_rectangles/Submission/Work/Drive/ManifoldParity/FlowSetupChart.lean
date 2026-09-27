import Mathlib
import Submission.Work.Drive.ManifoldParity.FlowSetupDefs
import Submission.Work.Drive.chart_visit_bddAbove

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Flow lines visit chart regions for bounded time, and the in-box arc is bounded

This is the abstract version (for a general tangential flow `FlowSetup`) of the vector-space
lemmas `Work.Drive.chart_exit` / `Work.Drive.chart_visit_bddAbove` (a flow line leaves a chart
region after bounded time) and `Work.Drive.in_box_arc_right` (the in-box arc of a flow line through
a boundary point of `K` is bounded).

The negative-time version `arc_bound_neg` is obtained from the positive-time one by applying it to
the reversed setup (`FlowSetup.reverse`), which is why only one of the two hard vector-space
arguments has to be redone.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set Filter

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {m : ℕ}

/-- A point of the boundary of the unit box is not in its interior. -/
theorem not_mem_interior_unitBox_of_mem_unitBoxBdry {m : ℕ} {b : Amb m}
    (hb : b ∈ Submission.Drive.unitBoxBdry m) : b ∉ interior (Submission.Drive.unitBox m) := by
  obtain ⟨_, i, hi⟩ := hb
  intro h
  rw [interior_unitBox m] at h
  have h' := h i
  rcases hi with h0 | h1
  · rw [h0] at h'; exact absurd h'.1 (lt_irrefl 0)
  · rw [h1] at h'; exact absurd h'.2 (lt_irrefl 1)

/-- **A chart visit of a flow line ends.**  Let `C` be a chart for `K` and let `x ∈ K`.  If the flow
line of `x` is at time `t` in the region of the chart, then there is a time `R ≥ t` at which it
leaves the region, through the boundary point prescribed by the sign of the `i`-th component of the
field at `S.line x t`: `S.line x R = C.graph (p i + chartSign (W (S.line x t) i) * δ)`. -/
theorem chart_exit_line_pos (S : FlowSetup m) {x : Amb m} (hx : x ∈ S.K) {p : Amb m}
    (C : FlowChart S.W S.K p) {t : ℝ} (ht : S.line x t ∈ C.region) (htpos : 0 ≤ t)
    (hKreg : ∀ s : ℝ, 0 ≤ s → S.line x s ∈ C.region → S.line x s ∈ S.K) :
    ∃ R : ℝ, t ≤ R ∧
      S.line x R = C.graph (p C.i + chartSign (S.W (S.line x t) C.i) * C.δ) := by
  classical
  set γ : ℝ → Amb m := S.line x with hγdef
  have hγ : ∀ t : ℝ, HasDerivAt γ (S.W (γ t)) t := fun t => S.line_deriv x t
  have hflow : Continuous S.W := S.cont
  set T : Set ℝ := {s | γ s ∈ C.region} with hTdef
  set u : ℝ → ℝ := fun s => γ s C.i with hudef
  set g : ℝ → ℝ := fun s => S.W (γ s) C.i with hgdef
  have hγc : Continuous γ := S.line_continuous x
  have huc : Continuous u := by
    rw [hudef]
    exact (PiLp.continuous_apply 2 (fun _ : Fin (m+1) => ℝ) C.i).comp hγc
  have hgc : Continuous g := by
    rw [hgdef]
    exact (PiLp.continuous_apply 2 (fun _ : Fin (m+1) => ℝ) C.i).comp (hflow.comp hγc)
  have hud : ∀ s, HasDerivAt u (g s) s := by
    intro s
    rw [hudef, hgdef]
    exact hasDerivAt_apply (hγ s) C.i
  have hgmem : ∀ s ∈ T, C.c ≤ |g s| := by
    intro s hs
    have hs' : γ s ∈ C.region := hs
    rw [FlowChart.mem_region] at hs'
    rw [hgdef]
    exact C.hvel (γ s) hs'.1 hs'.2
  have hu_mem : ∀ s ∈ T, |u s - p C.i| < C.δ := by
    intro s hs
    have hs' : γ s ∈ C.region := hs
    rw [FlowChart.mem_region] at hs'
    rw [hudef]
    exact hs'.1
  have htT : t ∈ T := ht
  have hgt_ne : g t ≠ 0 := by
    have h := hgmem t htT
    intro h0
    rw [h0, abs_zero] at h
    linarith [C.hc]
  set σ : ℝ := chartSign (g t) with hσdef
  have hσpos : 0 < σ * g t := by rw [hσdef]; exact chartSign_mul_pos hgt_ne
  have hσmem : σ = 1 ∨ σ = -1 := by rw [hσdef]; exact chartSign_eq_one_or_neg_one (g t)
  have hσsq : σ * σ = 1 := by rw [hσdef]; exact chartSign_mul_self (g t)
  set E : Set ℝ := {s | t ≤ s ∧ Set.Icc t s ⊆ T} with hEdef
  have htE : t ∈ E := by
    rw [hEdef]
    refine ⟨le_rfl, fun x hx => ?_⟩
    rw [Set.mem_Icc] at hx
    have : x = t := le_antisymm hx.2 hx.1
    rw [this]
    exact htT
  -- On an initial segment `Icc t s ⊆ T` the coordinate `σ * u` grows at speed at least `c`.
  have key : ∀ s ∈ E, σ * u t + C.c * (s - t) ≤ σ * u s := by
    intro s hsE
    rw [hEdef] at hsE
    obtain ⟨hts, hsub⟩ := hsE
    rcases lt_or_eq_of_le hts with hlt | heq
    · have hcont : ContinuousOn (fun r => σ * u r) (Set.Icc t s) :=
        (continuous_const.mul huc).continuousOn
      have hdiff : DifferentiableOn ℝ (fun r => σ * u r) (Set.Ioo t s) :=
        fun r _ => ((hud r).const_mul σ).differentiableAt.differentiableWithinAt
      obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope (fun r => σ * u r) hlt hcont hdiff
      have hξT : ξ ∈ T := hsub (Set.Ioo_subset_Icc_self hξ)
      have hne : ∀ r ∈ Set.Icc t s, σ * g r ≠ 0 := by
        intro r hr
        have hrT : r ∈ T := hsub hr
        have hgr : g r ≠ 0 := by
          have h := hgmem r hrT
          intro h0
          rw [h0, abs_zero] at h
          linarith [C.hc]
        rcases hσmem with h1 | h1
        · rw [h1, one_mul]; exact hgr
        · rw [h1, neg_one_mul]; exact neg_ne_zero.mpr hgr
      have hsign : 0 < σ * g ξ := by
        rcases sign_const_of_preconnected isPreconnected_Icc
          (continuous_const.mul hgc).continuousOn hne with h | h
        · exact h ξ (Set.Ioo_subset_Icc_self hξ)
        · exact absurd (h t (Set.left_mem_Icc.mpr hts)) (not_lt.mpr hσpos.le)
      have hcξ : C.c ≤ σ * g ξ := by
        have habs : σ * g ξ = |g ξ| := by
          rcases hσmem with h1 | h1
          · have hs1 : 0 < g ξ := by
              have h := hsign
              rw [h1, one_mul] at h
              exact h
            rw [h1, one_mul]
            exact (abs_of_pos hs1).symm
          · have hs1 : g ξ < 0 := by
              have h := hsign
              rw [h1, neg_one_mul] at h
              exact neg_pos.mp h
            rw [h1, neg_one_mul]
            exact (abs_of_neg hs1).symm
        rw [habs]
        exact hgmem ξ hξT
      have hder : σ * g ξ = (σ * u s - σ * u t) / (s - t) := by
        rw [← hξd]
        exact (((hud ξ).const_mul σ).deriv).symm
      have hst : 0 < s - t := by linarith
      have hmain : C.c * (s - t) ≤ σ * u s - σ * u t :=
        (le_div_iff₀ hst).mp (hder ▸ hcξ)
      linarith
    · rw [heq]
      simp
  have hEbdd : BddAbove E := by
    refine ⟨t + (σ * p C.i + C.δ - σ * u t) / C.c, fun s hs => ?_⟩
    have hkey := key s hs
    rw [hEdef] at hs
    obtain ⟨hts, hsub⟩ := hs
    have hsT : s ∈ T := hsub (Set.right_mem_Icc.mpr hts)
    have hus := hu_mem s hsT
    have hus' : σ * u s < σ * p C.i + C.δ := by
      have h := abs_lt.mp hus
      rcases hσmem with h1 | h1
      · rw [h1, one_mul]; linarith [h.2]
      · rw [h1]; linarith [h.1]
    have h1 : C.c * (s - t) < σ * p C.i + C.δ - σ * u t := by linarith
    have h2 : s - t < (σ * p C.i + C.δ - σ * u t) / C.c :=
      (lt_div_iff₀ C.hc).mpr (by rw [mul_comm]; exact h1)
    linarith
  have hEne : E.Nonempty := ⟨t, htE⟩
  set R : ℝ := sSup E with hRdef
  have htR : t ≤ R := le_csSup hEbdd htE
  have hsubR : Set.Ico t R ⊆ T := by
    intro s hs
    obtain ⟨hts, hsR⟩ := hs
    obtain ⟨s', hs'E, hss'⟩ := exists_lt_of_lt_csSup hEne hsR
    exact hs'E.2 ⟨hts, hss'.le⟩
  have hRnotT : R ∉ T := by
    intro hRT
    have hev : ∀ᶠ y in 𝓝 R, γ y ∈ C.region :=
      hγc.continuousAt.preimage_mem_nhds (C.isOpen_region.mem_nhds hRT)
    obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff.mp hev
    have hmem : R + η/2 ∈ E := by
      rw [hEdef]
      refine ⟨by linarith, fun y hy => ?_⟩
      rw [Set.mem_Icc] at hy
      rcases lt_or_ge y R with hyR | hyR
      · exact hsubR ⟨hy.1, hyR⟩
      · rcases eq_or_lt_of_le hyR with h | h
        · rw [← h]
          exact hRT
        · exact hη (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩)
    have hle := le_csSup hEbdd hmem
    linarith
  have htt : t < R := lt_of_le_of_ne htR (fun h => hRnotT (h ▸ htT))
  have hcl : R ∈ closure (Set.Ico t R) := by
    refine mem_closure_iff.mpr fun O hO hRO => ?_
    obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hRO)
    refine ⟨max t (R - η/2), ?_, ?_⟩
    · have hmax_le : max t (R - η/2) ≤ R := max_le htt.le (by linarith)
      have hmax_ge : R - η/2 ≤ max t (R - η/2) := le_max_right _ _
      refine hη ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    · rw [Set.mem_Ico]
      refine ⟨le_max_left _ _, ?_⟩
      rcases le_total t (R - η/2) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; exact htt
  have hgraph : ∀ s ∈ Set.Ico t R, γ s = C.graph (u s) := by
    intro s hs
    rw [hudef]
    exact C.eq_graph_of_mem_region (hsubR hs)
      (hKreg s (by linarith [hs.1, htpos]) (hsubR hs))
  have hγR : γ R = C.graph (u R) := by
    have hclosed : IsClosed {s : ℝ | γ s = C.graph (u s)} :=
      isClosed_eq hγc (C.continuous_graph.comp huc)
    have hsub' : Set.Ico t R ⊆ {s : ℝ | γ s = C.graph (u s)} := fun s hs => hgraph s hs
    exact (closure_minimal hsub' hclosed) hcl
  have hneBot : (𝓝[Set.Ico t R] R).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hIco_mem : Set.Ico t R ∈ 𝓝[Set.Ico t R] R := self_mem_nhdsWithin
  have hσu_tend : Tendsto (fun s => σ * u s) (𝓝[Set.Ico t R] R) (𝓝 (σ * u R)) :=
    ((continuous_const.mul huc).tendsto R).mono_left nhdsWithin_le_nhds
  have hlin_tend : Tendsto (fun s : ℝ => σ * u t + C.c * (s - t)) (𝓝[Set.Ico t R] R)
      (𝓝 (σ * u t + C.c * (R - t))) :=
    ((continuous_const.add (continuous_const.mul
      (continuous_id.sub continuous_const))).tendsto R).mono_left nhdsWithin_le_nhds
  have hev1 : ∀ᶠ s in 𝓝[Set.Ico t R] R, σ * u t + C.c * (s - t) - σ * u s ≤ 0 := by
    filter_upwards [hIco_mem] with s hs
    have hkey := key s (by rw [hEdef]; exact ⟨hs.1, (Set.Icc_subset_Ico_right hs.2).trans hsubR⟩)
    linarith
  have hineq1 : σ * u t + C.c * (R - t) ≤ σ * u R := by
    have h := le_of_tendsto (hlin_tend.sub hσu_tend) hev1
    linarith
  have hev2 : ∀ᶠ s in 𝓝[Set.Ico t R] R, σ * u s ≤ σ * p C.i + C.δ := by
    filter_upwards [hIco_mem] with s hs
    have hsT : s ∈ T := hsubR hs
    have hnorm := abs_lt.mp (hu_mem s hsT)
    have hlt : σ * (u s - p C.i) < C.δ := by
      rcases hσmem with h1 | h1
      · rw [h1, one_mul]; exact hnorm.2
      · rw [h1]; linarith [hnorm.1]
    rw [mul_sub] at hlt
    linarith
  have hineq2 : σ * u R ≤ σ * p C.i + C.δ := le_of_tendsto hσu_tend hev2
  have habs : C.δ ≤ |u R - p C.i| := by
    by_contra hcon
    rw [not_le] at hcon
    exact hRnotT (show R ∈ T from by
      show γ R ∈ C.region
      rw [hγR]
      exact C.graph_mem_region (by simpa using hcon))
  have hσx_le : σ * (u R - p C.i) ≤ C.δ := by
    rw [mul_sub]
    linarith [hineq2]
  have hσut : -C.δ < σ * (u t - p C.i) := by
    have hnorm := abs_lt.mp (hu_mem t htT)
    rcases hσmem with h1 | h1
    · rw [h1, one_mul]; exact hnorm.1
    · rw [h1]; linarith [hnorm.2]
  have hσx_gt : -C.δ < σ * (u R - p C.i) := by
    rw [mul_sub] at hσut ⊢
    have hcc : 0 < C.c * (R - t) := mul_pos C.hc (by linarith)
    linarith [hineq1, hσut, hcc]
  have hx : σ * (u R - p C.i) = C.δ := by
    have habsx : C.δ ≤ |σ * (u R - p C.i)| := by
      rcases hσmem with h1 | h1
      · rw [h1, one_mul]; exact habs
      · have : σ * (u R - p C.i) = -(u R - p C.i) := by rw [h1, neg_one_mul]
        rw [this, abs_neg]; exact habs
    rcases lt_or_ge (σ * (u R - p C.i)) 0 with h | h
    · rw [abs_of_neg h] at habsx
      linarith
    · rw [abs_of_nonneg h] at habsx
      linarith
  refine ⟨R, htR, ?_⟩
  have huR : u R = p C.i + chartSign (S.W (γ t) C.i) * C.δ := by
    have hσeq : σ = chartSign (S.W (γ t) C.i) := by simp only [hσdef, hgdef]
    rw [← hσeq]
    have h1 : u R - p C.i = σ * (σ * (u R - p C.i)) := by
      rw [← mul_assoc, hσsq, one_mul]
    rw [hx] at h1
    linarith
  rw [hγR, huR]

/-- **A flow line visits a chart region at non-negative times only for bounded time.**  If the flow
line of `x ∈ K` is injective and lies in `K` at every non-negative time at which it is in the chart
region, then the times `t ≥ 0` at which it is in the chart region are bounded above.

Indeed, by `chart_exit_line_pos` each such visit ends at the graph point with parameter
`p i + σ δ`, where `σ = ±1` is the sign of the `i`-th component of the field on the visit; since the
line is injective, all visits with the same sign have the same right end, so there are at most two
visits. -/
theorem chart_visit_le_of_pos (S : FlowSetup m) {x : Amb m} (hx : x ∈ S.K) {p : Amb m}
    (C : FlowChart S.W S.K p) (hinj : Function.Injective (S.line x))
    (hKreg : ∀ s : ℝ, 0 ≤ s → S.line x s ∈ C.region → S.line x s ∈ S.K) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → S.line x t ∈ C.region → t ≤ B := by
  classical
  by_contra hcon
  push Not at hcon
  have hexit : ∀ t : ℝ, 0 ≤ t → S.line x t ∈ C.region →
      ∃ R : ℝ, t ≤ R ∧
        S.line x R = C.graph (p C.i + chartSign (S.W (S.line x t) C.i) * C.δ) :=
    fun t htpos htreg => chart_exit_line_pos S hx C htreg htpos hKreg
  /- For a fixed sign `σ`, all visits of that sign have the same right end. -/
  have hkey : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      (∃ t : ℝ, 0 ≤ t ∧ S.line x t ∈ C.region ∧ chartSign (S.W (S.line x t) C.i) = σ) →
      ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → S.line x t ∈ C.region →
        chartSign (S.W (S.line x t) C.i) = σ → t ≤ B := by
    intro σ hσ ⟨t₀, ht₀, ht₀reg, ht₀sign⟩
    obtain ⟨R₀, ht₀R₀, hR₀⟩ := hexit t₀ ht₀ ht₀reg
    refine ⟨R₀, fun t ht htreg htsign => ?_⟩
    obtain ⟨R, htR, hR⟩ := hexit t ht htreg
    have hRR : R = R₀ := hinj (by rw [hR, hR₀, htsign, ht₀sign])
    linarith
  by_cases hpos : ∃ t : ℝ, 0 ≤ t ∧ S.line x t ∈ C.region ∧
      chartSign (S.W (S.line x t) C.i) = 1
  · obtain ⟨B₁, hB₁⟩ := hkey 1 (Or.inl rfl) hpos
    by_cases hneg : ∃ t : ℝ, 0 ≤ t ∧ S.line x t ∈ C.region ∧
        chartSign (S.W (S.line x t) C.i) = -1
    · obtain ⟨Bm, hBm⟩ := hkey (-1) (Or.inr rfl) hneg
      obtain ⟨t, ht, htreg, htgt⟩ := hcon (max B₁ Bm)
      rcases chartSign_eq_one_or_neg_one (S.W (S.line x t) C.i) with h | h
      · linarith [hB₁ t ht htreg h, le_max_left B₁ Bm]
      · linarith [hBm t ht htreg h, le_max_right B₁ Bm]
    · obtain ⟨t, ht, htreg, htgt⟩ := hcon B₁
      have hsign : chartSign (S.W (S.line x t) C.i) = 1 := by
        rcases chartSign_eq_one_or_neg_one (S.W (S.line x t) C.i) with h | h
        · exact h
        · exact absurd ⟨t, ht, htreg, h⟩ hneg
      linarith [hB₁ t ht htreg hsign]
  · obtain ⟨t, ht, htreg, -⟩ := hcon 0
    rcases chartSign_eq_one_or_neg_one (S.W (S.line x t) C.i) with h | h
    · exact hpos ⟨t, ht, htreg, h⟩
    · obtain ⟨Bm, hBm⟩ := hkey (-1) (Or.inr rfl) ⟨t, ht, htreg, h⟩
      obtain ⟨t', ht', ht'reg, ht'gt⟩ := hcon Bm
      rcases chartSign_eq_one_or_neg_one (S.W (S.line x t') C.i) with h' | h'
      · exact hpos ⟨t', ht', ht'reg, h'⟩
      · exact absurd (hBm t' ht' ht'reg h') (not_le.mpr ht'gt)

/-- **The in-box arc of a flow line through a boundary point of `K` is bounded above.**  If the flow
line of `b ∈ K` is in the interior of the box for small positive times, then there is `M` with
`[0,t]` in the box only for `t ≤ M`.

The proof: if the arc were unbounded, the whole positive arc would lie in the interior of the box;
then the flow line could not be periodic (it would come back to `b`, which is not interior), hence
would be injective; covering `K ∩ box` by finitely many chart regions and using that a visit to a
chart region is bounded (`chart_visit_bddAbove_line`) gives the contradiction. -/
theorem arc_bound_pos (S : FlowSetup m) (Cov : FlowCover S) {b : Amb m} (hbK : b ∈ S.K)
    (hbbdry : b ∈ Submission.Drive.unitBoxBdry m) :
    ∃ M : ℝ, ∀ t : ℝ,
      (∀ s ∈ Set.Ioo (0 : ℝ) t,
        S.line b s ∈ interior (Submission.Drive.unitBox m)) → t ≤ M := by
  by_contra hM
  push Not at hM
  -- If no bound existed, the whole positive arc would be inside the box.
  have hH : ∀ t : ℝ, 0 < t → S.line b t ∈ interior (Submission.Drive.unitBox m) := by
    intro t ht
    obtain ⟨t', ht', htt'⟩ := hM t
    exact ht' t ⟨ht, htt'⟩
  have hinj : Function.Injective (S.line b) := by
    intro s t hst
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hper : Function.Periodic (S.line b) (t - s) := by
        have h := S.line_periodic_of_eq (s := s) (t := t) hst
        simpa [neg_sub] using h.neg
      have hbT : S.line b (t - s) = b := by
        have := hper 0
        rwa [S.line_zero b, zero_add] at this
      have hbint : b ∈ interior (Submission.Drive.unitBox m) := by
        rw [← hbT]
        exact hH (t - s) (sub_pos.mpr hlt)
      exact not_mem_interior_unitBox_of_mem_unitBoxBdry hbbdry hbint
    · have hper : Function.Periodic (S.line b) (s - t) := S.line_periodic_of_eq hst
      have hbT : S.line b (s - t) = b := by
        have := hper 0
        rwa [S.line_zero b, zero_add] at this
      have hbint : b ∈ interior (Submission.Drive.unitBox m) := by
        rw [← hbT]
        exact hH (s - t) (sub_pos.mpr hlt)
      exact not_mem_interior_unitBox_of_mem_unitBoxBdry hbbdry hbint
  -- every positive time at which the line is in a chart region is a point of `K`
  have hKreg : ∀ j : Cov.ι, ∀ s : ℝ, 0 ≤ s → S.line b s ∈ (Cov.C j).region →
      S.line b s ∈ S.K := by
    intro j s hs hsreg
    refine S.mapsTo b hbK s ?_
    intro u hu
    have hu' : 0 ≤ u ∧ u ≤ s := by
      rcases Set.mem_uIcc.mp hu with h | h
      · exact ⟨by linarith [h.1, h.2, hs], by linarith [h.1, h.2, hs]⟩
      · exact ⟨by linarith [h.1, h.2, hs], by linarith [h.1, h.2, hs]⟩
    rcases lt_or_eq_of_le hu'.1 with h | h
    · exact interior_subset (hH u h)
    · rw [← h, S.zero b]
      exact hbbdry.1
  have hbdd : ∀ j : Cov.ι, ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
      S.line b t ∈ (Cov.C j).region → t ≤ B :=
    fun j => chart_visit_le_of_pos S hbK (Cov.C j) hinj (hKreg j)
  choose B hB using hbdd
  set Bs : ℝ := ∑ j : Cov.ι, max (B j) 0 with hBsdef
  have hBsnn : 0 ≤ Bs := by
    rw [hBsdef]
    exact Finset.sum_nonneg fun j _ => le_max_right _ _
  have ht0 : 0 < Bs + 1 := by linarith
  have hmemBox : S.line b (Bs + 1) ∈ Submission.Drive.unitBox m :=
    interior_subset (hH (Bs + 1) ht0)
  have hboxstay : ∀ u ∈ Set.uIcc (0 : ℝ) (Bs + 1),
      S.line b u ∈ Submission.Drive.unitBox m := by
    intro u hu
    have hu' : 0 ≤ u ∧ u ≤ Bs + 1 := by
      rcases Set.mem_uIcc.mp hu with h | h
      · exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2, Bs]⟩
      · exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2, Bs]⟩
    rcases lt_or_eq_of_le hu'.1 with h | h
    · exact interior_subset (hH u h)
    · rw [← h, S.line_zero b]
      exact hbbdry.1
  have hmemK : S.line b (Bs + 1) ∈ S.K := S.mapsTo b hbK (Bs + 1) hboxstay
  obtain ⟨j, hj⟩ := Cov.exists_chart_mem hmemK hmemBox
  have hle : Bs + 1 ≤ B j := hB j (Bs + 1) (by linarith) hj
  have hleBs : B j ≤ Bs := by
    rw [hBsdef]
    refine le_trans (le_max_left (B j) 0) ?_
    exact Finset.single_le_sum (f := fun j : Cov.ι => max (B j) 0)
      (fun i _ => le_max_right (B i) 0) (Finset.mem_univ j)
  linarith

/-- **The in-box arc of a flow line through a boundary point of `K` is bounded below.**  The
mirror image of `arc_bound_pos`, obtained from it by reversing the flow. -/
theorem arc_bound_neg (S : FlowSetup m) (Cov : FlowCover S) {b : Amb m} (hbK : b ∈ S.K)
    (hbbdry : b ∈ Submission.Drive.unitBoxBdry m) :
    ∃ M : ℝ, ∀ t : ℝ,
      (∀ s ∈ Set.Ioo t 0,
        S.line b s ∈ interior (Submission.Drive.unitBox m)) → M ≤ t := by
  obtain ⟨M, hM⟩ := arc_bound_pos S.reverse Cov.reverse hbK hbbdry
  refine ⟨-M, fun t ht => ?_⟩
  have h1 : ∀ s ∈ Set.Ioo (0 : ℝ) (-t),
      S.reverse.line b s ∈ interior (Submission.Drive.unitBox m) := by
    intro s hs
    have hs' : -s ∈ Set.Ioo t 0 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact ht (-s) hs'
  have h2 := hM (-t) h1
  linarith

end

end Work.Drive
