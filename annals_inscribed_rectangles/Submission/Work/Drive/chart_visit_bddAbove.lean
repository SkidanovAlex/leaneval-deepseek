import Mathlib
import Submission.Work.Drive.ChartData
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.crossing_of_deriv_ne_zero

/-!
# A flow line visits a chart region for bounded time

Let `F : ℝ^{m+1} → ℝ^m`, let `C = ChartData F p` be a local chart for the zero set of `F` near `p`,
and let `γ : ℝ → ℝ^{m+1}` be an injective integral curve of the tangential field `flowField F`
which lies in the zero set of `F`.  Write `u s = (γ s) i` for the chart coordinate and
`g s = (flowField F (γ s)) i` for the `i`-th component of the field, where `i = C.i`.

The chart says that on `C.region` the zero set of `F` is exactly the graph of `η`, and that
`|g| ≥ c > 0` there.  Hence, while `γ` is inside `C.region`, the coordinate `u` moves strictly
monotonically with speed at least `c` and stays in the interval `(|· - p i| < δ)`.

The main content of this file, `chart_exit`, is that such a visit must end: there is a time `R`
with `γ R` on the boundary of the chart region, and the side on which it leaves is dictated by the
sign of `g` at the start of the visit; more precisely
`γ R = C.graph (p i + chartSign (g t) * δ)`.

Since a given sign can only produce one such exit point (the curve is injective), a visit is a
bounded interval of time, and `chart_visit_bddAbove` follows: the set of times spent in
`C.region` is bounded above.
-/

namespace Work.Drive

open Set Filter
open scoped Topology

noncomputable section

/-- The sign of a real number, as `±1`. -/
def chartSign (x : ℝ) : ℝ := if 0 < x then 1 else -1

theorem chartSign_of_pos {x : ℝ} (h : 0 < x) : chartSign x = 1 := if_pos h

theorem chartSign_of_nonpos {x : ℝ} (h : ¬ 0 < x) : chartSign x = -1 := if_neg h

theorem chartSign_mul_pos {x : ℝ} (hx : x ≠ 0) : 0 < chartSign x * x := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [chartSign_of_nonpos (not_lt.mpr h.le), neg_one_mul]
    linarith
  · rw [chartSign_of_pos h, one_mul]
    exact h

theorem chartSign_mul_self (x : ℝ) : chartSign x * chartSign x = 1 := by
  rcases lt_or_ge (0:ℝ) x with h | h
  · rw [chartSign_of_pos h, one_mul]
  · rw [chartSign_of_nonpos (not_lt.mpr h), neg_mul_neg]
    norm_num

theorem chartSign_eq_one_or_neg_one (x : ℝ) : chartSign x = 1 ∨ chartSign x = -1 := by
  rcases lt_or_ge (0:ℝ) x with h | h
  · exact Or.inl (chartSign_of_pos h)
  · exact Or.inr (chartSign_of_nonpos (not_lt.mpr h))

theorem chartSign_eq_or_eq_neg (x y : ℝ) :
    chartSign x = chartSign y ∨ chartSign x = -chartSign y := by
  rcases chartSign_eq_one_or_neg_one y with hy | hy
  · rcases chartSign_eq_one_or_neg_one x with hx | hx
    · exact Or.inl (hx.trans hy.symm)
    · exact Or.inr (by rw [hx, hy])
  · rcases chartSign_eq_one_or_neg_one x with hx | hx
    · exact Or.inr (by rw [hx, hy]; norm_num)
    · exact Or.inl (hx.trans hy.symm)

/-- A continuous nowhere vanishing function on a preconnected set of reals has constant sign. -/
theorem sign_const_of_preconnected {f : ℝ → ℝ} {K : Set ℝ} (hK : IsPreconnected K)
    (hf : ContinuousOn f K) (hne : ∀ x ∈ K, f x ≠ 0) :
    (∀ x ∈ K, 0 < f x) ∨ (∀ x ∈ K, f x < 0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨x, hx, hxle⟩, ⟨y, hy, hyle⟩⟩ := h
  have hfx : f x < 0 := lt_of_le_of_ne hxle (hne x hx)
  have hfy : 0 < f y := lt_of_le_of_ne hyle (hne y hy).symm
  have h0 : (0:ℝ) ∈ f '' K :=
    (hK.image f hf).ordConnected.out ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨hfx.le, hfy.le⟩
  obtain ⟨z, hz, hz0⟩ := h0
  exact hne z hz hz0

/-- **A chart visit ends.**  Let `γ` be an injective integral curve of `flowField F` lying in the
zero set of `F`, and let `C` be a chart for `F` at `p`.  If `γ t` lies in the region of the chart,
then there is a time `R ≥ t` at which `γ` leaves the region, through the boundary point prescribed
by the sign of the `i`-th component of the field at `γ t`:
`γ R = C.graph (p i + chartSign (g t) * δ)`. -/
theorem chart_exit {m : ℕ} {F : Amb m → Tgt m} {p : Amb m} (C : ChartData F p)
    {γ : ℝ → Amb m} (hγ : ∀ t : ℝ, HasDerivAt γ (flowField F (γ t)) t)
    (hflow : Continuous (flowField F)) (hF0 : ∀ t : ℝ, F (γ t) = 0) {t : ℝ}
    (ht : γ t ∈ C.region) :
    ∃ R : ℝ, t ≤ R ∧
      γ R = C.graph (p C.i + chartSign ((flowField F (γ t)) C.i) * C.δ) := by
  classical
  set S : Set ℝ := {s | γ s ∈ C.region} with hSdef
  set u : ℝ → ℝ := fun s => γ s C.i with hudef
  set g : ℝ → ℝ := fun s => flowField F (γ s) C.i with hgdef
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun s => (hγ s).continuousAt
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
  have hgmem : ∀ s ∈ S, C.c ≤ |g s| := by
    intro s hs
    have hs' : γ s ∈ C.region := hs
    rw [ChartData.mem_region] at hs'
    rw [hgdef]
    exact C.hvel (γ s) hs'.1 hs'.2
  have hu_mem : ∀ s ∈ S, |u s - p C.i| < C.δ := by
    intro s hs
    have hs' : γ s ∈ C.region := hs
    rw [ChartData.mem_region] at hs'
    rw [hudef]
    exact hs'.1
  have hgraph : ∀ s ∈ S, γ s = C.graph (u s) := by
    intro s hs
    rw [hudef]
    exact C.eq_graph_of_mem_region hs (hF0 s)
  have htS : t ∈ S := ht
  have hgt_ne : g t ≠ 0 := by
    have h := hgmem t htS
    intro h0
    rw [h0, abs_zero] at h
    linarith [C.hc]
  set σ : ℝ := chartSign (g t) with hσdef
  have hσpos : 0 < σ * g t := by rw [hσdef]; exact chartSign_mul_pos hgt_ne
  have hσmem : σ = 1 ∨ σ = -1 := by rw [hσdef]; exact chartSign_eq_one_or_neg_one (g t)
  have hσsq : σ * σ = 1 := by rw [hσdef]; exact chartSign_mul_self (g t)
  set E : Set ℝ := {s | t ≤ s ∧ Set.Icc t s ⊆ S} with hEdef
  have htE : t ∈ E := by
    rw [hEdef]
    refine ⟨le_rfl, fun x hx => ?_⟩
    rw [Set.mem_Icc] at hx
    have : x = t := le_antisymm hx.2 hx.1
    rw [this]
    exact htS
  -- On an initial segment `Icc t s ⊆ S` the coordinate `σ * u` grows at speed at least `c`.
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
      have hξS : ξ ∈ S := hsub (Set.Ioo_subset_Icc_self hξ)
      have hne : ∀ r ∈ Set.Icc t s, σ * g r ≠ 0 := by
        intro r hr
        have hrS : r ∈ S := hsub hr
        have hgr : g r ≠ 0 := by
          have h := hgmem r hrS
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
        exact hgmem ξ hξS
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
    have hsS : s ∈ S := hsub (Set.right_mem_Icc.mpr hts)
    have hus := hu_mem s hsS
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
  have hsubR : Set.Ico t R ⊆ S := by
    intro s hs
    obtain ⟨hts, hsR⟩ := hs
    obtain ⟨s', hs'E, hss'⟩ := exists_lt_of_lt_csSup hEne hsR
    exact hs'E.2 ⟨hts, hss'.le⟩
  have hRnotS : R ∉ S := by
    intro hRS
    have hev : ∀ᶠ x in 𝓝 R, γ x ∈ C.region :=
      hγc.continuousAt.preimage_mem_nhds (C.isOpen_region.mem_nhds hRS)
    obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff.mp hev
    have hmem : R + η/2 ∈ E := by
      rw [hEdef]
      refine ⟨by linarith, fun x hx => ?_⟩
      rw [Set.mem_Icc] at hx
      rcases lt_or_ge x R with hxR | hxR
      · exact hsubR ⟨hx.1, hxR⟩
      · rcases eq_or_lt_of_le hxR with h | h
        · rw [← h]
          exact hRS
        · exact hη (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩)
    have hle := le_csSup hEbdd hmem
    linarith
  have htt : t < R := lt_of_le_of_ne htR (fun h => hRnotS (h ▸ htS))
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
  have hγR : γ R = C.graph (u R) := by
    have hclosed : IsClosed {s : ℝ | γ s = C.graph (u s)} :=
      isClosed_eq hγc (C.continuous_graph.comp huc)
    have hsub' : Set.Ico t R ⊆ {s : ℝ | γ s = C.graph (u s)} :=
      fun s hs => hgraph s (hsubR hs)
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
    have hsS : s ∈ S := hsubR hs
    have hnorm := abs_lt.mp (hu_mem s hsS)
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
    exact hRnotS (show R ∈ S from by
      show γ R ∈ C.region
      rw [hγR]
      exact C.graph_mem_region (by simpa using hcon))
  have hσx_le : σ * (u R - p C.i) ≤ C.δ := by
    rw [mul_sub]
    linarith [hineq2]
  have hσut : -C.δ < σ * (u t - p C.i) := by
    have hnorm := abs_lt.mp (hu_mem t htS)
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
  have huR : u R = p C.i + chartSign ((flowField F (γ t)) C.i) * C.δ := by
    have hσeq : σ = chartSign ((flowField F (γ t)) C.i) := by simp only [hσdef, hgdef]
    rw [← hσeq]
    have h1 : u R - p C.i = σ * (σ * (u R - p C.i)) := by
      rw [← mul_assoc, hσsq, one_mul]
    rw [hx] at h1
    linarith
  rw [hγR, huR]

/-- **Flow lines leave a chart region in bounded time.**  An injective integral curve of
`flowField F` lying in the zero set of `F` spends only a bounded set of times in the region of any
chart for `F`. -/
theorem chart_visit_bddAbove {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    {p : Work.Drive.Amb m} (C : Work.Drive.ChartData F p) {γ : ℝ → Work.Drive.Amb m}
    (hγ : ∀ t : ℝ, HasDerivAt γ (Work.Drive.flowField F (γ t)) t)
    (hflow : Continuous (Work.Drive.flowField F))
    (hinj : Function.Injective γ)
    (hF0 : ∀ t : ℝ, F (γ t) = 0) :
    ∃ B : ℝ, ∀ t : ℝ, γ t ∈ C.region → t ≤ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t₀, ht₀, -⟩ := hcon 0
  obtain ⟨R₀, -, hγR₀⟩ := chart_exit C hγ hflow hF0 ht₀
  by_cases hcase : ∃ t, γ t ∈ C.region ∧
      chartSign ((flowField F (γ t)) C.i) = - chartSign ((flowField F (γ t₀)) C.i)
  · obtain ⟨t₁, ht₁, hsign₁⟩ := hcase
    obtain ⟨R₁, -, hγR₁⟩ := chart_exit C hγ hflow hF0 ht₁
    obtain ⟨t, ht, htgt⟩ := hcon (max R₀ R₁)
    obtain ⟨R, htR, hγR⟩ := chart_exit C hγ hflow hF0 ht
    rcases chartSign_eq_or_eq_neg ((flowField F (γ t)) C.i) ((flowField F (γ t₀)) C.i)
      with hsame | hopp
    · have hRR : R = R₀ := hinj (by rw [hγR, hγR₀, hsame])
      rw [hRR] at htR
      linarith [htR, le_max_left R₀ R₁]
    · have hRR : R = R₁ := hinj (by rw [hγR, hγR₁, hopp, hsign₁])
      rw [hRR] at htR
      linarith [htR, le_max_right R₀ R₁]
  · obtain ⟨t, ht, htgt⟩ := hcon R₀
    obtain ⟨R, htR, hγR⟩ := chart_exit C hγ hflow hF0 ht
    have hsame : chartSign ((flowField F (γ t)) C.i) =
        chartSign ((flowField F (γ t₀)) C.i) := by
      rcases chartSign_eq_or_eq_neg ((flowField F (γ t)) C.i) ((flowField F (γ t₀)) C.i)
        with h | h
      · exact h
      · exact absurd ⟨t, ht, h⟩ hcase
    have hRR : R = R₀ := hinj (by rw [hγR, hγR₀, hsame])
    rw [hRR] at htR
    linarith

end

end Work.Drive
