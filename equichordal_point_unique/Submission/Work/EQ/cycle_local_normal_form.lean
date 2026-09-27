import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.EquiLocalDefs
import Submission.Work.EQ.fibre_finite_of_cover
import Submission.Work.EQ.chart_centre_section_values
import Submission.Work.EQ.chart_legs_dichotomy
import Submission.Work.EQ.compact_part_in_sec
import Submission.Work.EQ.leg_in_sec_of_centre_ne
import Submission.Work.EQ.leg_in_sec_of_redundant
import Submission.Work.EQ.roots_small
import Submission.Work.EQ.sections_agree_nearby
import Submission.Work.EQ.sections_distinct
import Submission.Work.EQ.dedup_finset
import Submission.Work.Analysis.Complex.punctured_ball_connected

set_option maxHeartbeats 1000000

namespace Work.EQ

open Filter _root_.Topology

/-! ## §1  Point-set preliminaries -/

/-- A component of `F` through a point of the component of `y` is the component of `y`. -/
lemma connectedComponentIn_eq_of_mem {α : Type*} [TopologicalSpace α] {F : Set α} {x y : α}
    (hxF : x ∈ F) (hyF : y ∈ F) (h : x ∈ connectedComponentIn F y) :
    connectedComponentIn F x = connectedComponentIn F y := by
  have h' : (⟨x, hxF⟩ : F) ∈ connectedComponent ⟨y, hyF⟩ := by
    rw [connectedComponentIn_eq_image hyF] at h
    obtain ⟨z, hz, hzx⟩ := h
    have hxz : (⟨x, hxF⟩ : F) = z := by
      apply Subtype.ext
      exact hzx.symm
    rw [hxz]
    exact hz
  rw [connectedComponentIn_eq_image hxF, connectedComponentIn_eq_image hyF,
    connectedComponent_eq h']

/-- The punctured disc in `ℂ` is preconnected. -/
lemma isPreconnected_punctured_ball' {r : ℝ} (hr : 0 < r) :
    IsPreconnected (Metric.ball (0 : ℂ) r \ {0}) := by
  have hset : Metric.ball (0 : ℂ) r \ {0} = {z : ℂ | 0 < ‖z - 0‖ ∧ ‖z - 0‖ < r} := by
    ext z
    simp only [Metric.mem_ball, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      dist_zero_right, sub_zero, norm_pos_iff]
    tauto
  rw [hset]
  exact (Work.Analysis.Complex.isConnected_punctured_ball_at 0 hr).isPreconnected

/-- If a preconnected image of a chart lies in `H0` and meets the component of `p`, it is
contained in that component. -/
lemma image_subset_component {a : ℝ} {h : ℂ → ℂ} {p y₀ : ChainData} {E : ℂ → ChainData}
    {A : Set ℂ} (hp : p ∈ H0 a h) (hA : IsPreconnected A) (hcont : ContinuousOn E A)
    (hAH : E '' A ⊆ H0 a h) (hy : y₀ ∈ E '' A)
    (hyS : y₀ ∈ connectedComponentIn (H0 a h) p) :
    E '' A ⊆ connectedComponentIn (H0 a h) p := by
  have hpre : IsPreconnected (E '' A) := hA.image E hcont
  have h1 : E '' A ⊆ connectedComponentIn (H0 a h) y₀ :=
    hpre.subset_connectedComponentIn hy hAH
  rw [connectedComponentIn_eq_of_mem (connectedComponentIn_subset _ _ hyS) hp hyS] at h1
  exact h1

/-- A ball statement turns into an `∀ᶠ` statement on the punctured neighbourhood of `u₁`. -/
lemma eventually_nhdsNE_of_ball {u₁ : ℂ} {P : ℂ → Prop} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ → P u) : ∀ᶠ u in 𝓝[≠] u₁, P u := by
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds u₁ hρ), self_mem_nhdsWithin]
    with u hu hu'
  exact h u hu hu'

/-! ## §2  A component of `H0` is closed in `H0` -/

/-- A point of `closure S` that lies in `H0` lies in the component `S` of `H0`. -/
lemma mem_of_mem_closure_connectedComponentIn {α : Type*} [TopologicalSpace α] {F : Set α}
    {x q : α} (hxF : x ∈ F) (hq : q ∈ closure (connectedComponentIn F x)) (hqF : q ∈ F) :
    q ∈ connectedComponentIn F x := by
  rw [connectedComponentIn_eq_image hxF] at hq ⊢
  obtain ⟨G, hGclosed, hG⟩ :=
    isClosed_induced_iff.mp (isClosed_connectedComponent (x := (⟨x, hxF⟩ : F)))
  have hsub : Subtype.val '' connectedComponent (⟨x, hxF⟩ : F) ⊆ G := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have : z ∈ Subtype.val ⁻¹' G := by rw [hG]; exact hz
    exact this
  have hqG : q ∈ G := closure_minimal hsub hGclosed hq
  have : (⟨q, hqF⟩ : F) ∈ Subtype.val ⁻¹' G := hqG
  rw [hG] at this
  exact ⟨⟨q, hqF⟩, this, rfl⟩

/-! ## §3  Fibres of `ψ₁` on a component -/

/-- The `ψ₁`-fibre of `S` over `u`. -/
def fibre (S : Set ChainData) (u : ℂ) : Set ChainData := {q | q ∈ S ∧ q.2.1 = u}

@[simp] lemma mem_fibre {S : Set ChainData} {u : ℂ} {q : ChainData} :
    q ∈ fibre S u ↔ q ∈ S ∧ q.2.1 = u := Iff.rfl

/-! ## §4  The local normal form -/

/-- **Local normal form of `ψ₁` on a component that is proper modulo punctures.** Over a small
punctured disc around any `u₁ ≠ 0`, the `ψ₁`-fibre of the component `S` of `p` is the disjoint
union, over finitely many pieces `i`, of the points `e i ζ` with `ζ ≠ 0` and `u₁ + κ i ζ^(k i) = u`.
Every chain coordinate of every piece is meromorphic at `ζ = 0`. Unramified pieces (`k i = 1`)
come from the local sections at the points of the fibre over `u₁`; the others come from the
punctured charts centred at `u₁` that have no limit in `H0`, one chart per puncture. The fibre
over `u₁` itself is finite, of size at most `∑ k i`. -/
theorem cycle_local_normal_form {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {p : ChainData} (hp : p ∈ H0 a h)
    (hcpt2 : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K →
      ∃ C : Set ChainData, IsCompact C ∧ C ⊆ H0 a h ∧
        ∃ (m : ℕ) (e : Fin m → ℂ → ChainData) (u₀ : Fin m → ℂ) (k : Fin m → ℕ),
          (∀ i, IsPuncturedChart a h (e i) (u₀ i) (k i)) ∧
          connectedComponentIn (H0 a h) p ∩ {q | q.2.1 ∈ K} ⊆
            C ∪ ⋃ i, e i '' (Metric.ball (0 : ℂ) (1 / 2) \ {0}))
    {u₁ : ℂ} (hu₁ : u₁ ≠ 0) :
    ∃ (ρ : ℝ) (m : ℕ) (k : Fin m → ℕ) (κ : Fin m → ℂ) (e : Fin m → ℂ → ChainData),
      0 < ρ ∧ (∀ i, 0 < k i ∧ κ i ≠ 0) ∧
      (∀ i, ∀ n : ℤ, MeromorphicAt (fun ζ => ((e i ζ).1 n).1) 0 ∧
        MeromorphicAt (fun ζ => ((e i ζ).1 n).2) 0) ∧
      {q | q ∈ connectedComponentIn (H0 a h) p ∧ q.2.1 = u₁}.Finite ∧
      {q | q ∈ connectedComponentIn (H0 a h) p ∧ q.2.1 = u₁}.ncard ≤ ∑ i, k i ∧
      ∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ →
        {q | q ∈ connectedComponentIn (H0 a h) p ∧ q.2.1 = u} =
            ⋃ i, e i '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ i * ζ ^ k i = u} ∧
          ∀ (i j : Fin m) (ζ ζ' : ℂ), ζ ≠ 0 → ζ' ≠ 0 → u₁ + κ i * ζ ^ k i = u →
            u₁ + κ j * ζ' ^ k j = u → e i ζ = e j ζ' → i = j ∧ ζ = ζ' := by
  classical
  obtain ⟨hloc, hsect, -, -⟩ := H0_structure ha0 ha1 hh
  have hLI : LocalInj a h := localInj_of_localHomeomorph hloc
  set S : Set ChainData := connectedComponentIn (H0 a h) p with hSdef
  have hSH : S ⊆ H0 a h := connectedComponentIn_subset (H0 a h) p
  have hScl : ∀ q ∈ closure S, q ∈ H0 a h → q ∈ S := by
    intro q hq hqH
    rw [hSdef] at hq ⊢
    exact mem_of_mem_closure_connectedComponentIn hp hq hqH
  have hu₁nz : (0 : ℝ) < ‖u₁‖ := norm_pos_iff.mpr hu₁
  have hK0 : (0 : ℂ) ∉ Metric.closedBall u₁ (‖u₁‖ / 2) := by
    intro hmem
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at hmem
    linarith
  obtain ⟨C, hC, hCH, m₀, E₀, w₀, k₀, hchart₀, hcov₀⟩ :=
    hcpt2 (Metric.closedBall u₁ (‖u₁‖ / 2)) (isCompact_closedBall u₁ _) hK0
  -- the chart data, with the scale `Kap`
  have hcd : ∀ i : Fin m₀, ∃ κ : ℂ, IsChartData a h (E₀ i) (w₀ i) κ (k₀ i) := by
    intro i
    obtain ⟨hk, -, κ, hκ, hmem, hinj, hcont, -, -⟩ := hchart₀ i
    exact ⟨κ, hk, hκ, hmem, hinj, hcont⟩
  let Kap : Fin m₀ → ℂ := fun i => Classical.choose (hcd i)
  have hKap : ∀ i : Fin m₀, IsChartData a h (E₀ i) (w₀ i) (Kap i) (k₀ i) :=
    fun i => Classical.choose_spec (hcd i)
  -- the fibre over `u₁`
  set F₁ : Set ChainData := {q : ChainData | q ∈ S ∧ q.2.1 = u₁} with hF₁def
  have hu₁K : u₁ ∈ Metric.closedBall u₁ (‖u₁‖ / 2) := by
    rw [Metric.mem_closedBall, dist_self]; positivity
  have hcovF : S ∩ {z : ChainData | z.2.1 = u₁} ⊆
      C ∪ ⋃ i, E₀ i '' (Metric.ball (0 : ℂ) (1 / 2) \ {0}) := by
    intro q hq
    have hq2 : q.2.1 = u₁ := hq.2
    exact hcov₀ ⟨hq.1, by
      show q.2.1 ∈ Metric.closedBall u₁ (‖u₁‖ / 2)
      rw [hq2]; exact hu₁K⟩
  have hF₁fin : F₁.Finite := by
    rw [hF₁def]
    exact fibre_finite_of_cover hSH hScl hLI hC hCH hchart₀ hcovF
  haveI : Fintype ↥F₁ := hF₁fin.fintype
  -- canonical sections of `ψ₁` through the points of `F₁`
  let secRad : ↥F₁ → ℝ := fun q => Classical.choose (hsect (q : ChainData) (hSH q.2.1))
  let secFun : ↥F₁ → ℂ → ChainData :=
    fun q => Classical.choose ((Classical.choose_spec (hsect (q : ChainData) (hSH q.2.1))).2)
  have hsecProp : ∀ q : ↥F₁, IsSection a h (secFun q) (q : ChainData) (secRad q) ∧
      secFun q '' Metric.ball (q : ChainData).2.1 (secRad q) ∈ 𝓝[H0 a h] (q : ChainData) := by
    intro q
    have hspec := Classical.choose_spec (hsect (q : ChainData) (hSH q.2.1))
    have h2 := Classical.choose_spec hspec.2
    exact ⟨⟨hspec.1, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1⟩, h2.2.2.2.2⟩
  -- the union of the section images
  set T : Set ChainData := ⋃ q : ↥F₁, secFun q '' Metric.ball (q : ChainData).2.1 (secRad q)
    with hTdef
  have hT_nhds : ∀ q ∈ S, q.2.1 = u₁ → T ∈ 𝓝[H0 a h] q := by
    intro q hqS hq1
    have hqF : q ∈ F₁ := by
      rw [hF₁def]
      simp only [Set.mem_setOf_eq]
      exact ⟨hqS, hq1⟩
    refine Filter.mem_of_superset (hsecProp ⟨q, hqF⟩).2 ?_
    rw [hTdef]
    exact Set.subset_iUnion
      (fun q : ↥F₁ => secFun q '' Metric.ball (q : ChainData).2.1 (secRad q)) ⟨q, hqF⟩
  have hT_fibre : ∀ x ∈ T, ∃ q : ↥F₁, x = secFun q x.2.1 := by
    intro x hx
    rw [hTdef] at hx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨v, hv, rfl⟩ := hq
    refine ⟨q, ?_⟩
    have hv' : (secFun q v).2.1 = v := (((hsecProp q).1).2.2.1 v hv).2
    rw [hv']
  have hT_sec : ∀ q : ↥F₁, ∀ u ∈ Metric.ball (q : ChainData).2.1 (secRad q), secFun q u ∈ T := by
    intro q u hu
    exact Set.mem_iUnion.mpr ⟨q, ⟨u, hu, rfl⟩⟩
  -- the charts whose image lies in `S`
  let InS : Fin m₀ → Prop := fun i => E₀ i '' (Metric.ball (0 : ℂ) (1/2) \ {0}) ⊆ S
  have hsub_half : Metric.ball (0 : ℂ) (1/2) \ {0} ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
    intro ζ hζ
    have hζ1 : ζ ∈ Metric.ball (0 : ℂ) (1/2) := hζ.1
    have hζ2 : ζ ≠ 0 := hζ.2
    refine ⟨?_, hζ2⟩
    rw [Metric.mem_ball] at hζ1 ⊢
    linarith
  have hInS_or_disj : ∀ i : Fin m₀,
      InS i ∨ (E₀ i '' (Metric.ball (0 : ℂ) (1/2) \ {0})) ∩ S = ∅ := by
    intro i
    by_cases h : InS i
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra hne
      obtain ⟨y, hyA, hyS⟩ := Set.nonempty_iff_ne_empty.mpr hne
      refine h (image_subset_component (y₀ := y) hp
        (isPreconnected_punctured_ball' (by norm_num))
        ((hKap i).2.2.2.2.mono hsub_half) ?_ hyA hyS)
      intro z ⟨ζ, hζ, hzζ⟩
      rw [← hzζ]
      exact ((hKap i).2.2.1 ζ (hsub_half hζ)).1
  -- the charts centred at `u₁` inside `S`, split into redundant / genuine
  let GoodSet : Set (Fin m₀) := {i | InS i ∧ w₀ i = u₁}
  haveI : Fintype ↥GoodSet := Fintype.ofFinite ↥GoodSet
  haveI : DecidableEq ↥GoodSet := inferInstance
  let chartR : ↥GoodSet → ℝ := fun i =>
    Classical.choose (chart_centre_section_values ha0 ha1 hh hp hu₁ (i.2.2 ▸ hKap i.1) i.2.1)
  let chartRed : ↥GoodSet → Prop := fun i => ∃ (q : ChainData) (ρ' : ℝ) (f : ℂ → ChainData),
      q ∈ S ∧ q.2.1 = u₁ ∧ 0 < ρ' ∧ IsSection a h f q ρ' ∧
      ∀ ζ ∈ Metric.ball (0 : ℂ) (chartR i) \ {0}, E₀ i.1 ζ ∈ f '' Metric.ball q.2.1 ρ'
  let chartGen : ↥GoodSet → Prop := fun i =>
      ∀ ζ ∈ Metric.ball (0 : ℂ) (chartR i) \ {0}, ∀ (q : ChainData) (ρ' : ℝ) (f : ℂ → ChainData),
        q ∈ S → q.2.1 = u₁ → IsSection a h f q ρ' → E₀ i.1 ζ ∉ f '' Metric.ball q.2.1 ρ'
  have hchartCase : ∀ i : ↥GoodSet, 0 < chartR i ∧ (chartRed i ∨ chartGen i) := by
    intro i
    exact Classical.choose_spec
      (chart_centre_section_values ha0 ha1 hh hp hu₁ (i.2.2 ▸ hKap i.1) i.2.1)
  have hLegChart : ∀ i : ↥GoodSet, IsChartData a h (E₀ i.1) u₁ (Kap i.1) (k₀ i.1) :=
    fun i => i.2.2 ▸ hKap i.1
  have hLegInS : ∀ i : ↥GoodSet,
      E₀ i.1 '' (Metric.ball (0 : ℂ) 1 \ {0}) ⊆ connectedComponentIn (H0 a h) p := by
    intro i
    have h1 : ((1 : ℂ) / 4) ∈ Metric.ball (0 : ℂ) (1/2) \ {0} := by
      refine ⟨?_, by norm_num⟩
      rw [Metric.mem_ball, dist_zero_right]
      norm_num
    refine image_subset_component (y₀ := E₀ i.1 ((1 : ℂ)/4)) hp
      (isPreconnected_punctured_ball' one_pos) ((hKap i.1).2.2.2.2) ?_ ?_ ?_
    · intro z ⟨ζ, hζ, hzζ⟩
      rw [← hzζ]
      exact ((hKap i.1).2.2.1 ζ hζ).1
    · refine ⟨(1 : ℂ)/4, ?_, rfl⟩
      refine ⟨?_, by norm_num⟩
      rw [Metric.mem_ball, dist_zero_right]
      norm_num
    · exact i.2.1 (Set.mem_image_of_mem (E₀ i.1) h1)
  -- dichotomy radii for the pairs of good charts
  let ρdich : ↥GoodSet → ↥GoodSet → ℝ := fun i j =>
    Classical.choose (chart_legs_dichotomy ha0 ha1 hh hp hu₁ (hLegChart i) (hLegChart j)
      (hLegInS i) (hLegInS j))
  have hρdich : ∀ i j : ↥GoodSet, 0 < ρdich i j ∧
      ∀ u ∈ Metric.ball u₁ (ρdich i j), u ≠ u₁ → ∀ v ∈ Metric.ball u₁ (ρdich i j), v ≠ u₁ →
        (legFibre (E₀ i.1) u₁ u (Kap i.1) (k₀ i.1) ∩
         legFibre (E₀ j.1) u₁ u (Kap j.1) (k₀ j.1)).Nonempty →
        legFibre (E₀ i.1) u₁ v (Kap i.1) (k₀ i.1) = legFibre (E₀ j.1) u₁ v (Kap j.1) (k₀ j.1) :=
    fun i j => Classical.choose_spec (chart_legs_dichotomy ha0 ha1 hh hp hu₁ (hLegChart i)
      (hLegChart j) (hLegInS i) (hLegInS j))
  let Rdich : Finset ℝ :=
    (Finset.univ.image (fun p : ↥GoodSet × ↥GoodSet => ρdich p.1 p.2)) ∪ {1}
  have hRdich_ne : Rdich.Nonempty := ⟨1, Finset.mem_union_right _ (Finset.mem_singleton_self 1)⟩
  have hRdich_pos : ∀ r ∈ Rdich, 0 < r := by
    intro r hr
    rcases Finset.mem_union.mp hr with h | h
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp h
      exact (hρdich p.1 p.2).1
    · rw [Finset.mem_singleton.mp h]; norm_num
  set tt : ℝ := Finset.min' Rdich hRdich_ne / 2 with htt
  have htt_pos : 0 < tt := by
    rw [htt]
    exact half_pos (hRdich_pos _ (Finset.min'_mem _ _))
  have htt_lt : ∀ i j : ↥GoodSet, tt < ρdich i j := by
    intro i j
    have hmem : ρdich i j ∈ Rdich :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    have hle : Finset.min' Rdich hRdich_ne ≤ ρdich i j := Finset.min'_le _ _ hmem
    have hpos : 0 < Finset.min' Rdich hRdich_ne := hRdich_pos _ (Finset.min'_mem _ _)
    rw [htt]; linarith
  set ustar : ℂ := u₁ + (tt : ℂ) with hustar
  have hnorm_star : ‖ustar - u₁‖ = tt := by
    have h1 : ustar - u₁ = (tt : ℂ) := by rw [hustar]; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htt_pos]
  have hstar_ne : ustar ≠ u₁ := by
    intro h
    have h0 : tt = 0 := by
      have := hnorm_star; rw [h, sub_self, norm_zero] at this; exact this.symm
    linarith
  have hstar_ball : ∀ i j : ↥GoodSet, ustar ∈ Metric.ball u₁ (ρdich i j) := by
    intro i j
    rw [Metric.mem_ball, dist_eq_norm, hnorm_star]
    exact htt_lt i j
  -- the leg fibres over `ustar` are nonempty
  have hleg_ne : ∀ i : ↥GoodSet,
      (legFibre (E₀ i.1) u₁ ustar (Kap i.1) (k₀ i.1)).Nonempty := by
    intro i
    have hk : 0 < k₀ i.1 := (hKap i.1).1
    have hκ : Kap i.1 ≠ 0 := (hKap i.1).2.1
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq ((ustar - u₁) / Kap i.1) hk
    have hζne : ζ ≠ 0 := by
      intro h0
      subst h0
      simp only [zero_pow hk.ne'] at hζ
      have h0' : ustar - u₁ = 0 := by
        rw [eq_div_iff hκ] at hζ
        simpa using hζ.symm
      exact sub_ne_zero.mpr hstar_ne h0'
    refine ⟨E₀ i.1 ζ, ⟨ζ, ⟨hζne, ?_⟩, rfl⟩⟩
    have hcancel : Kap i.1 * ((ustar - u₁) / Kap i.1) = (ustar - u₁) := by
      field_simp
    rw [hζ, hcancel]
    ring
  -- the deduplication relation
  let Rel : ↥GoodSet → ↥GoodSet → Prop := fun i j =>
    (legFibre (E₀ i.1) u₁ ustar (Kap i.1) (k₀ i.1) ∩
     legFibre (E₀ j.1) u₁ ustar (Kap j.1) (k₀ j.1)).Nonempty
  let G : Finset ↥GoodSet := Finset.univ.filter (fun i => chartGen i)
  have hRel_refl : ∀ i ∈ G, Rel i i := by
    intro i _
    obtain ⟨x, hx⟩ := hleg_ne i
    exact ⟨x, hx, hx⟩
  have hRel_symm : ∀ i ∈ G, ∀ j ∈ G, Rel i j → Rel j i := by
    intro i _ j _ h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, hx.2, hx.1⟩
  have hRel_eq : ∀ i j : ↥GoodSet, Rel i j →
      legFibre (E₀ i.1) u₁ ustar (Kap i.1) (k₀ i.1) =
        legFibre (E₀ j.1) u₁ ustar (Kap j.1) (k₀ j.1) := by
    intro i j hij
    exact (hρdich i j).2 ustar (hstar_ball i j) hstar_ne ustar (hstar_ball i j) hstar_ne hij
  have hRel_trans : ∀ i ∈ G, ∀ j ∈ G, ∀ k ∈ G, Rel i j → Rel j k → Rel i k := by
    intro i _ j _ k _ hij hjk
    change (legFibre (E₀ i.1) u₁ ustar (Kap i.1) (k₀ i.1) ∩
      legFibre (E₀ k.1) u₁ ustar (Kap k.1) (k₀ k.1)).Nonempty
    rw [hRel_eq i j hij, ← hRel_eq j k hjk]
    obtain ⟨x, hx⟩ := hleg_ne j
    exact ⟨x, hx, hx⟩
  obtain ⟨Rep, Reps, hRep_mem, hReps_subG, hRep_fix, hRel_rep, hRel_rep_ofEq, hRep_eq_ofRel⟩ :=
    dedup_finset G Rel hRel_refl hRel_symm hRel_trans
  -- the index type of the pieces
  let pieceK : (↥Reps ⊕ ↥F₁) → ℕ := fun x => match x with
    | Sum.inl i => k₀ i.1.1
    | Sum.inr _ => 1
  let pieceKap : (↥Reps ⊕ ↥F₁) → ℂ := fun x => match x with
    | Sum.inl i => Kap i.1.1
    | Sum.inr _ => 1
  let pieceE : (↥Reps ⊕ ↥F₁) → ℂ → ChainData := fun x ζ => match x with
    | Sum.inl i => E₀ i.1.1 ζ
    | Sum.inr q => secFun q (u₁ + ζ)
  let m : ℕ := Fintype.card (↥Reps ⊕ ↥F₁)
  let idx : Fin m ≃ (↥Reps ⊕ ↥F₁) := (Fintype.equivFin (↥Reps ⊕ ↥F₁)).symm
  let kk : Fin m → ℕ := fun i => pieceK (idx i)
  let κκ : Fin m → ℂ := fun i => pieceKap (idx i)
  let ee : Fin m → ℂ → ChainData := fun i => pieceE (idx i)
  have hidx : ∀ y : (↥Reps ⊕ ↥F₁), idx (Fintype.equivFin (↥Reps ⊕ ↥F₁) y) = y :=
    fun y => Equiv.symm_apply_apply _ y
  have hpiece_pos : ∀ y : (↥Reps ⊕ ↥F₁), 0 < pieceK y ∧ pieceKap y ≠ 0 := by
    rintro (i | q)
    · exact ⟨(hKap i.1.1).1, (hKap i.1.1).2.1⟩
    · exact ⟨one_pos, one_ne_zero⟩
  have hpiece_mero : ∀ y : (↥Reps ⊕ ↥F₁), ∀ n : ℤ,
      MeromorphicAt (fun ζ => ((pieceE y ζ).1 n).1) 0 ∧
      MeromorphicAt (fun ζ => ((pieceE y ζ).1 n).2) 0 := by
    rintro (i | q) n
    · obtain ⟨-, -, -, -, -, -, -, hmer1, hmer2⟩ := hchart₀ i.1.1
      exact hmer2 n
    · have hsec := (hsecProp q).1
      have hball : u₁ ∈ Metric.ball (q : ChainData).2.1 (secRad q) := by
        rw [(q.2).2, Metric.mem_ball, dist_self]
        exact hsec.1
      have hg : AnalyticAt ℂ (fun ζ : ℂ => u₁ + ζ) 0 := by fun_prop
      have hcomp : AnalyticAt ℂ (fun ζ : ℂ => (secFun q (u₁ + ζ)).1 n) 0 :=
        AnalyticAt.comp (x := (0:ℂ)) (g := fun u : ℂ => (secFun q u).1 n)
          (by simpa using ((hsec.2.2.2.1 n) u₁ hball)) hg
      refine ⟨?_, ?_⟩
      · show MeromorphicAt (fun ζ : ℂ => ((secFun q (u₁ + ζ)).1 n).1) 0
        exact (AnalyticAt.comp (analyticAt_fst) hcomp).meromorphicAt
      · show MeromorphicAt (fun ζ : ℂ => ((secFun q (u₁ + ζ)).1 n).2) 0
        exact (AnalyticAt.comp ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _) hcomp).meromorphicAt
  have hE_idx : ∀ i : Fin m, ee i = pieceE (idx i) := fun i => rfl
  have hKap_idx : ∀ i : Fin m, κκ i = pieceKap (idx i) := fun i => rfl
  have hK_idx : ∀ i : Fin m, kk i = pieceK (idx i) := fun i => rfl
  have hK_inr : ∀ q : ↥F₁, pieceK (Sum.inr q) = 1 := fun q => rfl
  have hKap_inr : ∀ q : ↥F₁, pieceKap (Sum.inr q) = 1 := fun q => rfl
  have hE_inr : ∀ (q : ↥F₁) (ζ : ℂ), pieceE (Sum.inr q) ζ = secFun q (u₁ + ζ) :=
    fun q ζ => rfl
  have hK_inl : ∀ i : ↥Reps, pieceK (Sum.inl i) = k₀ i.1.1 := fun i => rfl
  have hKap_inl : ∀ i : ↥Reps, pieceKap (Sum.inl i) = Kap i.1.1 := fun i => rfl
  have hE_inl : ∀ (i : ↥Reps) (ζ : ℂ), pieceE (Sum.inl i) ζ = E₀ i.1.1 ζ := fun i ζ => rfl
  have hncard : F₁.ncard ≤ ∑ i : Fin m, kk i := by
    have h1 : (∑ i : Fin m, kk i) =
        (∑ y : ↥Reps, pieceK (Sum.inl y)) + (∑ y : ↥F₁, pieceK (Sum.inr y)) := by
      have ha : (∑ i : Fin m, kk i) = ∑ y : (↥Reps ⊕ ↥F₁), pieceK y :=
        Equiv.sum_comp idx pieceK
      rw [ha]
      exact Fintype.sum_sum_type pieceK
    have h2 : (∑ y : ↥F₁, pieceK (Sum.inr y)) = F₁.ncard := by
      have h3 : (∑ y : ↥F₁, pieceK (Sum.inr y)) = Fintype.card ↥F₁ := by
        have : ∀ y : ↥F₁, pieceK (Sum.inr y) = 1 := fun y => rfl
        rw [Finset.sum_congr rfl (fun y _ => this y)]
        simp
      rw [h3, Set.ncard_eq_toFinset_card F₁ hF₁fin, Set.Finite.card_toFinset hF₁fin]
    rw [h1, h2]
    exact Nat.le_add_left _ _
  have hUnionIdx : ∀ u : ℂ,
      (⋃ i : Fin m, ee i '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κκ i * ζ ^ kk i = u})
        = ⋃ y : (↥Reps ⊕ ↥F₁),
            pieceE y '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + pieceKap y * ζ ^ pieceK y = u} := by
    intro u
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨idx i, ?_⟩
      simpa only [hE_idx i, hKap_idx i, hK_idx i] using hi
    · intro hx
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨Fintype.equivFin (↥Reps ⊕ ↥F₁) y, ?_⟩
      rw [hE_idx, hKap_idx, hK_idx, hidx y]
      exact hy
  have key : ∀ᶠ u in 𝓝[≠] u₁,
      (fibre S u = ⋃ y : (↥Reps ⊕ ↥F₁),
        pieceE y '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + pieceKap y * ζ ^ pieceK y = u}) ∧
      (∀ (y y' : (↥Reps ⊕ ↥F₁)) (ζ ζ' : ℂ), ζ ≠ 0 → ζ' ≠ 0 →
        u₁ + pieceKap y * ζ ^ pieceK y = u →
        u₁ + pieceKap y' * ζ' ^ pieceK y' = u →
        pieceE y ζ = pieceE y' ζ' → y = y' ∧ ζ = ζ') := by
    -- (1) the compact part is eventually in the union of the section images
    obtain ⟨ρC, hρCpos, hρC⟩ := compact_part_in_sec ha0 ha1 hh hu₁ hSH hScl hT_nhds hC hCH
    have ev_C : ∀ᶠ u in 𝓝[≠] u₁, ∀ x ∈ C, x ∈ S → x.2.1 = u → x ∈ T :=
      eventually_nhdsNE_of_ball hρCpos hρC
    -- (2) the charts with centre different from `u₁`
    have ev_leg : ∀ᶠ u in 𝓝[≠] u₁, ∀ i : Fin m₀, w₀ i ≠ u₁ →
        ∀ ζ ∈ Metric.ball (0 : ℂ) (1/2) \ {0},
          w₀ i + Kap i * ζ ^ k₀ i = u → E₀ i ζ ∈ S → E₀ i ζ ∈ T := by
      rw [Filter.eventually_all]
      intro i
      by_cases hw : w₀ i = u₁
      · exact Filter.Eventually.of_forall (fun u h => absurd hw h)
      · obtain ⟨r, hr, hrest⟩ :=
          leg_in_sec_of_centre_ne ha0 ha1 hh hu₁ hSH hScl hT_nhds (hKap i) hw
        exact eventually_nhdsNE_of_ball hr (fun u hu hu' _ => hrest u hu hu')
    -- (3) the redundant charts centred at `u₁`
    have ev_red : ∀ᶠ u in 𝓝[≠] u₁, ∀ i : ↥GoodSet, chartRed i →
        ∀ ζ ∈ Metric.ball (0 : ℂ) (1/2) \ {0},
          u₁ + Kap i.1 * ζ ^ k₀ i.1 = u → E₀ i.1 ζ ∈ S → E₀ i.1 ζ ∈ T := by
      rw [Filter.eventually_all]
      intro i
      by_cases hred : chartRed i
      · obtain ⟨q, hp', f, hqS, hq1, hρ', hf, hleg⟩ := hred
        obtain ⟨r, hr, hrest⟩ := leg_in_sec_of_redundant ha0 ha1 hh hu₁ hSH hScl hT_nhds
          (hLegChart i) (hchartCase i).1 hqS hq1 hf hleg
        exact eventually_nhdsNE_of_ball hr (fun u hu hu' _ => hrest u hu hu')
      · exact Filter.Eventually.of_forall (fun u h => absurd h hred)
    -- (4) the section balls
    have ev_sec : ∀ᶠ u in 𝓝[≠] u₁, ∀ q : ↥F₁, u ∈ Metric.ball (q : ChainData).2.1 (secRad q) := by
      rw [Filter.eventually_all]
      intro q
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      have hmem : Metric.ball (q : ChainData).2.1 (secRad q) ∈ 𝓝 u₁ := by
        rw [(q.2).2]
        exact Metric.ball_mem_nhds _ (hsecProp q).1.1
      filter_upwards [hmem] with u hu
      exact hu
    -- (5) the roots are small
    have ev_roots : ∀ᶠ u in 𝓝[≠] u₁, ∀ i : ↥GoodSet, ∀ ζ : ℂ, ζ ≠ 0 →
        u₁ + Kap i.1 * ζ ^ k₀ i.1 = u → ‖ζ‖ < 1/2 := by
      rw [Filter.eventually_all]
      intro i
      obtain ⟨r, hr, hrest⟩ := roots_small (hKap i.1).2.1 (hKap i.1).1 (by norm_num : (0:ℝ) < 1/2)
      exact eventually_nhdsNE_of_ball hr hrest
    have ev_rootsr : ∀ᶠ u in 𝓝[≠] u₁, ∀ i : ↥GoodSet, chartGen i → ∀ ζ : ℂ, ζ ≠ 0 →
        u₁ + Kap i.1 * ζ ^ k₀ i.1 = u → ‖ζ‖ < chartR i := by
      rw [Filter.eventually_all]
      intro i
      obtain ⟨r, hr, hrest⟩ := roots_small (hKap i.1).2.1 (hKap i.1).1 (hchartCase i).1
      exact eventually_nhdsNE_of_ball hr (fun u hu hu' _ => hrest u hu hu')
    -- (6) the dichotomy radii
    have ev_dich : ∀ᶠ u in 𝓝[≠] u₁, ∀ i : ↥GoodSet, Rel i (Rep i) →
        legFibre (E₀ i.1) u₁ u (Kap i.1) (k₀ i.1) =
          legFibre (E₀ (Rep i).1) u₁ u (Kap (Rep i).1) (k₀ (Rep i).1) := by
      rw [Filter.eventually_all]
      intro i
      obtain ⟨hr, hrest⟩ := hρdich i (Rep i)
      exact eventually_nhdsNE_of_ball hr
        (fun u hu hu' => fun hrel => hrest ustar (hstar_ball i (Rep i)) hstar_ne u hu hu' hrel)
    have ev_dball : ∀ᶠ u in 𝓝[≠] u₁, ∀ i i' : ↥GoodSet, u ∈ Metric.ball u₁ (ρdich i i') := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro i'
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Metric.ball_mem_nhds u₁ (hρdich i i').1)
    -- (7) distinct sections do not meet
    have ev_A2 : ∀ᶠ u in 𝓝[≠] u₁, ∀ q q' : ↥F₁, q ≠ q' → secFun q u ≠ secFun q' u := by
      rw [Filter.eventually_all]
      intro q
      rw [Filter.eventually_all]
      intro q'
      by_cases hqq : q = q'
      · exact Filter.Eventually.of_forall (fun u h => absurd hqq h)
      · obtain ⟨r, hr, -, -, hrest⟩ := sections_distinct (hSH q.2.1) (hSH q'.2.1)
          (fun h => hqq (Subtype.ext h))
          (((q.2).2).trans (((q'.2).2).symm)) (hsecProp q).1 (hsecProp q').1
        refine eventually_nhdsNE_of_ball hr (fun u hu _ _ => ?_)
        exact hrest u (by rw [(q.2).2]; exact hu)
    have ev_cover : ∀ᶠ u in 𝓝[≠] u₁, u ∈ Metric.closedBall u₁ (‖u₁‖ / 2) := by
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds u₁ (half_pos hu₁nz))]
        with u hu
      rw [Metric.mem_closedBall]
      exact le_of_lt (Metric.mem_ball.mp hu)
    filter_upwards [ev_cover, ev_C, ev_leg, ev_red, ev_sec, ev_roots, ev_rootsr, ev_dich, ev_dball,
      ev_A2, self_mem_nhdsWithin] with u hcover hC' hleg' hred' hsec' hroots' hrootsr' hdich'
      hdball' hA2' hu_ne
    refine ⟨?_, ?_⟩
    · -- the fibre equality
      refine Set.Subset.antisymm ?_ ?_
      · -- LHS ⊆ RHS
        intro x hx
        have hxS : x ∈ S := hx.1
        have hxψ : x.2.1 = u := hx.2
        have hT_to_piece : ∀ x : ChainData, x ∈ T → x.2.1 = u → x ∈
            (⋃ y : (↥Reps ⊕ ↥F₁),
              pieceE y '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + pieceKap y * ζ ^ pieceK y = u}) := by
          intro x hxT hxψ
          obtain ⟨q, hq⟩ := hT_fibre x hxT
          refine Set.mem_iUnion.mpr ⟨Sum.inr q, ?_⟩
          refine ⟨u - u₁, ⟨?_, ?_⟩, ?_⟩
          · intro h0; exact hu_ne (sub_eq_zero.mp h0)
          · rw [hKap_inr q, hK_inr q, one_mul, pow_one]; ring
          · show secFun q (u₁ + (u - u₁)) = x
            rw [hq, hxψ, show u₁ + (u - u₁) = u by ring]
        rcases hcov₀ ⟨by rwa [hSdef] at hxS, by
          show x.2.1 ∈ Metric.closedBall u₁ (‖u₁‖ / 2)
          rw [hxψ]; exact hcover⟩ with hxC | hxch
        · exact hT_to_piece x (hC' x hxC hxS hxψ) hxψ
        · obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hxch
          obtain ⟨ζ₀, hζ₀mem, hζ₀eq⟩ := hi₀
          by_cases hInS_i : InS i₀
          · by_cases hw : w₀ i₀ = u₁
            · have hEq : u₁ + Kap i₀ * ζ₀ ^ k₀ i₀ = u := by
                have hthis : (E₀ i₀ ζ₀).2.1 = u₁ + Kap i₀ * ζ₀ ^ k₀ i₀ := by
                  simpa only [hw] using ((hKap i₀).2.2.1 ζ₀ (hsub_half hζ₀mem)).2
                rw [← hthis, hζ₀eq, hxψ]
              rcases (hchartCase ⟨i₀, hInS_i, hw⟩).2 with hred | hgen
              · have hxT' : E₀ i₀ ζ₀ ∈ T :=
                  hred' ⟨i₀, hInS_i, hw⟩ hred ζ₀ hζ₀mem hEq (hζ₀eq ▸ hxS)
                exact hT_to_piece x (by rwa [hζ₀eq] at hxT') hxψ
              · have hxLeg : x ∈ legFibre (E₀ i₀) u₁ u (Kap i₀) (k₀ i₀) :=
                  ⟨ζ₀, ⟨hζ₀mem.2, hEq⟩, hζ₀eq⟩
                have hi'G : (⟨i₀, hInS_i, hw⟩ : ↥GoodSet) ∈ G :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgen⟩
                have hL := hdich' ⟨i₀, hInS_i, hw⟩ (hRel_rep ⟨i₀, hInS_i, hw⟩ hi'G)
                rw [hL] at hxLeg
                exact Set.mem_iUnion.mpr
                  ⟨Sum.inl ⟨Rep ⟨i₀, hInS_i, hw⟩,
                    hRep_mem ⟨i₀, hInS_i, hw⟩ hi'G⟩, hxLeg⟩
            · have hEq : w₀ i₀ + Kap i₀ * ζ₀ ^ k₀ i₀ = u := by
                have hthis : (E₀ i₀ ζ₀).2.1 = w₀ i₀ + Kap i₀ * ζ₀ ^ k₀ i₀ :=
                  ((hKap i₀).2.2.1 ζ₀ (hsub_half hζ₀mem)).2
                rw [← hthis, hζ₀eq, hxψ]
              have hxT' : E₀ i₀ ζ₀ ∈ T :=
                hleg' i₀ hw ζ₀ hζ₀mem hEq (hζ₀eq ▸ hxS)
              exact hT_to_piece x (by rwa [hζ₀eq] at hxT') hxψ
          · have hdisj : (E₀ i₀ '' (Metric.ball (0:ℂ) (1/2) \ {0})) ∩ S = ∅ :=
              (hInS_or_disj i₀).resolve_left hInS_i
            have hmem : x ∈ (E₀ i₀ '' (Metric.ball (0:ℂ) (1/2) \ {0})) ∩ S :=
              ⟨⟨ζ₀, hζ₀mem, hζ₀eq⟩, hxS⟩
            rw [hdisj] at hmem
            exact absurd hmem (Set.notMem_empty x)
      · -- RHS ⊆ LHS
        intro x hx
        obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
        obtain ⟨ζ, hζmem, hζeq⟩ := hy
        have hEq : u₁ + pieceKap y * ζ ^ pieceK y = u := hζmem.2
        rcases y with i | q
        · have hEqC : u₁ + Kap i.1.1 * ζ ^ k₀ i.1.1 = u := hEq
          have hw' : w₀ i.1.1 = u₁ := i.1.2.2
          have hInS' : InS i.1.1 := i.1.2.1
          have hnorm : ‖ζ‖ < 1/2 := hroots' i.1 ζ hζmem.1 hEqC
          have hζin : ζ ∈ Metric.ball (0 : ℂ) (1/2) := by
            rw [Metric.mem_ball, dist_zero_right]; exact hnorm
          have hψ : (E₀ i.1.1 ζ).2.1 = u₁ + Kap i.1.1 * ζ ^ k₀ i.1.1 := by
            simpa only [hw'] using ((hKap i.1.1).2.2.1 ζ (hsub_half ⟨hζin, hζmem.1⟩)).2
          refine ⟨?_, ?_⟩
          · exact hInS' ⟨ζ, ⟨hζin, hζmem.1⟩, hζeq⟩
          · rw [← hζeq, hψ, hEqC]
        · have hsum : u₁ + ζ = u := by
            have h := hζmem.2
            rw [hKap_inr q, hK_inr q] at h
            simpa only [one_mul, pow_one] using h
          have hx : x = secFun q u := by
            rw [← hζeq]
            show secFun q (u₁ + ζ) = secFun q u
            rw [hsum]
          have hqmem : (q : ChainData) ∈ connectedComponentIn (H0 a h) p := by
            rw [← hSdef]; exact q.2.1
          refine ⟨?_, ?_⟩
          · rw [hx]
            have hsub := IsSection.image_subset_connectedComponentIn (hsecProp q).1 (hSH q.2.1)
            have hmem' : secFun q u ∈ connectedComponentIn (H0 a h) q := hsub ⟨u, hsec' q, rfl⟩
            rw [connectedComponentIn_eq_of_mem (hSH q.2.1) hp hqmem] at hmem'
            rw [← hSdef] at hmem'
            exact hmem'
          · rw [hx]
            exact (((hsecProp q).1).2.2.1 u (hsec' q)).2
    · -- injectivity
      rintro (i | q) (i' | q') ζ ζ' hζ hζ' heq1 heq2 hpt
      · -- two chart pieces
        have hEqC : u₁ + Kap i.1.1 * ζ ^ k₀ i.1.1 = u := by
          simpa only [hKap_inl i, hK_inl i] using heq1
        have hEqC' : u₁ + Kap i'.1.1 * ζ' ^ k₀ i'.1.1 = u := by
          simpa only [hKap_inl i', hK_inl i'] using heq2
        have hmeet : (legFibre (E₀ i.1.1) u₁ u (Kap i.1.1) (k₀ i.1.1) ∩
            legFibre (E₀ i'.1.1) u₁ u (Kap i'.1.1) (k₀ i'.1.1)).Nonempty :=
          ⟨E₀ i.1.1 ζ, ⟨⟨ζ, ⟨hζ, hEqC⟩, rfl⟩, ⟨ζ', ⟨hζ', hEqC'⟩, hpt.symm⟩⟩⟩
        have hdich := (hρdich i.1 i'.1).2 u (hdball' i.1 i'.1) hu_ne ustar
          (hstar_ball i.1 i'.1) hstar_ne hmeet
        obtain ⟨x, hx⟩ := hleg_ne i.1
        have hRel : Rel i.1 i'.1 := ⟨x, hx, hdich ▸ hx⟩
        have hii' : i = i' := by
          have h1 := hRep_eq_ofRel i.1 (hReps_subG i.1 i.2) i'.1 (hReps_subG i'.1 i'.2) hRel
          rw [hRep_fix i.1 i.2, hRep_fix i'.1 i'.2] at h1
          exact Subtype.ext h1
        subst hii'
        have hnorm : ‖ζ‖ < 1/2 := hroots' i.1 ζ hζ hEqC
        have hnorm' : ‖ζ'‖ < 1/2 := hroots' i.1 ζ' hζ' hEqC'
        have hb1 : ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
          ⟨by rw [Metric.mem_ball, dist_zero_right]; linarith, hζ⟩
        have hb2 : ζ' ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
          ⟨by rw [Metric.mem_ball, dist_zero_right]; linarith, hζ'⟩
        exact ⟨rfl, (hKap i.1.1).2.2.2.1 hb1 hb2 hpt⟩
      · -- chart against section
        exfalso
        have hgen_i : chartGen i.1 := (Finset.mem_filter.mp (hReps_subG i.1 i.2)).2
        have hsum : u₁ + ζ' = u := by
          have h := heq2
          rw [hKap_inr q', hK_inr q'] at h
          simpa only [one_mul, pow_one] using h
        have hEqC : u₁ + Kap i.1.1 * ζ ^ k₀ i.1.1 = u := by
          simpa only [hKap_inl i, hK_inl i] using heq1
        have hnorm : ‖ζ‖ < chartR i.1 := hrootsr' i.1 hgen_i ζ hζ hEqC
        have hsub1 : ζ ∈ Metric.ball (0 : ℂ) (chartR i.1) \ {0} := by
          refine ⟨?_, hζ⟩
          rw [Metric.mem_ball, dist_zero_right]
          exact hnorm
        have hnot := hgen_i ζ hsub1 q' (secRad q') (secFun q') q'.2.1 ((q'.2).2) (hsecProp q').1
        have hmem : secFun q' u ∈ secFun q' '' Metric.ball (q' : ChainData).2.1 (secRad q') :=
          ⟨u, hsec' q', rfl⟩
        have hpt' : E₀ i.1.1 ζ = secFun q' u := by
          have h1 : E₀ i.1.1 ζ = secFun q' (u₁ + ζ') := hpt
          rw [h1, hsum]
        exact hnot (hpt' ▸ hmem)
      · -- section against chart
        exfalso
        have hgen_i : chartGen i'.1 := (Finset.mem_filter.mp (hReps_subG i'.1 i'.2)).2
        have hsum : u₁ + ζ = u := by
          have h := heq1
          rw [hKap_inr q, hK_inr q] at h
          simpa only [one_mul, pow_one] using h
        have hEqC : u₁ + Kap i'.1.1 * ζ' ^ k₀ i'.1.1 = u := by
          simpa only [hKap_inl i', hK_inl i'] using heq2
        have hnorm : ‖ζ'‖ < chartR i'.1 := hrootsr' i'.1 hgen_i ζ' hζ' hEqC
        have hsub1 : ζ' ∈ Metric.ball (0 : ℂ) (chartR i'.1) \ {0} := by
          refine ⟨?_, hζ'⟩
          rw [Metric.mem_ball, dist_zero_right]
          exact hnorm
        have hnot := hgen_i ζ' hsub1 q (secRad q) (secFun q) q.2.1 ((q.2).2) (hsecProp q).1
        have hmem : secFun q u ∈ secFun q '' Metric.ball (q : ChainData).2.1 (secRad q) :=
          ⟨u, hsec' q, rfl⟩
        have hpt' : E₀ i'.1.1 ζ' = secFun q u := by
          have h1 : E₀ i'.1.1 ζ' = secFun q (u₁ + ζ) := hpt.symm
          rw [h1, hsum]
        exact hnot (hpt' ▸ hmem)
      · -- two section pieces
        have h1 : u₁ + ζ = u := by
          have h := heq1
          rw [hKap_inr q, hK_inr q] at h
          simpa only [one_mul, pow_one] using h
        have h2 : u₁ + ζ' = u := by
          have h := heq2
          rw [hKap_inr q', hK_inr q'] at h
          simpa only [one_mul, pow_one] using h
        have hζζ' : ζ = ζ' := add_left_cancel (h1.trans h2.symm)
        have hpt' : secFun q u = secFun q' u := by
          have e1 : secFun q u = secFun q (u₁ + ζ) := by rw [h1]
          have e2 : secFun q' (u₁ + ζ') = secFun q' u := by rw [h2]
          calc secFun q u = secFun q (u₁ + ζ) := e1
            _ = secFun q' (u₁ + ζ') := hpt
            _ = secFun q' u := e2
        have hqq' : q = q' := by
          by_contra hne
          exact hA2' q q' hne hpt'
        exact ⟨by rw [hqq'], hζζ'⟩
  have hEv : ∀ᶠ u in 𝓝[≠] u₁,
      (fibre S u = ⋃ i : Fin m, ee i '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κκ i * ζ ^ kk i = u}) ∧
      (∀ (i j : Fin m) (ζ ζ' : ℂ), ζ ≠ 0 → ζ' ≠ 0 → u₁ + κκ i * ζ ^ kk i = u →
        u₁ + κκ j * ζ' ^ kk j = u → ee i ζ = ee j ζ' → i = j ∧ ζ = ζ') := by
    filter_upwards [key] with u hkey
    refine ⟨by rw [hUnionIdx u]; exact hkey.1, ?_⟩
    intro i j ζ ζ' hζ hζ' heq1 heq2 hpt
    have h2 := hkey.2 (idx i) (idx j) ζ ζ' hζ hζ' heq1 heq2 hpt
    exact ⟨idx.injective h2.1, h2.2⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hEv
  obtain ⟨ρ, hρpos, hρ⟩ := hEv
  refine ⟨ρ, m, kk, κκ, ee, hρpos, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact hpiece_pos (idx i)
  · intro i n; exact hpiece_mero (idx i) n
  · exact hF₁fin
  · exact hncard
  · intro u hu hu₁'
    have hdist : dist u u₁ < ρ := by rwa [Metric.mem_ball] at hu
    exact hρ hdist hu₁'


end Work.EQ
