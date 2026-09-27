import Mathlib
import Submission.Work.Noncompact.CompressionTube.spike_removal
import Submission.Work.Noncompact.CompressionTube.isPathConnected_sdiff_iUnion_arcs_finite
import Submission.Work.Noncompact.CompressionTube.arc_head_away
import Submission.Work.Whitney.PathTools.exists_arc_of_isPathConnected
import Submission.Work.Whitney.PathTools.joinedIn_compl_Icc_of_joinedIn_tails
import Submission.Work.Noncompact.Canals.arc_interior_empty
import Submission.Work.Noncompact.CompressionTube.nested_pacmans_to_arc

namespace Work.Noncompact.CompressionTube

open Set Metric Topology
open scoped Topology

/-- A set `X` admits an *accessible arc* from `0`: a continuous `Icc 0 1`-injective arc
starting at `0` whose positive-time values lie in `X`. -/
def ArcOut (E : Type*) [TopologicalSpace E] [Zero E] (X : Set E) : Prop :=
  ∃ γ : ℝ → E, Continuous γ ∧ Set.InjOn γ (Set.Icc (0:ℝ) 1) ∧ γ 0 = 0 ∧
    ∀ t ∈ Set.Ioc (0:ℝ) 1, γ t ∈ X

/-- **Preconnected rooms upgrade to path-connected rooms.** -/
lemma pathConnected_rooms_of_preconnected {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsClosed K)
    (h : ∀ N ∈ nhds (0:E), ∃ O : Set E, IsOpen O ∧ (0:E) ∈ O ∧ O ⊆ N ∧
      (O \ K).Nonempty ∧ IsPreconnected (O \ K)) :
    ∀ N ∈ nhds (0:E), ∃ U : Set E, IsOpen U ∧ (0:E) ∈ U ∧ U ⊆ N ∧
      IsPathConnected (U \ K) := by
  intro N hN
  obtain ⟨O, hOo, h0O, hON, hOne, hOpre⟩ := h N hN
  exact ⟨O, hOo, h0O, hON,
    (hOo.sdiff hK).isConnected_iff_isPathConnected.mp ⟨hOne, hOpre⟩⟩

/-- **Trimming.**  If `L₁` is a compact obstacle not containing `0`, then an accessible arc for
`ball 0 ε \ L₂` can be trimmed so as to avoid `L₁` as well. -/
lemma arcOut_sdiff_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L₁ L₂ : Set E} (h0L₁ : (0:E) ∉ closure L₁) {ε : ℝ} (hε : 0 < ε)
    (h : ArcOut E (Metric.ball (0:E) ε \ L₂)) :
    ArcOut E (Metric.ball (0:E) ε \ (L₁ ∪ L₂)) := by
  classical
  rcases Set.eq_empty_or_nonempty L₁ with rfl | hL₁ne
  · simpa using h
  obtain ⟨γ, hγc, hγinj, hγ0, hγX⟩ := h
  have hpos : 0 < Metric.infDist (0:E) L₁ :=
    (Metric.infDist_pos_iff_notMem_closure hL₁ne).mp h0L₁
  set s : ℝ := min (Metric.infDist (0:E) L₁) ε / 2 with hsdef
  have hs_pos : 0 < s := by rw [hsdef]; positivity
  have hs_lt : s < Metric.infDist (0:E) L₁ := by
    rw [hsdef]
    have h2 : min (Metric.infDist (0:E) L₁) ε ≤ Metric.infDist (0:E) L₁ := min_le_left _ _
    linarith
  have hs_lt_eps : s < ε := by
    rw [hsdef]
    have h2 : min (Metric.infDist (0:E) L₁) ε ≤ ε := min_le_right _ _
    linarith
  set T : Set ℝ := {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ s ≤ ‖γ t‖} with hTdef
  have hTclosed : IsClosed T := by
    rw [hTdef]
    exact isClosed_Icc.inter (isClosed_le continuous_const (continuous_norm.comp hγc))
  obtain ⟨τ, hτpos, hτle⟩ : ∃ τ : ℝ, 0 < τ ∧ ∀ u ∈ Set.Ico (0:ℝ) τ, ‖γ u‖ < s := by
    rcases T.eq_empty_or_nonempty with hT0 | hTne
    · refine ⟨1, one_pos, ?_⟩
      intro u hu
      by_contra hcon
      push_neg at hcon
      exact (Set.eq_empty_iff_forall_notMem.mp hT0) u ⟨⟨hu.1, hu.2.le⟩, hcon⟩
    · have hbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
      have hτle1 : sInf T ≤ 1 := le_trans (csInf_le hbdd hTne.some_mem) hTne.some_mem.1.2
      have hopen : IsOpen ((fun t : ℝ => ‖γ t‖) ⁻¹' (Set.Iio s)) :=
        isOpen_Iio.preimage (continuous_norm.comp hγc)
      have h0 : (0:ℝ) ∈ (fun t : ℝ => ‖γ t‖) ⁻¹' (Set.Iio s) := by
        simp only [Set.mem_preimage, Set.mem_Iio, hγ0, norm_zero]; exact hs_pos
      obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds h0)
      have hlb : ∀ t ∈ T, δ ≤ t := by
        intro t ht
        by_contra hcon
        push_neg at hcon
        have h1 : dist t 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1.1]; exact hcon
        exact absurd ht.2 (not_le.mpr (hδ h1))
      have hsInfmem : sInf T ∈ T := hTclosed.csInf_mem hTne hbdd
      have hτpos : 0 < sInf T := lt_of_lt_of_le hδpos (hlb (sInf T) hsInfmem)
      refine ⟨sInf T, hτpos, ?_⟩
      intro u hu
      by_contra hcon
      push_neg at hcon
      have huT : u ∈ T := ⟨⟨hu.1, le_trans hu.2.le hτle1⟩, hcon⟩
      exact absurd (csInf_le hbdd huT) (not_le.mpr hu.2)
  · have hτ'pos : (0:ℝ) < min τ 1 / 2 := by
      have := lt_min hτpos one_pos; linarith
    have hτ'le : min τ 1 / 2 ≤ 1 := by
      have := min_le_right τ (1:ℝ); linarith
    have hτ'lt : min τ 1 / 2 < τ := by
      rcases le_total τ 1 with h' | h'
      · rw [min_eq_left h']; linarith
      · rw [min_eq_right h']; linarith
    refine ⟨fun t => γ (min τ 1 / 2 * t), ?_, ?_, ?_, ?_⟩
    · fun_prop
    · intro a ha b hb hab
      have ha' : min τ 1 / 2 * a ∈ Set.Icc (0:ℝ) 1 :=
        ⟨by nlinarith [ha.1, hτ'pos], by nlinarith [ha.2, hτ'le]⟩
      have hb' : min τ 1 / 2 * b ∈ Set.Icc (0:ℝ) 1 :=
        ⟨by nlinarith [hb.1, hτ'pos], by nlinarith [hb.2, hτ'le]⟩
      exact mul_left_cancel₀ (ne_of_gt hτ'pos) (hγinj ha' hb' hab)
    · simp [hγ0]
    · intro t ht
      have hltτ : min τ 1 / 2 * t < τ := by
        have h1 : min τ 1 / 2 * t ≤ min τ 1 / 2 := by nlinarith [ht.2]
        linarith
      have hsmall : ‖γ (min τ 1 / 2 * t)‖ < s :=
        hτle _ ⟨by nlinarith [ht.1, hτ'pos], hltτ⟩
      have hmem : γ (min τ 1 / 2 * t) ∈ Metric.ball (0:E) ε \ L₂ :=
        hγX _ ⟨by nlinarith [ht.1, hτ'pos], by nlinarith [ht.2, hτ'le]⟩
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        linarith
      · intro hL₁mem
        have hmemL₁ : γ (min τ 1 / 2 * t) ∈ L₁ := by
          rcases hL₁mem with h' | h'
          · exact h'
          · exact absurd h' hmem.2
        have h2 := Metric.infDist_le_dist_of_mem (x := (0:E)) hmemL₁
        rw [dist_eq_norm, zero_sub, norm_neg] at h2
        linarith

/-- **Nested rooms.**  From rooms of arbitrary smallness for `K` around `0` one gets a nested
sequence of rooms `U n` shrinking to `0`, each with `U n \ K` path connected. -/
lemma nested_rooms {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E}
    (hrooms : ∀ N ∈ nhds (0:E), ∃ U : Set E, IsOpen U ∧ (0:E) ∈ U ∧ U ⊆ N ∧
      IsPathConnected (U \ K)) :
    ∃ U : ℕ → Set E, (∀ n, IsOpen (U n) ∧ (0:E) ∈ U n) ∧
      (∀ n, U (n+1) ⊆ U n) ∧ (∀ n, IsPathConnected (U n \ K)) ∧
      (∀ n, U (n+1) ⊆ Metric.ball (0:E) (1 / ((n:ℝ)+2))) := by
  classical
  obtain ⟨U₀, hU₀o, hU₀0, _hU₀sub, hU₀pc⟩ :=
    hrooms (Metric.ball (0:E) (1/2)) (Metric.ball_mem_nhds 0 (by norm_num))
  let φ : ℕ → Set E → Set E := fun n V =>
    if h : V ∈ nhds (0:E) then
      Classical.choose (hrooms (V ∩ Metric.ball (0:E) (1 / ((n:ℝ)+2)))
        (Filter.inter_mem h (Metric.ball_mem_nhds 0 (by positivity))))
    else Metric.ball (0:E) 1
  let U : ℕ → Set E := fun n => Nat.rec U₀ φ n
  have hUsucc : ∀ n, U (n+1) = φ n (U n) := fun n => rfl
  have hφspec : ∀ n V, V ∈ nhds (0:E) →
      IsOpen (φ n V) ∧ (0:E) ∈ φ n V ∧ φ n V ⊆ V ∧
        φ n V ⊆ Metric.ball (0:E) (1 / ((n:ℝ)+2)) ∧ IsPathConnected (φ n V \ K) := by
    intro n V hV
    have h1 : φ n V = Classical.choose (hrooms (V ∩ Metric.ball (0:E) (1 / ((n:ℝ)+2)))
        (Filter.inter_mem hV (Metric.ball_mem_nhds 0 (by positivity)))) := by
      simp only [φ]; rw [dif_pos hV]
    rw [h1]
    obtain ⟨ho, h0, hsub, hpc⟩ := Classical.choose_spec (hrooms
      (V ∩ Metric.ball (0:E) (1 / ((n:ℝ)+2)))
      (Filter.inter_mem hV (Metric.ball_mem_nhds 0 (by positivity))))
    exact ⟨ho, h0, hsub.trans Set.inter_subset_left, hsub.trans Set.inter_subset_right, hpc⟩
  have hUnhds : ∀ n, U n ∈ nhds (0:E) := by
    intro n
    induction n with
    | zero => exact hU₀o.mem_nhds hU₀0
    | succ n ih =>
      have h := hφspec n (U n) ih
      rw [hUsucc n]
      exact h.1.mem_nhds h.2.1
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro n
    induction n with
    | zero => exact ⟨hU₀o, hU₀0⟩
    | succ n ih =>
      exact ⟨(hφspec n (U n) (hUnhds n)).1, (hφspec n (U n) (hUnhds n)).2.1⟩
  · intro n
    rw [hUsucc n]
    exact (hφspec n (U n) (hUnhds n)).2.2.1
  · intro n
    induction n with
    | zero => exact hU₀pc
    | succ n ih => exact (hφspec n (U n) (hUnhds n)).2.2.2.2
  · intro n
    rw [hUsucc n]
    exact (hφspec n (U n) (hUnhds n)).2.2.2.1

/-! ## Clamping to `[0,1]` -/

/-- Clamp a real number into the unit interval. -/
noncomputable def clamp01 (t : ℝ) : ℝ := (Set.projIcc (0:ℝ) 1 zero_le_one t : ℝ)

@[simp] lemma clamp01_zero : clamp01 0 = 0 := by
  rw [clamp01, Set.projIcc_of_mem zero_le_one (x := (0:ℝ)) (by norm_num)]

@[simp] lemma clamp01_one : clamp01 1 = 1 := by
  rw [clamp01, Set.projIcc_of_mem zero_le_one (x := (1:ℝ)) (by norm_num)]

lemma continuous_clamp01 : Continuous clamp01 :=
  continuous_subtype_val.comp continuous_projIcc

lemma clamp01_mem (t : ℝ) : clamp01 t ∈ Set.Icc (0:ℝ) 1 := (Set.projIcc _ _ _ t).2

lemma clamp01_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : clamp01 t = t := by
  rw [clamp01, Set.projIcc_of_mem zero_le_one ht]


/-! ## The local room at the free end of an arc (the "weakened pacman")

The classical pacman construction gives a room at the endpoint `γ 0` of an arc, at the cost of
requiring the *whole* arc to lie in the ambient open set `W`.  Here only the initial piece
`γ '' Icc 0 c` is required to lie in `W`: the construction removes the *tail* `γ '' Icc (c,1)` from
`W ∩ e.source` anyway, so the far parts of the arc are irrelevant. -/

/-- `[0,c)` is preconnected. -/
theorem isPreconnected_Ico_aux {c : ℝ} (hc : 0 < c) : IsPreconnected (Set.Ico (0:ℝ) c) := by
  have h1 : IsPreconnected (Set.Ioo (0:ℝ) c) := isPreconnected_Ioo
  refine h1.subset_closure ?_ ?_
  · intro x hx; exact ⟨le_of_lt hx.1, hx.2⟩
  · intro x hx
    rw [closure_Ioo (ne_of_lt hc)]
    exact ⟨hx.1, le_of_lt hx.2⟩

theorem symm_image_inter_of_subset_aux {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : OpenPartialHomeomorph α β) {s : Set β} (hs : s ⊆ e.target) {a : Set α}
    (ha : a ⊆ e.source) : e.symm '' (s ∩ e '' a) = (e.symm '' s) ∩ a := by
  apply subset_antisymm
  · rintro z ⟨w, ⟨hw, hwe⟩, hwz⟩
    constructor
    · exact ⟨w, hw, hwz⟩
    · obtain ⟨a', ha', haw⟩ := hwe
      rw [← hwz, ← haw, e.left_inv (ha ha')]
      exact ha'
  · rintro z ⟨hz, hza⟩
    obtain ⟨w, hw, hwz⟩ := hz
    exact Exists.intro w (And.intro (And.intro hw
      (Exists.intro z (And.intro hza (by rw [← hwz]; exact e.right_inv (hs hw))))) hwz)

theorem symm_image_sdiff_of_subset_aux {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : OpenPartialHomeomorph α β) {s : Set β} (hs : s ⊆ e.target) {a : Set α}
    (ha : a ⊆ e.source) : e.symm '' (s \ e '' a) = (e.symm '' s) \ a := by
  apply subset_antisymm
  · rintro z ⟨w, ⟨hw, hwe⟩, hwz⟩
    constructor
    · exact ⟨w, hw, hwz⟩
    · intro hza
      refine hwe (Exists.intro z (And.intro hza ?_))
      rw [← hwz]
      exact e.right_inv (hs hw)
  · rintro z ⟨hz, hza⟩
    obtain ⟨w, hw, hwz⟩ := hz
    refine ⟨w, ⟨hw, ?_⟩, hwz⟩
    rintro ⟨a', ha', haw⟩
    refine hza ?_
    rw [← hwz, ← haw, e.left_inv (ha ha')]
    exact ha'

theorem pacman_room_local {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {W : Set M} (hW : IsOpen W)
    {γ : ℝ → M} (hγ : Continuous γ) (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hγ0W : γ 0 ∈ W)
    (hpiece : ∃ c ∈ Set.Ioc (0:ℝ) 1, γ '' Set.Icc (0:ℝ) c ⊆ W) :
    ∃ (U : Set M) (c : ℝ), IsOpen U ∧ U ⊆ W ∧ γ 0 ∈ U ∧ 0 < c ∧ c ≤ 1 ∧
      U ∩ γ '' Set.Icc (0:ℝ) 1 = γ '' (Set.Ico 0 c) ∧
      IsPreconnected (U \ γ '' Set.Icc (0:ℝ) 1) := by
  classical
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := 2)
  haveI : LocallyConnectedSpace M := inferInstance
  set E := EuclideanSpace ℝ (Fin 2)
  set e : OpenPartialHomeomorph M E := chartAt E (γ 0) with he
  have hγ0S : γ 0 ∈ e.source := mem_chart_source E (γ 0)
  have hnbhd : γ ⁻¹' e.source ∈ nhds (0:ℝ) :=
    hγ.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hγ0S)
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hnbhd
  obtain ⟨c₁, hc₁, hc₁W⟩ := hpiece
  set c : ℝ := min (min (δ / 2) (1 / 2)) c₁ with hcdef
  have hcpos : 0 < c := lt_min (lt_min (by linarith) (by norm_num)) hc₁.1
  have hc1 : c ≤ 1 :=
    le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (by norm_num)
  have hcδ : c ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcc₁ : c ≤ c₁ := min_le_right _ _
  have hcW : γ '' Set.Icc (0:ℝ) c ⊆ W :=
    (Set.image_mono (Set.Icc_subset_Icc le_rfl hcc₁)).trans hc₁W
  have harc_c : γ '' Set.Icc (0:ℝ) c ⊆ e.source := by
    rintro z ⟨t, ht, rfl⟩
    apply hδsub
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    have h1 : |t| ≤ c := by rw [abs_of_nonneg ht.1]; exact ht.2
    linarith
  have hγcS : γ c ∈ e.source := harc_c ⟨c, ⟨hcpos.le, le_rfl⟩, rfl⟩
  set h : ℝ → E := fun t => e (γ t) with hh
  set V : Set M := (W ∩ e.source) \ (γ '' Set.Icc c 1) with hV
  have hVopen : IsOpen V := (hW.inter e.open_source).sdiff (isCompact_Icc.image hγ).isClosed
  have hVsub : V ⊆ e.source := fun z hz => hz.1.2
  set Ω : Set E := e '' V with hΩ
  have hΩopen : IsOpen Ω := e.isOpen_image_of_subset_source hVopen hVsub
  have hγ0V : γ 0 ∈ V := by
    refine ⟨⟨hγ0W, hγ0S⟩, ?_⟩
    rintro ⟨t, ht, hte⟩
    have ht0 : t = 0 :=
      hinj ⟨le_trans (le_of_lt hcpos) ht.1, ht.2⟩ ⟨le_rfl, zero_le_one⟩ hte
    rw [ht0] at ht
    exact absurd ht.1 (not_le.mpr hcpos)
  have h0Ω : e (γ 0) ∈ Ω := ⟨γ 0, hγ0V, rfl⟩
  set Ωp : Set E := connectedComponentIn Ω (e (γ 0)) with hΩp
  have hΩpopen : IsOpen Ωp := hΩopen.connectedComponentIn
  have hΩppre : IsPreconnected Ωp := isPreconnected_connectedComponentIn
  have hΩpsub : Ωp ⊆ Ω := connectedComponentIn_subset _ _
  have h0Ωp : e (γ 0) ∈ Ωp := mem_connectedComponentIn h0Ω
  set U : Set M := e.symm '' Ωp with hU
  have hΩptgt : Ωp ⊆ e.target := fun z hz => by
    obtain ⟨v, hv, rfl⟩ := hΩpsub hz
    exact e.map_source hv.1.2
  have hUopen : IsOpen U := e.isOpen_image_symm_of_subset_target hΩpopen hΩptgt
  have hUsub : U ⊆ W := by
    rintro z ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hvz⟩ := hΩpsub hw
    rw [← hvz, e.left_inv hv.1.2]
    exact hv.1.1
  have hγ0U : γ 0 ∈ U := ⟨e (γ 0), h0Ωp, e.left_inv hγ0S⟩
  have hh_cont : ContinuousOn h (Set.Icc (0:ℝ) c) :=
    e.continuousOn.comp hγ.continuousOn (fun t ht => harc_c ⟨t, ht, rfl⟩)
  have hh_inj : Set.InjOn h (Set.Icc (0:ℝ) c) := by
    intro t₁ ht₁ t₂ ht₂ h12
    exact hinj ⟨ht₁.1, le_trans ht₁.2 hc1⟩ ⟨ht₂.1, le_trans ht₂.2 hc1⟩
      (e.injOn (harc_c ⟨t₁, ht₁, rfl⟩) (harc_c ⟨t₂, ht₂, rfl⟩) h12)
  have hhsub : ∀ c' < c, h '' Set.Icc (0:ℝ) c' ⊆ Ω := by
    intro c'' hc''
    rintro z ⟨t, ht, rfl⟩
    have ht1 : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, le_trans ht.2 (le_trans (le_of_lt hc'') hc1)⟩
    have hsrc : γ t ∈ e.source := harc_c ⟨t, ⟨ht.1, le_trans ht.2 (le_of_lt hc'')⟩, rfl⟩
    refine ⟨γ t, ⟨⟨hcW ⟨t, ⟨ht.1, le_trans ht.2 (le_of_lt hc'')⟩, rfl⟩, hsrc⟩, ?_⟩, rfl⟩
    rintro ⟨s, hs, hse⟩
    have hs1 : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans (le_of_lt hcpos) hs.1, hs.2⟩
    have hts : s = t := hinj hs1 ht1 hse
    rw [hts] at hs
    linarith [hs.1, ht.2, hc'']
  have hhout : h c ∉ Ω := by
    rintro ⟨v, hv, hvc⟩
    have heq : v = γ c := e.injOn hv.1.2 hγcS hvc
    exact hv.2 ⟨c, ⟨le_rfl, hc1⟩, heq.symm⟩
  have hhsubΩp : ∀ c'' < c, h '' Set.Icc (0:ℝ) c'' ⊆ Ωp := by
    intro c'' hc''
    by_cases hc''0 : 0 ≤ c''
    swap
    · rintro z ⟨t, ht, rfl⟩
      exact absurd (le_trans ht.1 ht.2) hc''0
    refine IsPreconnected.subset_connectedComponentIn
      ((isPreconnected_Icc).image h (hh_cont.mono (fun t ht => ⟨ht.1, le_trans ht.2 (le_of_lt hc'')⟩)))
      ⟨0, ⟨le_rfl, hc''0⟩, rfl⟩ ?_
    rintro z ⟨t, ht, rfl⟩
    exact hhsub c'' hc'' ⟨t, ht, rfl⟩
  have hhoutΩp : h c ∉ Ωp := fun h => hhout (hΩpsub h)
  have hcrux : IsPreconnected (Ωp \ h '' Set.Ico (0:ℝ) c) :=
    planar_slit_free_end hΩpopen hΩppre hcpos hh_cont hh_inj hhsubΩp hhoutΩp
  have hhIco_sub_Ωp : h '' Set.Ico (0:ℝ) c ⊆ Ωp := by
    refine IsPreconnected.subset_connectedComponentIn
      ((isPreconnected_Ico_aux hcpos).image h (hh_cont.mono (fun t ht => ⟨ht.1, le_of_lt ht.2⟩)))
      ⟨0, ⟨le_rfl, hcpos⟩, rfl⟩ ?_
    rintro z ⟨t, ht, rfl⟩
    exact hhsub t ht.2 ⟨t, ⟨ht.1, le_refl t⟩, rfl⟩
  have hkey1 : Ωp ∩ (e '' (γ '' Set.Icc (0:ℝ) 1 ∩ e.source)) = h '' Set.Ico (0:ℝ) c := by
    apply subset_antisymm
    · rintro z ⟨hzp, hze⟩
      obtain ⟨a, ha, haz⟩ := hze
      obtain ⟨t, ht, rfl⟩ := ha.1
      have hzt : γ t ∈ e.source := ha.2
      have hzv : γ t ∈ V := by
        obtain ⟨v, hv, hve⟩ := hΩpsub hzp
        have hvz : v = γ t := e.injOn hv.1.2 hzt (by rw [haz, hve])
        rw [← hvz]; exact hv
      refine ⟨t, ⟨ht.1, ?_⟩, ?_⟩
      · by_contra hcon
        push_neg at hcon
        exact hzv.2 ⟨t, ⟨hcon, ht.2⟩, rfl⟩
      · rw [hh]; exact haz
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := hz
      refine ⟨hhIco_sub_Ωp ⟨t, ht, rfl⟩, ?_⟩
      exact ⟨γ t, ⟨⟨t, ⟨ht.1, le_trans ht.2.le hc1⟩, rfl⟩,
        harc_c ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩⟩, rfl⟩
  refine ⟨U, c, hUopen, hUsub, hγ0U, hcpos, hc1, ?_, ?_⟩
  · have hsub : e.symm '' Ωp ⊆ e.source := by
      rintro z ⟨w, hw, rfl⟩
      exact e.symm.map_source (by rw [OpenPartialHomeomorph.symm_source]; exact hΩptgt hw)
    have hA : (γ '' Set.Icc (0:ℝ) 1) ∩ e.source ⊆ e.source := inter_subset_right
    have h1 : U ∩ (γ '' Set.Icc (0:ℝ) 1)
        = e.symm '' (Ωp ∩ (e '' ((γ '' Set.Icc (0:ℝ) 1) ∩ e.source))) := by
      rw [show U = e.symm '' Ωp from rfl, symm_image_inter_of_subset_aux e hΩptgt hA]
      ext z
      constructor
      · rintro ⟨hz, hzA⟩; exact ⟨hz, hzA, hsub hz⟩
      · rintro ⟨hz, hzA, -⟩; exact ⟨hz, hzA⟩
    rw [h1, hkey1]
    apply subset_antisymm
    · rintro z ⟨w, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      show γ t = e.symm (e (γ t))
      rw [e.left_inv (harc_c ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)]
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨h t, ⟨t, ht, rfl⟩, by
        show e.symm (e (γ t)) = γ t
        rw [e.left_inv (harc_c ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)]⟩
  · have hsub : e.symm '' Ωp ⊆ e.source := by
      rintro z ⟨w, hw, rfl⟩
      exact e.symm.map_source (by rw [OpenPartialHomeomorph.symm_source]; exact hΩptgt hw)
    have hA : (γ '' Set.Icc (0:ℝ) 1) ∩ e.source ⊆ e.source := inter_subset_right
    have heq : (e.symm '' Ωp) \ (γ '' Set.Icc (0:ℝ) 1)
        = (e.symm '' Ωp) \ ((γ '' Set.Icc (0:ℝ) 1) ∩ e.source) := by
      ext z
      constructor
      · rintro ⟨hz1, hz2⟩; exact ⟨hz1, fun h => hz2 h.1⟩
      · rintro ⟨hz1, hz2⟩; exact ⟨hz1, fun h => hz2 ⟨h, hsub hz1⟩⟩
    have h1 : U \ (γ '' Set.Icc (0:ℝ) 1)
        = e.symm '' (Ωp \ (e '' ((γ '' Set.Icc (0:ℝ) 1) ∩ e.source))) := by
      show (e.symm '' Ωp) \ (γ '' Set.Icc (0:ℝ) 1) = _
      rw [heq, symm_image_sdiff_of_subset_aux e hΩptgt hA]
    rw [h1]
    have hset : Ωp \ (e '' ((γ '' Set.Icc (0:ℝ) 1) ∩ e.source))
        = Ωp \ h '' Set.Ico (0:ℝ) c := by
      rw [← hkey1]
      ext z
      simp only [Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rw [hset]
    exact hcrux.image e.symm (e.continuousOn_symm.mono (fun z hz => hΩptgt hz.1))

/-! ## Rooms at the free end of an arc (both in the plane and in dimension `≥ 3`) -/

/-- **The rooms at the endpoint of a plane arc.** -/
theorem rooms_at_zero_plane {β : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hβc : Continuous β) (hβinj : Set.InjOn β (Set.Icc (0:ℝ) 1)) (hβ1 : β 1 = 0) :
    ∀ N ∈ nhds (0 : EuclideanSpace ℝ (Fin 2)),
      ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ N ∧
        IsPathConnected (U \ β '' Set.Icc (0:ℝ) 1) := by
  intro N hN
  obtain ⟨η, hηpos, hηN⟩ := Metric.mem_nhds_iff.mp hN
  set γ : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => β (1 - t) with hγdef
  have hγc : Continuous γ := hβc.comp (continuous_const.sub continuous_id)
  have hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1) := by
    intro a ha b hb hab
    have h1 : 1 - a ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ha.2], by linarith [ha.1]⟩
    have h2 : 1 - b ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
    have := hβinj h1 h2 hab
    linarith
  have hγ0 : γ 0 = 0 := by simp [hγdef, hβ1]
  have hγ0W : γ 0 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) η := by
    rw [hγ0]; exact Metric.mem_ball_self hηpos
  have hpiece : ∃ c ∈ Set.Ioc (0:ℝ) 1,
      γ '' Set.Icc (0:ℝ) c ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) η := by
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.continuousAt_iff.mp hγc.continuousAt η hηpos
    refine ⟨min (ρ / 2) (1 / 2), ⟨lt_min (by linarith) (by norm_num),
      le_trans (min_le_right _ _) (by norm_num)⟩, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h1 : |t| ≤ min (ρ / 2) (1 / 2) := by rw [abs_of_nonneg ht.1]; exact ht.2
    have h2 : min (ρ / 2) (1 / 2) ≤ ρ / 2 := min_le_left _ _
    have := hρ (by rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]; linarith)
    rwa [hγ0, dist_eq_norm, sub_zero] at this
  obtain ⟨U, c, hUo, hUW, hγ0U, hcpos, hc1, hUinter, hUpre⟩ :=
    pacman_room_local (W := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) η)
      Metric.isOpen_ball hγc hγinj hγ0W hpiece
  have himg : γ '' Set.Icc (0:ℝ) 1 = β '' Set.Icc (0:ℝ) 1 := by
    rw [hγdef, ← Set.image_image]
    congr 1
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · intro hz; exact ⟨1 - z, ⟨by linarith [hz.2], by linarith [hz.1]⟩, by ring⟩
  rw [← himg]
  refine ⟨U, hUo, ?_, hUW.trans hηN, ?_⟩
  · rw [← hγ0]; exact hγ0U
  have hclosed : IsClosed (β '' Set.Icc (0:ℝ) 1) := (isCompact_Icc.image hβc).isClosed
  have hopen : IsOpen (U \ γ '' Set.Icc (0:ℝ) 1) := hUo.sdiff ((isCompact_Icc.image hγc).isClosed)
  have hInt : interior (β '' Set.Icc (0:ℝ) 1) = ∅ :=
    Work.Noncompact.Canals.interior_image_arc_empty_euclidean (n := 2) (by norm_num)
      isCompact_Icc hβc.continuousOn hβinj
  have hne : (U \ γ '' Set.Icc (0:ℝ) 1).Nonempty := by
    have hnotsub : ¬ (U ⊆ γ '' Set.Icc (0:ℝ) 1) := by
      intro hsub
      have hmem : γ 0 ∈ interior (γ '' Set.Icc (0:ℝ) 1) :=
        mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (hUo.mem_nhds hγ0U) hsub)
      rw [himg, hInt] at hmem
      exact hmem
    obtain ⟨x, hxU, hxK⟩ := Set.not_subset.mp hnotsub
    exact ⟨x, hxU, hxK⟩
  exact hopen.isConnected_iff_isPathConnected.mp ⟨hne, hUpre⟩

/-- **The rooms at the endpoint of an arc in `ℝ^m`, `m ≥ 3`** (there is enough room in dimension
`≥ 3` to walk around a point of a one-dimensional arc, even around its endpoint). -/
theorem rooms_at_zero_ge3 {m : ℕ} (hm : 3 ≤ m)
    {β : ℝ → EuclideanSpace ℝ (Fin m)}
    (hβc : Continuous β) (hβinj : Set.InjOn β (Set.Icc (0:ℝ) 1)) (hβ1 : β 1 = 0) :
    ∀ N ∈ nhds (0 : EuclideanSpace ℝ (Fin m)),
      ∃ U : Set (EuclideanSpace ℝ (Fin m)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ N ∧
        IsPathConnected (U \ β '' Set.Icc (0:ℝ) 1) := by
  intro N hN
  obtain ⟨O, hOo, hOs, hON, hOpc⟩ :=
    Work.Whitney.PathTools.room_at_arc_manifold (n := m) hm hβc hβinj
      (s := 1) (by norm_num) (show N ∈ nhds (β 1) from by rwa [hβ1])
  exact ⟨O, hOo, by simpa [hβ1] using hOs, hON, hOpc⟩

/-! ## From rooms to an accessible arc, and the Euclidean endpoint lemma -/

/-- **Rooms at `0` give an accessible arc.** -/
theorem arcOut_of_rooms {m : ℕ} (hm : 2 ≤ m) {K : Set (EuclideanSpace ℝ (Fin m))}
    (hKc : IsCompact K) (h0K : (0 : EuclideanSpace ℝ (Fin m)) ∈ K) (hempty : interior K = ∅)
    (hrooms : ∀ N ∈ nhds (0 : EuclideanSpace ℝ (Fin m)),
      ∃ U : Set (EuclideanSpace ℝ (Fin m)), IsOpen U ∧ (0 : EuclideanSpace ℝ (Fin m)) ∈ U ∧
        U ⊆ N ∧ IsPathConnected (U \ K))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ℝ → EuclideanSpace ℝ (Fin m), Continuous v ∧ Set.InjOn v (Set.Icc (0:ℝ) 1) ∧
      v 0 = 0 ∧ (∀ t ∈ Set.Icc (0:ℝ) 1, v t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε) ∧
      ∀ t ∈ Set.Ioc (0:ℝ) 1, v t ∉ K := by
  classical
  obtain ⟨U, hUo0, hUne, hUpc, hUball⟩ := nested_rooms hrooms
  have hUo : ∀ n, IsOpen (U n) := fun n => (hUo0 n).1
  have hU0 : ∀ n, (0 : EuclideanSpace ℝ (Fin m)) ∈ U n := fun n => (hUo0 n).2
  have hKclosed : IsClosed K := hKc.isClosed
  have hKcpt : IsCompact K := hKc
  -- a scale with `1/(N₀+1) < ε`
  obtain ⟨N₀, hN₀⟩ : ∃ N : ℕ, 1 / ((N : ℝ) + 1) < ε := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
    refine ⟨M + 1, ?_⟩
    have hcast : (((M + 1 : ℕ)) : ℝ) + 1 = (M : ℝ) + 2 := by push_cast; ring
    rw [hcast, div_lt_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 2)]
    rw [div_lt_iff₀ hε] at hM
    nlinarith
  set V : ℕ → Set (EuclideanSpace ℝ (Fin m)) := fun n => U (N₀ + n + 1) \ K with hVdef
  set r : ℕ → ℝ := fun n => 1 / (((N₀ + n : ℕ) : ℝ) + 2) with hrdef
  have hVopen : ∀ n, IsOpen (V n) := fun n => (hUo (N₀ + n + 1)).sdiff hKclosed
  have hVpc : ∀ n, IsPathConnected (V n) := fun n => hUpc (N₀ + n + 1)
  have hVsub : ∀ n, V n ⊆ Kᶜ := fun n x hx => hx.2
  have hVball : ∀ n, V n ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (r n) := by
    intro n x hx
    rw [hVdef] at hx
    have hx' : x ∈ U (N₀ + n + 1) := hx.1
    have h := hUball (N₀ + n) hx'
    simpa [hrdef] using h
  have hVε : ∀ n, V n ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε := by
    intro n x hx
    have h1 : ‖x‖ < r n := by simpa [Metric.mem_ball, dist_zero_right] using hVball n hx
    rw [Metric.mem_ball, dist_zero_right]
    have h2 : r n ≤ (1:ℝ) / (((N₀ : ℕ) : ℝ) + 1) := by
      rw [hrdef]
      refine one_div_le_one_div_of_le (show (0:ℝ) < ((N₀ : ℕ) : ℝ) + 1 by positivity) ?_
      push_cast
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have h3 : ‖x‖ < (1:ℝ) / (((N₀ : ℕ) : ℝ) + 1) := lt_of_lt_of_le h1 h2
    exact lt_trans h3 hN₀
  have hrV : Filter.Tendsto r Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
    refine ⟨M, fun n hn => ?_⟩
    have hpos : (0 : ℝ) < (((N₀ + n : ℕ)) : ℝ) + 2 := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_pos (by rw [hrdef]; positivity), hrdef]
    rw [div_lt_iff₀ hpos]
    have h3 : (M : ℝ) ≤ (((N₀ + n : ℕ)) : ℝ) := by
      exact_mod_cast (le_trans hn (Nat.le_add_left n N₀))
    rw [div_lt_iff₀ hδ] at hM
    nlinarith
  have hcl : ∀ n, (0 : EuclideanSpace ℝ (Fin m)) ∈ closure (V n) := by
    intro n
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨ρ, hρpos, hρsub⟩ :=
      Metric.mem_nhds_iff.mp ((hUo (N₀ + n + 1)).mem_nhds (hU0 (N₀ + n + 1)))
    have hne : (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (min δ ρ) \ K).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (min δ ρ) ⊆ K := by
        intro x hx
        by_contra hxK
        exact (Set.eq_empty_iff_forall_notMem.mp hcon) x ⟨hx, hxK⟩
      have hmem : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K :=
        mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (Metric.ball_mem_nhds 0 (lt_min hδ hρpos)) hsub)
      rw [hempty] at hmem
      exact hmem
    obtain ⟨x, hx⟩ := hne
    have hx1 : x ∈ U (N₀ + n + 1) := hρsub (Metric.ball_subset_ball (min_le_right _ _) hx.1)
    refine ⟨x, ?_, ?_⟩
    · rw [hVdef]
      exact ⟨hx1, hx.2⟩
    · rw [dist_comm]
      linarith [Metric.mem_ball.mp hx.1, min_le_left δ ρ]
  have hmonoV : ∀ n, V (n + 1) ⊆ V n := by
    intro n
    exact Set.sdiff_subset_sdiff (hUne (N₀ + n + 1)) (subset_rfl)
  exact nested_pacmans_to_arc hε h0K V r hVopen hVpc hVsub hVε hVball hrV hcl hmonoV

/-- **The endpoint of an injective arc in Euclidean space is the initial point of an arc avoiding
the trace of the arc.** -/
theorem euclid_endpoint_arc {m : ℕ} (hm : 2 ≤ m) {β : ℝ → EuclideanSpace ℝ (Fin m)}
    (hβc : Continuous β) (hβinj : Set.InjOn β (Set.Icc (0:ℝ) 1)) (hβ1 : β 1 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (hβball : ∀ t ∈ Set.Icc (0:ℝ) 1, β t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε) :
    ∃ v : ℝ → EuclideanSpace ℝ (Fin m), Continuous v ∧ Set.InjOn v (Set.Icc (0:ℝ) 1) ∧
      v 0 = 0 ∧ (∀ t ∈ Set.Icc (0:ℝ) 1, v t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε) ∧
      (∀ t ∈ Set.Ioc (0:ℝ) 1, v t ∉ β '' Set.Icc (0:ℝ) 1) := by
  classical
  have hKc : IsCompact (β '' Set.Icc (0:ℝ) 1) := isCompact_Icc.image hβc
  have h0K : (0 : EuclideanSpace ℝ (Fin m)) ∈ β '' Set.Icc (0:ℝ) 1 :=
    ⟨1, ⟨zero_le_one, le_rfl⟩, hβ1⟩
  have hempty : interior (β '' Set.Icc (0:ℝ) 1) = ∅ :=
    Work.Noncompact.Canals.interior_image_arc_empty_euclidean (n := m) hm (γ := β)
      (K := Set.Icc (0:ℝ) 1) isCompact_Icc hβc.continuousOn hβinj
  have hrooms : ∀ N ∈ nhds (0 : EuclideanSpace ℝ (Fin m)),
      ∃ U : Set (EuclideanSpace ℝ (Fin m)), IsOpen U ∧ (0 : EuclideanSpace ℝ (Fin m)) ∈ U ∧
        U ⊆ N ∧ IsPathConnected (U \ β '' Set.Icc (0:ℝ) 1) := by
    rcases eq_or_lt_of_le hm with h2 | h3
    · subst h2
      exact rooms_at_zero_plane hβc hβinj hβ1
    · exact rooms_at_zero_ge3 (by omega) hβc hβinj hβ1
  exact arcOut_of_rooms hm hKc h0K hempty hrooms hε

/-! ## From the Euclidean endpoint lemma to the manifold statement -/

/-- **The endpoint of an injective arc in a manifold is the initial point of an arc avoiding the
trace of the given arc, inside any prescribed open neighbourhood of the endpoint.**

This is the manifold form of the classical fact that the free end of a compact arc is accessible.
The proof localises to a chart ball around `q`: the tail of the arc is transferred to a Euclidean
arc `β` (which lies in a ball), the Euclidean accessibility lemma produces an arc `v` there, and
`v` is trimmed once more against the chart image of the arc's *head* (which is compact and stays
away from `q`). -/
theorem exists_side_arc_of_arc_end_of_crux
    (hcrux : ∀ {m : ℕ}, 2 ≤ m → ∀ {β : ℝ → EuclideanSpace ℝ (Fin m)}, Continuous β →
      Set.InjOn β (Set.Icc (0:ℝ) 1) → β 1 = 0 → ∀ {ε : ℝ}, 0 < ε →
      (∀ t ∈ Set.Icc (0:ℝ) 1, β t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε) →
      ∃ v : ℝ → EuclideanSpace ℝ (Fin m), Continuous v ∧ Set.InjOn v (Set.Icc (0:ℝ) 1) ∧
        v 0 = 0 ∧ (∀ t ∈ Set.Icc (0:ℝ) 1, v t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε) ∧
        (∀ t ∈ Set.Ioc (0:ℝ) 1, v t ∉ β '' Set.Icc (0:ℝ) 1))
    {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {w : ℝ → M} (hwc : Continuous w) (hwi : Set.InjOn w (Set.Icc (0:ℝ) 1))
    {q : M} (hq : w 1 = q) {B : Set M} (hBo : IsOpen B) (hqB : q ∈ B) :
    ∃ y ∈ B, y ≠ q ∧ ∃ κ : ℝ → M, Continuous κ ∧ Set.InjOn κ (Set.Icc (0:ℝ) 1) ∧
      κ 0 = q ∧ κ 1 = y ∧ (∀ t ∈ Set.Icc (0:ℝ) 1, κ t ∈ B) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ t' ∈ Set.Icc (0:ℝ) 1, κ t ≠ w t' ∨ κ t = q := by
  classical
  set E := EuclideanSpace ℝ (Fin n) with hE
  set e : OpenPartialHomeomorph M E := chartAt E q with he
  have hqsrc : q ∈ e.source := mem_chart_source E q
  have hqtgt : e q ∈ e.target := e.map_source hqsrc
  -- chart balls: one inside the chart target, one inside `B`
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hqtgt)
  have hsymm_at : ContinuousAt e.symm (e q) := e.continuousAt_symm hqtgt
  have hpreB : e.symm ⁻¹' B ∈ nhds (e q) := by
    refine hsymm_at.preimage_mem_nhds ?_
    rw [e.left_inv hqsrc]
    exact hBo.mem_nhds hqB
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hpreB
  set δ : ℝ := min δ₀ δ₁ / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith [lt_min hδ₀pos hδ₁pos]
  have hδle₀ : δ ≤ δ₀ := by rw [hδdef]; linarith [min_le_left δ₀ δ₁]
  have hδle₁ : δ ≤ δ₁ := by rw [hδdef]; linarith [min_le_right δ₀ δ₁]
  -- the tail of `w` near `1` lies in the chart and close to `q`
  have hsrc_nhds : w ⁻¹' e.source ∈ nhds (1:ℝ) := by
    refine hwc.continuousAt.preimage_mem_nhds ?_
    rw [hq]; exact e.open_source.mem_nhds hqsrc
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := Metric.mem_nhds_iff.mp hsrc_nhds
  have hcew : ContinuousAt (fun t : ℝ => e (w t)) 1 := by
    have h2 : ContinuousAt e (w 1) := by rw [hq]; exact e.continuousAt hqsrc
    exact h2.comp hwc.continuousAt
  have hpre_ball : (fun t : ℝ => e (w t)) ⁻¹' Metric.ball (e q) δ ∈ nhds (1:ℝ) := by
    have hq' : e (w 1) = e q := by rw [hq]
    exact hcew.preimage_mem_nhds (hq' ▸ Metric.ball_mem_nhds (e (w 1)) hδpos)
  obtain ⟨ε₂, hε₂pos, hε₂sub⟩ := Metric.mem_nhds_iff.mp hpre_ball
  set ε : ℝ := min (min ε₁ ε₂) 1 / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith [lt_min (lt_min hε₁pos hε₂pos) one_pos]
  have hεlt₁ : ε < ε₁ := by
    rw [hεdef]; have := min_le_left (min ε₁ ε₂) 1; have := min_le_left ε₁ ε₂; linarith
  have hεlt₂ : ε < ε₂ := by
    rw [hεdef]; have := min_le_left (min ε₁ ε₂) 1; have := min_le_right ε₁ ε₂; linarith
  have hεle : ε ≤ 1 / 2 := by
    rw [hεdef]; have := min_le_right (min ε₁ ε₂) 1; linarith
  set t₀ : ℝ := 1 - ε with ht₀def
  have ht₀lt : t₀ < 1 := by rw [ht₀def]; linarith
  have ht₀le : t₀ ≤ 1 := ht₀lt.le
  have ht₀ge : 0 ≤ t₀ := by rw [ht₀def]; linarith
  have hdist : ∀ t ∈ Set.Icc t₀ 1, dist t 1 ≤ ε := by
    intro t ht
    rw [Real.dist_eq, abs_le]
    refine ⟨?_, by linarith [ht.2]⟩
    have h1 : (1:ℝ) - ε ≤ t := by rw [← ht₀def]; exact ht.1
    linarith
  have htail_src : ∀ t ∈ Set.Icc t₀ 1, w t ∈ e.source := fun t ht =>
    hε₁sub (by rw [Metric.mem_ball]; linarith [hdist t ht, hεlt₁])
  have htail_ball : ∀ t ∈ Set.Icc t₀ 1, e (w t) ∈ Metric.ball (e q) δ := fun t ht =>
    hε₂sub (by rw [Metric.mem_ball]; linarith [hdist t ht, hεlt₂])
  -- the head of the arc
  have hHclosed : IsClosed (w '' Set.Icc (0:ℝ) t₀) := isClosed_image_Icc_of_le_one hwc ht₀le
  have hqH : q ∉ w '' Set.Icc (0:ℝ) t₀ := notMem_image_Icc_of_lt_one hwi hq ht₀lt
  -- the transferred arc
  set τ : ℝ → ℝ := fun t => t₀ + (1 - t₀) * clamp01 t with hτdef
  have hτmem : ∀ t, τ t ∈ Set.Icc t₀ 1 := by
    intro t
    have hc := clamp01_mem t
    have h1 : t₀ ≤ τ t := by
      rw [hτdef]
      have : 0 ≤ (1 - t₀) * clamp01 t := mul_nonneg (by linarith [ht₀lt]) hc.1
      linarith
    have h2 : τ t ≤ 1 := by
      rw [hτdef]
      have : (1 - t₀) * clamp01 t ≤ (1 - t₀) * 1 :=
        mul_le_mul_of_nonneg_left hc.2 (by linarith [ht₀lt])
      linarith
    exact ⟨h1, h2⟩
  have hτ01 : ∀ t, τ t ∈ Set.Icc (0:ℝ) 1 := fun t =>
    ⟨le_trans ht₀ge (hτmem t).1, (hτmem t).2⟩
  have hτcont : Continuous τ := by
    rw [hτdef]
    exact continuous_const.add ((continuous_const.sub continuous_const).mul continuous_clamp01)
  have hτinjOn : Set.InjOn τ (Set.Icc (0:ℝ) 1) := by
    intro a ha b hb hab
    have hne : (1 - t₀) ≠ 0 := by linarith [ht₀lt]
    have h1 : (1 - t₀) * clamp01 a = (1 - t₀) * clamp01 b := by
      rw [hτdef] at hab; linarith
    have h2 : clamp01 a = clamp01 b := mul_left_cancel₀ hne h1
    rw [clamp01_of_mem ha, clamp01_of_mem hb] at h2
    exact h2
  set β : ℝ → E := fun t => e (w (τ t)) - e q with hβdef
  have hτ1 : τ 1 = 1 := by
    rw [hτdef]
    show t₀ + (1 - t₀) * clamp01 1 = 1
    rw [clamp01_one]; ring
  have hβ1 : β 1 = 0 := by
    rw [hβdef]
    show e (w (τ 1)) - e q = 0
    rw [hτ1, hq, sub_self]
  have hβc : Continuous β := by
    rw [hβdef]
    have hww : Continuous fun t : ℝ => w (τ t) := hwc.comp hτcont
    have heww : Continuous fun t : ℝ => e (w (τ t)) := by
      have h2 : ContinuousOn (fun t : ℝ => e (w (τ t))) Set.univ :=
        e.continuousOn.comp (s := Set.univ) (t := e.source) hww.continuousOn
          (fun t _ => htail_src (τ t) (hτmem t))
      rwa [continuousOn_univ] at h2
    exact heww.sub continuous_const
  have hβinj : Set.InjOn β (Set.Icc (0:ℝ) 1) := by
    intro a ha b hb hab
    rw [hβdef] at hab
    have hab' : e (w (τ a)) - e q = e (w (τ b)) - e q := hab
    have h1 : e (w (τ a)) = e (w (τ b)) := sub_left_inj.mp hab'
    have h2 : w (τ a) = w (τ b) :=
      e.injOn (htail_src (τ a) (hτmem a)) (htail_src (τ b) (hτmem b)) h1
    have h3 : τ a = τ b := hwi (hτ01 a) (hτ01 b) h2
    exact hτinjOn ha hb h3
  have hβsmall : ∀ t ∈ Set.Icc (0:ℝ) 1, β t ∈ Metric.ball (0:E) δ := by
    intro t ht
    have hm : dist (e (w (τ t))) (e q) < δ := Metric.mem_ball.mp (htail_ball (τ t) (hτmem t))
    rw [Metric.mem_ball, dist_zero_right]
    show ‖e (w (τ t)) - e q‖ < δ
    rwa [dist_eq_norm] at hm
  -- the Euclidean accessibility lemma
  obtain ⟨v, hvc, hvinj, hv0, hvball, hvavoid⟩ := hcrux hn hβc hβinj hβ1 hδpos hβsmall
  -- the chart image of the head is an obstacle away from the origin
  set L₁ : Set E := (fun y : E => y - e q) '' (e '' ((w '' Set.Icc (0:ℝ) t₀) ∩ e.source))
    with hL₁def
  have hΨcont : ContinuousAt (fun y : E => e.symm (y + e q)) (0:E) := by
    have h1 : ContinuousOn (fun y : E => e.symm (y + e q)) (Metric.ball (0:E) δ) := by
      have hcont : ContinuousOn (fun y : E => y + e q) (Metric.ball (0:E) δ) :=
        (continuous_id.add continuous_const).continuousOn
      refine e.continuousOn_symm.comp (s := Metric.ball (0:E) δ) (t := e.target) hcont ?_
      intro y hy
      have h2 : dist (y + e q) (e q) < δ := by
        rw [dist_eq_norm, add_sub_cancel_right]
        simpa [dist_eq_norm] using Metric.mem_ball.mp hy
      exact hδ₀sub (Metric.mem_ball.mpr (lt_of_lt_of_le h2 hδle₀))
    exact h1.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδpos))
  have hΨL₁ : (fun y : E => e.symm (y + e q)) '' L₁ ⊆ w '' Set.Icc (0:ℝ) t₀ := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨m, hm, rfl⟩ := hz
    show e.symm ((e m - e q) + e q) ∈ w '' Set.Icc (0:ℝ) t₀
    rw [sub_add_cancel, e.left_inv hm.2]
    exact hm.1
  have h0L₁ : (0:E) ∉ closure L₁ := by
    have hHc : (w '' Set.Icc (0:ℝ) t₀)ᶜ ∈ nhds q := hHclosed.isOpen_compl.mem_nhds hqH
    have hpre : (fun y : E => e.symm (y + e q)) ⁻¹' (w '' Set.Icc (0:ℝ) t₀)ᶜ ∈ nhds (0:E) := by
      refine hΨcont.preimage_mem_nhds ?_
      rw [zero_add, e.left_inv hqsrc]
      exact hHc
    obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp hpre
    intro hcl
    obtain ⟨y, hyL₁, hydist⟩ := Metric.mem_closure_iff.mp hcl η hηpos
    have hyball : y ∈ Metric.ball (0:E) η := by
      rw [Metric.mem_ball]; rwa [dist_comm] at hydist
    exact (hηsub hyball) (hΨL₁ ⟨y, hyL₁, rfl⟩)
  have hAcc : ArcOut E (Metric.ball (0:E) δ \ β '' Set.Icc (0:ℝ) 1) :=
    ⟨v, hvc, hvinj, hv0, fun t ht => ⟨hvball t ⟨ht.1.le, ht.2⟩, hvavoid t ht⟩⟩
  obtain ⟨v', hv'c, hv'inj, hv'0, hv'X⟩ := arcOut_sdiff_compact h0L₁ hδpos hAcc
  -- the accessible arc in the manifold
  set κ : ℝ → M := fun t => e.symm (v' (clamp01 t) + e q) with hκdef
  have hv'ball : ∀ t, v' (clamp01 t) ∈ Metric.ball (0:E) δ := by
    intro t
    rcases eq_or_lt_of_le (clamp01_mem t).1 with h0 | h0
    · rw [← h0]; rw [hv'0]; exact Metric.mem_ball_self hδpos
    · exact (hv'X (clamp01 t) ⟨h0, (clamp01_mem t).2⟩).1
  have hvtgt : ∀ t, v' (clamp01 t) + e q ∈ e.target := by
    intro t
    have h1 : v' (clamp01 t) ∈ Metric.ball (0:E) δ := hv'ball t
    have h2 : dist (v' (clamp01 t) + e q) (e q) < δ := by
      rw [dist_eq_norm, add_sub_cancel_right]
      simpa [dist_eq_norm] using Metric.mem_ball.mp h1
    exact hδ₀sub (Metric.mem_ball.mpr (lt_of_lt_of_le h2 hδle₀))
  have hκc : Continuous κ := by
    have h1 : ContinuousOn (fun s : ℝ => v' (clamp01 s) + e q) Set.univ :=
      ((hv'c.comp continuous_clamp01).add continuous_const).continuousOn
    have h2 : ContinuousOn (fun s : ℝ => e.symm (v' (clamp01 s) + e q)) Set.univ :=
      e.continuousOn_symm.comp (s := Set.univ) (t := e.target) h1 (fun s _ => hvtgt s)
    rw [hκdef]
    rwa [continuousOn_univ] at h2
  have hκ0 : κ 0 = q := by
    rw [hκdef]
    show e.symm (v' (clamp01 0) + e q) = q
    rw [clamp01_zero, hv'0, zero_add, e.left_inv hqsrc]
  have hκB : ∀ t ∈ Set.Icc (0:ℝ) 1, κ t ∈ B := by
    intro t ht
    rw [hκdef]
    refine hδ₁sub ?_
    rw [Metric.mem_ball]
    have h1 : ‖v' (clamp01 t)‖ < δ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp (hv'ball t)
    rw [dist_eq_norm, add_sub_cancel_right]
    linarith [hδle₁]
  have hκinj : Set.InjOn κ (Set.Icc (0:ℝ) 1) := by
    intro a ha b hb hab
    rw [hκdef] at hab
    have hab' : e.symm (v' (clamp01 a) + e q) = e.symm (v' (clamp01 b) + e q) := hab
    have h1 : v' (clamp01 a) + e q = v' (clamp01 b) + e q :=
      e.symm.injOn (by rw [OpenPartialHomeomorph.symm_source]; exact hvtgt a)
        (by rw [OpenPartialHomeomorph.symm_source]; exact hvtgt b) hab'
    have h2 : v' (clamp01 a) = v' (clamp01 b) := by
      rw [clamp01_of_mem ha, clamp01_of_mem hb] at h1 ⊢
      exact add_right_cancel h1
    rw [clamp01_of_mem ha, clamp01_of_mem hb] at h2
    exact hv'inj ha hb h2
  refine ⟨κ 1, hκB 1 ⟨zero_le_one, le_rfl⟩, ?_, κ, hκc, hκinj, hκ0, rfl,
    hκB, ?_⟩
  · intro hy
    have h1 : v' 1 + e q = e q := by
      have h2 : κ 1 = κ 0 := by rw [hy, hκ0]
      rw [hκdef] at h2
      have h2' : e.symm (v' (clamp01 1) + e q) = e.symm (v' (clamp01 0) + e q) := h2
      have h5 := e.symm.injOn
        (by rw [OpenPartialHomeomorph.symm_source]; exact hvtgt 1)
        (by rw [OpenPartialHomeomorph.symm_source]; exact hvtgt 0) h2'
      rw [clamp01_one, clamp01_zero, hv'0, zero_add] at h5
      exact h5
    have h3 : v' 1 = 0 := by
      have h4 : v' 1 + e q = 0 + e q := by rw [zero_add]; exact h1
      exact add_right_cancel h4
    have h4 := hv'inj (by norm_num : (1:ℝ) ∈ Set.Icc 0 1) (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)
      (by rw [h3, hv'0])
    norm_num at h4
  · intro t ht t' ht'
    by_cases h0 : clamp01 t = 0
    · refine Or.inr ?_
      rw [hκdef]
      show e.symm (v' (clamp01 t) + e q) = q
      rw [h0, hv'0, zero_add, e.left_inv hqsrc]
    · refine Or.inl fun heq => ?_
      have hmemIoc : clamp01 t ∈ Set.Ioc (0:ℝ) 1 :=
        ⟨lt_of_le_of_ne (clamp01_mem t).1 (Ne.symm h0), (clamp01_mem t).2⟩
      have hκsrc : κ t ∈ e.source := by
        rw [hκdef]
        exact e.symm.map_source (by
          rw [OpenPartialHomeomorph.symm_source]; exact hvtgt t)
      have heκ : e (κ t) = v' (clamp01 t) + e q := by
        rw [hκdef]; exact e.right_inv (hvtgt t)
      have hveq : v' (clamp01 t) = e (w t') - e q := by
        have h1 : e (w t') = v' (clamp01 t) + e q := by
          rw [← heq, heκ]
        rw [h1]; abel
      have hwt'src : w t' ∈ e.source := by rw [← heq]; exact hκsrc
      rcases le_or_gt t₀ t' with hge | hlt
      · -- the terminal piece case
        have hs01 : (t' - t₀) / (1 - t₀) ∈ Set.Icc (0:ℝ) 1 := by
          refine ⟨?_, ?_⟩
          · apply div_nonneg <;> linarith [hge, ht₀lt]
          · rw [div_le_one (by linarith [ht₀lt] : (0:ℝ) < 1 - t₀)]; linarith [ht'.2, ht₀lt]
        have hmem : v' (clamp01 t) ∈ β '' Set.Icc (0:ℝ) 1 := by
          refine ⟨(t' - t₀) / (1 - t₀), hs01, ?_⟩
          show e (w (τ ((t' - t₀) / (1 - t₀)))) - e q = v' (clamp01 t)
          rw [hτdef]
          show e (w (t₀ + (1 - t₀) * clamp01 ((t' - t₀) / (1 - t₀)))) - e q = v' (clamp01 t)
          rw [clamp01_of_mem hs01]
          have harg : t₀ + (1 - t₀) * ((t' - t₀) / (1 - t₀)) = t' := by
            rw [mul_div_cancel₀ _ (by linarith [ht₀lt] : (1 - t₀) ≠ 0)]; ring
          rw [harg, hveq]
        exact (hv'X (clamp01 t) hmemIoc).2 (Or.inr hmem)
      · -- the head case
        have hmemH : w t' ∈ (w '' Set.Icc (0:ℝ) t₀) ∩ e.source :=
          ⟨⟨t', ⟨ht'.1, hlt.le⟩, rfl⟩, hwt'src⟩
        have hmem : v' (clamp01 t) ∈ L₁ := by
          refine ⟨e (w t'), ⟨w t', hmemH, rfl⟩, ?_⟩
          show e (w t') - e q = v' (clamp01 t)
          rw [hveq]
        exact (hv'X (clamp01 t) hmemIoc).2 (Or.inl hmem)

/-- **Whitney's local free-end lemma.**  The endpoint `q = w 1` of a (locally) injective arc in an
`n`-manifold, `n ≥ 2`, is the initial point of an arc `κ` which stays in any prescribed open
neighbourhood `B` of `q` and meets the trace of `w` only at `q`. -/
theorem exists_side_arc_of_arc_end {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {w : ℝ → M} (hwc : Continuous w) (hwi : Set.InjOn w (Set.Icc (0:ℝ) 1))
    {q : M} (hq : w 1 = q) {B : Set M} (hBo : IsOpen B) (hqB : q ∈ B) :
    ∃ y ∈ B, y ≠ q ∧ ∃ κ : ℝ → M, Continuous κ ∧ Set.InjOn κ (Set.Icc (0:ℝ) 1) ∧
      κ 0 = q ∧ κ 1 = y ∧ (∀ t ∈ Set.Icc (0:ℝ) 1, κ t ∈ B) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ t' ∈ Set.Icc (0:ℝ) 1, κ t ≠ w t' ∨ κ t = q :=
  exists_side_arc_of_arc_end_of_crux
    (fun {m : ℕ} hm {β : ℝ → EuclideanSpace ℝ (Fin m)} hβc hβinj hβ1 {ε : ℝ} hε hβball =>
      euclid_endpoint_arc hm hβc hβinj hβ1 hε hβball)
    hn hwc hwi hq hBo hqB

end Work.Noncompact.CompressionTube
