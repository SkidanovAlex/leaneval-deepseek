import Mathlib
import Submission.Work.OneDim.ArcDefs
import Submission.Work.OneDim.ArcSet
import Submission.Work.OneDim.ift_real
import Submission.Work.OneDim.local_diffeo_congr

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Set Function Filter

namespace Work.OneDim

/-- A continuous injective function on a half-line with positive values tending to `0` at `+∞` is
strictly antitone there. -/
theorem strictAntiOn_Ici_of_contOn_injOn_tendsto_zero {b : ℝ → ℝ} {t₁ : ℝ}
    (hcont : ContinuousOn b (Set.Ici t₁)) (hinj : Set.InjOn b (Set.Ici t₁))
    (hpos : ∀ t, t₁ ≤ t → 0 < b t)
    (htend : Filter.Tendsto b Filter.atTop (nhds 0)) :
    StrictAntiOn b (Set.Ici t₁) := by
  intro a ha c hc hac
  by_contra h
  rw [not_lt] at h
  have hlt : b a < b c :=
    lt_of_le_of_ne h (fun heq => absurd (hinj ha hc heq) (ne_of_lt hac))
  have hbapos : 0 < b a := hpos a ha
  have hev : ∀ᶠ t in Filter.atTop, b t < b a := by
    have h1 : ∀ᶠ t in Filter.atTop, b t ∈ Metric.ball (0:ℝ) (b a) :=
      htend.eventually (Metric.ball_mem_nhds (0:ℝ) hbapos)
    filter_upwards [h1] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact lt_of_le_of_lt (le_abs_self _) ht
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
  set T' : ℝ := max T (max (c + 1) t₁) with hT'def
  have hTT' : T ≤ T' := le_max_left _ _
  have hcT' : c + 1 ≤ T' := le_trans (le_max_left _ _) (le_max_right _ _)
  have hbT' : b T' < b a := hT T' hTT'
  have hacT' : a ≤ T' := le_trans hac.le (by linarith)
  have hcT'2 : c ≤ T' := by linarith
  have hsub : Set.Icc a T' ⊆ Set.Ici t₁ := fun x hx => le_trans ha hx.1
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' hacT' (hcont.mono hsub) (hinj.mono hsub) with
    hmono | hanti
  · have h1 : b a < b c := hmono (left_mem_Icc.mpr hacT') ⟨hac.le, hcT'2⟩ hac
    have h2 : b c < b T' := hmono ⟨hac.le, hcT'2⟩ (right_mem_Icc.mpr hacT') (by linarith)
    linarith
  · have h1 : b c < b a := hanti (left_mem_Icc.mpr hacT') ⟨hac.le, hcT'2⟩ hac
    linarith

/-- A smooth strictly increasing "step" `H` with `H = id` far to the right, `H 0 = -ε`, nowhere
vanishing derivative and `H '' (0,c₁) = (-ε, c₁)`. -/
theorem exists_smooth_H (c₁ ε : ℝ) (hc₁ : 0 < c₁) (hε : 0 < ε) :
    ∃ H : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H ∧ StrictMono H ∧
      (∀ y : ℝ, c₁ / 4 ≤ y → H y = y) ∧ H 0 = -ε ∧ (∀ y : ℝ, deriv H y ≠ 0) ∧
      H '' Set.Ioo 0 c₁ = Set.Ioo (-ε) c₁ := by
  set μ : ℝ → ℝ := fun y => Real.smoothTransition (1 - 4 * y / c₁) with hμ
  have hμcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ := by
    rw [hμ]; fun_prop
  have hμanti : Antitone μ := by
    rw [hμ]
    refine Real.smoothTransition.monotone.comp_antitone ?_
    intro x y hxy
    have h : 4 * x / c₁ ≤ 4 * y / c₁ := div_le_div_of_nonneg_right (by linarith) hc₁.le
    linarith
  have hμzero : ∀ y : ℝ, c₁ / 4 ≤ y → μ y = 0 := by
    intro y hy
    rw [hμ]
    apply Real.smoothTransition.zero_of_nonpos
    have h : (1:ℝ) ≤ 4 * y / c₁ := (one_le_div hc₁).2 (by linarith)
    linarith
  set H : ℝ → ℝ := fun y => y - ε * μ y with hHdef
  have hHcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H := by
    rw [hHdef]; exact contDiff_id.sub (contDiff_const.mul hμcont)
  have hμ0 : μ 0 = 1 := by simp [hμ]
  have hHid : ∀ y : ℝ, c₁ / 4 ≤ y → H y = y := by
    intro y hy; change y - ε * μ y = y; rw [hμzero y hy]; ring
  have hHmono : StrictMono H := by
    intro y₁ y₂ hy
    have h : μ y₂ ≤ μ y₁ := hμanti hy.le
    rw [hHdef]; simp only; nlinarith [hε]
  have hH0 : H 0 = -ε := by rw [hHdef]; simp [hμ0]
  have hHderiv : ∀ y : ℝ, deriv H y ≠ 0 := by
    intro y
    have hμdiff : DifferentiableAt ℝ μ y := (hμcont.differentiable (by decide)).differentiableAt
    have hderiv : deriv H y = 1 - ε * deriv μ y := by
      have h1 : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id y
      have h2 : HasDerivAt (fun y : ℝ => ε * μ y) (ε * deriv μ y) y :=
        hμdiff.hasDerivAt.const_mul ε
      have h3 : HasDerivAt (fun y : ℝ => y - ε * μ y) (1 - ε * deriv μ y) y := h1.sub h2
      rw [hHdef, h3.deriv]
    rw [hderiv]
    have h : deriv μ y ≤ 0 := hμanti.deriv_nonpos
    have : ε * deriv μ y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le h
    linarith
  have hHimage : H '' Set.Ioo 0 c₁ = Set.Ioo (-ε) c₁ := by
    have hc1 : c₁ / 4 ≤ c₁ := by linarith
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : H 0 < H y := hHmono hy.1
      have h2 : H y < H c₁ := hHmono hy.2
      rw [hH0] at h1
      rw [hHid c₁ hc1] at h2
      exact ⟨h1, h2⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := hz
      have hcont : ContinuousOn H (Set.Icc 0 c₁) := hHcont.continuous.continuousOn
      have hmem : z ∈ Set.Icc (H 0) (H c₁) := by
        rw [hH0, hHid c₁ hc1]; exact ⟨hz1.le, hz2.le⟩
      obtain ⟨y, hyI, hyz⟩ := intermediate_value_Icc hc₁.le hcont hmem
      refine ⟨y, ⟨?_, ?_⟩, hyz⟩
      · rcases eq_or_lt_of_le hyI.1 with h | h
        · exfalso; rw [← h, hH0] at hyz; linarith
        · exact h
      · rcases lt_or_eq_of_le hyI.2 with h | h
        · exact h
        · exfalso; rw [h, hHid c₁ hc1] at hyz; linarith
  exact ⟨H, hHcont, hHmono, hHid, hH0, hHderiv, hHimage⟩


/-- Tail data for the extension lemma. -/
theorem tail_data {C : Type*} [TopologicalSpace C] [ChartedSpace Work.OneDim.E1 C]
    [IsManifold Work.OneDim.I1 Work.OneDim.sm C]
    {γ : ℝ → C} (hinj : Function.Injective γ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1 Work.OneDim.sm γ)
    {q : C} (hconv : Filter.Tendsto γ Filter.atTop (nhds q))
    (φ : PartialDiffeomorph Work.OneDim.I1 (modelWithCornersSelf ℝ ℝ) C ℝ Work.OneDim.sm)
    (hqsrc : q ∈ φ.source) (hq0 : φ q = 0) {δ : ℝ}
    (hpos : ∃ T : ℝ, ∀ t ≥ T, γ t ∈ φ.source ∧ 0 < φ (γ t) ∧ φ (γ t) < δ) :
    ∃ t₁ c₁ : ℝ, 0 < c₁ ∧ c₁ < δ ∧ φ (γ t₁) = c₁ ∧
      (∀ t : ℝ, t₁ ≤ t → γ t ∈ φ.source ∧ 0 < φ (γ t) ∧ φ (γ t) ≤ c₁) ∧
      StrictAntiOn (fun t : ℝ => φ (γ t)) (Set.Ici t₁) ∧
      Filter.Tendsto (fun t : ℝ => φ (γ t)) Filter.atTop (nhds 0) ∧
      (∀ y ∈ Set.Ioo (0:ℝ) c₁, ∃ t : ℝ, t₁ < t ∧ φ (γ t) = y) ∧
      (∀ s : ℝ, γ s ∈ φ.source → φ (γ s) ∈ Set.Ioo (0:ℝ) c₁ → t₁ < s) := by
  obtain ⟨T, hT⟩ := hpos
  have hγc : Continuous γ := hld.contMDiff.continuous
  have hcont : ContinuousOn (fun t : ℝ => φ (γ t)) (Set.Ici T) :=
    (φ.contMDiffOn_toFun.continuousOn).comp hγc.continuousOn (fun t ht => (hT t ht).1)
  have hinj' : Set.InjOn (fun t : ℝ => φ (γ t)) (Set.Ici T) := by
    intro s hs t ht hst
    have hs' : γ s ∈ φ.source := (hT s hs).1
    have ht' : γ t ∈ φ.source := (hT t ht).1
    exact hinj (φ.toPartialEquiv.injOn hs' ht' hst)
  have hpos' : ∀ t : ℝ, T ≤ t → 0 < φ (γ t) := fun t ht => (hT t ht).2.1
  have htend : Filter.Tendsto (fun t : ℝ => φ (γ t)) Filter.atTop (nhds 0) := by
    have hcontq : ContinuousAt (fun x : C => φ x) q :=
      φ.contMDiffOn_toFun.continuousOn.continuousAt (φ.open_source.mem_nhds hqsrc)
    have h1 : Filter.Tendsto (fun t : ℝ => φ (γ t)) Filter.atTop (nhds (φ q)) :=
      hcontq.tendsto.comp hconv
    rwa [hq0] at h1
  have hanti : StrictAntiOn (fun t : ℝ => φ (γ t)) (Set.Ici T) :=
    strictAntiOn_Ici_of_contOn_injOn_tendsto_zero hcont hinj' hpos' htend
  refine ⟨T, φ (γ T), (hT T le_rfl).2.1, (hT T le_rfl).2.2, rfl, ?_, hanti, htend, ?_, ?_⟩
  · intro t ht
    refine ⟨(hT t ht).1, (hT t ht).2.1, ?_⟩
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]
    · exact le_of_lt (hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) h)
  · intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hev : ∀ᶠ t in Filter.atTop, φ (γ t) < y := by
      have h1 : ∀ᶠ t in Filter.atTop, φ (γ t) ∈ Metric.ball (0:ℝ) y :=
        htend.eventually (Metric.ball_mem_nhds (0:ℝ) hy1)
      filter_upwards [h1] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact lt_of_le_of_lt (le_abs_self _) ht
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
    set T'' : ℝ := max T₀ (T + 1) with hT''def
    have hT₀T'' : T₀ ≤ T'' := le_max_left _ _
    have hTT'' : T + 1 ≤ T'' := le_max_right _ _
    have hyy : φ (γ T'') < y := hT₀ T'' hT₀T''
    have hsub : Set.Icc T T'' ⊆ Set.Ici T := fun x hx => hx.1
    have hcont'' : ContinuousOn (fun t : ℝ => φ (γ t)) (Set.Icc T T'') := hcont.mono hsub
    have hmem : y ∈ Set.Icc (φ (γ T'')) (φ (γ T)) :=
      ⟨hyy.le, hy2.le⟩
    obtain ⟨t, htI, hty⟩ := intermediate_value_Icc' (by linarith : T ≤ T'') hcont'' hmem
    refine ⟨t, ?_, hty⟩
    rcases eq_or_lt_of_le htI.1 with h | h
    · exfalso; rw [← h] at hty; linarith [hy2]
    · exact h
  · intro s hssrc hys
    by_contra hcon
    rw [not_lt] at hcon
    rcases eq_or_lt_of_le hcon with h | h
    · exfalso; rw [← h] at hys; exact absurd hys.2 (by simp)
    · -- s < T
      have hy1 : (0:ℝ) < φ (γ s) := hys.1
      have hy2 : φ (γ s) < φ (γ T) := hys.2
      have hev : ∀ᶠ t in Filter.atTop, φ (γ t) < φ (γ s) := by
        have h1 : ∀ᶠ t in Filter.atTop, φ (γ t) ∈ Metric.ball (0:ℝ) (φ (γ s)) :=
          htend.eventually (Metric.ball_mem_nhds (0:ℝ) hy1)
        filter_upwards [h1] with t ht
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
        exact lt_of_le_of_lt (le_abs_self _) ht
      obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
      set T'' : ℝ := max T₀ (T + 1) with hT''def
      have hT₀T'' : T₀ ≤ T'' := le_max_left _ _
      have hTT'' : T + 1 ≤ T'' := le_max_right _ _
      have hyy : φ (γ T'') < φ (γ s) := hT₀ T'' hT₀T''
      have hsub : Set.Icc T T'' ⊆ Set.Ici T := fun x hx => hx.1
      have hcont'' : ContinuousOn (fun t : ℝ => φ (γ t)) (Set.Icc T T'') := hcont.mono hsub
      have hmem : φ (γ s) ∈ Set.Icc (φ (γ T'')) (φ (γ T)) :=
        ⟨hyy.le, hy2.le⟩
      obtain ⟨t, htI, hty⟩ := intermediate_value_Icc' (by linarith : T ≤ T'') hcont'' hmem
      have htT : T < t := by
        rcases eq_or_lt_of_le htI.1 with h' | h'
        · exfalso; rw [← h'] at hty; linarith [hy2]
        · exact h'
      have : γ t = γ s := φ.toPartialEquiv.injOn (hT t htT.le).1 hssrc hty
      have hts : t = s := hinj this
      linarith

/-- **Extending an open arc past a free endpoint.** -/
theorem extend_arc {C : Type*} [TopologicalSpace C] [ChartedSpace Work.OneDim.E1 C]
    [IsManifold Work.OneDim.I1 Work.OneDim.sm C]
    {γ : ℝ → C} (hinj : Function.Injective γ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1 Work.OneDim.sm γ)
    {q : C} (hq : q ∉ Set.range γ)
    (hconv : Filter.Tendsto γ Filter.atTop (nhds q))
    (φ : PartialDiffeomorph Work.OneDim.I1 (modelWithCornersSelf ℝ ℝ) C ℝ Work.OneDim.sm)
    (hqsrc : q ∈ φ.source) (hq0 : φ q = 0) {δ : ℝ} (hδ : 0 < δ)
    (htgt : Set.Ioo (-δ) δ ⊆ φ.target)
    (hpos : ∃ T : ℝ, ∀ t ≥ T, γ t ∈ φ.source ∧ 0 < φ (γ t) ∧ φ (γ t) < δ)
    (hfree : ∀ t : ℝ, γ t ∈ φ.source → φ (γ t) ∈ Set.Ioo (-δ) δ → 0 ≤ φ (γ t)) :
    ∃ A' : Set C, Work.OneDim.IsOpenArc A' ∧ Set.range γ ⊆ A' ∧ ¬ (A' ⊆ Set.range γ) := by
  obtain ⟨t₁, c₁, hc₁pos, hc₁lt, hc₁eq, hmem, hanti, hbtend, hsurj, hF3⟩ :=
    tail_data hinj hld hconv φ hqsrc hq0 hpos
  set ε : ℝ := c₁ / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεleδ : ε ≤ δ := by rw [hεdef]; linarith
  obtain ⟨H, hHcont, hHmono, hHid, hH0, hHderiv, hHimage⟩ :=
    exists_smooth_H c₁ ε hc₁pos hεpos
  have hHld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      Work.OneDim.sm H := ift_real hHcont hHderiv
  set G : ℝ → ℝ := fun t => H (φ (γ t)) with hGdef
  set γ' : ℝ → C := fun t => if t ≤ t₁ then γ t else φ.symm (G t) with hγ'def
  have hγsrc₁ : γ t₁ ∈ φ.source := (hmem t₁ le_rfl).1
  -- continuity of `φ ∘ γ` at `t₁`
  have hbcont_at : ContinuousAt (fun t : ℝ => φ (γ t)) t₁ := by
    have hcomp : ContMDiffAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        Work.OneDim.sm (fun t : ℝ => φ (γ t)) t₁ :=
      (φ.contMDiffOn_toFun.contMDiffAt (φ.open_source.mem_nhds hγsrc₁)).comp t₁
        (hld.contMDiff.contMDiffAt)
    exact hcomp.continuousAt
  -- a right-neighbourhood of `t₁` on which `φ (γ t) ≥ c₁/4`
  have h4c : c₁ / 4 < φ (γ t₁) := by rw [hc₁eq]; linarith
  have hnhds : (fun t : ℝ => φ (γ t)) ⁻¹' (Set.Ioi (c₁/4)) ∈ 𝓝 t₁ :=
    hbcont_at.preimage_mem_nhds (isOpen_Ioi.mem_nhds h4c)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have ht₁t₂ : t₁ < t₁ + r := by linarith
  have ht₂' : ∀ t : ℝ, t₁ < t → t < t₁ + r → c₁ / 4 < φ (γ t) := by
    intro t ht1 ht2
    exact hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩)
  -- `φ (γ t) ∈ (0,c₁)` for `t₁ < t`
  have hIoo : ∀ u : ℝ, t₁ < u → φ (γ u) ∈ Set.Ioo (0:ℝ) c₁ := by
    intro u hu
    refine ⟨(hmem u hu.le).2.1, ?_⟩
    have h : φ (γ u) < φ (γ t₁) := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hu.le) hu
    rw [hc₁eq] at h
    exact h
  have hGmem : ∀ u : ℝ, t₁ < u → G u ∈ Set.Ioo (-ε) c₁ := by
    intro u hu
    rw [hGdef]
    exact hHimage ▸ (⟨φ (γ u), hIoo u hu, rfl⟩ : H (φ (γ u)) ∈ H '' Set.Ioo 0 c₁)
  have hsubδ : Set.Ioo (-ε) c₁ ⊆ φ.target := by
    intro z hz
    exact htgt ⟨by linarith [hz.1, hεleδ], by linarith [hz.2, hc₁lt]⟩
  have hGtgt : ∀ u : ℝ, t₁ < u → G u ∈ φ.target := fun u hu => hsubδ (hGmem u hu)
  -- `γ' = γ` on `(-∞, t₁+r)`
  have hγ'eq_fun : ∀ t : ℝ, t < t₁ + r → γ' t = γ t := by
    intro t ht
    by_cases hle : t ≤ t₁
    · simp only [hγ'def, if_pos hle]
    · rw [not_le] at hle
      have hGt : G t = φ (γ t) := by
        rw [hGdef]
        exact hHid (φ (γ t)) (le_of_lt (ht₂' t hle ht))
      simp only [hγ'def, if_neg (not_le.mpr hle)]
      rw [hGt]
      exact φ.toPartialEquiv.left_inv (hmem t hle.le).1
  -- local diffeomorphism
  have hγ'ld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1 Work.OneDim.sm γ' := by
    intro t
    rcases lt_trichotomy t t₁ with h | h | h
    · -- t < t₁
      have hEq : γ =ᶠ[𝓝 t] γ' := by
        refine eventuallyEq_of_mem (isOpen_Iio.mem_nhds h) ?_
        intro s hs
        have hs1 : s < t₁ := hs
        exact (hγ'eq_fun s (by linarith)).symm
      exact local_diffeo_congr hEq (hld t)
    · -- t = t₁
      have hEq : γ =ᶠ[𝓝 t] γ' := by
        rw [h]
        refine eventuallyEq_of_mem (isOpen_Iio.mem_nhds ht₁t₂) ?_
        intro s hs
        exact (hγ'eq_fun s hs).symm
      refine local_diffeo_congr hEq ?_
      rw [h]
      exact hld t₁
    · -- t > t₁
      have ht : t₁ < t := h
      have hγt : γ t ∈ φ.source := (hmem t ht.le).1
      have hbld : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
          Work.OneDim.sm (fun s : ℝ => φ (γ s)) t :=
        IsLocalDiffeomorphAt.comp (K := modelWithCornersSelf ℝ ℝ) (P := ℝ)
          (hld t) (PartialDiffeomorph.isLocalDiffeomorphAt I1 (modelWithCornersSelf ℝ ℝ) sm φ hγt)
      have hGld : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
          Work.OneDim.sm G t :=
        IsLocalDiffeomorphAt.comp (K := modelWithCornersSelf ℝ ℝ) (P := ℝ) hbld (hHld (φ (γ t)))
      have hφsymm : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1 Work.OneDim.sm
          (↑φ.symm) (G t) :=
        PartialDiffeomorph.isLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) I1 sm φ.symm (hGtgt t ht)
      have hΦld : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1
          Work.OneDim.sm (fun s : ℝ => φ.symm (G s)) t :=
        IsLocalDiffeomorphAt.comp (K := Work.OneDim.I1) (P := C) hGld hφsymm
      have hEq : (fun s : ℝ => φ.symm (G s)) =ᶠ[𝓝 t] γ' := by
        refine eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht) ?_
        intro s hs
        have hs1 : t₁ < s := hs
        simp only [hγ'def, if_neg (not_le.mpr hs1)]
      exact local_diffeo_congr hEq hΦld
  -- injectivity
  have hγ'inj : Function.Injective γ' := by
    intro s t hst
    simp only [hγ'def] at hst
    by_cases hs : s ≤ t₁
    · by_cases ht : t ≤ t₁
      · rw [if_pos hs, if_pos ht] at hst
        exact hinj hst
      · rw [if_pos hs, if_neg ht] at hst
        exfalso
        have ht' : t₁ < t := not_le.mp ht
        have hssrc : γ s ∈ φ.source := by
          rw [hst]; exact (φ.symm).toPartialEquiv.map_source (hGtgt t ht')
        have hphieq : φ (γ s) = G t := by
          rw [hst]; exact φ.toPartialEquiv.right_inv (hGtgt t ht')
        have hGδ : G t ∈ Set.Ioo (-δ) δ :=
          ⟨by linarith [(hGmem t ht').1, hεleδ], by linarith [(hGmem t ht').2, hc₁lt]⟩
        have hfree' : 0 ≤ G t := by
          rw [← hphieq]; exact hfree s hssrc (by rw [hphieq]; exact hGδ)
        rcases lt_or_eq_of_le hfree' with hpos | hzero
        · have : t₁ < s := hF3 s hssrc (by rw [hphieq]; exact ⟨hpos, (hGmem t ht').2⟩)
          exact absurd hs (not_le.mpr this)
        · have hγs : γ s = q := by
            rw [hst, ← hzero]
            simpa [hq0] using φ.toPartialEquiv.left_inv hqsrc
          exact absurd ⟨s, hγs⟩ hq
    · by_cases ht : t ≤ t₁
      · rw [if_neg hs, if_pos ht] at hst
        exfalso
        have hs' : t₁ < s := not_le.mp hs
        have htsrc : γ t ∈ φ.source := by
          rw [← hst]; exact (φ.symm).toPartialEquiv.map_source (hGtgt s hs')
        have hphieq : φ (γ t) = G s := by
          rw [← hst]; exact φ.toPartialEquiv.right_inv (hGtgt s hs')
        have hGδ : G s ∈ Set.Ioo (-δ) δ :=
          ⟨by linarith [(hGmem s hs').1, hεleδ], by linarith [(hGmem s hs').2, hc₁lt]⟩
        have hfree' : 0 ≤ G s := by
          rw [← hphieq]; exact hfree t htsrc (by rw [hphieq]; exact hGδ)
        rcases lt_or_eq_of_le hfree' with hpos | hzero
        · have : t₁ < t := hF3 t htsrc (by rw [hphieq]; exact ⟨hpos, (hGmem s hs').2⟩)
          exact absurd ht (not_le.mpr this)
        · have hγt : γ t = q := by
            rw [← hst, ← hzero]
            simpa [hq0] using φ.toPartialEquiv.left_inv hqsrc
          exact absurd ⟨t, hγt⟩ hq
      · rw [if_neg hs, if_neg ht] at hst
        have hs' : t₁ < s := not_le.mp hs
        have ht' : t₁ < t := not_le.mp ht
        have hGsGt : G s = G t :=
          (φ.symm).toPartialEquiv.injOn (hGtgt s hs') (hGtgt t ht') hst
        have hH : H (φ (γ s)) = H (φ (γ t)) := by simpa only [hGdef] using hGsGt
        have hb : φ (γ s) = φ (γ t) := hHmono.injective hH
        exact hinj (φ.toPartialEquiv.injOn (hmem s hs'.le).1 (hmem t ht'.le).1 hb)
  have hsub : Set.range γ ⊆ Set.range γ' := by
    rintro x ⟨s, rfl⟩
    by_cases hs : s ≤ t₁
    · exact ⟨s, by simp only [hγ'def, if_pos hs]⟩
    · have hs' : t₁ < s := not_le.mp hs
      have hy : φ (γ s) ∈ H '' Set.Ioo 0 c₁ := by
        rw [hHimage]
        exact ⟨by linarith [hεpos, (hIoo s hs').1], (hIoo s hs').2⟩
      obtain ⟨y, hyI, hHy⟩ := hy
      obtain ⟨u, hu, hbu⟩ := hsurj y hyI
      refine ⟨u, ?_⟩
      simp only [hγ'def, if_neg (not_le.mpr hu)]
      have hGu : G u = φ (γ s) := by simp only [hGdef]; rw [hbu, hHy]
      rw [hGu]
      exact φ.toPartialEquiv.left_inv (hmem s hs'.le).1
  have hnotsub : ¬ (Set.range γ' ⊆ Set.range γ) := by
    intro hcontra
    have h0mem : (0:ℝ) ∈ H '' Set.Ioo 0 c₁ := by
      rw [hHimage]; exact ⟨by linarith [hεpos], hc₁pos⟩
    obtain ⟨y₀, hy₀, hHy₀⟩ := h0mem
    have hev : ∀ᶠ t in Filter.atTop, φ (γ t) < y₀ := by
      have h1 : ∀ᶠ t in Filter.atTop, φ (γ t) ∈ Metric.ball (0:ℝ) y₀ :=
        hbtend.eventually (Metric.ball_mem_nhds (0:ℝ) hy₀.1)
      filter_upwards [h1] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact lt_of_le_of_lt (le_abs_self _) ht
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
    set u : ℝ := max T₀ (t₁ + 1) with hudef
    have huT₀ : T₀ ≤ u := le_max_left _ _
    have hut₁ : t₁ + 1 ≤ u := le_max_right _ _
    have hut : t₁ < u := by linarith
    have hbu : φ (γ u) < y₀ := hT₀ u huT₀
    have hGu : G u ∈ Set.Ioo (-ε) c₁ := hGmem u hut
    have hGneg : G u < 0 := by
      rw [hGdef]
      have h := hHmono hbu
      rwa [hHy₀] at h
    obtain ⟨s, hs⟩ := hcontra ⟨u, rfl⟩
    have hsmem : γ s ∈ φ.source := by
      rw [hs]; simp only [hγ'def, if_neg (not_le.mpr hut)]
      exact (φ.symm).toPartialEquiv.map_source (hGtgt u hut)
    have hphieq : φ (γ s) = G u := by
      rw [hs]; simp only [hγ'def, if_neg (not_le.mpr hut)]
      exact φ.toPartialEquiv.right_inv (hGtgt u hut)
    have hGδ : G u ∈ Set.Ioo (-δ) δ :=
      ⟨by linarith [hGu.1, hεleδ], by linarith [hGu.2, hc₁lt]⟩
    have hfree' : 0 ≤ φ (γ s) := hfree s hsmem (by rw [hphieq]; exact hGδ)
    rw [hphieq] at hfree'
    linarith
  exact ⟨Set.range γ', ⟨γ', hγ'inj, hγ'ld, rfl⟩, hsub, hnotsub⟩

end Work.OneDim
