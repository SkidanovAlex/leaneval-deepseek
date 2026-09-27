import Mathlib
import Submission.Work.EQ.H0_path_limit
import Submission.Work.EQ.H0_path_limit_Iio
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.Refl.path_lift_defs

namespace Work.EQ.Refl

open Filter _root_.Topology Set Metric

noncomputable section

/-- **Openness of the set of lift times.**  If `γ` lifts on `[0,s]` and `s < 1`, it lifts on
`[0,s+ε]` for some `ε > 0`, by extending with a local section of `ψ₁` at the endpoint. -/
theorem hasLift_step_up {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {p : Work.EQ.ChainData}
    {γ : ℝ → ℂ} (hcont : ContinuousOn γ (Set.Icc 0 1))
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) (hs1 : s < 1) (hL : HasLift a h p γ s) :
    ∃ ε : ℝ, 0 < ε ∧ s + ε ∈ Set.Icc 0 1 ∧ HasLift a h p γ (s + ε) := by
  obtain ⟨G, hGcont, hG0, hGmem⟩ := hL
  have hss : s ∈ Set.Icc 0 s := ⟨hs.1, le_rfl⟩
  have hq : G s ∈ H0 a h := (hGmem s hss).1
  have hqpsi : (G s).2.1 = γ s := (hGmem s hss).2
  obtain ⟨ρ, hρ, f, hf0, hfmem, hfan, hfan2, _⟩ := (H0_structure ha0 ha1 hh).2.1 (G s) hq
  have hfcont : ContinuousOn f (Metric.ball (G s).2.1 ρ) := by
    refine ContinuousOn.prodMk (continuousOn_pi' fun n => (hfan n).continuousOn) ?_
    refine ContinuousOn.prodMk ?_ hfan2.continuousOn
    exact continuousOn_id.congr (fun u hu => (hfmem u hu).2)
  have hballmem : γ ⁻¹' Metric.ball (G s).2.1 ρ ∈ 𝓝[Set.Icc 0 1] s :=
    (hcont s hs) (Metric.isOpen_ball.mem_nhds (by rw [hqpsi]; exact Metric.mem_ball_self hρ))
  rw [mem_nhdsWithin_iff] at hballmem
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := hballmem
  set ε : ℝ := min δ₁ (1 - s) / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact div_pos (lt_min hδ₁ (by linarith)) (by norm_num)
  have hεlt : ε < δ₁ := by
    rw [hεdef]
    have : min δ₁ (1 - s) ≤ δ₁ := min_le_left _ _
    linarith
  have hεle2 : ε ≤ (1 - s) / 2 := by
    rw [hεdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hsε1 : s + ε ≤ 1 := by linarith
  have hsε0 : 0 ≤ s + ε := by linarith [hs.1, hεpos]
  refine ⟨ε, hεpos, ⟨hsε0, hsε1⟩, ?_⟩
  set G' : ℝ → ChainData := fun t => if t ≤ s then G t else f (γ t) with hG'def
  have hG'def' : ∀ t : ℝ, G' t = if t ≤ s then G t else f (γ t) := fun t => by rw [hG'def]
  have hG'G : ∀ t ∈ Set.Icc 0 s, G' t = G t := by
    intro t ht; rw [hG'def' t, if_pos ht.2]
  have hγball : ∀ t ∈ Set.Icc s (s + ε), γ t ∈ Metric.ball (G s).2.1 ρ := by
    intro t ht
    apply hδ₁sub
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
      linarith [ht.2]
    · exact ⟨le_trans hs.1 ht.1, le_trans ht.2 hsε1⟩
  have hG'fγ : ∀ t ∈ Set.Icc s (s + ε), G' t = f (γ t) := by
    intro t ht
    rw [hG'def' t]
    by_cases hts : t ≤ s
    · rw [if_pos hts]
      have hts' : t = s := le_antisymm hts ht.1
      rw [hts', ← hf0, hqpsi]
    · rw [if_neg hts]
  have hcont1 : ContinuousOn G' (Set.Icc 0 s) :=
    hGcont.congr (fun t ht => (hG'G t ht))
  have hcompon : ContinuousOn (f ∘ γ) (Set.Icc s (s + ε)) :=
    hfcont.comp (hcont.mono (fun t ht => ⟨le_trans hs.1 ht.1, le_trans ht.2 hsε1⟩)) hγball
  have hcont2 : ContinuousOn G' (Set.Icc s (s + ε)) :=
    hcompon.congr (fun t ht => (hG'fγ t ht))
  have hcontall : ContinuousOn G' (Set.Icc 0 (s + ε)) := by
    have h := hcont1.union_of_isClosed hcont2 isClosed_Icc isClosed_Icc
    rwa [Set.Icc_union_Icc_eq_Icc hs.1 (by linarith [hεpos])] at h
  refine ⟨G', hcontall, ?_, ?_⟩
  · rw [hG'G 0 ⟨le_rfl, hs.1⟩]; exact hG0
  · intro t ht
    rw [hG'def' t]
    by_cases hts : t ≤ s
    · rw [if_pos hts]
      exact hGmem t ⟨ht.1, hts⟩
    · rw [if_neg hts]
      exact hfmem (γ t) (hγball t ⟨le_of_lt (lt_of_not_ge hts), ht.2⟩)

/-- **Closedness of the set of lift times.**  If `γ` lifts on `[0,s']` for every `s' < s`, then it
lifts on `[0,s]`: glue the lifts on `[0,s')` to a lift on `[0,s)`, and extend it to `s` by the
limit delivered by `H0_path_limit_Iio`. -/
theorem hasLift_step_close {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {p : Work.EQ.ChainData} (hp : p ∈ Work.EQ.H0 a h)
    {c : ℂ} (hval : ∀ x ∈ connectedComponentIn (Work.EQ.H0 a h) p, x.2.1 * x.2.2 = c)
    {γ : ℝ → ℂ} (hγ0 : γ 0 = p.2.1) (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ 0)
    (hgen : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ (e : ℂ → Work.EQ.ChainData) (k : ℕ),
      Work.EQ.IsPuncturedChart a h e (γ t) k →
        ∃ q ∈ Work.EQ.H0 a h,
          Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q))
    {s : ℝ} (hspos : 0 < s) (hsle : s ≤ 1)
    (hA : ∀ s' : ℝ, s' ∈ Set.Icc 0 1 → s' < s → HasLift a h p γ s') :
    HasLift a h p γ s := by
  have hlo := (H0_structure ha0 ha1 hh).1
  have hs_1 : s ∈ Set.Icc 0 1 := ⟨hspos.le, hsle⟩
  -- lifts on the half-intervals
  have hhalf_mem : ∀ t ∈ Set.Ico 0 s, (t + s) / 2 ∈ Set.Icc 0 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2, hsle]⟩
  have hhalf_lt : ∀ t ∈ Set.Ico 0 s, (t + s) / 2 < s := by
    intro t ht; linarith [ht.2]
  have hA2 : ∀ t ∈ Set.Ico 0 s, HasLift a h p γ ((t + s) / 2) :=
    fun t ht => hA _ (hhalf_mem t ht) (hhalf_lt t ht)
  -- the glued lift on [0,s)
  set Gf : ℝ → ChainData := fun t => if ht : t ∈ Set.Ico 0 s then (hA2 t ht).choose t else p
    with hGfdef
  have hGfdef' : ∀ t : ℝ, Gf t =
      if ht : t ∈ Set.Ico 0 s then (hA2 t ht).choose t else p := fun t => by rw [hGfdef]
  have hGf_mem : ∀ t ∈ Set.Ico 0 s, Gf t ∈ H0 a h ∧ (Gf t).2.1 = γ t := by
    intro t ht
    have h := (hA2 t ht).choose_spec
    rw [hGfdef' t, dif_pos ht]
    exact h.2.2 t ⟨ht.1, by linarith [ht.2]⟩
  have hGf0 : Gf 0 = p := by
    have h0Ico : (0 : ℝ) ∈ Set.Ico 0 s := ⟨le_rfl, hspos⟩
    rw [hGfdef' 0, dif_pos h0Ico]
    exact ((hA2 0 h0Ico).choose_spec).2.1
  have hGf_agree : ∀ t (ht : t ∈ Set.Ico 0 s),
      Set.EqOn Gf ((hA2 t ht).choose) (Set.Icc 0 ((t + s) / 2)) := by
    intro t ht u hu
    have huIco : u ∈ Set.Ico 0 s := ⟨hu.1, by linarith [hu.2, ht.2]⟩
    have hmin : min ((u + s) / 2) ((t + s) / 2) ∈ Set.Icc 0 1 :=
      ⟨le_min (by linarith [hu.1]) (by linarith [ht.1]),
        le_trans (min_le_right _ _) (by linarith [ht.2, hsle])⟩
    have huI : u ∈ Set.Icc 0 (min ((u + s) / 2) ((t + s) / 2)) :=
      ⟨hu.1, le_min (by linarith [huIco.2]) hu.2⟩
    have hm1 : min ((u + s) / 2) ((t + s) / 2) ≤ (u + s) / 2 := min_le_left _ _
    have hm2 : min ((u + s) / 2) ((t + s) / 2) ≤ (t + s) / 2 := min_le_right _ _
    have hLu := H0_lift_unique (a := a) (h := h) (p := p) (γ := γ) hlo hmin
      (((hA2 u huIco).choose_spec).1.mono (Set.Icc_subset_Icc_right hm1))
      (fun v hv => ((hA2 u huIco).choose_spec).2.2 v (Set.Icc_subset_Icc_right hm1 hv))
      (((hA2 u huIco).choose_spec).2.1)
      (((hA2 t ht).choose_spec).1.mono (Set.Icc_subset_Icc_right hm2))
      (fun v hv => ((hA2 t ht).choose_spec).2.2 v (Set.Icc_subset_Icc_right hm2 hv))
      (((hA2 t ht).choose_spec).2.1)
    rw [hGfdef' u, dif_pos huIco]
    exact hLu u huI
  -- component membership
  have hcomp_mem : ∀ t ∈ Set.Ico 0 s, Gf t ∈ connectedComponentIn (H0 a h) p := by
    intro t ht
    have hLc := ((hA2 t ht).choose_spec).1
    have hL0 := ((hA2 t ht).choose_spec).2.1
    have hLmem := ((hA2 t ht).choose_spec).2.2
    have hpre : IsPreconnected (((hA2 t ht).choose) '' Set.Icc 0 ((t + s) / 2)) :=
      isPreconnected_Icc.image _ hLc
    have hp_in : p ∈ ((hA2 t ht).choose) '' Set.Icc 0 ((t + s) / 2) :=
      ⟨0, ⟨le_rfl, by linarith [ht.1, hspos]⟩, hL0⟩
    have hsub : ((hA2 t ht).choose) '' Set.Icc 0 ((t + s) / 2) ⊆ H0 a h := by
      rintro _ ⟨v, hv, rfl⟩
      exact (hLmem v hv).1
    have hcc := hpre.subset_connectedComponentIn hp_in hsub
    have htI : t ∈ Set.Icc 0 ((t + s) / 2) := ⟨ht.1, by linarith [ht.2]⟩
    rw [hGf_agree t ht htI]
    exact hcc ⟨t, htI, rfl⟩
  -- continuity away from 0 and at 0
  have hGf_contIoo : ∀ t ∈ Set.Ioo 0 s, ContinuousAt Gf t := by
    intro t ht
    have htIco : t ∈ Set.Ico 0 s := ⟨ht.1.le, ht.2⟩
    have htmid : t < (t + s) / 2 := by linarith [ht.2]
    have hLca : ContinuousAt ((hA2 t htIco).choose) t :=
      (((hA2 t htIco).choose_spec).1).continuousAt (Icc_mem_nhds ht.1 htmid)
    have hev : Gf =ᶠ[𝓝 t] ((hA2 t htIco).choose) :=
      Filter.eventually_of_mem (Ioo_mem_nhds ht.1 htmid)
        (fun u hu => hGf_agree t htIco ⟨hu.1.le, hu.2.le⟩)
    exact hLca.congr hev.symm
  have hGf_cont0 : ContinuousWithinAt Gf (Set.Ici 0) 0 := by
    have h0Ico : (0 : ℝ) ∈ Set.Ico 0 s := ⟨le_rfl, hspos⟩
    have hLc := ((hA2 0 h0Ico).choose_spec).1
    have hIv : Set.Icc 0 ((0 + s) / 2) ∈ 𝓝[Set.Ici 0] (0 : ℝ) := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Iio ((0 + s) / 2), Iio_mem_nhds (by linarith), ?_⟩
      intro u hu
      exact ⟨hu.2, le_of_lt hu.1⟩
    have hLcw : ContinuousWithinAt ((hA2 0 h0Ico).choose) (Set.Icc 0 ((0 + s) / 2)) 0 :=
      hLc 0 ⟨le_rfl, by linarith⟩
    have hLcw' : ContinuousWithinAt ((hA2 0 h0Ico).choose) (Set.Ici 0) 0 := by
      refine hLcw.mono_left ?_
      rw [nhdsWithin_le_iff]
      exact hIv
    have hev : Gf =ᶠ[𝓝[Set.Ici 0] 0] ((hA2 0 h0Ico).choose) :=
      Filter.eventually_of_mem hIv (fun u hu => hGf_agree 0 h0Ico hu)
    have hgf0 : Gf 0 = ((hA2 0 h0Ico).choose) 0 := by
      rw [hGfdef' 0, dif_pos h0Ico]
    exact hLcw'.congr_of_eventuallyEq hev hgf0
  -- the reparametrised path
  set η : ℝ → ChainData := fun t => if t < 1 then Gf (s * max t (1 / 2)) else p with hηdef
  have hηdef' : ∀ t : ℝ, η t = if t < 1 then Gf (s * max t (1 / 2)) else p :=
    fun t => by rw [hηdef]
  have harg_mem : ∀ t ∈ Set.Iio (1 : ℝ), s * max t (1 / 2) ∈ Set.Ico 0 s := by
    intro t ht
    have hm : max t (1 / 2) < 1 := max_lt ht (by norm_num)
    refine ⟨mul_nonneg hspos.le (le_trans (by norm_num) (le_max_right t (1 / 2))), ?_⟩
    simpa using mul_lt_mul_of_pos_left hm hspos
  have harg_Ioo : ∀ t ∈ Set.Iio (1 : ℝ), s * max t (1 / 2) ∈ Set.Ioo 0 s := by
    intro t ht
    have hm : max t (1 / 2) < 1 := max_lt ht (by norm_num)
    refine ⟨mul_pos hspos (lt_max_of_lt_right (by norm_num)), ?_⟩
    simpa using mul_lt_mul_of_pos_left hm hspos
  have hη_mem : ∀ t ∈ Set.Iio (1 : ℝ), η t ∈ H0 a h ∧ (η t).2.1 = γ (s * max t (1 / 2)) := by
    intro t ht
    rw [hηdef' t, if_pos (show t < 1 from ht)]
    exact hGf_mem _ (harg_mem t ht)
  have hηcont : ContinuousOn η (Set.Iio 1) := by
    intro t ht
    have hin : ContinuousAt (fun r : ℝ => s * max r (1 / 2)) t :=
      continuous_const.continuousAt.mul (continuous_id.max continuous_const).continuousAt
    have hg : ContinuousAt Gf (s * max t (1 / 2)) := hGf_contIoo _ (harg_Ioo t ht)
    have hcomp : ContinuousWithinAt (fun r : ℝ => Gf (s * max r (1 / 2))) (Set.Iio 1) t :=
      (ContinuousAt.comp (f := fun r : ℝ => s * max r (1 / 2)) (x := t) hg hin).continuousWithinAt
    have hev : η =ᶠ[𝓝[Set.Iio 1] t] (fun r : ℝ => Gf (s * max r (1 / 2))) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [hηdef' r, if_pos (show r < 1 from hr)]
    exact hcomp.congr_of_eventuallyEq hev (by rw [hηdef' t, if_pos (show t < 1 from ht)])
  -- the two limits
  have hcomp_maps : MapsTo (fun r : ℝ => s * max r (1 / 2)) (Set.Iio 1) (Set.Icc 0 1) := by
    intro t ht
    refine ⟨mul_nonneg hspos.le (le_trans (by norm_num) (le_max_right t (1 / 2))), ?_⟩
    have hm : max t (1 / 2) < 1 := max_lt ht (by norm_num)
    nlinarith [hspos, hm, hsle]
  have hbaseγ : Tendsto (fun r : ℝ => γ (s * max r (1 / 2))) (𝓝[Set.Iio 1] 1) (𝓝 (γ s)) := by
    have hin : ContinuousWithinAt (fun r : ℝ => s * max r (1 / 2)) (Set.Iio 1) 1 :=
      ((continuous_const.mul (continuous_id.max continuous_const)).continuousAt).continuousWithinAt
    have hγcont' : ContinuousWithinAt γ (Set.Icc 0 1) (s * max 1 (1 / 2)) := by
      rw [show s * max 1 (1 / 2) = s by rw [max_eq_left (by norm_num)]; ring]
      exact hcont.continuousWithinAt hs_1
    have hcomp : ContinuousWithinAt (fun r : ℝ => γ (s * max r (1 / 2))) (Set.Iio 1) 1 :=
      ContinuousWithinAt.comp (f := fun r : ℝ => s * max r (1 / 2)) (x := 1) hγcont' hin hcomp_maps
    have := hcomp.tendsto
    rwa [show s * max 1 (1 / 2) = s by rw [max_eq_left (by norm_num)]; ring] at this
  have hψ1 : Tendsto (fun r => (η r).2.1) (𝓝[Set.Iio 1] 1) (𝓝 (γ s)) :=
    hbaseγ.congr' (Filter.eventually_of_mem self_mem_nhdsWithin
      (fun r hr => ((hη_mem r hr).2).symm))
  have hψ2eq : ∀ r ∈ Set.Iio (1 : ℝ), (η r).2.2 = c / γ (s * max r (1 / 2)) := by
    intro r hr
    have harg := harg_mem r hr
    have hηr : η r = Gf (s * max r (1 / 2)) := by rw [hηdef' r, if_pos (show r < 1 from hr)]
    have hv := hval _ (hcomp_mem _ harg)
    have hpsi : (Gf (s * max r (1 / 2))).2.1 = γ (s * max r (1 / 2)) := (hGf_mem _ harg).2
    have hne' : γ (s * max r (1 / 2)) ≠ 0 :=
      hne _ ⟨harg.1, le_trans harg.2.le hsle⟩
    rw [hpsi] at hv
    rw [hηr, eq_div_iff hne', mul_comm]
    exact hv
  have hψ2 : Tendsto (fun r => (η r).2.2) (𝓝[Set.Iio 1] 1) (𝓝 (c / γ s)) := by
    have hγs : γ s ≠ 0 := hne s ⟨hspos.le, hsle⟩
    have hbase : Tendsto (fun r : ℝ => c / γ (s * max r (1 / 2))) (𝓝[Set.Iio 1] 1)
        (𝓝 (c / γ s)) := by
      have := hbaseγ
      exact tendsto_const_nhds.div this hγs
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hψ2eq r hr).symm
  have hγs : γ s ≠ 0 := hne s ⟨hspos.le, hsle⟩
  have hc : c ≠ 0 := by
    have hpcc : p ∈ connectedComponentIn (H0 a h) p := mem_connectedComponentIn hp
    have hv := hval p hpcc
    have hpc : IsChain a h p := isChain_of_mem_H0 hp
    rw [← hv]
    exact mul_ne_zero hpc.2.1 hpc.2.2.1
  have hv_ne : c / γ s ≠ 0 := div_ne_zero hc hγs
  -- apply the path-limit theorem
  have hlim : ∃ q ∈ H0 a h, Tendsto η (𝓝[Set.Iio 1] 1) (𝓝 q) := by
    rcases H0_path_limit_Iio ha0 ha1 hh (fun t ht => (hη_mem t ht).1) hηcont hγs hv_ne hψ1 hψ2
      with ⟨q, hq, hqlim⟩ | ⟨e, k, hchart, hρ⟩
    · exact ⟨q, hq, hqlim⟩
    · obtain ⟨q, hq, hqlim⟩ := hgen s ⟨hspos.le, hsle⟩ e k hchart
      refine ⟨q, hq, ?_⟩
      refine tendsto_iff_forall_eventually_mem.mpr (fun V hV => ?_)
      obtain ⟨ρ, hρpos, hρsub⟩ :=
        mem_nhdsWithin_iff.mp (Filter.tendsto_def.mp hqlim V hV)
      filter_upwards [hρ ρ hρpos] with u hu
      obtain ⟨ζ, hζ, hζeq⟩ := hu
      rw [← hζeq]
      exact hρsub ⟨hζ.1, hζ.2⟩
  obtain ⟨q, hq, hqlim⟩ := hlim
  have hqpsi : q.2.1 = γ s := by
    have h1 : Tendsto (fun r => (η r).2.1) (𝓝[Set.Iio 1] 1) (𝓝 q.2.1) :=
      ((continuous_fst.comp continuous_snd).continuousAt.tendsto).comp hqlim
    exact tendsto_nhds_unique h1 hψ1
  -- the extension
  set Gs : ℝ → ChainData := fun t => if t < s then Gf t else q with hGsdef
  have hGsdef' : ∀ t : ℝ, Gs t = if t < s then Gf t else q := fun t => by rw [hGsdef]
  have hGf_tendsto : Tendsto Gf (𝓝[Set.Iio s] s) (𝓝 q) := by
    have hφ : Tendsto (fun t : ℝ => t / s) (𝓝[Set.Iio s] s) (𝓝[Set.Iio 1] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun t : ℝ => t / s) s := continuousAt_id.div_const s
        have hcc := hc.tendsto
        rw [show s / s = 1 by field_simp] at hcc
        exact hcc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact (div_lt_one hspos).mpr ht
    have hcomp := hqlim.comp hφ
    refine hcomp.congr' ?_
    have hIoi : ∀ᶠ t in 𝓝[Set.Iio s] s, s / 2 < t :=
      Filter.eventually_of_mem
        (nhdsWithin_le_nhds (Ioi_mem_nhds (show s / 2 < s by linarith)))
        (fun _ hx => hx)
    filter_upwards [self_mem_nhdsWithin, hIoi] with t ht hgt
    show η (t / s) = Gf t
    rw [hηdef' (t / s), if_pos (show t / s < 1 from (div_lt_one hspos).mpr ht),
      max_eq_left (by rw [le_div_iff₀ hspos]; linarith)]
    congr 1
    rw [mul_div_cancel₀ t hspos.ne']
  have hGs_cont_s : ContinuousAt Gs s := by
    rw [continuousAt_iff_continuous_left'_right']
    refine ⟨?_, ?_⟩
    · have : Tendsto Gs (𝓝[Set.Iio s] s) (𝓝 (Gs s)) := by
        rw [hGsdef' s, if_neg (lt_irrefl s)]
        exact hGf_tendsto.congr' (Filter.eventually_of_mem self_mem_nhdsWithin
          (fun t ht => by rw [hGsdef' t, if_pos (show t < s from ht)]))
      exact this
    · refine (continuousWithinAt_const (b := q)).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hGsdef' t, if_neg (show ¬ t < s from not_lt.mpr ht.le)]
      · rw [hGsdef' s, if_neg (lt_irrefl s)]
  have hGs_contOn : ContinuousOn Gs (Set.Icc 0 s) := by
    intro t ht
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · exact absurd ht.1 (not_le.mpr hlt)
    · subst heq
      have h1 : ContinuousWithinAt Gf (Set.Icc 0 s) 0 := hGf_cont0.mono (fun x hx => hx.1)
      have hev : Gs =ᶠ[𝓝[Set.Icc 0 s] 0] Gf := by
        filter_upwards [self_mem_nhdsWithin,
          (eventually_ne_nhds (show (0 : ℝ) ≠ s from ne_of_lt hspos)).filter_mono nhdsWithin_le_nhds]
          with x hx hxne
        rw [hGsdef' x, if_pos (show x < s from lt_of_le_of_ne hx.2 hxne)]
      exact h1.congr_of_eventuallyEq hev (by rw [hGsdef' 0, if_pos (show (0:ℝ) < s from hspos)])
    · rcases lt_trichotomy t s with hlt2 | heq2 | hgt2
      · have hc : ContinuousAt Gs t := by
          have hGft : ContinuousAt Gf t := hGf_contIoo t ⟨hgt, hlt2⟩
          have hev : Gf =ᶠ[𝓝 t] Gs :=
            Filter.eventually_of_mem (Ioo_mem_nhds hgt hlt2)
              (fun u hu => by rw [hGsdef' u, if_pos (show u < s from hu.2)])
          exact hGft.congr hev
        exact hc.continuousWithinAt
      · subst heq2
        exact hGs_cont_s.continuousWithinAt
      · exact absurd ht.2 (not_le.mpr hgt2)
  refine ⟨Gs, hGs_contOn, ?_, ?_⟩
  · rw [hGsdef' 0, if_pos (show (0:ℝ) < s from hspos)]; exact hGf0
  · intro t ht
    rw [hGsdef' t]
    by_cases hts : t < s
    · rw [if_pos hts]
      exact hGf_mem t ⟨ht.1, hts⟩
    · rw [if_neg hts]
      have hts' : t = s := le_antisymm ht.2 (le_of_not_gt hts)
      refine ⟨hq, ?_⟩
      rw [hts']
      exact hqpsi

/-- **Path lifting into a component of `⁰H` away from the punctures.**  Let `p ∈ H0 a h` lie in a
component on which the invariant parameter `ψ = ψ₁ψ₂` is the constant `c`, and let `γ : ℝ → ℂ*` be
continuous on `[0,1]` with `γ 0 = ψ₁ p`.  Suppose that no point `γ t` is the `ψ₁`-value of a
*genuine* punctured chart of `H0` (a chart `e` with `IsPuncturedChart a h e (γ t) k` which has
**no** limit in `H0 a h` at `ζ = 0`).  Then `γ` lifts to a continuous path in `H0` starting at `p`. -/
theorem path_lift_component {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {p : Work.EQ.ChainData} (hp : p ∈ Work.EQ.H0 a h)
    {c : ℂ} (hval : ∀ x ∈ connectedComponentIn (Work.EQ.H0 a h) p, x.2.1 * x.2.2 = c)
    {γ : ℝ → ℂ} (hγ0 : γ 0 = p.2.1) (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ 0)
    (hgen : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ (e : ℂ → Work.EQ.ChainData) (k : ℕ),
      Work.EQ.IsPuncturedChart a h e (γ t) k →
        ∃ q ∈ Work.EQ.H0 a h,
          Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) :
    ∃ G : ℝ → Work.EQ.ChainData, ContinuousOn G (Set.Icc 0 1) ∧ G 0 = p ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, G t ∈ Work.EQ.H0 a h ∧ (G t).2.1 = γ t) := by
  let A : Set ℝ := {s | s ∈ Set.Icc 0 1 ∧ HasLift a h p γ s}
  have h0A : (0 : ℝ) ∈ A := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    refine ⟨fun _ => p, continuousOn_const, rfl, ?_⟩
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    rw [ht0]
    exact ⟨hp, hγ0.symm⟩
  have hdown : ∀ s ∈ A, ∀ s' ∈ Set.Icc 0 1, s' ≤ s → s' ∈ A :=
    fun s hs s' hs' hs's => ⟨hs', (hs.2).mono hs's⟩
  have hup : ∀ s ∈ A, s < 1 → ∃ ε : ℝ, 0 < ε ∧ s + ε ∈ A := by
    intro s hs hs1
    obtain ⟨ε, hε, hsε, hL⟩ := hasLift_step_up ha0 ha1 hh hcont hs.1 hs1 hs.2
    exact ⟨ε, hε, hsε, hL⟩
  have hclose : ∀ s ∈ Set.Icc 0 1, (∀ s' ∈ Set.Icc 0 1, s' < s → s' ∈ A) → s ∈ A := by
    intro s hs hlt
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · rw [← h0]; exact h0A
    · exact ⟨hs, hasLift_step_close ha0 ha1 hh hp hval hγ0 hcont hne hgen hpos hs.2
        (fun s' hs' hs'lt => (hlt s' hs' hs'lt).2)⟩
  have hbdd : BddAbove A := ⟨1, fun s hs => hs.1.2⟩
  have hneA : A.Nonempty := ⟨0, h0A⟩
  set sstar : ℝ := sSup A with hss
  have hsstar_ge : 0 ≤ sstar := le_csSup hbdd h0A
  have hsstar_le : sstar ≤ 1 := csSup_le hneA (fun s hs => hs.1.2)
  have hsstarA : sstar ∈ A := by
    refine hclose sstar ⟨hsstar_ge, hsstar_le⟩ ?_
    intro s' hs' hs'lt
    obtain ⟨b, hbA, hltb⟩ := (lt_csSup_iff hbdd hneA).mp hs'lt
    exact hdown b hbA s' hs' hltb.le
  have hsstar_eq : sstar = 1 := by
    by_contra hne1
    have hlt1 : sstar < 1 := lt_of_le_of_ne hsstar_le hne1
    obtain ⟨ε, hε, hsεA⟩ := hup sstar hsstarA hlt1
    have := le_csSup hbdd hsεA
    linarith
  have h1A : (1 : ℝ) ∈ A := hsstar_eq ▸ hsstarA
  obtain ⟨G, hGc, hG0, hGm⟩ := h1A.2
  exact ⟨G, hGc, hG0, hGm⟩

end

end Work.EQ.Refl
