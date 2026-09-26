import Mathlib
import Submission.Work.Drive.circleBandArc

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- The derivative of a periodic map is periodic. -/
private lemma periodic_deriv {f : ℝ → Space} {c : ℝ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  have hx : deriv (fun y : ℝ => f (y + c)) x = deriv f x := by
    rw [show (fun y : ℝ => f (y + c)) = f from funext h]
  rwa [deriv_comp_add_const f c x] at hx

/-- A C¹-small analytic `period`-periodic correction of a smooth knot is again a smooth knot: compactness of the period gives a positive minimal separation for parameters far apart on the circle, and the mean-value bound gives injectivity for nearby ones. -/
theorem smallCorrectionKnot {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      ContDiff ℝ ⊤ w → Function.Periodic w LeanEval.KnotTheory.Quadrisecant.period →
      (∀ t : ℝ, ‖w t‖ < ε ∧
        ‖LeanEval.KnotTheory.Quadrisecant.velocity w t‖ < ε) →
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot (fun t : ℝ => r t + w t) := by
  have hp : 0 < period := by unfold period; positivity
  have hrdiff : Differentiable ℝ r := hr.smooth.differentiable (by decide)
  have hrc : Continuous r := hr.smooth.continuous
  have hvc : Continuous (velocity r) := by
    show Continuous (deriv r)
    exact hr.smooth.continuous_deriv le_top
  -- minimal speed on the period
  obtain ⟨t₀, ht₀, hmin₀⟩ := isCompact_Icc.exists_isMinOn
    (⟨0, le_rfl, hp.le⟩ : (Set.Icc (0:ℝ) period).Nonempty) hvc.norm.continuousOn
  set m₀ : ℝ := ‖velocity r t₀‖ with hm₀def
  have hm₀pos : 0 < m₀ := by
    rw [hm₀def]; exact norm_pos_iff.mpr (hr.regular t₀)
  have hvper : Function.Periodic (velocity r) period := periodic_deriv hr.periodic
  have hm₀lower : ∀ t : ℝ, m₀ ≤ ‖velocity r t‖ := by
    intro t
    obtain ⟨y, hy, hty⟩ := hvper.exists_mem_Ico hp t 0
    have hy' : y ∈ Set.Icc (0:ℝ) period := Set.Ico_subset_Icc_self (by simpa using hy)
    calc m₀ = ‖velocity r t₀‖ := hm₀def
      _ ≤ ‖velocity r y‖ := hmin₀ hy'
      _ = ‖velocity r t‖ := by rw [hty]
  -- uniform continuity of the velocity on the double period
  have huc : UniformContinuousOn (velocity r) (Set.Icc (0:ℝ) (2*period)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hvc.continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff_le.mp huc (m₀/2) (by linarith)
  set α : ℝ := min δ (period/4) with hαdef
  have hαpos : 0 < α := by rw [hαdef]; exact lt_min hδpos (by linarith)
  have hαδ : α ≤ δ := by rw [hαdef]; exact min_le_left _ _
  have hαper : α ≤ period/4 := by rw [hαdef]; exact min_le_right _ _
  have hαle : α ≤ period := by linarith
  -- the compact far-parameter set
  set KK : Set (ℝ × ℝ) := (Set.Icc (0:ℝ) period ×ˢ Set.Icc (0:ℝ) period) ∩
      ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' Set.Icc α (period - α)) with hKKdef
  have hKclosed : IsClosed KK := by
    rw [hKKdef]
    exact (isClosed_Icc.prod isClosed_Icc).inter
      (isClosed_Icc.preimage (continuous_fst.sub continuous_snd))
  have hKsub : KK ⊆ Set.Icc (0:ℝ) period ×ˢ Set.Icc (0:ℝ) period := by
    rw [hKKdef]; exact Set.inter_subset_left
  have hKcompact : IsCompact KK :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKclosed hKsub
  have hKne : KK.Nonempty := by
    refine ⟨(α, 0), ?_⟩
    rw [hKKdef, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, Set.mem_Icc]
    exact ⟨⟨⟨hαpos.le, hαle⟩, ⟨le_rfl, hp.le⟩⟩, by simp, by linarith⟩
  have hφcont : Continuous (fun p : ℝ × ℝ => ‖r p.1 - r p.2‖) :=
    ((hrc.comp continuous_fst).sub (hrc.comp continuous_snd)).norm
  obtain ⟨p₀, hp₀K, hminK⟩ := hKcompact.exists_isMinOn hKne hφcont.continuousOn
  set d : ℝ := ‖r p₀.1 - r p₀.2‖ with hddef
  have hdpos : 0 < d := by
    have hmem := hp₀K
    rw [hKKdef, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, Set.mem_Icc] at hmem
    obtain ⟨⟨ha, hb⟩, hcd1, hcd2⟩ := hmem
    have hne : r p₀.1 ≠ r p₀.2 := by
      intro hcon
      have hb' : p₀.2 ∈ Set.Ico (0:ℝ) period := ⟨hb.1, by linarith⟩
      rcases lt_or_eq_of_le ha.2 with hlt | heq
      · have ha' : p₀.1 ∈ Set.Ico (0:ℝ) period := ⟨by linarith, hlt⟩
        have := hr.injective_on_period ha' hb' hcon
        linarith
      · have hr0 : r period = r 0 := by simpa using hr.periodic 0
        have hcon' : r 0 = r p₀.2 := by rw [← hr0, ← heq]; exact hcon
        have h0 : (0:ℝ) ∈ Set.Ico (0:ℝ) period := ⟨le_rfl, hp⟩
        have h02 := hr.injective_on_period h0 hb' hcon'
        have : p₀.1 - p₀.2 = period := by rw [heq, ← h02]; ring
        linarith
    rw [hddef]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hfar : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) period → t ∈ Set.Icc (0:ℝ) period →
      α ≤ s - t → s - t ≤ period - α → d ≤ ‖r s - r t‖ := by
    intro s t hs ht h1 h2
    have hmem : (s, t) ∈ KK := by
      rw [hKKdef]; exact ⟨⟨hs, ht⟩, by rw [Set.mem_preimage]; exact ⟨h1, h2⟩⟩
    have := hminK hmem
    simpa [hddef] using this
  -- local lower bound for nearby parameters
  have hloc_mono : ∀ a b : ℝ, a ∈ Set.Icc (0:ℝ) (2*period) → b ∈ Set.Icc (0:ℝ) (2*period) →
      a ≤ b → b - a ≤ α → (m₀/2) * (b - a) ≤ ‖r b - r a‖ := by
    intro a b ha hb hab hba
    set c : Space := velocity r a with hcdef
    set G : ℝ → Space := fun x => r x - x • c with hGdef
    have hGdiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ G x := by
      intro x hx
      have h1 : G = (fun y : ℝ => r y) - (fun y : ℝ => y • c) := by
        rw [hGdef]; funext y; rfl
      rw [h1]
      exact (hrdiff x).sub (differentiableAt_id.smul_const c)
    have hGderiv : ∀ x ∈ Set.Icc a b, deriv G x = velocity r x - c := by
      intro x hx
      have h1 : G = (fun y : ℝ => r y) - (fun y : ℝ => y • c) := by
        rw [hGdef]; funext y; rfl
      have hd1 : HasDerivAt (fun y : ℝ => y • c) c x := by
        simpa using (hasDerivAt_id x).smul_const c
      have hd2 : HasDerivAt (fun y : ℝ => r y) (velocity r x) x := by
        simpa only [velocity] using (hrdiff x).hasDerivAt
      have hd : HasDerivAt G (velocity r x - c) x := by
        rw [h1]; exact hd2.sub hd1
      exact hd.deriv
    have hGbound : ∀ x ∈ Set.Icc a b, ‖deriv G x‖ ≤ m₀/2 := by
      intro x hx
      have hx2 : x ∈ Set.Icc (0:ℝ) (2*period) := ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩
      have hdist : dist x a ≤ δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
        linarith [hx.1, hx.2, hba, hαδ]
      have hthis := hδ x hx2 a ha hdist
      rw [dist_eq_norm] at hthis
      rw [hGderiv x hx, hcdef]
      exact hthis
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := G) (s := Set.Icc a b)
      hGdiff hGbound (convex_Icc a b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hmvt
    have hGa : G a = r a - a • c := by simp only [hGdef]
    have hGb : G b = r b - b • c := by simp only [hGdef]
    have hab' : G b - G a = (r b - r a) - (b - a) • c := by
      rw [hGb, hGa, sub_smul]; abel
    rw [hab'] at hmvt
    have hcs : ‖(b - a) • c‖ = (b - a) * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)]
    have hcl : m₀ ≤ ‖c‖ := by rw [hcdef]; exact hm₀lower a
    have h2 : ‖(b - a) • c‖ ≤ ‖r b - r a‖ + ‖(r b - r a) - (b - a) • c‖ := by
      have h := norm_sub_le (r b - r a) ((r b - r a) - (b - a) • c)
      rwa [sub_sub_cancel] at h
    rw [hcs] at h2
    have h3 : (b - a) * m₀ ≤ (b - a) * ‖c‖ :=
      mul_le_mul_of_nonneg_left hcl (sub_nonneg.mpr hab)
    linarith
  have hloc : ∀ u v : ℝ, u ∈ Set.Icc (0:ℝ) (2*period) → v ∈ Set.Icc (0:ℝ) (2*period) →
      |v - u| ≤ α → (m₀/2) * |v - u| ≤ ‖r v - r u‖ := by
    intro u v hu hv huv
    rcases le_total u v with huv' | huv'
    · have hle : v - u ≤ α := by
        have := huv
        rwa [abs_of_nonneg (sub_nonneg.mpr huv')] at this
      have h := hloc_mono u v hu hv huv' hle
      rwa [abs_of_nonneg (sub_nonneg.mpr huv')]
    · have hle : u - v ≤ α := by
        have hthis := huv
        rw [abs_of_nonpos (sub_nonpos.mpr huv'), neg_sub] at hthis
        exact hthis
      have h := hloc_mono v u hv hu huv' hle
      rw [norm_sub_rev] at h
      rwa [abs_of_nonpos (sub_nonpos.mpr huv'), neg_sub]
  -- the smallness scale
  set ε : ℝ := min (m₀/4) (d/4) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (by linarith) (by linarith)
  have hεm : ε < m₀/2 := by
    rw [hεdef]; have := min_le_left (m₀/4) (d/4); linarith
  have hεd : 2*ε < d := by
    rw [hεdef]; have := min_le_right (m₀/4) (d/4); linarith
  refine ⟨ε, hεpos, ?_⟩
  intro w hw_smooth hwper hwsmall
  have hwdiff : Differentiable ℝ w := hw_smooth.differentiable (by decide)
  have hwlip : ∀ a b : ℝ, ‖w b - w a‖ ≤ ε * |b - a| := by
    intro a b
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := w) (s := Set.univ)
      (fun x _ => hwdiff x) (fun x _ => le_of_lt (hwsmall x).2) convex_univ
      (Set.mem_univ a) (Set.mem_univ b)
    rwa [Real.norm_eq_abs] at h
  have key : ∀ s t : ℝ, s ∈ Set.Ico (0:ℝ) period → t ∈ Set.Ico (0:ℝ) period → t < s →
      (fun t : ℝ => r t + w t) s = (fun t : ℝ => r t + w t) t → False := by
    intro s t hs ht hts heq
    have heq' : r s + w s = r t + w t := heq
    have hhpos : 0 < s - t := sub_pos.mpr hts
    have hhpt : s - t < period := by have := hs.2; have := ht.1; linarith
    by_cases hle : s - t ≤ α
    · have hu : t ∈ Set.Icc (0:ℝ) (2*period) := ⟨ht.1, by linarith [ht.2, hp]⟩
      have hsv : s ∈ Set.Icc (0:ℝ) (2*period) := ⟨hs.1, by linarith [hs.2, hp]⟩
      have habs : |s - t| ≤ α := by rwa [abs_of_pos hhpos]
      have hl := hloc t s hu hsv habs
      have hw := hwlip t s
      have hcomb : (m₀/2 - ε) * |s - t| ≤ ‖(r s + w s) - (r t + w t)‖ := by
        have htri : ‖r s - r t‖ - ‖w s - w t‖ ≤ ‖(r s + w s) - (r t + w t)‖ := by
          have h := norm_sub_le ((r s - r t) + (w s - w t)) (w s - w t)
          rw [add_sub_cancel_right] at h
          have he : (r s - r t) + (w s - w t) = (r s + w s) - (r t + w t) := by abel
          rw [he] at h
          linarith
        have hsub : (m₀/2 - ε) * |s - t| ≤ ‖r s - r t‖ - ‖w s - w t‖ := by
          have hrw : (m₀/2 - ε) * |s - t| = (m₀/2) * |s - t| - ε * |s - t| := by ring
          rw [hrw]; linarith
        linarith
      have hzero : ‖(r s + w s) - (r t + w t)‖ = 0 := by rw [heq', sub_self, norm_zero]
      have hpp : 0 < (m₀/2 - ε) * |s - t| :=
        mul_pos (by linarith) (abs_pos.mpr (ne_of_gt hhpos))
      linarith
    · have hgt : α < s - t := not_le.mp hle
      by_cases hle2 : s - t ≤ period - α
      · have hsv : s ∈ Set.Icc (0:ℝ) period := Set.Ico_subset_Icc_self hs
        have htv : t ∈ Set.Icc (0:ℝ) period := Set.Ico_subset_Icc_self ht
        have hd := hfar s t hsv htv hgt.le hle2
        have hcomb : d - 2*ε ≤ ‖(r s + w s) - (r t + w t)‖ := by
          have h := norm_sub_le ((r s - r t) + (w s - w t)) (w s - w t)
          rw [add_sub_cancel_right] at h
          have he : (r s - r t) + (w s - w t) = (r s + w s) - (r t + w t) := by abel
          rw [he] at h
          have hw' : ‖w s - w t‖ ≤ 2*ε := by
            have h2 := norm_sub_le (w s) (w t)
            linarith [(hwsmall s).1, (hwsmall t).1]
          linarith
        have hzero : ‖(r s + w s) - (r t + w t)‖ = 0 := by rw [heq', sub_self, norm_zero]
        have hpp : 0 < d - 2*ε := by linarith
        linarith
      · have hgt2 : period - α < s - t := not_le.mp hle2
        set t' : ℝ := t + period with ht'def
        have ht'mem : t' ∈ Set.Icc (0:ℝ) (2*period) := by
          rw [ht'def]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hsmem : s ∈ Set.Icc (0:ℝ) (2*period) := ⟨hs.1, by linarith [hs.2, hp]⟩
        have hsmall : |s - t'| ≤ α := by
          rw [ht'def]
          have hneg : s - (t + period) ≤ 0 := by linarith
          rw [abs_of_nonpos hneg]
          linarith
        have hl := hloc t' s ht'mem hsmem hsmall
        have hw := hwlip t' s
        have hper' : r t' + w t' = r t + w t := by
          rw [ht'def, hr.periodic t, hwper t]
        have hzero : ‖(r s + w s) - (r t' + w t')‖ = 0 := by
          rw [hper', ← heq', sub_self, norm_zero]
        have hcomb : (m₀/2 - ε) * |s - t'| ≤ ‖(r s + w s) - (r t' + w t')‖ := by
          have htri : ‖r s - r t'‖ - ‖w s - w t'‖ ≤ ‖(r s + w s) - (r t' + w t')‖ := by
            have h := norm_sub_le ((r s - r t') + (w s - w t')) (w s - w t')
            rw [add_sub_cancel_right] at h
            have he : (r s - r t') + (w s - w t') = (r s + w s) - (r t' + w t') := by abel
            rw [he] at h
            linarith
          have hsub : (m₀/2 - ε) * |s - t'| ≤ ‖r s - r t'‖ - ‖w s - w t'‖ := by
            have hrw : (m₀/2 - ε) * |s - t'| = (m₀/2) * |s - t'| - ε * |s - t'| := by ring
            rw [hrw]; linarith
          linarith
        have hpp : 0 < (m₀/2 - ε) * |s - t'| := by
          refine mul_pos (by linarith) ?_
          exact abs_pos.mpr (by
            intro hc
            rw [sub_eq_zero] at hc
            rw [ht'def] at hc
            linarith)
        linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hr.smooth.add hw_smooth
  · exact hr.periodic.add hwper
  · intro s hs t ht heq
    rcases lt_trichotomy t s with h | h | h
    · exact absurd heq (key s t hs ht h)
    · exact h.symm
    · exact absurd heq.symm (key t s ht hs h)
  · intro t
    have hsum : velocity (fun t : ℝ => r t + w t) t = velocity r t + velocity w t := by
      simp only [velocity]
      change deriv (r + w) t = deriv r t + deriv w t
      rw [deriv_add (hrdiff t) (hwdiff t)]
    rw [hsum]
    have h1 : ‖velocity r t‖ - ‖velocity w t‖ ≤ ‖velocity r t + velocity w t‖ := by
      have h := norm_sub_le (velocity r t + velocity w t) (velocity w t)
      rw [add_sub_cancel_right] at h
      linarith
    have : 0 < ‖velocity r t + velocity w t‖ := by
      linarith [hm₀lower t, (hwsmall t).2, h1, hεm]
    exact norm_pos_iff.mp this

end Work.Drive
