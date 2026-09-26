import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function

noncomputable section

/-- Degenerate case of the extension lemma: an arc parametrised on the single point `a` can be
extended a little beyond `a`, using an arc chart at the image point. -/
private theorem localArcExistsExtensionIcc_eq {X : Type*} [TopologicalSpace X]
    (H : Work.Smooth.SphereJordan.IsLocallyArc X) (a : ℝ) {α : ℝ → X} {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ → X, ContinuousOn β (Set.Icc a (a + ε)) ∧ Set.InjOn β (Set.Icc a (a + ε)) ∧
      Set.EqOn β α (Set.Icc a a) := by
  classical
  let c : ArcChart X (α a) := Work.Smooth.SphereJordan.chartOf H (α a)
  set L : ℝ := 1 / (2 * ε) with hL_def
  have hLpos : 0 < L := by rw [hL_def]; positivity
  let g : ℝ → ℝ := fun t => L * (t - a)
  have hgcont : Continuous g := by
    rw [show g = (fun t : ℝ => L * (t - a)) from rfl]
    exact (continuous_const : Continuous fun _ : ℝ => L).mul (continuous_id.sub continuous_const)
  let β : ℝ → X := fun t => if t ≤ a then α t else c.map (g t)
  have hβa : ∀ t, t ≤ a → β t = α t := fun t ht => if_pos ht
  have hgb : g a = 0 := by
    rw [show g a = L * (a - a) from rfl, sub_self, mul_zero]
  have hβb : ∀ t, a ≤ t → β t = c.map (g t) := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · subst h
      show (if a ≤ a then α a else c.map (g a)) = c.map (g a)
      rw [if_pos le_rfl, hgb, c.map_zero]
    · show (if t ≤ a then α t else c.map (g t)) = c.map (g t)
      rw [if_neg (not_le.mpr h)]
  have hgt0 : ∀ t, a < t → g t ≠ 0 := by
    intro t ht
    rw [show g t = L * (t - a) from rfl]
    exact mul_ne_zero hLpos.ne' (by linarith)
  have hgcancel : ∀ s t, a < s → a < t → g s = g t → s = t := by
    intro s t hs ht h
    have h' : L * (s - a) = L * (t - a) := by simpa [g] using h
    have h2 : s - a = t - a := mul_left_cancel₀ hLpos.ne' h'
    linarith
  refine ⟨β, ?_, ?_, fun t ht => hβa t ht.2⟩
  · exact (ContinuousOn.congr_mono ((c.continuous_map.comp hgcont).continuousOn)
      (fun t ht => hβb t ht.1) (subset_univ _))
  · intro s hs t ht hst
    rcases eq_or_lt_of_le hs.1 with hsa | hsa
    · rcases eq_or_lt_of_le ht.1 with hta | hta
      · exact hsa.symm.trans hta
      · exfalso
        have hβs : β s = α a := by rw [← hsa]; exact hβa a le_rfl
        have hβt : β t = c.map (g t) := hβb t hta.le
        rw [hβs, hβt] at hst
        exact (hgt0 t hta) (c.injective_map (hst.symm.trans c.map_zero.symm))
    · rcases eq_or_lt_of_le ht.1 with hta | hta
      · exfalso
        have hβt : β t = α a := by rw [← hta]; exact hβa a le_rfl
        have hβs : β s = c.map (g s) := hβb s hsa.le
        rw [hβs, hβt] at hst
        exact (hgt0 s hsa) (c.injective_map (hst.trans c.map_zero.symm))
      · rw [hβb s hsa.le, hβb t hta.le] at hst
        exact hgcancel s t hsa hta (c.injective_map hst)

theorem localArcExistsExtensionIcc {X : Type*} [TopologicalSpace X] [T2Space X]
    (H : Work.Smooth.SphereJordan.IsLocallyArc X) {a b : ℝ} (hab : a ≤ b) {α : ℝ → X}
    (hc : ContinuousOn α (Set.Icc a b)) (hi : Set.InjOn α (Set.Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ → X, ContinuousOn β (Set.Icc a (b + ε)) ∧ Set.InjOn β (Set.Icc a (b + ε)) ∧
      Set.EqOn β α (Set.Icc a b) := by
  classical
  rcases lt_or_eq_of_le hab with hablt | habeq
  · let c : ArcChart X (α b) := Work.Smooth.SphereJordan.chartOf H (α b)
    -- Step 1: `α` maps a left-neighbourhood of `b` inside the chart
    obtain ⟨u, hu_open, hbu, hu_sub⟩ :=
      (continuousOn_iff.mp hc) b (right_mem_Icc.mpr hab) c.V c.isOpen_V c.mem_V
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hu_open b hbu
    set δ : ℝ := ρ / 2 with hδ_def
    have hδpos : 0 < δ := by rw [hδ_def]; linarith
    set m : ℝ := max a (b - δ) with hm_def
    have ham : a ≤ m := by rw [hm_def]; exact le_max_left _ _
    have hmb : m ≤ b := by rw [hm_def]; exact max_le hab (by linarith)
    have hmltb : m < b := by rw [hm_def]; exact max_lt hablt (by linarith)
    have hαV : ∀ t ∈ Icc m b, α t ∈ c.V := by
      intro t ht
      have htm : b - δ ≤ m := by rw [hm_def]; exact le_max_right _ _
      have htI : t ∈ Icc a b := ⟨le_trans ham ht.1, ht.2⟩
      have hdist : dist t b < ρ := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith [ht.2])]
        rw [hδ_def] at htm
        linarith [ht.1, ht.2, htm, hρpos]
      exact hu_sub ⟨hρsub (by rw [Metric.mem_ball]; exact hdist), htI⟩
    -- Step 2: the compact "far" piece and a small chart interval avoiding it
    set K : Set X := α '' Icc a m with hK_def
    have hKcomp : IsCompact K := by
      rw [hK_def]
      exact isCompact_Icc.image_of_continuousOn (hc.mono (Icc_subset_Icc le_rfl hmb))
    have hxK : α b ∉ K := by
      rw [hK_def]
      rintro ⟨t, ht, htm⟩
      have htI : t ∈ Icc a b := ⟨ht.1, le_trans ht.2 hmb⟩
      have htb : t = b := hi htI (right_mem_Icc.mpr hab) htm
      linarith [ht.2, hmltb, htb]
    have hKclosed : IsClosed K := hKcomp.isClosed
    have hclosed : IsClosed (c.map ⁻¹' K) := hKclosed.preimage c.continuous_map
    have h0not : (0 : ℝ) ∉ c.map ⁻¹' K := by
      simp only [mem_preimage]
      rw [c.map_zero]
      exact hxK
    obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds h0not)
    have hηK : ∀ t : ℝ, t ∈ Ioo (-η) η → c.map t ∉ K := by
      intro t ht
      have hball : t ∈ Metric.ball (0 : ℝ) η := by
        rw [Real.ball_eq_Ioo]
        simpa using ht
      have h := hηsub hball
      simpa using h
    -- Step 3: the coordinate function of `α` on the closed interval `[m,b]`
    let f : ℝ → ℝ := fun t => if h : α t ∈ c.V then c.coord ⟨α t, h⟩ else 0
    have hf_apply : ∀ t (ht : t ∈ Icc m b), f t = c.coord ⟨α t, hαV t ht⟩ :=
      fun t ht => dif_pos (hαV t ht)
    have hαmaps : MapsTo α (Icc m b) c.V := hαV
    have hf_cont : ContinuousOn f (Icc m b) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have h1 : Continuous (fun t : Icc m b => c.coord (hαmaps.restrict α (Icc m b) c.V t)) :=
        c.continuous_coord.comp ((hc.mono (Icc_subset_Icc ham le_rfl)).mapsToRestrict hαmaps)
      convert h1 using 1
      funext t
      rw [Set.domRestrict_apply,
        show f t.1 = c.coord ⟨α t.1, hαV t.1 t.2⟩ from dif_pos (hαV t.1 t.2)]
      exact congrArg c.coord (Subtype.ext (by rw [MapsTo.val_restrict_apply]))
    have hf_inj : InjOn f (Icc m b) := by
      intro s hs t ht hst
      have hs' : f s = c.coord ⟨α s, hαV s hs⟩ := dif_pos (hαV s hs)
      have ht' : f t = c.coord ⟨α t, hαV t ht⟩ := dif_pos (hαV t ht)
      rw [hs', ht'] at hst
      have h1 : (⟨α s, hαV s hs⟩ : c.V) = ⟨α t, hαV t ht⟩ := c.injective_coord hst
      exact hi (Icc_subset_Icc ham le_rfl hs) (Icc_subset_Icc ham le_rfl ht)
        (congrArg Subtype.val h1)
    have hfb : f b = 0 := by
      have h1 : f b = c.coord ⟨α b, hαV b (right_mem_Icc.mpr hmb)⟩ :=
        dif_pos (hαV b (right_mem_Icc.mpr hmb))
      rw [h1]
      have h2 : (⟨α b, hαV b (right_mem_Icc.mpr hmb)⟩ : c.V) = ⟨c.map 0, c.map_mem 0⟩ := by
        apply Subtype.ext
        show α b = c.map 0
        rw [c.map_zero]
      rw [h2, c.coord_apply_map]
    -- Step 4: monotonicity, sign, and the interpolation parameter
    have hdisj := ContinuousOn.strictMonoOn_of_injOn_Icc' hmb hf_cont hf_inj
    set σ : ℝ := if StrictMonoOn f (Icc m b) then -1 else 1 with hσ_def
    have hσsq : σ * σ = 1 := by
      by_cases hm : StrictMonoOn f (Icc m b)
      · rw [hσ_def]; simp [hm]
      · rw [hσ_def]; simp [hm]
    have hσne : σ ≠ 0 := by
      intro h
      rw [h] at hσsq
      norm_num at hσsq
    have hσabs : |σ| = 1 := by
      have h2 : |σ| * |σ| = 1 := by rw [abs_mul_abs_self, hσsq]
      nlinarith [abs_nonneg σ]
    have hσf : ∀ t ∈ Ioc m b, 0 ≤ σ * f t := by
      intro t ht
      by_cases hm : StrictMonoOn f (Icc m b)
      · have hσ : σ = -1 := by rw [hσ_def]; simp [hm]
        have hft : f t ≤ 0 := by
          rcases lt_or_eq_of_le ht.2 with hltb | hb
          · have h1 := hm ⟨le_of_lt ht.1, le_of_lt hltb⟩ (right_mem_Icc.mpr hmb) hltb
            rw [hfb] at h1; linarith
          · simp [hb, hfb]
        rw [hσ]; linarith
      · have hanti : StrictAntiOn f (Icc m b) := hdisj.resolve_left hm
        have hσ : σ = 1 := by rw [hσ_def]; simp [hm]
        have hft : 0 ≤ f t := by
          rcases lt_or_eq_of_le ht.2 with hltb | hb
          · have h1 := hanti ⟨le_of_lt ht.1, le_of_lt hltb⟩ (right_mem_Icc.mpr hmb) hltb
            rw [hfb] at h1; linarith
          · simp [hb, hfb]
        rw [hσ]; linarith
    set L : ℝ := η / (2 * ε) with hL_def
    have hLpos : 0 < L := by rw [hL_def]; positivity
    have hLε : L * ε = η / 2 := by rw [hL_def]; field_simp
    have hη2 : η / 2 < η := by linarith
    let g : ℝ → ℝ := fun t => -σ * (L * (t - b))
    have hσg : ∀ t, b < t → σ * g t < 0 := by
      intro t ht
      rw [show g t = -σ * (L * (t - b)) from rfl,
        show σ * (-σ * (L * (t - b))) = -(σ * σ) * (L * (t - b)) by ring, hσsq, neg_one_mul]
      have h2 : 0 < L * (t - b) := mul_pos hLpos (by linarith)
      linarith
    have hgb0 : g b = 0 := by
      rw [show g b = -σ * (L * (b - b)) from rfl, sub_self, mul_zero, mul_zero]
    -- Step 5: the extension
    let β : ℝ → X := fun t => if t ≤ b then α t else c.map (g t)
    have hβa : ∀ t, t ≤ b → β t = α t := fun t ht => if_pos ht
    have hβb : ∀ t, b ≤ t → β t = c.map (g t) := by
      intro t ht
      rcases eq_or_lt_of_le ht with h | h
      · subst h
        show (if b ≤ b then α b else c.map (g b)) = c.map (g b)
        rw [if_pos le_rfl, hgb0, c.map_zero]
      · show (if t ≤ b then α t else c.map (g t)) = c.map (g t)
        rw [if_neg (not_le.mpr h)]
    have hgcont : Continuous g := by
      rw [show g = (fun t : ℝ => -σ * (L * (t - b))) from rfl]
      exact (continuous_const : Continuous fun _ : ℝ => -σ).mul
        ((continuous_const : Continuous fun _ : ℝ => L).mul (continuous_id.sub continuous_const))
    have hcont_left : ContinuousOn β (Icc a b) := hc.congr (fun t ht => hβa t ht.2)
    have hcont_right : ContinuousOn β (Icc b (b + ε)) :=
      ContinuousOn.congr_mono ((c.continuous_map.comp hgcont).continuousOn)
        (fun t ht => hβb t ht.1) (subset_univ _)
    have hcontβ : ContinuousOn β (Icc a (b + ε)) := by
      have h := hcont_left.union_of_isClosed hcont_right isClosed_Icc isClosed_Icc
      rwa [Icc_union_Icc_eq_Icc hab (le_add_of_nonneg_right hε.le)] at h
    have hgt_mem : ∀ t, b ≤ t → t ≤ b + ε → g t ∈ Ioo (-η) η := by
      intro t hbt hte
      have htb0 : 0 ≤ t - b := by linarith
      have hg_abs : |g t| ≤ η / 2 := by
        rw [show g t = -σ * (L * (t - b)) from rfl, abs_mul, abs_neg, hσabs, one_mul,
          abs_of_nonneg (mul_nonneg hLpos.le htb0)]
        calc L * (t - b) ≤ L * ε := mul_le_mul_of_nonneg_left (by linarith) hLpos.le
          _ = η / 2 := hLε
      rw [mem_Ioo, ← abs_lt]
      linarith
    have key : ∀ s t, s ∈ Icc a (b + ε) → t ∈ Icc a (b + ε) → s ≤ b → b < t → β s ≠ β t := by
      intro s t hs ht hsb hbt
      rw [hβa s hsb, hβb t hbt.le]
      intro heq
      by_cases hsm : s ≤ m
      · have hsK : α s ∈ K := by
          rw [hK_def]
          exact ⟨s, ⟨hs.1, hsm⟩, rfl⟩
        exact (hηK (g t) (hgt_mem t hbt.le ht.2)) (heq ▸ hsK)
      · simp only [not_le] at hsm
        have hsnear : s ∈ Ioc m b := ⟨hsm, hsb⟩
        have hsmm : s ∈ Icc m b := ⟨le_of_lt hsm, hsb⟩
        have hfs : f s = c.coord ⟨α s, hαV s hsmm⟩ := dif_pos (hαV s hsmm)
        have hαs : α s = c.map (f s) := by
          rw [hfs]
          exact (c.map_coord ⟨α s, hαV s hsmm⟩).symm
        have hfst : f s = g t := c.injective_map (hαs.symm.trans heq)
        have h1 : 0 ≤ σ * f s := hσf s hsnear
        have h2 : σ * g t < 0 := hσg t hbt
        have h3 : σ * f s = σ * g t := congrArg (fun x => σ * x) hfst
        linarith
    have hinj : InjOn β (Icc a (b + ε)) := by
      intro s hs t ht hst
      rcases le_or_gt s b with hsb | hsb
      · rcases le_or_gt t b with htb | htb
        · rw [hβa s hsb, hβa t htb] at hst
          exact hi ⟨hs.1, hsb⟩ ⟨ht.1, htb⟩ hst
        · exact absurd hst (key s t hs ht hsb htb)
      · rcases le_or_gt t b with htb | htb
        · exact absurd hst.symm (key t s ht hs htb hsb)
        · rw [hβb s hsb.le, hβb t htb.le] at hst
          have hgs : g s = g t := c.injective_map hst
          have h1 : (-σ) * (L * (s - b)) = (-σ) * (L * (t - b)) := by simpa [g] using hgs
          have h2 : L * (s - b) = L * (t - b) :=
            mul_left_cancel₀ (neg_ne_zero.mpr hσne) h1
          have h3 : s - b = t - b := mul_left_cancel₀ hLpos.ne' h2
          linarith
    exact ⟨β, hcontβ, hinj, fun t ht => hβa t ht.2⟩
  · rw [habeq]
    exact localArcExistsExtensionIcc_eq H b hε

end

end Work.Smooth.SphereJordan.LocalArc
