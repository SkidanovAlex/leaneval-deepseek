import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic

/-!
# A closed-up arc is a circle

If an injective continuous map `α : ℝ → X` tends to the same point `p` at both ends, misses `p`,
and together with `p` covers `X`, then `X` admits a `2π`-periodic parametrisation.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter
open scoped Topology

noncomputable section

/-- The tangent parametrisation of `(0, 2π)` onto `ℝ`, with poles at `0` and `2π`. -/
private def tanParam (t : ℝ) : ℝ := Real.tan ((t - Real.pi) / 2)

private lemma tanParam_continuousAt {t : ℝ} (ht : t ∈ Set.Ioo 0 (2 * Real.pi)) :
    ContinuousAt tanParam t := by
  have hg : ContinuousAt (fun s : ℝ => (s - Real.pi) / 2) t :=
    ((continuous_id.sub continuous_const).div_const 2).continuousAt
  have hcos : Real.cos ((t - Real.pi) / 2) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hfun : tanParam = fun s : ℝ =>
      Real.sin ((s - Real.pi) / 2) / Real.cos ((s - Real.pi) / 2) := by
    funext s
    show Real.tan ((s - Real.pi) / 2) =
      Real.sin ((s - Real.pi) / 2) / Real.cos ((s - Real.pi) / 2)
    exact Real.tan_eq_sin_div_cos _
  rw [hfun]
  exact (Real.continuous_sin.continuousAt.comp hg).div
    (Real.continuous_cos.continuousAt.comp hg) hcos

private lemma tendsto_tanParam_atBot :
    Tendsto tanParam (𝓝[>] (0:ℝ)) atBot := by
  have hg : Tendsto (fun s : ℝ => (s - Real.pi) / 2) (𝓝[>] (0:ℝ)) (𝓝[>] (-(Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun s : ℝ => (s - Real.pi) / 2) 0 :=
        ((continuous_id.sub continuous_const).div_const 2).continuousAt
      have h := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0:ℝ)] 0 ≤ 𝓝 0)
      have hval : ((0:ℝ) - Real.pi) / 2 = -(Real.pi / 2) := by ring
      rwa [hval] at h
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ioi] at ht ⊢
      linarith [Real.pi_pos]
  exact Real.tendsto_tan_neg_pi_div_two.comp hg

private lemma tendsto_tanParam_atTop :
    Tendsto tanParam (𝓝[<] (2 * Real.pi)) atTop := by
  have hg : Tendsto (fun s : ℝ => (s - Real.pi) / 2) (𝓝[<] (2 * Real.pi)) (𝓝[<] (Real.pi / 2)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun s : ℝ => (s - Real.pi) / 2) (2 * Real.pi) :=
        ((continuous_id.sub continuous_const).div_const 2).continuousAt
      have h := hc.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[Set.Iio (2 * Real.pi)] (2 * Real.pi) ≤ 𝓝 (2 * Real.pi))
      have hval : ((2 * Real.pi) - Real.pi) / 2 = Real.pi / 2 := by ring
      rwa [hval] at h
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Iio] at ht ⊢
      linarith [Real.pi_pos]
  exact Real.tendsto_tan_pi_div_two.comp hg

private lemma tanParam_injOn : InjOn tanParam (Set.Ioo 0 (2 * Real.pi)) := by
  intro s hs t ht hst
  have hs' : (s - Real.pi) / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ht' : (t - Real.pi) / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h := Real.tan_inj_of_lt_of_lt_pi_div_two hs'.1 hs'.2 ht'.1 ht'.2 hst
  linarith

private lemma tanParam_surjOn : tanParam '' Set.Ioo 0 (2 * Real.pi) = Set.univ := by
  ext y
  simp only [Set.mem_image, Set.mem_univ, iff_true]
  refine ⟨Real.pi + 2 * Real.arctan y, ⟨?_, ?_⟩, ?_⟩
  · have := Real.arctan_mem_Ioo y
    linarith [this.1]
  · have := Real.arctan_mem_Ioo y
    linarith [this.2]
  · simp only [tanParam]
    rw [show (Real.pi + 2 * Real.arctan y - Real.pi) / 2 = Real.arctan y from by ring]
    exact Real.tan_arctan y

/-- **A closed-up arc is a circle.** -/
theorem localArcExistsCircleParamOfTendsto {X : Type*} [TopologicalSpace X]
    {α : ℝ → X} {p : X} (hc : Continuous α) (hinj : Function.Injective α)
    (htop : Tendsto α atTop (nhds p)) (hbot : Tendsto α atBot (nhds p))
    (hp : p ∉ Set.range α) (hcover : Set.range α ∪ {p} = Set.univ) :
    ∃ γ : ℝ → X, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧ Set.range γ = Set.univ := by
  classical
  have h2π : 0 < 2 * Real.pi := by positivity
  haveI : Fact (0 < 2 * Real.pi) := ⟨h2π⟩
  set f : ℝ → X := fun t => if t ∈ Set.Ioo 0 (2 * Real.pi) then α (tanParam t) else p with hfdef
  have hfeq : ∀ t ∈ Set.Ioo 0 (2 * Real.pi), f t = α (tanParam t) := by
    intro t ht
    simp only [hfdef]
    rw [if_pos ht]
  have hf0 : f 0 = p := by
    simp only [hfdef]
    rw [if_neg (by simp)]
  have hf2 : f (2 * Real.pi) = p := by
    simp only [hfdef]
    rw [if_neg (by intro h; linarith [h.2, Real.pi_pos])]
  -- one-sided limits
  have hlim0 : Tendsto (fun t : ℝ => α (tanParam t)) (𝓝[>] (0:ℝ)) (nhds p) :=
    hbot.comp tendsto_tanParam_atBot
  have hlim2 : Tendsto (fun t : ℝ => α (tanParam t)) (𝓝[<] (2 * Real.pi)) (nhds p) :=
    htop.comp tendsto_tanParam_atTop
  -- continuity on `[0, π]` and `[π, 2π]`
  have hcont_left : ContinuousOn f (Set.Icc 0 Real.pi) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0
      change Tendsto f (𝓝[Set.Icc (0:ℝ) Real.pi] 0) (𝓝 (f 0))
      rw [hf0]
      have hmono : 𝓝[Set.Icc (0:ℝ) Real.pi] 0 ≤ 𝓝[>] (0:ℝ) ⊔ pure 0 := by
        have hsub : Set.Icc (0:ℝ) Real.pi ⊆ Set.Ioi (0:ℝ) ∪ {0} := by
          intro u hu
          rcases eq_or_lt_of_le hu.1 with rfl | h
          · exact Or.inr rfl
          · exact Or.inl h
        have h := nhdsWithin_mono (0:ℝ) hsub
        rwa [nhdsWithin_union, nhdsWithin_singleton] at h
      have hf0' : Tendsto f (𝓝[>] (0:ℝ)) (nhds p) := hlim0.congr' (by
        filter_upwards [self_mem_nhdsWithin,
          (by
            rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
            exact ⟨Set.Ioo (-1) (2 * Real.pi),
              Ioo_mem_nhds (by linarith) (by positivity),
              fun x hx => hx.1.2⟩ :
            Set.Iio (2 * Real.pi) ∈ 𝓝[Set.Ioi (0:ℝ)] 0)] with u hu hu2
        exact (hfeq u ⟨hu, hu2⟩).symm)
      have hsup : Tendsto f (𝓝[>] (0:ℝ) ⊔ pure 0) (nhds p) := by
        rw [tendsto_sup]
        refine ⟨hf0', ?_⟩
        rw [← hf0]
        exact tendsto_pure_nhds f 0
      exact hsup.mono_left hmono
    · have ht' : t ∈ Set.Ioo 0 (2 * Real.pi) := ⟨h0, by linarith [ht.2, Real.pi_pos]⟩
      have hcomp : ContinuousAt (fun s : ℝ => α (tanParam s)) t :=
        hc.continuousAt.comp (tanParam_continuousAt ht')
      have heq : (fun s : ℝ => α (tanParam s)) =ᶠ[𝓝 t] f := by
        filter_upwards [isOpen_Ioo.mem_nhds ht'] with s hs
        exact (hfeq s hs).symm
      exact (hcomp.congr heq).continuousWithinAt
  have hcont_right : ContinuousOn f (Set.Icc Real.pi (2 * Real.pi)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h2 | h2
    · subst h2
      change Tendsto f (𝓝[Set.Icc Real.pi (2 * Real.pi)] (2 * Real.pi)) (𝓝 (f (2 * Real.pi)))
      rw [hf2]
      have hmono : 𝓝[Set.Icc Real.pi (2 * Real.pi)] (2 * Real.pi) ≤
          𝓝[<] (2 * Real.pi) ⊔ pure (2 * Real.pi) := by
        have hsub : Set.Icc Real.pi (2 * Real.pi) ⊆ Set.Iio (2 * Real.pi) ∪ {2 * Real.pi} := by
          intro u hu
          rcases eq_or_lt_of_le hu.2 with rfl | h
          · exact Or.inr rfl
          · exact Or.inl h
        have h := nhdsWithin_mono (2 * Real.pi) hsub
        rwa [nhdsWithin_union, nhdsWithin_singleton] at h
      have hf2' : Tendsto f (𝓝[<] (2 * Real.pi)) (nhds p) := hlim2.congr' (by
        filter_upwards [self_mem_nhdsWithin,
          (by
            rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
            exact ⟨Set.Ioo 0 (4 * Real.pi),
              Ioo_mem_nhds (by positivity) (by linarith [Real.pi_pos]),
              fun x hx => hx.1.1⟩ :
            Set.Ioi (0:ℝ) ∈ 𝓝[Set.Iio (2 * Real.pi)] (2 * Real.pi))] with u hu hu2
        exact (hfeq u ⟨hu2, hu⟩).symm)
      have hsup : Tendsto f (𝓝[<] (2 * Real.pi) ⊔ pure (2 * Real.pi)) (nhds p) := by
        rw [tendsto_sup]
        refine ⟨hf2', ?_⟩
        rw [← hf2]
        exact tendsto_pure_nhds f (2 * Real.pi)
      exact hsup.mono_left hmono
    · have ht' : t ∈ Set.Ioo 0 (2 * Real.pi) := ⟨by linarith [ht.1, Real.pi_pos], h2⟩
      have hcomp : ContinuousAt (fun s : ℝ => α (tanParam s)) t :=
        hc.continuousAt.comp (tanParam_continuousAt ht')
      have heq : (fun s : ℝ => α (tanParam s)) =ᶠ[𝓝 t] f := by
        filter_upwards [isOpen_Ioo.mem_nhds ht'] with s hs
        exact (hfeq s hs).symm
      exact (hcomp.congr heq).continuousWithinAt
  have hf_cont : ContinuousOn f (Set.Icc 0 (2 * Real.pi)) := by
    have h := hcont_left.union_of_isClosed hcont_right isClosed_Icc isClosed_Icc
    rwa [Set.Icc_union_Icc_eq_Icc (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at h
  -- injectivity on the fundamental domain
  have hf_inj : InjOn f (Set.Ico 0 (2 * Real.pi)) := by
    intro s hs t ht hst
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · subst h0
      rcases eq_or_lt_of_le ht.1 with h0' | h0'
      · rw [h0']
      · exfalso
        have hmem : p ∈ Set.range α := by
          rw [← hf0, hst, hfeq t ⟨h0', ht.2⟩]
          exact ⟨_, rfl⟩
        exact hp hmem
    · rcases eq_or_lt_of_le ht.1 with h0' | h0'
      · subst h0'
        exfalso
        have hmem : p ∈ Set.range α := by
          rw [← hf0, hst.symm, hfeq s ⟨h0, hs.2⟩]
          exact ⟨_, rfl⟩
        exact hp hmem
      · have hs' : s ∈ Set.Ioo 0 (2 * Real.pi) := ⟨h0, hs.2⟩
        have ht' : t ∈ Set.Ioo 0 (2 * Real.pi) := ⟨h0', ht.2⟩
        have hfe : f s = f t := hst
        rw [hfeq s hs', hfeq t ht'] at hfe
        exact tanParam_injOn hs' ht' (hinj hfe)
  -- surjectivity on the fundamental domain
  have hf_witness : ∀ y : X, ∃ u ∈ Set.Ico 0 (2 * Real.pi), f u = y := by
    intro y
    rcases (hcover ▸ Set.mem_univ y : y ∈ Set.range α ∪ {p}) with ⟨s, rfl⟩ | rfl
    · refine ⟨Real.pi + 2 * Real.arctan s, ⟨?_, ?_⟩, ?_⟩
      · have := Real.arctan_mem_Ioo s
        linarith [this.1]
      · have := Real.arctan_mem_Ioo s
        linarith [this.2]
      · have ht : Real.pi + 2 * Real.arctan s ∈ Set.Ioo 0 (2 * Real.pi) := by
          have := Real.arctan_mem_Ioo s
          exact ⟨by linarith [this.1], by linarith [this.2]⟩
        rw [hfeq _ ht]
        simp only [tanParam]
        rw [show (Real.pi + 2 * Real.arctan s - Real.pi) / 2 = Real.arctan s from by ring,
          Real.tan_arctan]
    · exact ⟨0, ⟨le_refl _, by positivity⟩, hf0⟩
  -- the circle parametrisation
  have hf0' : f 0 = f (0 + 2 * Real.pi) := by rw [zero_add, hf2, hf0]
  set F : AddCircle (2 * Real.pi) → X := AddCircle.liftIco (2 * Real.pi) 0 f with hFdef
  have hFcont : Continuous F :=
    AddCircle.liftIco_continuous hf0' (by rwa [zero_add])
  have hFeq : ∀ u ∈ Set.Ico 0 (2 * Real.pi), F (u : AddCircle (2 * Real.pi)) = f u := by
    intro u hu
    rw [hFdef]
    exact AddCircle.liftIco_coe_apply (by rwa [zero_add])
  have hF_inj : Function.Injective F := by
    intro x y hxy
    set u : ℝ := ((AddCircle.equivIco (2 * Real.pi) 0 x : Set.Ico 0 (0 + 2 * Real.pi)) : ℝ)
      with hu
    set v : ℝ := ((AddCircle.equivIco (2 * Real.pi) 0 y : Set.Ico 0 (0 + 2 * Real.pi)) : ℝ)
      with hv
    have huI : u ∈ Set.Ico 0 (2 * Real.pi) := by
      rw [hu]
      simpa using (AddCircle.equivIco (2 * Real.pi) 0 x).2
    have hvI : v ∈ Set.Ico 0 (2 * Real.pi) := by
      rw [hv]
      simpa using (AddCircle.equivIco (2 * Real.pi) 0 y).2
    have hux : (u : AddCircle (2 * Real.pi)) = x := by
      rw [hu]
      exact AddCircle.coe_equivIco
    have hvy : (v : AddCircle (2 * Real.pi)) = y := by
      rw [hv]
      exact AddCircle.coe_equivIco
    have h1 : F (u : AddCircle (2 * Real.pi)) = f u := hFeq u huI
    have h2 : F (v : AddCircle (2 * Real.pi)) = f v := hFeq v hvI
    rw [← hux, ← hvy] at hxy
    rw [h1, h2] at hxy
    have huv : u = v := hf_inj huI hvI hxy
    rw [← hux, ← hvy, huv]
  have hF_surj : Function.Surjective F := by
    intro y
    obtain ⟨u, hu, hueq⟩ := hf_witness y
    exact ⟨(u : AddCircle (2 * Real.pi)), by rw [hFeq u hu, hueq]⟩
  refine ⟨fun t : ℝ => F (t : AddCircle (2 * Real.pi)),
    hFcont.comp (AddCircle.continuous_mk' (2 * Real.pi)), ?_, ?_, ?_⟩
  · intro t
    show F ((t + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = F (t : AddCircle (2 * Real.pi))
    rw [AddCircle.coe_add_period]
  · intro s hs t ht hst
    have hs2 : ((s : AddCircle (2 * Real.pi))) = ((t : AddCircle (2 * Real.pi))) := hF_inj hst
    exact AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) (p := 2 * Real.pi)
      (by rwa [zero_add]) (by rwa [zero_add]) |>.mp hs2
  · rw [Set.range_eq_univ]
    intro y
    obtain ⟨x, hx⟩ := hF_surj y
    set u : ℝ := ((AddCircle.equivIco (2 * Real.pi) 0 x : Set.Ico 0 (0 + 2 * Real.pi)) : ℝ)
      with hu
    have hux : (u : AddCircle (2 * Real.pi)) = x := by
      rw [hu]
      exact AddCircle.coe_equivIco
    exact ⟨u, by simpa only [hux] using hx⟩

end

end Work.Smooth.SphereJordan.LocalArc
