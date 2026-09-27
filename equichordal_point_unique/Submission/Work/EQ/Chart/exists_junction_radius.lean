import Mathlib
import Submission.Work.EQ.TailGlueDefs
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.branchPt_meromorphic
import Submission.Work.EQ.H0_section_local

namespace Work.EQ.Chart

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-- The last point (`j = 0`) of the middle segment of the glued F3 family (sign sequence `σ`,
parameter `t`, depth `dep`). -/
private def glueLastPt (a : ℝ) (h : ℂ → ℂ) (z₀ : ℂ) (dep : ℕ) (σ : Fin (2 * dep) → Bool) (t : ℂ) :
    ℂ × ℂ :=
  branchPt a (endFun a h dep) z₀ 1 σ t ⟨0, by omega⟩

/-- The point of the principal unstable leaf attached to the glued family at parameter `t`. -/
private def leafPt (a : ℝ) (h : ℂ → ℂ) (c z₀ : ℂ) (dep : ℕ) (t : ℂ) : ℂ × ℂ :=
  ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * (c / (z₀ + t ^ (2 ^ (2 * dep)))))

/-- **Radius on which the unstable-leaf coordinate of a glued family is analytic.**

For `z₀ ≠ 0`, a germ `germC a h` analytic on `ball 0 ρg` and a value `λ^dep · c/z₀` of norm `< ρg`,
the function `t ↦ ugermC a h (λ^dep · c/(z₀ + t^(2^(2*dep))))` is analytic on a disc about `0`:
take the disc small enough that `z₀ + t^(2^(2*dep)) ≠ 0` (where the denominator degenerates) and
that `λ^dep · c/(z₀ + t^(2^(2*dep)))` stays in `ball 0 ρg`. -/
private lemma tail_analytic_radius {a : ℝ} {h : ℂ → ℂ} {c z₀ : ℂ} (hz₀ : z₀ ≠ 0) {dep : ℕ}
    {ρg : ℝ} (hρg : 0 < ρg) (hgerm : AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρg))
    (hbound : ‖((eqLam a : ℝ) : ℂ) ^ dep * (c / z₀)‖ < ρg) :
    ∃ δ : ℝ, 0 < δ ∧ AnalyticOnNhd ℂ (fun t : ℂ => leafPt a h c z₀ dep t) (Metric.ball 0 δ) := by
  have hn : (2 : ℕ) ^ (2 * dep) ≠ 0 := by positivity
  set g : ℂ → ℂ :=
    fun t => ((eqLam a : ℝ) : ℂ) ^ dep * (c / (z₀ + t ^ (2 ^ (2 * dep)))) with hg
  have hg0 : g 0 = ((eqLam a : ℝ) : ℂ) ^ dep * (c / z₀) := by
    rw [hg]; simp
  have hcont : ContinuousAt g 0 := by
    rw [hg]
    have hden : ContinuousAt (fun t : ℂ => z₀ + t ^ (2 ^ (2 * dep))) 0 :=
      continuousAt_const.add (continuousAt_id.pow _)
    have hquot : ContinuousAt (fun t : ℂ => c / (z₀ + t ^ (2 ^ (2 * dep)))) 0 :=
      ContinuousAt.div continuousAt_const hden (by simpa using hz₀)
    exact continuousAt_const.mul hquot
  have hmem1 : g ⁻¹' (Metric.ball 0 ρg) ∈ 𝓝 (0 : ℂ) :=
    hcont.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by rw [hg0, Metric.mem_ball, dist_zero_right]; exact hbound))
  have hmem2 : (fun t : ℂ => t ^ (2 ^ (2 * dep))) ⁻¹' (Metric.ball 0 ‖z₀‖) ∈ 𝓝 (0 : ℂ) :=
    (continuousAt_id.pow _).preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by
      show (0 : ℂ) ^ (2 ^ (2 * dep)) ∈ Metric.ball 0 ‖z₀‖
      rw [zero_pow hn, Metric.mem_ball, dist_zero_right]
      simpa using norm_pos_iff.mpr hz₀))
  have hmem : g ⁻¹' (Metric.ball 0 ρg) ∩ (fun t : ℂ => t ^ (2 ^ (2 * dep))) ⁻¹' (Metric.ball 0 ‖z₀‖)
      ∈ 𝓝 (0 : ℂ) := inter_mem hmem1 hmem2
  rw [Metric.mem_nhds_iff] at hmem
  obtain ⟨δ, hδ0, hδ⟩ := hmem
  refine ⟨δ, hδ0, ?_⟩
  have hmaps : Set.MapsTo (fun t : ℂ => ((eqLam a : ℝ) : ℂ) ^ dep * (c / (z₀ + t ^ (2 ^ (2 * dep)))))
      (Metric.ball 0 δ) (Metric.ball 0 ρg) := fun t ht => (hδ ht).1
  have han : AnalyticOnNhd ℂ
      (fun t : ℂ => ((eqLam a : ℝ) : ℂ) ^ dep * (c / (z₀ + t ^ (2 ^ (2 * dep)))))
      (Metric.ball 0 δ) := by
    intro t ht
    have hlt : ‖t ^ (2 ^ (2 * dep))‖ < ‖z₀‖ := by
      have h := (hδ ht).2
      rwa [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at h
    have hne : z₀ + t ^ (2 ^ (2 * dep)) ≠ 0 := by
      intro h0
      have h1 : t ^ (2 ^ (2 * dep)) = -z₀ := by linear_combination h0
      rw [h1, norm_neg] at hlt
      exact lt_irrefl _ hlt
    exact analyticAt_const.mul (AnalyticAt.div analyticAt_const
      (analyticAt_const.add (analyticAt_pow_id _)) hne)
  exact analyticOnNhd_ugermC_comp hgerm han hmaps

/-- **Radius below which an eventually nonvanishing function has no zeros.** -/
private lemma exists_radius_of_eventually_ne_zero {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ᶠ t in nhdsWithin (0 : ℂ) ({0}ᶜ), f t ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ → f t ≠ 0 := by
  rw [eventually_nhdsWithin_iff] at h
  rw [Filter.eventually_iff, Metric.mem_nhds_iff] at h
  obtain ⟨ε, hε0, hε⟩ := h
  refine ⟨min ε ρ, lt_min hε0 hρ, min_le_right _ _, fun t ht0 htδ => ?_⟩
  exact hε (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le htδ (min_le_left _ _))
    (by simp only [Set.mem_compl_singleton_iff]; exact norm_ne_zero_iff.mp ht0.ne')

theorem exists_junction_radius {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {c z₀ : ℂ} (hz₀ : z₀ ≠ 0) {dep : ℕ} (hdep : 1 ≤ dep)
    (hend : AnalyticOnNhd ℂ (endFun a h dep) (Metric.ball z₀ 1))
    {ρg : ℝ} (hρg : 0 < ρg) (hgerm : AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρg))
    (hbound : ‖((eqLam a : ℝ) : ℂ) ^ dep * (c / z₀)‖ < ρg) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ rhoFin' a (endFun a h dep) z₀ 1 (2 * dep) ∧
      ∀ (σ : Fin (2 * dep) → Bool), Adm a (endFun a h dep) z₀ 1 σ → ∀ t₀ : ℂ,
        0 < ‖t₀‖ → ‖t₀‖ < r₀ →
        branchPt a (endFun a h dep) z₀ 1 σ t₀ ⟨0, by omega⟩ =
          ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * (c / (z₀ + t₀ ^ (2 ^ (2 * dep))))) →
        ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < r₀ →
          branchPt a (endFun a h dep) z₀ 1 σ t ⟨0, by omega⟩ =
            ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * (c / (z₀ + t ^ (2 ^ (2 * dep))))) := by
  classical
  -- (0) `rhoFin'` is positive, and the leaf coordinate is analytic near `0`
  have hρfin : 0 < rhoFin' a (endFun a h dep) z₀ 1 (2 * dep) := rhoFin'_pos one_pos hend
  obtain ⟨δ₁, hδ₁0, hleaf_an⟩ :=
    tail_analytic_radius (a := a) (h := h) (c := c) (z₀ := z₀) hz₀ hρg hgerm hbound
  have hleaf_an1 : AnalyticOnNhd ℂ (fun t : ℂ => (leafPt a h c z₀ dep t).1)
      (Metric.ball 0 δ₁) := fun t ht => analyticAt_fst.comp (hleaf_an t ht)
  have hleaf_an2 : AnalyticOnNhd ℂ (fun t : ℂ => (leafPt a h c z₀ dep t).2)
      (Metric.ball 0 δ₁) := fun t ht => analyticAt_snd.comp (hleaf_an t ht)
  have hleaf_me1 : MeromorphicAt (fun t : ℂ => (leafPt a h c z₀ dep t).1) 0 :=
    (hleaf_an1 0 (by simpa using hδ₁0)).meromorphicAt
  have hleaf_me2 : MeromorphicAt (fun t : ℂ => (leafPt a h c z₀ dep t).2) 0 :=
    (hleaf_an2 0 (by simpa using hδ₁0)).meromorphicAt
  -- (1) the working radius `ρs`
  set ρs : ℝ := min (rhoFin' a (endFun a h dep) z₀ 1 (2 * dep)) δ₁ with hρs_def
  have hρs0 : 0 < ρs := lt_min hρfin hδ₁0
  have hρs_fin : ρs ≤ rhoFin' a (endFun a h dep) z₀ 1 (2 * dep) := min_le_left _ _
  have hρs_δ₁ : ρs ≤ δ₁ := min_le_right _ _
  -- (2) for every sign sequence, the junction identity is either everywhere or nowhere near `0`
  let Jg : (Fin (2 * dep) → Bool) → Prop := fun σ =>
    ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρs → glueLastPt a h z₀ dep σ t = leafPt a h c z₀ dep t
  let Ng : (Fin (2 * dep) → Bool) → Prop := fun σ =>
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρs ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ →
      glueLastPt a h z₀ dep σ t ≠ leafPt a h c z₀ dep t
  have key : ∀ σ : Fin (2 * dep) → Bool, Adm a (endFun a h dep) z₀ 1 σ → Jg σ ∨ Ng σ := by
    intro σ hAdm
    have hL := branchPt_analytic (a := a) (c := endFun a h dep) (u₀ := z₀) (R := 1)
      (N := 2 * dep) one_pos hend hAdm (⟨0, by omega⟩ : Fin (2 * dep + 1))
    have hLm := branchPt_meromorphic (a := a) (c := endFun a h dep) (u₀ := z₀) (R := 1)
      (N := 2 * dep) one_pos hend hAdm (⟨0, by omega⟩ : Fin (2 * dep + 1))
    have hb₁ : Metric.ball (0 : ℂ) ρs ⊆ Metric.ball (0 : ℂ) δ₁ := Metric.ball_subset_ball hρs_δ₁
    have hb₂ : Metric.ball (0 : ℂ) ρs ⊆
        Metric.ball (0 : ℂ) (rhoFin' a (endFun a h dep) z₀ 1 (2 * dep)) :=
      Metric.ball_subset_ball hρs_fin
    have hAn1 : AnalyticOnNhd ℂ
        (fun t : ℂ => (glueLastPt a h z₀ dep σ t).1 - (leafPt a h c z₀ dep t).1)
        (Metric.ball 0 ρs \ {0}) :=
      (hL.1.mono (fun z hz => ⟨hb₂ hz.1, hz.2⟩)).sub (hleaf_an1.mono (fun z hz => hb₁ hz.1))
    have hAn2 : AnalyticOnNhd ℂ
        (fun t : ℂ => (glueLastPt a h z₀ dep σ t).2 - (leafPt a h c z₀ dep t).2)
        (Metric.ball 0 ρs \ {0}) :=
      (hL.2.mono (fun z hz => ⟨hb₂ hz.1, hz.2⟩)).sub (hleaf_an2.mono (fun z hz => hb₁ hz.1))
    have hMe1 : MeromorphicAt
        (fun t : ℂ => (glueLastPt a h z₀ dep σ t).1 - (leafPt a h c z₀ dep t).1) 0 :=
      hLm.1.sub hleaf_me1
    have hMe2 : MeromorphicAt
        (fun t : ℂ => (glueLastPt a h z₀ dep σ t).2 - (leafPt a h c z₀ dep t).2) 0 :=
      hLm.2.sub hleaf_me2
    rcases MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero hMe1 with h1z | h1nz
    · -- first coordinate vanishes near `0`: it vanishes on the whole punctured disc
      have h1id := eqOn_zero_of_eventually_zero hρs0 hAn1 h1z
      rcases MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero hMe2 with h2z | h2nz
      · -- both coordinates vanish: the junction identity holds everywhere
        left
        intro t ht0 htρ
        have htmem : t ∈ Metric.ball (0 : ℂ) ρs \ {0} :=
          ⟨by rwa [Metric.mem_ball, dist_zero_right], by simp only [Set.mem_singleton_iff]; exact norm_ne_zero_iff.mp ht0.ne'⟩
        have h2id := eqOn_zero_of_eventually_zero hρs0 hAn2 h2z
        exact Prod.ext (sub_eq_zero.mp (h1id t htmem)) (sub_eq_zero.mp (h2id t htmem))
      · -- second coordinate nonzero near `0`: the identity fails near `0`
        right
        obtain ⟨δ, hδ0, hδρ, hδne⟩ := exists_radius_of_eventually_ne_zero hρs0 h2nz
        exact ⟨δ, hδ0, hδρ, fun t ht0 htδ hEq => hδne t ht0 htδ (by rw [hEq, sub_self])⟩
    · -- first coordinate nonzero near `0`: the identity fails near `0`
      right
      obtain ⟨δ, hδ0, hδρ, hδne⟩ := exists_radius_of_eventually_ne_zero hρs0 h1nz
      exact ⟨δ, hδ0, hδρ, fun t ht0 htδ hEq => hδne t ht0 htδ (by rw [hEq, sub_self])⟩
  -- (3) a uniform radius: choose one for each sign sequence and intersect
  have hδex : ∀ σ : Fin (2 * dep) → Bool, ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρs ∧
      (Ng σ → ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ →
        glueLastPt a h z₀ dep σ t ≠ leafPt a h c z₀ dep t) := by
    intro σ
    by_cases hN : Ng σ
    · exact ⟨Classical.choose hN, (Classical.choose_spec hN).1,
        (Classical.choose_spec hN).2.1, fun _ => (Classical.choose_spec hN).2.2⟩
    · exact ⟨ρs, hρs0, le_rfl, fun h => absurd h hN⟩
  set δσ : (Fin (2 * dep) → Bool) → ℝ := fun σ => Classical.choose (hδex σ) with hδσdef
  have hδσ_spec : ∀ σ : Fin (2 * dep) → Bool, Ng σ → ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δσ σ →
      glueLastPt a h z₀ dep σ t ≠ leafPt a h c z₀ dep t := by
    intro σ hN t ht0 htδ
    exact (Classical.choose_spec (hδex σ)).2.2 hN t ht0 htδ
  have hfin_ne : (Finset.univ : Finset (Fin (2 * dep) → Bool)).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  set r₀ : ℝ := min ρs ((Finset.univ : Finset (Fin (2 * dep) → Bool)).inf' hfin_ne δσ) with hr₀def
  have hr₀pos : 0 < r₀ := by
    rw [hr₀def]
    exact lt_min hρs0
      ((Finset.lt_inf'_iff hfin_ne).mpr (fun σ _ => (Classical.choose_spec (hδex σ)).1))
  have hr₀_le_δσ : ∀ σ : Fin (2 * dep) → Bool, r₀ ≤ δσ σ := by
    intro σ
    rw [hr₀def]
    exact le_trans (min_le_right _ _) (Finset.inf'_le δσ (Finset.mem_univ σ))
  have hr₀_le_ρs : r₀ ≤ ρs := by rw [hr₀def]; exact min_le_left _ _
  refine ⟨r₀, hr₀pos, le_trans hr₀_le_ρs hρs_fin, ?_⟩
  intro σ hAdm t₀ ht₀0 ht₀r hjun t ht0 htr
  by_cases hJ : Jg σ
  · have hJ' : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρs →
        glueLastPt a h z₀ dep σ t = leafPt a h c z₀ dep t := hJ
    exact hJ' t ht0 (lt_of_lt_of_le htr hr₀_le_ρs)
  · exfalso
    have hN : Ng σ := (key σ hAdm).resolve_left hJ
    exact hδσ_spec σ hN t₀ ht₀0 (lt_of_lt_of_le ht₀r (hr₀_le_δσ σ)) hjun


end

end Work.EQ.Chart
