import Mathlib

namespace Work.WilE7.AboveAux

theorem preconn_over_graph {α : Type*} [TopologicalSpace α] {C : Set α}
    (hC : IsPreconnected C) {σ : α → ℝ} (hσ : ContinuousOn σ C)
    (hσ1 : ∀ x ∈ C, σ x < 1) :
    IsPreconnected {q : α × ℝ | q.1 ∈ C ∧ σ q.1 < q.2 ∧ q.2 ≤ 1} := by
  -- `S = {(x,t) : x ∈ C, σ x < t ≤ 1}` is the image of the preconnected set
  -- `C × (0,1]` under the continuous (on `C × (0,1]`) map `(x,s) ↦ (x, (1-s) σ x + s)`.
  have hDpre : IsPreconnected (C ×ˢ Set.Ioc (0:ℝ) 1) := hC.prod isPreconnected_Ioc
  have hcont : ContinuousOn (fun q : α × ℝ => (q.1, (1 - q.2) * σ q.1 + q.2))
      (C ×ˢ Set.Ioc (0:ℝ) 1) := by
    refine ContinuousOn.prodMk continuous_fst.continuousOn ?_
    have hσc : ContinuousOn (fun q : α × ℝ => σ q.1) (C ×ˢ Set.Ioc (0:ℝ) 1) :=
      hσ.comp continuous_fst.continuousOn (fun q hq => hq.1)
    have hlin : ContinuousOn (fun q : α × ℝ => (1 : ℝ) - q.2)
        (C ×ˢ Set.Ioc (0:ℝ) 1) :=
      ContinuousOn.sub continuous_const.continuousOn continuous_snd.continuousOn
    exact ContinuousOn.add (ContinuousOn.mul hlin hσc) continuous_snd.continuousOn
  have himg : (fun q : α × ℝ => (q.1, (1 - q.2) * σ q.1 + q.2)) ''
        (C ×ˢ Set.Ioc (0:ℝ) 1)
      = {q : α × ℝ | q.1 ∈ C ∧ σ q.1 < q.2 ∧ q.2 ≤ 1} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [Set.mem_prod, Set.mem_Ioc] at hp
      obtain ⟨hpC, hp2pos, hp2le⟩ := hp
      have h1 : σ p.1 < 1 := hσ1 p.1 hpC
      refine ⟨hpC, ?_, ?_⟩
      · -- `σ p.1 < (1 - p.2) σ p.1 + p.2`, the difference being `p.2 (1 - σ p.1) > 0`
        nlinarith [mul_pos hp2pos (sub_pos.mpr h1)]
      · -- `(1 - p.2) σ p.1 + p.2 ≤ 1`, the difference being `(1 - p.2) (1 - σ p.1) ≥ 0`
        nlinarith [mul_nonneg (sub_nonneg.mpr hp2le) (sub_nonneg.mpr h1.le)]
    · rintro ⟨hqC, hq2, hq3⟩
      have h1 : σ q.1 < 1 := hσ1 q.1 hqC
      have hden : 0 < 1 - σ q.1 := sub_pos.mpr h1
      -- the fibre coordinate `t` is attained at `s = (t - σ x) / (1 - σ x) ∈ (0,1]`
      refine ⟨(q.1, (q.2 - σ q.1) / (1 - σ q.1)), ?_, ?_⟩
      · rw [Set.mem_prod, Set.mem_Ioc]
        exact ⟨hqC, div_pos (sub_pos.mpr hq2) hden,
          (div_le_one hden).mpr (by linarith)⟩
      · have hne : (1 : ℝ) - σ q.1 ≠ 0 := ne_of_gt hden
        have hsval : (1 - (q.2 - σ q.1) / (1 - σ q.1)) * σ q.1 +
            (q.2 - σ q.1) / (1 - σ q.1) = q.2 := by
          field_simp
          ring
        exact Prod.ext rfl hsval
  rw [← himg]
  exact hDpre.image _ hcont

end Work.WilE7.AboveAux
