import Mathlib

namespace Work.WilE7.BelowAux

/-- The region `{(x,t) : x ∈ C, -1 ≤ t < σ x}` beneath the graph of `σ` (and above the
level `-1`) is preconnected, whenever `C` is preconnected and `σ` is continuous on `C`
with `σ > -1` on `C`.

The region is the continuous image of the preconnected set `C × [0,1)` under the map
`(x,s) ↦ (x, -1 + s·(σ x + 1))`, which is a bijection because `σ x + 1 > 0`. -/
theorem preconn_under_graph {α : Type*} [TopologicalSpace α] {C : Set α}
    (hC : IsPreconnected C) {σ : α → ℝ} (hσ : ContinuousOn σ C)
    (hσ1 : ∀ x ∈ C, -1 < σ x) :
    IsPreconnected {q : α × ℝ | q.1 ∈ C ∧ -1 ≤ q.2 ∧ q.2 < σ q.1} := by
  let S : Set (α × ℝ) := C ×ˢ Set.Ico (0 : ℝ) 1
  let F : α × ℝ → α × ℝ := fun p => (p.1, -1 + p.2 * (σ p.1 + 1))
  have hS : IsPreconnected S := hC.prod isPreconnected_Ico
  have hσcont : ContinuousOn (fun p : α × ℝ => σ p.1) S :=
    hσ.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hF : ContinuousOn F S := by
    refine ContinuousOn.prodMk continuous_fst.continuousOn ?_
    refine continuousOn_const.add (continuous_snd.continuousOn.mul ?_)
    exact hσcont.add continuousOn_const
  have himg : IsPreconnected (F '' S) := hS.image F hF
  have heq : F '' S = {q : α × ℝ | q.1 ∈ C ∧ -1 ≤ q.2 ∧ q.2 < σ q.1} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
      obtain ⟨hp2a, hp2b⟩ := hp2
      have hs : -1 < σ p.1 := hσ1 p.1 hp1
      refine ⟨hp1, ?_, ?_⟩
      · nlinarith [hp2a, hs]
      · nlinarith [hp2a, hp2b, hs]
    · rintro ⟨hq1, hq2a, hq2b⟩
      have hs : -1 < σ q.1 := hσ1 q.1 hq1
      refine ⟨(q.1, (q.2 + 1) / (σ q.1 + 1)), ?_, ?_⟩
      · refine ⟨hq1, ?_, ?_⟩
        · exact div_nonneg (by linarith) (by linarith)
        · rw [div_lt_one (by linarith : (0 : ℝ) < σ q.1 + 1)]
          linarith
      · refine Prod.ext rfl ?_
        simp only [F]
        rw [div_mul_cancel₀ _ (by linarith : σ q.1 + 1 ≠ 0)]
        ring
  rw [← heq]
  exact himg

end Work.WilE7.BelowAux
