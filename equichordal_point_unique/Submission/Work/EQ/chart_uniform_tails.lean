import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.tail_uniform_of_isPreconnected
import Submission.Work.Analysis.Complex.punctured_ball_connected

namespace Work.EQ

open Filter _root_.Topology

/-- The punctured disc `ball 0 δ \ {0}` in `ℂ` is connected, for `δ > 0`. -/
lemma isConnected_punctured_ball_zero {δ : ℝ} (hδ : 0 < δ) :
    IsConnected (Metric.ball (0 : ℂ) δ \ {0}) := by
  have h := Work.Analysis.Complex.isConnected_punctured_ball_at (0 : ℂ) hδ
  have hset : {z : ℂ | 0 < ‖z - 0‖ ∧ ‖z - 0‖ < δ} = Metric.ball (0 : ℂ) δ \ {0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, Set.mem_sdiff,
      Set.mem_singleton_iff, sub_zero]
    exact ⟨fun h => ⟨h.2, norm_pos_iff.mp h.1⟩, fun h => ⟨norm_pos_iff.mpr h.2, h.1⟩⟩
  rwa [hset] at h

theorem chart_uniform_tails {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {u₀ : ℂ} {k : ℕ}
    (he : IsPuncturedChart a h e u₀ k)
    (hB : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ B : ℝ, ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < δ → ‖(e ζ).2.2‖ ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ N : ℕ, ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < δ →
      (∀ n : ℕ, N ≤ n → (e ζ).1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * (e ζ).2.1)) ∧
      (∀ n : ℕ, N ≤ n → (e ζ).1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * (e ζ).2.2)) := by
  obtain ⟨δB, hδBpos, hδBle, B, hBnd⟩ := hB
  obtain ⟨hkk, hu₀, κ, hκ0, hchart, hInj, hCont, hMer, hMern⟩ := he
  set δ : ℝ := min δB 1 with hδdef
  have hδ0 : 0 < δ := lt_min hδBpos one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδB : δ ≤ δB := min_le_left _ _
  set Bt : ℝ := max B (‖u₀‖ + ‖κ‖) with hBtdef
  have hballsub : Metric.ball (0 : ℂ) δ \ {0} ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
    intro z hz
    refine ⟨?_, hz.2⟩
    have h1 : ‖z‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hz.1
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using lt_of_lt_of_le h1 hδ1
  refine ⟨δ, hδ0, hδ1, ?_⟩
  obtain ⟨N, hN⟩ := tail_uniform_of_isPreconnected ha0 ha1 hh
    ((isConnected_punctured_ball_zero hδ0).image e (hCont.mono hballsub)).isPreconnected
    (by
      intro q hq
      obtain ⟨ζ, hζ, rfl⟩ := hq
      exact (hchart ζ (hballsub hζ)).1)
    (by
      intro q hq
      obtain ⟨ζ, hζ, rfl⟩ := hq
      have hζlt : ‖ζ‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hζ.1
      rw [(hchart ζ (hballsub hζ)).2]
      have h1 : ‖ζ ^ k‖ ≤ 1 := by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (le_of_lt (lt_of_lt_of_le hζlt hδ1))
      calc ‖u₀ + κ * ζ ^ k‖ ≤ ‖u₀‖ + ‖κ * ζ ^ k‖ := norm_add_le _ _
        _ = ‖u₀‖ + ‖κ‖ * ‖ζ ^ k‖ := by rw [norm_mul]
        _ ≤ ‖u₀‖ + ‖κ‖ := by
              have h2 : ‖κ‖ * ‖ζ ^ k‖ ≤ ‖κ‖ * 1 :=
                mul_le_mul_of_nonneg_left h1 (norm_nonneg κ)
              linarith
        _ ≤ Bt := le_max_right _ _)
    (by
      intro q hq
      obtain ⟨ζ, hζ, rfl⟩ := hq
      have hζlt : ‖ζ‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hζ.1
      exact le_trans (hBnd ζ (norm_pos_iff.mpr hζ.2) (lt_of_lt_of_le hζlt hδB))
        (le_max_left _ _))
  refine ⟨N, ?_⟩
  intro ζ hζ0 hζlt
  have hζmem : ζ ∈ Metric.ball (0 : ℂ) δ \ {0} :=
    ⟨by rw [Metric.mem_ball, dist_eq_norm]; simpa using hζlt, norm_pos_iff.mp hζ0⟩
  have hq := hN (e ζ) ⟨ζ, hζmem, rfl⟩
  exact ⟨fun n hn => (hq n hn).1, fun n hn => (hq n hn).2⟩

end Work.EQ
