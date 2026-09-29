import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Scale.lyapAvg_lipschitz

namespace Work.TMC7Core.Scale

open Work.TMC7Core

/-- Purely numerical core: from the two margins `m1 = A - 100κ`, `m2 = B - (9/10)A` and the
Lipschitz estimates `|A - A'| ≤ K·2η`, `|B - B'| ≤ K·2η`, with `η ≤ mᵢ/(8K)`, both level
conditions persist. -/
theorem persists_pair_step (κ A A' B B' η K m1 m2 : ℝ)
    (hm1 : m1 = A - 100 * κ) (hm2 : m2 = B - (9 / 10) * A)
    (hm1pos : 0 < m1) (hm2pos : 0 < m2) (hKpos : 0 < K)
    (hA : |A - A'| ≤ K * (2 * η)) (hB : |B - B'| ≤ K * (2 * η))
    (hηm1 : η ≤ m1 / (8 * K)) (hηm2 : η ≤ m2 / (8 * K)) :
    100 * κ < A' ∧ (9 / 10) * A' < B' := by
  have h8K : (0 : ℝ) < 8 * K := by linarith only [hKpos]
  have h1 : K * (2 * η) ≤ m1 / 4 := by
    have h' : η * (8 * K) ≤ m1 := (le_div_iff₀ h8K).mp hηm1
    nlinarith only [h']
  have h2 : K * (2 * η) ≤ m2 / 4 := by
    have h' : η * (8 * K) ≤ m2 := (le_div_iff₀ h8K).mp hηm2
    nlinarith only [h']
  have ha : A - A' ≤ K * (2 * η) := le_trans (le_abs_self _) hA
  have hb : B - B' ≤ K * (2 * η) := le_trans (le_abs_self _) hB
  have hAe : A = m1 + 100 * κ := by linarith only [hm1]
  have hA'e : A' - A ≤ K * (2 * η) := by
    calc A' - A = -(A - A') := by ring
      _ ≤ |A - A'| := neg_le_abs _
      _ ≤ K * (2 * η) := hA
  constructor
  · linarith only [ha, h1, hAe, hm1pos]
  · nlinarith only [hA'e, hb, h2, hm2, hm2pos]

/-- Purely numerical core of the Diophantine condition: an open condition is stable. -/
theorem persists_frac_step (a : ℤ) (q : ℕ) (α α' m3 η : ℝ)
    (hm3 : m3 = 1 / ((q : ℝ) ^ 2) - |α - (a : ℝ) / (q : ℝ)|)
    (hm3pos : 0 < m3) (hηm3 : η ≤ m3 / 2) (hα' : |α' - α| < η) :
    |α' - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2) := by
  have hc : |α' - (a : ℝ) / (q : ℝ)| ≤ |α' - α| + |α - (a : ℝ) / (q : ℝ)| := by
    have e : α' - (a : ℝ) / (q : ℝ) = (α' - α) + (α - (a : ℝ) / (q : ℝ)) := by ring
    rw [e]; exact abs_add_le _ _
  have h3 : η < m3 := by linarith only [hηm3, hm3pos]
  rw [hm3] at h3
  linarith only [hc, h3, hα']

/-- **Persistence of the level pairing.**  If at `(α, E)` the `t`-scale average dominates the
barrier `100 κ` and the ratio condition `(9/10) L_t < L_{2t}` holds, and if moreover
`|α - a/q| < 1/q²`, then all three conditions persist on a whole neighbourhood of `(α, E)`.
This is purely a continuity (in fact Lipschitz) statement about the finite-scale averages. -/
theorem persists_level_pairing (lam : ℝ) (κ : ℝ) (hκ : 0 < κ) (α E : ℝ) (a : ℤ) (q : ℕ)
    (hq : 1 ≤ q) (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) (t : ℕ) (ht1 : 1 ≤ t)
    (hLt : 100 * κ < lyapAvg α lam (E : ℂ) t)
    (hpair : (9 / 10) * lyapAvg α lam (E : ℂ) t < lyapAvg α lam (E : ℂ) (2 * t)) :
    ∃ η : ℝ, 0 < η ∧ ∀ (α' E' : ℝ),
      |E' - E| < η → |α' - α| < η →
      100 * κ < lyapAvg α' lam (E' : ℂ) t ∧
      (9 / 10) * lyapAvg α' lam (E' : ℂ) t < lyapAvg α' lam (E' : ℂ) (2 * t) ∧
      |α' - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2) := by
  -- reference values, kept as opaque variables
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = lyapAvg α lam (E : ℂ) t := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = lyapAvg α lam (E : ℂ) (2 * t) := ⟨_, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m1 : ℝ, m1 = A - 100 * κ := ⟨_, rfl⟩
  have hm1pos : 0 < m1 := by rw [hm1]; linarith only [hLt, hA]
  obtain ⟨m2, hm2⟩ : ∃ m2 : ℝ, m2 = B - (9 / 10) * A := ⟨_, rfl⟩
  have hm2pos : 0 < m2 := by rw [hm2]; linarith only [hpair, hA, hB]
  obtain ⟨m3, hm3⟩ : ∃ m3 : ℝ, m3 = 1 / ((q : ℝ) ^ 2) - |α - (a : ℝ) / (q : ℝ)| := ⟨_, rfl⟩
  have hm3pos : 0 < m3 := by rw [hm3]; linarith only [hα]
  -- a bounded ball around (α, E)
  set R : ℝ := |α| + |E| + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  obtain ⟨K1, hK1pos, hK1⟩ := lyapAvg_lipschitz lam t ht1 R hRpos
  have h2t : 1 ≤ 2 * t := by omega
  obtain ⟨K2, hK2pos, hK2⟩ := lyapAvg_lipschitz lam (2 * t) h2t R hRpos
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max K1 K2 := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; exact lt_of_lt_of_le hK1pos (le_max_left _ _)
  have hK1le : K1 ≤ K := by rw [hK]; exact le_max_left _ _
  have hK2le : K2 ≤ K := by rw [hK]; exact le_max_right _ _
  -- the neighbourhood radius
  obtain ⟨η, hη⟩ : ∃ η : ℝ,
      η = min (min 1 (m3 / 2)) (min (m1 / (8 * K)) (m2 / (8 * K))) := ⟨_, rfl⟩
  have hηpos : 0 < η := by
    rw [hη]
    exact lt_min (lt_min one_pos (by linarith only [hm3pos]))
      (lt_min (div_pos hm1pos (by linarith only [hKpos]))
        (div_pos hm2pos (by linarith only [hKpos])))
  have hη1 : η ≤ 1 := by rw [hη]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hηm3 : η ≤ m3 / 2 := by rw [hη]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hηm1 : η ≤ m1 / (8 * K) := by
    rw [hη]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hηm2 : η ≤ m2 / (8 * K) := by
    rw [hη]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨η, hηpos, ?_⟩
  intro α' E' hE' hα'
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = lyapAvg α' lam (E' : ℂ) t := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ, B' = lyapAvg α' lam (E' : ℂ) (2 * t) := ⟨_, rfl⟩
  -- membership in the ball
  have hαR : |α| ≤ R := by rw [hRdef]; linarith only [abs_nonneg E]
  have hER : |E| ≤ R := by rw [hRdef]; linarith only [abs_nonneg α]
  have hα'R : |α'| ≤ R := by
    have h1 : |α'| - |α| ≤ |α' - α| := abs_sub_abs_le_abs_sub α' α
    have h2 : |α'| < |α| + η := by linarith only [h1, hα']
    rw [hRdef]; linarith only [h2, hη1, abs_nonneg E]
  have hE'R : |E'| ≤ R := by
    have h1 : |E'| - |E| ≤ |E' - E| := abs_sub_abs_le_abs_sub E' E
    have h2 : |E'| < |E| + η := by linarith only [h1, hE']
    rw [hRdef]; linarith only [h2, hη1, abs_nonneg α]
  have hdist : |α - α'| + |E - E'| < 2 * η := by
    have ha : |α - α'| < η := by rw [abs_sub_comm]; exact hα'
    have he : |E - E'| < η := by rw [abs_sub_comm]; exact hE'
    linarith only [ha, he]
  have hdist0 : 0 ≤ |α - α'| + |E - E'| := by positivity
  -- Lipschitz estimates at the two scales
  have hAt : |A - A'| ≤ K * (2 * η) := by
    have h1 : |lyapAvg α lam (E : ℂ) t - lyapAvg α' lam (E' : ℂ) t|
        ≤ K1 * (|α - α'| + |E - E'|) := hK1 α E α' E' hαR hER hα'R hE'R
    have h2 : |A - A'| = |lyapAvg α lam (E : ℂ) t - lyapAvg α' lam (E' : ℂ) t| := by
      rw [hA, hA']
    rw [h2]
    calc |lyapAvg α lam (E : ℂ) t - lyapAvg α' lam (E' : ℂ) t|
        ≤ K1 * (|α - α'| + |E - E'|) := h1
      _ ≤ K * (|α - α'| + |E - E'|) := mul_le_mul_of_nonneg_right hK1le hdist0
      _ ≤ K * (2 * η) := mul_le_mul_of_nonneg_left (le_of_lt hdist) (le_of_lt hKpos)
  have hBt : |B - B'| ≤ K * (2 * η) := by
    have h1 : |lyapAvg α lam (E : ℂ) (2 * t) - lyapAvg α' lam (E' : ℂ) (2 * t)|
        ≤ K2 * (|α - α'| + |E - E'|) := hK2 α E α' E' hαR hER hα'R hE'R
    have h2 : |B - B'| = |lyapAvg α lam (E : ℂ) (2 * t) - lyapAvg α' lam (E' : ℂ) (2 * t)| := by
      rw [hB, hB']
    rw [h2]
    calc |lyapAvg α lam (E : ℂ) (2 * t) - lyapAvg α' lam (E' : ℂ) (2 * t)|
        ≤ K2 * (|α - α'| + |E - E'|) := h1
      _ ≤ K * (|α - α'| + |E - E'|) := mul_le_mul_of_nonneg_right hK2le hdist0
      _ ≤ K * (2 * η) := mul_le_mul_of_nonneg_left (le_of_lt hdist) (le_of_lt hKpos)
  obtain ⟨g1, g2⟩ :=
    persists_pair_step κ A A' B B' η K m1 m2 hm1 hm2 hm1pos hm2pos hKpos hAt hBt hηm1 hηm2
  exact ⟨by rw [← hA']; exact g1,
    by rw [← hA', ← hB']; exact g2,
    persists_frac_step a q α α' m3 η hm3 hm3pos hηm3 hα'⟩

end Work.TMC7Core.Scale
