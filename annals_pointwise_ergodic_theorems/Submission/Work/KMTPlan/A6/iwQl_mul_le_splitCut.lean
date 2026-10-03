import Mathlib
import Submission.Work.KMTAreas.A7.Split

namespace Work.KMTPlan.A6

/-!
# The doubly exponential cut dominates `24 · Q_{≤l}`

The scale split of the paper's §7/§8 (`Work.KMTAreas.A7.splitCut`) cuts the admissible scales at
the doubly exponential threshold

  `splitCut ρ L = 2 ^ (2 ^ (scaleCount 1 ρ L))`,  `scaleCount 1 ρ L = ⌊2 ^ (2ρL)⌋`.

For the small-scale regime one has to know that this threshold eventually dominates the common
denominator `Q_{≤l} = iwQl ρ l` of the Ionescu–Wainger frequency set, *uniformly for all
`l ≤ L`*: this is the content of `iwQl_mul_le_splitCut` below.

The proof is the comparison of two exponentials.  Appendix A bounds
`iwQl ρ l ≤ 2 ^ (C · 2 ^ l)` (`Work.Analysis.IonescuWainger.iwQl_le`), so that for `l ≤ L`

  `24 · iwQl ρ l ≤ 2 ^ 5 · 2 ^ (C · 2 ^ L) = 2 ^ (5 + C · 2 ^ L) ≤ 2 ^ ((5 + C) · 2 ^ L)`

(using `2 ^ L ≥ 1`).  Since `scaleCount` grows like `2 ^ (2ρL)`, it satisfies
`scaleCount 1 ρ L ≥ L + K` for every fixed `K` once `L` is large (`2 ^ (2ρL)` eventually beats the
linear function `L + K`, the only limit statement in the proof), so choosing `K` with
`2 ^ K ≥ 5 + C` we conclude

  `2 ^ ((5 + C) · 2 ^ L) ≤ 2 ^ (2 ^ K · 2 ^ L) = 2 ^ (2 ^ (L + K)) ≤ 2 ^ (2 ^ scaleCount 1 ρ L)`

for all large `L`.  Note that no hypothesis `ρ > 1/2` is needed: the inner exponent `2 ^ (2ρL)`
grows exponentially with *any* positive rate `2ρ > 0`, which is enough to beat the linear bound
`L + K` demanded by the `2 ^ (·)` of the outer exponent. -/

/-- **Exponential beats linear.**  `2 ^ (2ρL)` eventually dominates the linear function `L + K`. -/
private lemma exists_nat_le_two_rpow (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) :
    ∃ L₁ : ℕ, ∀ L : ℕ, L₁ ≤ L → ((L + K : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβ : 0 < 2 * ρ * Real.log 2 := by positivity
  -- `exp` beats `id`: `exp z / z → ∞`
  have hz : Filter.Tendsto (fun z : ℝ => Real.exp z / z) Filter.atTop Filter.atTop := by
    simpa using Real.tendsto_exp_div_pow_atTop 1
  have hev := hz.eventually_ge_atTop (((K : ℝ) + 1) / (2 * ρ * Real.log 2))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨Y, hY⟩ := hev
  refine ⟨max 1 ⌈Y / (2 * ρ * Real.log 2)⌉₊, ?_⟩
  intro L hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  -- `2ρL` is past the threshold `Y`
  have hLY : Y ≤ (L : ℝ) * (2 * ρ * Real.log 2) := by
    have h2 : ⌈Y / (2 * ρ * Real.log 2)⌉₊ ≤ L := le_trans (le_max_right _ _) hL
    have h3 : Y / (2 * ρ * Real.log 2) ≤ (L : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast h2)
    have h4 := mul_le_mul_of_nonneg_right h3 hβ.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hβ)] at h4
  -- hence `(K+1)/β · (Lβ) ≤ exp (Lβ)`, and `(K+1)/β · (Lβ) = (K+1)L`
  have h := hY ((L : ℝ) * (2 * ρ * Real.log 2)) hLY
  rw [le_div_iff₀ (mul_pos (by exact_mod_cast hL1 : (0 : ℝ) < L) hβ)] at h
  have hsimp : ((K : ℝ) + 1) / (2 * ρ * Real.log 2) * ((L : ℝ) * (2 * ρ * Real.log 2))
      = ((K : ℝ) + 1) * (L : ℝ) := by
    field_simp
  rw [hsimp] at h
  -- `exp (2ρL log 2) = 2 ^ (2ρL)`
  have hexp : Real.exp ((L : ℝ) * (2 * ρ * Real.log 2)) = (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hexp] at h
  -- `L + K ≤ (K+1)L` because `L ≥ 1`
  have hLK : ((L + K : ℕ) : ℝ) ≤ ((K : ℝ) + 1) * (L : ℝ) := by
    rw [Nat.cast_add]
    have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith
  linarith

/-- The scale cut as a real number: `splitCut ρ L = 2 ^ (2 ^ scaleCount 1 ρ L)`, with the outer
`2 ^ (·)` read as a real power of the natural number `2 ^ scaleCount 1 ρ L`. -/
private lemma splitCut_cast_eq (ρ : ℝ) (L : ℕ) :
    ((Work.KMTAreas.A7.splitCut ρ L : ℕ) : ℝ)
      = (2 : ℝ) ^ ((2 : ℝ) ^ ((Work.Analysis.EndVar.scaleCount 1 ρ L : ℕ) : ℝ)) := by
  rw [Work.KMTAreas.A7.splitCut, Nat.cast_pow]
  push_cast
  rw [← Real.rpow_natCast (2 : ℝ) (2 ^ Work.Analysis.EndVar.scaleCount 1 ρ L)]
  congr 1
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]

/-- `scaleCount 1 ρ L = ⌊2 ^ (2ρL)⌋` with the outer floor read as `Nat.floor`. -/
private lemma scaleCount_one_floor (ρ : ℝ) (L : ℕ) :
    Work.Analysis.EndVar.scaleCount 1 ρ L = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ := by
  simp only [Work.Analysis.EndVar.scaleCount, Int.floor_toNat, Nat.cast_one, one_mul]

/-- The arithmetic of the A6 core: beyond a threshold `L₁` (depending on `ρ`), the *doubly
exponential* scale cut `splitCut ρ L = 2 ^ (2 ^ ⌊2 ^ (2ρL)⌋)` dominates `24 · iwQl ρ l` for every
`l ≤ L`.  This is what allows the decimation (large-scale) route to the low-pass variational
estimate on the A6 core scales. -/
theorem iwQl_mul_le_splitCut (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ L₁ : ℕ, ∀ (L l : ℕ), L₁ ≤ L → l ≤ L →
      24 * Work.Analysis.IonescuWainger.iwQl ρ l ≤ Work.KMTAreas.A7.splitCut ρ L := by
  -- `iwQl ρ l ≤ 2 ^ (C · 2 ^ l)` (Appendix A)
  obtain ⟨C, hCpos, hC⟩ := Work.Analysis.IonescuWainger.iwQl_le hρ hρ1
  -- `K` with `5 + C < 2 ^ K`
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (5 + C) (show (1 : ℝ) < 2 by norm_num)
  -- beyond `L₁`, `L + K ≤ 2 ^ (2ρL)`, hence `scaleCount 1 ρ L ≥ L + K`
  obtain ⟨L₁, hL₁⟩ := exists_nat_le_two_rpow ρ hρ K
  refine ⟨max L₁ 1, fun L l hL hl => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLK : ((L + K : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := hL₁ L hL1
  have hsc : L + K ≤ Work.Analysis.EndVar.scaleCount 1 ρ L := by
    rw [scaleCount_one_floor]
    exact Nat.le_floor hLK
  have hmono : (2 : ℝ) ^ (((L + K : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.scaleCount 1 ρ L : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hsc)
  have hKle : (5 + C) ≤ (2 : ℝ) ^ (K : ℝ) := by
    simpa [Real.rpow_natCast] using hK.le
  have hsplit : (2 : ℝ) ^ (((L + K : ℕ) : ℝ))
      = (2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (K : ℝ) := by
    rw [Nat.cast_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_natCast, Real.rpow_natCast]
  -- `(5 + C) · 2 ^ L ≤ 2 ^ (scaleCount 1 ρ L)`
  have h2s : (5 + C) * (2 : ℝ) ^ (L : ℝ)
      ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.scaleCount 1 ρ L : ℕ) : ℝ) := by
    calc (5 + C) * (2 : ℝ) ^ (L : ℝ) ≤ (2 : ℝ) ^ (K : ℝ) * (2 : ℝ) ^ (L : ℝ) :=
          mul_le_mul_of_nonneg_right hKle (by positivity)
      _ = (2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (K : ℝ) := by ring
      _ = (2 : ℝ) ^ (((L + K : ℕ) : ℝ)) := hsplit.symm
      _ ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.scaleCount 1 ρ L : ℕ) : ℝ) := hmono
  -- `24 · iwQl ρ l ≤ 2 ^ (5 + C · 2 ^ L) ≤ 2 ^ ((5 + C) · 2 ^ L) ≤ 2 ^ (2 ^ scaleCount)`
  have hmain : ((24 * Work.Analysis.IonescuWainger.iwQl ρ l : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ ((2 : ℝ) ^ ((Work.Analysis.EndVar.scaleCount 1 ρ L : ℕ) : ℝ)) := by
    have hl1 := hC l
    calc ((24 * Work.Analysis.IonescuWainger.iwQl ρ l : ℕ) : ℝ)
        = 24 * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ) := by push_cast; ring
      _ ≤ 24 * (2 : ℝ) ^ (C * (2 : ℝ) ^ (l : ℝ)) :=
          mul_le_mul_of_nonneg_left hl1 (by norm_num)
      _ ≤ (2 : ℝ) ^ (5 : ℝ) * (2 : ℝ) ^ (C * (2 : ℝ) ^ (l : ℝ)) := by
          have h24 : (24 : ℝ) ≤ (2 : ℝ) ^ (5 : ℝ) := by norm_num [Real.rpow_natCast]
          exact mul_le_mul_of_nonneg_right h24 (by positivity)
      _ = (2 : ℝ) ^ (5 + C * (2 : ℝ) ^ (l : ℝ)) :=
          (Real.rpow_add (by norm_num : (0 : ℝ) < 2) 5 (C * (2 : ℝ) ^ (l : ℝ))).symm
      _ ≤ (2 : ℝ) ^ (5 + C * (2 : ℝ) ^ (L : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          have h2l : (2 : ℝ) ^ (l : ℝ) ≤ (2 : ℝ) ^ (L : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by exact_mod_cast hl)
          have := mul_le_mul_of_nonneg_left h2l hCpos.le
          linarith
      _ ≤ (2 : ℝ) ^ ((5 + C) * (2 : ℝ) ^ (L : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          have h2L : (1 : ℝ) ≤ (2 : ℝ) ^ (L : ℝ) := Real.one_le_rpow (by norm_num) (by positivity)
          nlinarith
      _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ ((Work.Analysis.EndVar.scaleCount 1 ρ L : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h2s
  exact Nat.cast_le.mp (hmain.trans (le_of_eq (splitCut_cast_eq ρ L).symm))

end Work.KMTPlan.A6
