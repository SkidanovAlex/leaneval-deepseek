import Mathlib
import Submission.Work.Holonomy3.assembly_defs
import Submission.Work.Holonomy3.siegel
import Submission.Work.Holonomy3.sieve_err_bound
import Submission.Work.Holonomy3.log_succ_div_small

namespace Work.Holonomy3

set_option linter.unusedVariables false

/-- **The numeric sift of the fine holonomy bound.**

Given the constants of the problem (`G₀ B C₀ M' U₀ ≥ 0`, `M' ≥ 1`), a target accuracy `η₁ > 0`, a
threshold `ε₀ > 0` for the sieve parameter, the Shidlovsky constant `Csh : ℕ`, and the functions
`δf`, `d₀`, `D₀` produced by `Work.Holonomy3.siegel` (with `δf ε ∈ (0, ε)` for `0 < ε < 1`),
there are `ε ∈ (0, min ε₀ 1)`, `d` a multiple of `m` with `d₀ ε ≤ d`, and `D ≥ D₀ ε d` with
`(m + Csh + 1 : ℝ) ≤ δf ε * D` and
`Work.Holonomy3.sieveErr m l d D G₀ B C₀ M' U₀ ε (η₁ / (16 * m)) ≤ η₁`.

(Note `η := η₁/(16 m)`, as the reviewer of the previous version observed: the last summand of
`sieveErr` contributes `m·η` after cancelling the factor `2/(dD)`, so `η` must carry the factor
`1/m`.)

The proof is elementary: take `ε` small enough that the `ε`-terms of `sieveErr` are `≤ η₁/4` (only
`ε(2 + 2G₀ + 6mB)` remains after cancelling the `2/(dD)` factor), then `d ≥ max (d₀ ε) N₁` large
enough that the three `d`-terms are each `≤ η₁/32`, then `D ≥ max (D₀ ε d) N₂
⌈(m+Csh+2)/δf ε⌉` large enough that the six `D`-terms are each `≤ η₁/32`; the `m·η = η₁/16` from
the last summand and the `η₁/4` from the `ε`-terms then leave total room.  Use
`Work.Holonomy3.exists_div_le` (in `siegel.lean`) and `Real.isLittleO_log_id_atTop` (or
`Real.isLittleO_log_rpow_atTop` with `r = 1`) for the `log (D+1)/D` term. -/
theorem exists_sieve_params {m l : ℕ} (hm : 0 < m) {G₀ B C₀ M' U₀ : ℝ}
    (hG₀ : 0 ≤ G₀) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hU₀ : 0 ≤ U₀) (hM' : 1 ≤ M')
    {η₁ : ℝ} (hη₁ : 0 < η₁) {ε₀ : ℝ} (hε₀ : 0 < ε₀) {Csh : ℕ}
    {δf : ℝ → ℝ} (hδ0 : ∀ ε, 0 < ε → ε < 1 → 0 < δf ε)
    (hδlt : ∀ ε, 0 < ε → ε < 1 → δf ε < ε)
    {d₀ : ℝ → ℕ} {D₀ : ℝ → ℕ → ℕ} :
    ∃ (ε : ℝ) (d D : ℕ), 0 < ε ∧ ε < 1 ∧ ε < ε₀ ∧ 0 < d ∧ m ∣ d ∧ d₀ ε ≤ d ∧
      0 < D ∧ D₀ ε d ≤ D ∧ ((m : ℝ) + (Csh : ℝ) + 1 ≤ δf ε * D) ∧
      Work.Holonomy3.sieveErr m l d D G₀ B C₀ M' U₀ ε (η₁ / (16 * (m : ℝ))) ≤ η₁ := by
  -- ═══ the constant of the `ε`-group and the choice of `ε`
  set K : ℝ := 2 + 2 * G₀ + 6 * ((m : ℝ) * B) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    positivity
  set ε : ℝ := min (min (ε₀ / 2) (1 / 2)) (η₁ / (4 * (K + 1))) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (lt_min (by linarith) (by norm_num)) (by positivity)
  have hεlt1 : ε < 1 := by
    rw [hεdef]
    have h : min (min (ε₀ / 2) (1 / 2)) (η₁ / (4 * (K + 1))) ≤ 1 / 2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hεlte₀ : ε < ε₀ := by
    rw [hεdef]
    have h : min (min (ε₀ / 2) (1 / 2)) (η₁ / (4 * (K + 1))) ≤ ε₀ / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hεK : ε * K ≤ η₁ / 4 := by
    have h1 : ε ≤ η₁ / (4 * (K + 1)) := by rw [hεdef]; exact min_le_right _ _
    have hpos : 0 < 4 * (K + 1) := by linarith
    calc ε * K ≤ (η₁ / (4 * (K + 1))) * K := mul_le_mul_of_nonneg_right h1 hKnn
      _ = η₁ * (K / (4 * (K + 1))) := by ring
      _ ≤ η₁ * (1 / 4) := by
          apply mul_le_mul_of_nonneg_left _ hη₁.le
          rw [div_le_iff₀ hpos]; linarith [hKnn]
      _ = η₁ / 4 := by ring
  rw [hKdef] at hεK
  -- ═══ the common budget `η' = η₁/32` for the `d`- and `D`-terms
  set η' : ℝ := η₁ / 32 with hη'def
  have hη'pos : 0 < η' := by rw [hη'def]; positivity
  -- ═══ the four `d`-thresholds
  obtain ⟨Nr1, hNr1⟩ := exists_div_le (B := G₀ * (16 * ((l : ℝ) + 1) ^ 2 + 1)) (by positivity) hη'pos
  obtain ⟨Nr2, hNr2⟩ := exists_div_le (B := 2 * G₀) (by positivity) hη'pos
  obtain ⟨Nr3, hNr3⟩ := exists_div_le (B := 32 * ((m : ℝ) * B) * ((l : ℝ) + 1)) (by positivity) hη'pos
  obtain ⟨Nr4, hNr4⟩ := exists_div_le (B := 2 * Real.log 2)
    (by have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); linarith) hη'pos
  -- ═══ the choice of `d`: a large multiple of `m`, at least `d₀ ε`
  set N : ℕ := Nr1 + Nr2 + Nr3 + Nr4 + 1 + d₀ ε with hNdef
  have hNpos : 0 < N := by rw [hNdef]; omega
  set d : ℕ := m * N with hddef
  have hdpos : 0 < d := by rw [hddef]; exact Nat.mul_pos hm hNpos
  have hdge : N ≤ d := by rw [hddef]; exact Nat.le_mul_of_pos_left N hm
  have hdNr1 : Nr1 ≤ d := le_trans (by rw [hNdef]; omega) hdge
  have hdNr2 : Nr2 ≤ d := le_trans (by rw [hNdef]; omega) hdge
  have hdNr3 : Nr3 ≤ d := le_trans (by rw [hNdef]; omega) hdge
  have hdNr4 : Nr4 ≤ d := le_trans (by rw [hNdef]; omega) hdge
  have hdd₀ : d₀ ε ≤ d := le_trans (by rw [hNdef]; omega) hdge
  have hdvd : m ∣ d := ⟨N, hddef⟩
  -- ═══ the six `D`-thresholds
  obtain ⟨Mr1, hMr1⟩ := log_succ_div_small hη'pos
  obtain ⟨Mr2, hMr2⟩ := exists_div_le (B := 2 * Real.log (m : ℝ))
    (by have h : (1 : ℝ) ≤ m := by exact_mod_cast hm
        have := Real.log_nonneg h; linarith) hη'pos
  obtain ⟨Mr3, hMr3⟩ := exists_div_le (B := 2 * Real.log M')
    (by have := Real.log_nonneg hM'; linarith) hη'pos
  obtain ⟨Mr4, hMr4⟩ := exists_div_le (B := 4 * G₀) (by positivity) hη'pos
  obtain ⟨Mr5, hMr5⟩ := exists_div_le (B := 2 * ((m : ℝ) * B)) (by positivity) hη'pos
  obtain ⟨Mr6, hMr6⟩ := exists_div_le (B := 2 * (C₀ + U₀)) (by positivity) hη'pos
  -- ═══ the choice of `D`
  set M : ℕ := Mr1 + Mr2 + Mr3 + Mr4 + Mr5 + Mr6 + 1 with hMdef
  set DC : ℕ := Nat.ceil (((m : ℝ) + (Csh : ℝ) + 2) / δf ε) with hDCdef
  set D : ℕ := D₀ ε d + M + DC + 1 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; omega
  have hD1 : 1 ≤ D := by rw [hDdef]; omega
  have hDB : D₀ ε d ≤ D := by rw [hDdef]; omega
  have hDM : M ≤ D := by rw [hDdef]; omega
  have hDDC : DC ≤ D := by rw [hDdef]; omega
  have hMr1' : Mr1 ≤ D := le_trans (by rw [hMdef]; omega) hDM
  have hMr2' : Mr2 ≤ D := le_trans (by rw [hMdef]; omega) hDM
  have hMr3' : Mr3 ≤ D := le_trans (by rw [hMdef]; omega) hDM
  have hMr4' : Mr4 ≤ D := le_trans (by rw [hMdef]; omega) hDM
  have hMr5' : Mr5 ≤ D := le_trans (by rw [hMdef]; omega) hDM
  have hMr6' : Mr6 ≤ D := le_trans (by rw [hMdef]; omega) hDM
  -- ═══ the Shidlovsky condition `m + Csh + 1 ≤ δf ε · D`
  have hδpos : 0 < δf ε := hδ0 ε hεpos hεlt1
  have hCsh : (m : ℝ) + (Csh : ℝ) + 1 ≤ δf ε * D := by
    have h1 : ((m : ℝ) + (Csh : ℝ) + 2) / δf ε ≤ (DC : ℝ) := by
      rw [hDCdef]; exact Nat.le_ceil _
    have h2 : (DC : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDDC
    have h3 : ((m : ℝ) + (Csh : ℝ) + 2) / δf ε ≤ (D : ℝ) := le_trans h1 h2
    have h4 := mul_le_mul_of_nonneg_left h3 hδpos.le
    have h5 : δf ε * (((m : ℝ) + (Csh : ℝ) + 2) / δf ε) = (m : ℝ) + (Csh : ℝ) + 2 := by
      field_simp
    rw [h5] at h4
    linarith
  -- ═══ assembly
  refine ⟨ε, d, D, hεpos, hεlt1, hεlte₀, hdpos, hdvd, hdd₀, hDpos, hDB, hCsh, ?_⟩
  refine sieve_err_bound hm hdpos hD1 hG₀ hB (le_of_lt hεpos) hη₁ hεK ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  · have := hNr1 d hdNr1; rwa [hη'def] at this
  · have := hNr2 d hdNr2; rwa [hη'def] at this
  · have := hNr3 d hdNr3; rwa [hη'def] at this
  · have := hNr4 d hdNr4; rwa [hη'def] at this
  · have := hMr1 D hMr1'; rwa [hη'def] at this
  · have := hMr2 D hMr2'; rwa [hη'def] at this
  · have := hMr3 D hMr3'; rwa [hη'def] at this
  · have := hMr4 D hMr4'; rwa [hη'def] at this
  · have := hMr5 D hMr5'; rwa [hη'def] at this
  · have := hMr6 D hMr6'; rwa [hη'def] at this

end Work.Holonomy3
