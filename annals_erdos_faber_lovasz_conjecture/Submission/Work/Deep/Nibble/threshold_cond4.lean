import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.threshold_tools

namespace Work.Deep.Nibble

/-- **Clause 4 of the asymptotic side conditions of `cor:sparse_egj`** (threshold form).
For every `E > 0` and `κ > 0` there is `N > 0` such that for all `n ≥ N` and all
`D ≥ n^{1/100}` one has `2 n D ≤ exp(((1+κ)D)^E)`.

Route: by `Real.log_le_iff_le_exp` it suffices that `log 2 + log n + log D ≤ ((1+κ)D)^E`.
From `n^{1/100} ≤ D` get `n ≤ D^100` (raise to the power `100`), hence `log n ≤ 100 log D`.
With `Work.Deep.Nibble.log_le_two_div` (`log D ≤ (2/E) D^(E/2)` for `D ≥ 1`:
`E/2 * log D ≤ D^(E/2)` from `Real.log_le_sub_one_of_pos` on `log(D^(E/2))`) one gets
`log 2 + 101 log D ≤ (202/E + log 2) * D^(E/2)`, and `((1+κ)D)^E ≥ D^E = D^(E/2) * D^(E/2)`,
so it suffices that `202/E + log 2 ≤ D^(E/2)`, i.e. it suffices to take
`N := (202/E + Real.log 2) ^ (200/E)` (since `D^(E/2) ≥ (n^{1/100})^(E/2) = n^(E/200)`). -/
theorem threshold_cond4 {E κ : ℝ} (hE : 0 < E) (hκ : 0 < κ) :
    ∃ N : ℝ, 0 < N ∧ ∀ n : ℕ, N ≤ (n : ℝ) → ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      2 * (n : ℝ) * D ≤ Real.exp (((1 + κ) * D) ^ E) := by
  -- The threshold constant `L = log 2 + 101 * (2/E)` and the threshold `N = L^(200/E) + 1`.
  set L : ℝ := Real.log 2 + 101 * (2 / E) with hLdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2divE : 0 < 2 / E := div_pos (by norm_num) hE
  have hLpos : 0 < L := by
    rw [hLdef]
    have h101 : 0 < 101 * (2 / E) := mul_pos (by norm_num) h2divE
    linarith
  have hLnn : (0 : ℝ) ≤ L := hLpos.le
  have hEne : E ≠ 0 := ne_of_gt hE
  refine ⟨L ^ (200 / E) + 1, ?_, ?_⟩
  · have hnn : (0 : ℝ) ≤ L ^ (200 / E) := Real.rpow_nonneg hLnn _
    linarith
  · intro n hnN D hnD
    -- elementary consequences of the two threshold hypotheses
    have hLrpow_nn : (0 : ℝ) ≤ L ^ (200 / E) := Real.rpow_nonneg hLnn _
    have hLrpow_pos : 0 < L ^ (200 / E) + 1 := by linarith
    have hN1 : (1 : ℝ) ≤ L ^ (200 / E) + 1 := by linarith
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := hN1.trans hnN
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := hnpos.le
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hD1 : 1 ≤ D := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := by
        have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hn1
          (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 100)
        rwa [Real.one_rpow] at h
      exact h1.trans hnD
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
    have hDnn : (0 : ℝ) ≤ D := hDpos.le
    have hDne : D ≠ 0 := ne_of_gt hDpos
    have hE2pos : 0 < E / 2 := div_pos hE (by norm_num)
    have hE2nn : (0 : ℝ) ≤ E / 2 := hE2pos.le
    have hE200pos : 0 < E / 200 := div_pos hE (by norm_num)
    -- (1) `log n ≤ 100 * log D`
    have hlogn : Real.log (n : ℝ) ≤ 100 * Real.log D := by
      have h := Real.log_le_log (Real.rpow_pos_of_pos hnpos _) hnD
      rw [Real.log_rpow hnpos] at h
      have h2 : (100 : ℝ) * ((1 : ℝ) / 100 * Real.log (n : ℝ)) ≤ 100 * Real.log D :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      have h3 : (100 : ℝ) * ((1 : ℝ) / 100 * Real.log (n : ℝ)) = Real.log (n : ℝ) := by
        rw [← mul_assoc, show (100 : ℝ) * ((1 : ℝ) / 100) = 1 from by norm_num, one_mul]
      rwa [h3] at h2
    -- (2) `log D ≤ (2/E) * D^(E/2)`
    have hlogD : Real.log D ≤ (2 / E) * D ^ (E / 2) := log_le_two_div hE hD1
    -- (3) `1 ≤ D^(E/2)`
    have hX1 : (1 : ℝ) ≤ D ^ (E / 2) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hD1 hE2nn
      rwa [Real.one_rpow] at h
    have hXnn : (0 : ℝ) ≤ D ^ (E / 2) := le_trans zero_le_one hX1
    -- (4) `L ≤ D^(E/2)`
    have hLD : L ≤ D ^ (E / 2) := by
      have hLpow : (L ^ (200 / E)) ^ (E / 200) = L := by
        rw [← Real.rpow_mul hLnn, show (200 : ℝ) / E * (E / 200) = 1 by field_simp,
          Real.rpow_one]
      rw [← hLpow]
      have hstep1 : (L ^ (200 / E)) ^ (E / 200) ≤ (L ^ (200 / E) + 1) ^ (E / 200) :=
        Real.rpow_le_rpow hLrpow_nn (by linarith) hE200pos.le
      have hstep2 : (L ^ (200 / E) + 1) ^ (E / 200) ≤ (n : ℝ) ^ (E / 200) :=
        Real.rpow_le_rpow hLrpow_pos.le hnN hE200pos.le
      have hstep3 : (n : ℝ) ^ (E / 200) ≤ D ^ (E / 2) := by
        rw [show E / 200 = (1 : ℝ) / 100 * (E / 2) by
              rw [div_mul_div_comm, one_mul, show (100 : ℝ) * 2 = 200 from by norm_num],
          Real.rpow_mul hn0]
        exact Real.rpow_le_rpow (Real.rpow_pos_of_pos hnpos _).le hnD hE2nn
      exact hstep1.trans (hstep2.trans hstep3)
    -- (5) the logarithmic comparison
    have hchain1 : Real.log 2 + Real.log (n : ℝ) + Real.log D
        ≤ Real.log 2 * D ^ (E / 2) + 101 * ((2 / E) * D ^ (E / 2)) := by
      have hA : Real.log (n : ℝ) + Real.log D ≤ 100 * Real.log D + (2 / E) * D ^ (E / 2) :=
        add_le_add hlogn hlogD
      have hB : 100 * Real.log D + (2 / E) * D ^ (E / 2)
          ≤ 101 * ((2 / E) * D ^ (E / 2)) := by
        have h1 : 100 * Real.log D ≤ 100 * ((2 / E) * D ^ (E / 2)) :=
          mul_le_mul_of_nonneg_left hlogD (by norm_num)
        calc 100 * Real.log D + (2 / E) * D ^ (E / 2)
            = 100 * Real.log D + 1 * ((2 / E) * D ^ (E / 2)) := by rw [one_mul]
          _ ≤ 100 * ((2 / E) * D ^ (E / 2)) + 1 * ((2 / E) * D ^ (E / 2)) :=
              add_le_add h1 le_rfl
          _ = 101 * ((2 / E) * D ^ (E / 2)) := by ring
      have hC : Real.log 2 ≤ Real.log 2 * D ^ (E / 2) := by
        calc Real.log 2 = Real.log 2 * 1 := (mul_one _).symm
          _ ≤ Real.log 2 * D ^ (E / 2) := mul_le_mul_of_nonneg_left hX1 hlog2.le
      calc Real.log 2 + Real.log (n : ℝ) + Real.log D
          = Real.log 2 + (Real.log (n : ℝ) + Real.log D) := by ring
        _ ≤ Real.log 2 * D ^ (E / 2) + (100 * Real.log D + (2 / E) * D ^ (E / 2)) :=
            add_le_add hC hA
        _ ≤ Real.log 2 * D ^ (E / 2) + 101 * ((2 / E) * D ^ (E / 2)) :=
            add_le_add le_rfl hB
    -- (6) split the logarithm and conclude
    have hsplit : Real.log (2 * (n : ℝ) * D)
        = Real.log 2 + Real.log (n : ℝ) + Real.log D := by
      rw [Real.log_mul (mul_ne_zero (by norm_num) hnne) hDne,
        Real.log_mul (by norm_num) hnne]
    have hmain : Real.log (2 * (n : ℝ) * D) ≤ ((1 + κ) * D) ^ E := by
      rw [hsplit]
      calc Real.log 2 + Real.log (n : ℝ) + Real.log D
          ≤ Real.log 2 * D ^ (E / 2) + 101 * ((2 / E) * D ^ (E / 2)) := hchain1
        _ = L * D ^ (E / 2) := by rw [hLdef]; ring
        _ ≤ D ^ (E / 2) * D ^ (E / 2) := mul_le_mul_of_nonneg_right hLD hXnn
        _ = D ^ E := by rw [← Real.rpow_add hDpos, add_halves]
        _ ≤ ((1 + κ) * D) ^ E :=
            Real.rpow_le_rpow hDnn (le_mul_of_one_le_left hDnn (by linarith)) hE.le
    have h2nD : 0 < 2 * (n : ℝ) * D := mul_pos (mul_pos (by norm_num) hnpos) hDpos
    exact (Real.log_le_iff_le_exp h2nD).mp hmain

end Work.Deep.Nibble
