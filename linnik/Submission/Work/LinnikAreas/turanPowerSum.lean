import Mathlib
import Submission.Work.LinnikAreas.turanFejerComplex
import Submission.Work.LinnikAreas.turanPerTerm
import Submission.Work.LinnikAreas.turanPerTermZero
import Submission.Work.LinnikAreas.summableNormOfWeyl
import Submission.Work.LinnikAreas.summablePowOfWeyl

namespace Work.LinnikAreas

open scoped BigOperators

/-! ### Elementary estimates -/

lemma fejerWeight_nonneg {J j : ℕ} (hj : j ≤ J) : 0 ≤ 1 - (j : ℝ) / (J + 1) := by
  have h : (j : ℝ) ≤ (J : ℝ) + 1 := by
    have h' : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj
    linarith
  have hd : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  rw [sub_nonneg, div_le_one hd]
  exact h

lemma pow_le_self_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {j : ℕ} (hj : 1 ≤ j) :
    x ^ j ≤ x := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : x ^ k ≤ 1 := pow_le_one₀ hx0 hx1
  rw [pow_succ]
  calc x ^ k * x ≤ 1 * x := mul_le_mul_of_nonneg_right hk hx0
    _ = x := one_mul x

lemma norm_pow_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) {j : ℕ} (hj : 1 ≤ j) : ‖z ^ j‖ ≤ 1 := by
  rw [Complex.norm_pow]
  exact pow_le_one₀ (norm_nonneg z) hz

lemma re_bounds {z : ℂ} (hz : ‖z‖ ≤ 1) : -1 ≤ z.re ∧ z.re ≤ 1 := by
  have h := Complex.abs_re_le_norm z
  rw [abs_le] at h
  exact ⟨by linarith [h.1, hz], by linarith [h.2, hz]⟩

/-- Absolute value bound for a single term of the double sum behind the power-sum method. -/
lemma term_abs_bound {J : ℕ} {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) {j : ℕ}
    (hj1 : 1 ≤ j) (hjJ : j ≤ J) :
    |(1 - (j : ℝ) / (J + 1)) * ((u ^ j).re * (1 + (v ^ j).re))| ≤ 2 * ‖u‖ := by
  have hw0 : 0 ≤ 1 - (j : ℝ) / (J + 1) := fejerWeight_nonneg hjJ
  have hw1 : 1 - (j : ℝ) / (J + 1) ≤ 1 := by
    have : 0 ≤ (j : ℝ) / (J + 1) := by positivity
    linarith
  have ha : |(u ^ j).re| ≤ ‖u‖ := by
    calc |(u ^ j).re| ≤ ‖u ^ j‖ := Complex.abs_re_le_norm _
      _ = ‖u‖ ^ j := Complex.norm_pow u j
      _ ≤ ‖u‖ := pow_le_self_one (norm_nonneg u) hu hj1
  have hb : |1 + (v ^ j).re| ≤ 2 := by
    have h := re_bounds (norm_pow_le_one hv hj1)
    rw [abs_le]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hw : |1 - (j : ℝ) / (J + 1)| ≤ 1 := by
    rw [abs_of_nonneg hw0]; exact hw1
  rw [abs_mul, abs_mul]
  calc |1 - (j : ℝ) / (J + 1)| * (|(u ^ j).re| * |1 + (v ^ j).re|)
      ≤ 1 * (‖u‖ * 2) :=
        mul_le_mul hw (mul_le_mul ha hb (abs_nonneg _) (norm_nonneg _))
          (by positivity) (by norm_num)
    _ = 2 * ‖u‖ := by ring

/-- The weighted Fejér sum equals the `tsum` over `n` of the per-`n` quantities. -/
lemma sum_eq_tsum_terms (J : ℕ) (z : ℕ → ℂ)
    (hpowsum : ∀ j : ℕ, 1 ≤ j → Summable fun n : ℕ => (z n) ^ j)
    (_hCsum : Summable fun n : ℕ =>
      ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * ((z n ^ j).re * (1 + (z 0 ^ j).re))) :
    (∑ j ∈ Finset.Icc 1 J,
        (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re) * (∑' n : ℕ, (z n) ^ j).re)
      = ∑' n : ℕ, ∑ j ∈ Finset.Icc 1 J,
          (1 - (j : ℝ) / (J + 1)) * ((z n ^ j).re * (1 + (z 0 ^ j).re)) := by
  have hresumm : ∀ j ∈ Finset.Icc 1 J, Summable fun n : ℕ => ((z n) ^ j).re := by
    intro j hj
    refine Summable.of_norm_bounded (g := fun n : ℕ => ‖(z n) ^ j‖) ?_ ?_
    · exact summable_norm_iff.mpr (hpowsum j (Finset.mem_Icc.mp hj).1)
    · intro n; exact Complex.abs_re_le_norm _
  have hsumm : ∀ j ∈ Finset.Icc 1 J,
      Summable fun n : ℕ =>
        (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re) * ((z n) ^ j).re :=
    fun j hj => Summable.mul_left _ (hresumm j hj)
  calc (∑ j ∈ Finset.Icc 1 J,
          (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re) * (∑' n : ℕ, (z n) ^ j).re)
      = ∑ j ∈ Finset.Icc 1 J,
          ∑' n : ℕ, (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re) * ((z n) ^ j).re := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [Complex.re_tsum (hpowsum j (Finset.mem_Icc.mp hj).1)]
        exact (Summable.tsum_mul_left _ (hresumm j hj)).symm
    _ = ∑' n : ℕ, ∑ j ∈ Finset.Icc 1 J,
          (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re) * ((z n) ^ j).re :=
        (Summable.tsum_finsetSum hsumm).symm
    _ = ∑' n : ℕ, ∑ j ∈ Finset.Icc 1 J,
          (1 - (j : ℝ) / (J + 1)) * ((z n ^ j).re * (1 + (z 0 ^ j).re)) := by
        refine tsum_congr ?_
        intro n
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring

/-! ### The lower bound -/

theorem turanPowerSum_lower (J : ℕ) (hJ : 1 ≤ J) (z : ℕ → ℂ) (h0 : ‖z 0‖ = 1)
    (hle : ∀ n : ℕ, ‖z n‖ ≤ 1)
    (hnormsum : Summable fun n : ℕ => ‖z n‖)
    (hweyl : Summable fun n : ℕ => ‖z n‖ / (1 + ‖z n‖))
    (hpowsum : ∀ j : ℕ, 1 ≤ j → Summable fun n : ℕ => (z n) ^ j) :
    ((J : ℝ) + 1) / 4 - 2 * (∑' n : ℕ, ‖z n‖ / (1 + ‖z n‖)) ≤
      ∑ j ∈ Finset.Icc 1 J,
        (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re) * (∑' n : ℕ, (z n) ^ j).re := by
  have hfejer : ∀ w : ℂ, ‖w‖ ≤ 1 →
      -‖w‖ / (1 + ‖w‖) ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re :=
    fun w hw => turanFejerComplex J hJ w hw
  have hCsum : Summable fun n : ℕ =>
      ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * ((z n ^ j).re * (1 + (z 0 ^ j).re)) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => 2 * (J : ℝ) * ‖z n‖) ?_ ?_
    · simpa using hnormsum.mul_left (2 * (J : ℝ))
    · intro n
      calc ‖∑ j ∈ Finset.Icc 1 J,
              (1 - (j : ℝ) / (J + 1)) * ((z n ^ j).re * (1 + (z 0 ^ j).re))‖
          ≤ ∑ j ∈ Finset.Icc 1 J,
              ‖(1 - (j : ℝ) / (J + 1)) * ((z n ^ j).re * (1 + (z 0 ^ j).re))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.Icc 1 J, 2 * ‖z n‖ := by
            refine Finset.sum_le_sum ?_
            intro j hj
            rw [Real.norm_eq_abs]
            exact term_abs_bound (hle n) (le_of_eq h0) (Finset.mem_Icc.mp hj).1
              (Finset.mem_Icc.mp hj).2
        _ = 2 * (J : ℝ) * ‖z n‖ := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
            push_cast
            ring
  rw [sum_eq_tsum_terms J z hpowsum hCsum]
  rw [hCsum.tsum_eq_zero_add]
  have hC0 : ((J : ℝ) + 1) / 4 - 1 ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * ((z 0 ^ j).re * (1 + (z 0 ^ j).re)) :=
    turanPerTermZero J hJ hfejer (z 0) h0
  have hCn : ∀ n : ℕ, -2 * (‖z (n + 1)‖ / (1 + ‖z (n + 1)‖)) ≤
      ∑ j ∈ Finset.Icc 1 J,
        (1 - (j : ℝ) / (J + 1)) * ((z (n + 1) ^ j).re * (1 + (z 0 ^ j).re)) := by
    intro n
    exact turanPerTerm J hJ hfejer (z (n + 1)) (z 0) (hle (n + 1)) (le_of_eq h0)
  have hsum_tailb : Summable fun n : ℕ => ‖z (n + 1)‖ / (1 + ‖z (n + 1)‖) := by
    have h1 : Summable ((fun n : ℕ => ‖z n‖ / (1 + ‖z n‖)) ∘ fun n : ℕ => n + 1) :=
      hweyl.comp_injective (fun a b hab => by omega)
    simpa [Function.comp_def] using h1
  have hsum_tail1 : Summable fun n : ℕ => -2 * (‖z (n + 1)‖ / (1 + ‖z (n + 1)‖)) :=
    hsum_tailb.mul_left (-2)
  have hsum_tail2 : Summable fun n : ℕ =>
      ∑ j ∈ Finset.Icc 1 J,
        (1 - (j : ℝ) / (J + 1)) * ((z (n + 1) ^ j).re * (1 + (z 0 ^ j).re)) := by
    have h1 : Summable ((fun n : ℕ => ∑ j ∈ Finset.Icc 1 J,
        (1 - (j : ℝ) / (J + 1)) * ((z n ^ j).re * (1 + (z 0 ^ j).re))) ∘ fun n : ℕ => n + 1) :=
      hCsum.comp_injective (fun a b hab => by omega)
    simpa [Function.comp_def] using h1
  have htail : (∑' n : ℕ, (-2 * (‖z (n + 1)‖ / (1 + ‖z (n + 1)‖)))) ≤
      ∑' n : ℕ, ∑ j ∈ Finset.Icc 1 J,
        (1 - (j : ℝ) / (J + 1)) * ((z (n + 1) ^ j).re * (1 + (z 0 ^ j).re)) :=
    Summable.tsum_le_tsum hCn hsum_tail1 hsum_tail2
  have htail_eq : (∑' n : ℕ, (-2 * (‖z (n + 1)‖ / (1 + ‖z (n + 1)‖))))
      = -2 * ((∑' n : ℕ, ‖z n‖ / (1 + ‖z n‖)) - 1 / 2) := by
    have hb0 : ‖z 0‖ / (1 + ‖z 0‖) = 1 / 2 := by rw [h0]; norm_num
    have hsplitb : (∑' n : ℕ, ‖z (n + 1)‖ / (1 + ‖z (n + 1)‖))
        = (∑' n : ℕ, ‖z n‖ / (1 + ‖z n‖)) - 1 / 2 := by
      have h := hweyl.sum_add_tsum_nat_add 1
      simp only [Finset.sum_range_one, hb0] at h
      linarith
    rw [Summable.tsum_mul_left (-2) hsum_tailb, hsplitb]
  linarith [hC0, htail, htail_eq]

/-! ### The upper bound -/

theorem turanPowerSum_upper (J : ℕ) (hJ : 1 ≤ J) (z : ℕ → ℂ) (h0 : ‖z 0‖ = 1)
    (hle : ∀ n : ℕ, ‖z n‖ ≤ 1)
    (j0 : ℕ) (hj0 : j0 ∈ Finset.Icc 1 J)
    (hmax : ∀ k ∈ Finset.Icc 1 J,
      (∑' n : ℕ, (z n) ^ k).re ≤ (∑' n : ℕ, (z n) ^ j0).re) :
    ∑ j ∈ Finset.Icc 1 J,
        (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re) * (∑' n : ℕ, (z n) ^ j).re
      ≤ max ((∑' n : ℕ, (z n) ^ j0).re) 0 * (J : ℝ) := by
  have hWnn : ∀ j ∈ Finset.Icc 1 J, 0 ≤ (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re) := by
    intro j hj
    have hnorm : ‖z 0 ^ j‖ ≤ 1 := by rw [Complex.norm_pow, h0, one_pow]
    have h := re_bounds hnorm
    exact mul_nonneg (fejerWeight_nonneg (Finset.mem_Icc.mp hj).2) (by linarith [h.1])
  have hWsumnn : 0 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re) :=
    Finset.sum_nonneg hWnn
  have hdiff : (∑ j ∈ Finset.Icc 1 J,
          (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re) * (∑' n : ℕ, (z n) ^ j).re)
        - (∑' n : ℕ, (z n) ^ j0).re *
            (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re))
      = ∑ j ∈ Finset.Icc 1 J, ((1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re)) *
          ((∑' n : ℕ, (z n) ^ j).re - (∑' n : ℕ, (z n) ^ j0).re) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  have hle0 : (∑ j ∈ Finset.Icc 1 J, ((1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re)) *
        ((∑' n : ℕ, (z n) ^ j).re - (∑' n : ℕ, (z n) ^ j0).re)) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro j hj
    exact mul_nonpos_of_nonneg_of_nonpos (hWnn j hj) (by linarith [hmax j hj])
  have hWsum : (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re))
      ≤ (J : ℝ) := by
    have h1 : (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re))
        ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * 2 := by
      refine Finset.sum_le_sum ?_
      intro j hj
      have hnorm : ‖z 0 ^ j‖ ≤ 1 := by rw [Complex.norm_pow, h0, one_pow]
      have h := re_bounds hnorm
      exact mul_le_mul_of_nonneg_left (by linarith [h.2])
        (fejerWeight_nonneg (Finset.mem_Icc.mp hj).2)
    have h2 : (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * 2) = (J : ℝ) := by
      rw [← Finset.sum_mul, turanPerTermZero_sumW]
      ring
    linarith
  have hkey : (∑' n : ℕ, (z n) ^ j0).re *
        (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + (z 0 ^ j).re))
      ≤ max ((∑' n : ℕ, (z n) ^ j0).re) 0 * (J : ℝ) := by
    rcases le_total (0 : ℝ) ((∑' n : ℕ, (z n) ^ j0).re) with h | h
    · rw [max_eq_left h]
      exact mul_le_mul_of_nonneg_left hWsum h
    · rw [max_eq_right h, zero_mul]
      exact mul_nonpos_of_nonpos_of_nonneg h hWsumnn
  linarith [hdiff.symm ▸ hle0, hkey]

/-! ### The normalized version of Turán's power-sum method -/

theorem turanPowerSum_normalized (ε : ℝ) (hε : 0 < ε) (z : ℕ → ℂ)
    (h0 : ‖z 0‖ = 1) (hle : ∀ n : ℕ, ‖z n‖ ≤ 1)
    (hweyl : Summable fun n : ℕ => ‖z n‖ / (1 + ‖z n‖)) :
    ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ (8 + ε) * (∑' n : ℕ, ‖z n‖ / (1 + ‖z n‖)) ∧
      ε / (32 + 4 * ε) ≤ (∑' n : ℕ, (z n) ^ j).re := by
  have hz0 : z 0 ≠ 0 := by
    intro h
    rw [h] at h0
    norm_num at h0
  have hle0 : ∀ n : ℕ, ‖z n‖ ≤ ‖z 0‖ := fun n => by rw [h0]; exact hle n
  have hnormsum : Summable fun n : ℕ => ‖z n‖ :=
    summableNormOfWeyl z hz0 hle0 (by simpa [h0] using hweyl)
  have hpowsum : ∀ j : ℕ, 1 ≤ j → Summable fun n : ℕ => (z n) ^ j := fun j hj =>
    summablePowOfWeyl z hz0 hle0 (by simpa [h0] using hweyl) j hj
  have hMge : (1 : ℝ) / 2 ≤ ∑' n : ℕ, ‖z n‖ / (1 + ‖z n‖) := by
    have h := hweyl.le_tsum 0 (fun j hj => by positivity)
    rw [h0] at h
    norm_num at h
    linarith
  set M : ℝ := ∑' n : ℕ, ‖z n‖ / (1 + ‖z n‖) with hM
  have hMge' : (1 : ℝ) / 2 ≤ M := by rw [hM]; exact hMge
  set J : ℕ := ⌊(8 + ε) * M⌋₊ with hJ
  have hJM : (J : ℝ) ≤ (8 + ε) * M := by
    rw [hJ]; exact Nat.floor_le (by positivity)
  have hJM' : (8 + ε) * M < (J : ℝ) + 1 := by
    rw [hJ]; exact Nat.lt_floor_add_one _
  have hJ1 : 1 ≤ J := by
    rw [hJ]
    apply Nat.le_floor
    push_cast
    nlinarith [hMge', hε]
  have hsne : (Finset.Icc 1 J).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hJ1⟩⟩
  obtain ⟨j0, hj0, hj0max⟩ :=
    Finset.exists_max_image (Finset.Icc 1 J) (fun j => (∑' n : ℕ, (z n) ^ j).re) hsne
  have hj0ge : 1 ≤ j0 := (Finset.mem_Icc.mp hj0).1
  have hj0le : j0 ≤ J := (Finset.mem_Icc.mp hj0).2
  have hlow := turanPowerSum_lower J hJ1 z h0 hle hnormsum hweyl hpowsum
  have hup := turanPowerSum_upper J hJ1 z h0 hle j0 hj0 hj0max
  set S0 : ℝ := (∑' n : ℕ, (z n) ^ j0).re with hS0
  have hcombine : ((J : ℝ) + 1) / 4 - 2 * M ≤ max S0 0 * (J : ℝ) := hlow.trans hup
  have hJpos : (0 : ℝ) < (J : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hJ1
  have hge : ε * M / 4 ≤ max S0 0 * (J : ℝ) := by
    have h2 : 2 * M + ε * M / 4 < ((J : ℝ) + 1) / 4 := by nlinarith [hJM']
    linarith
  have hmaxpos : 0 < max S0 0 := by nlinarith [hge, hε, hJpos]
  have hS0eq : max S0 0 = S0 := by
    rcases le_total (0 : ℝ) S0 with h | h
    · exact max_eq_left h
    · exfalso
      rw [max_eq_right h] at hmaxpos
      exact lt_irrefl 0 hmaxpos
  rw [hS0eq] at hge
  have hmid : ε * M / (4 * (J : ℝ)) ≤ S0 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (J : ℝ))]
    nlinarith [hge]
  have hfinal : ε / (32 + 4 * ε) ≤ ε * M / (4 * (J : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 32 + 4 * ε)
      (by positivity : (0 : ℝ) < 4 * (J : ℝ))]
    have h4 : (4 : ℝ) * (J : ℝ) ≤ (32 + 4 * ε) * M := by nlinarith [hJM]
    nlinarith [h4, hε]
  refine ⟨j0, hj0ge, ?_, ?_⟩
  · calc (j0 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj0le
      _ ≤ (8 + ε) * M := hJM
      _ = (8 + ε) * (∑' n : ℕ, ‖z n‖ / (1 + ‖z n‖)) := by rw [hM]
  · rw [← hS0]
    linarith [hmid, hfinal]

/-! ### Turán's power-sum method -/

/-- Turán's power-sum method (Kadiri–Ng–Wong, arXiv:1902.08640, Theorem 2.2), in the
normalization used for the Deuring–Heilbronn phenomenon: for a sequence of complex numbers
`z` with `‖z n‖ ≤ ‖z 0‖` and `z 0 ≠ 0`, if the "Weyl sum"
`M = ∑' n, ‖z n‖ / (‖z 0‖ + ‖z n‖)` is finite then some power `1 ≤ j ≤ (8+ε)M` has a
power sum with real part at least `(ε/(32+4ε))‖z 0‖^j`.
See `Work.LinnikAreas.turanFejerLower` for the Fejér-kernel inequality the proof uses.

Proof sketch (KNW §2): normalize `‖z 0‖ = 1`; with `P(r,θ) = Σ_{j=1}^J (1-j/(J+1)) r^j cos(jθ)`
one has `Σ_{j=1}^J (1-j/(J+1)) Re(s_j)(1+cos(jθ_0)) = Σ_n b_n (P(r_n,θ_n) + P(r_n,θ_n-θ_0)/2 +
P(r_n,θ_n+θ_0)/2)`; bound the `n = 0` term below with `P(1,0) = J/2` and the rest with
`P(r,θ) ≥ -r/(1+r)` (`turanFejerLower`), and compare with `J · max_j Re(s_j)`. -/
theorem turanPowerSum (ε : ℝ) (hε : 0 < ε) (z : ℕ → ℂ) (hz : z 0 ≠ 0)
    (hle : ∀ n : ℕ, ‖z n‖ ≤ ‖z 0‖)
    (hsum : Summable fun n : ℕ => ‖z n‖ / (‖z 0‖ + ‖z n‖)) :
    ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ (8 + ε) * (∑' n : ℕ, ‖z n‖ / (‖z 0‖ + ‖z n‖)) ∧
      ε / (32 + 4 * ε) * ‖z 0‖ ^ j ≤ (∑' n : ℕ, (z n) ^ j).re := by
  set R : ℝ := ‖z 0‖ with hR
  have hRpos : 0 < R := by
    rw [hR]
    exact norm_pos_iff.mpr hz
  have hRne : (R : ℂ) ≠ 0 := by
    simp [Complex.ofReal_eq_zero, hRpos.ne']
  have hnormR : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
  set w : ℕ → ℂ := fun n => (R : ℂ)⁻¹ * z n with hw
  have hwz : ∀ n : ℕ, (R : ℂ) * w n = z n := by
    intro n
    rw [hw]
    exact mul_inv_cancel_left₀ hRne (z n)
  have hw0 : ‖w 0‖ = 1 := by
    rw [hw, norm_mul, norm_inv, hnormR, ← hR]
    exact inv_mul_cancel₀ hRpos.ne'
  have hwle : ∀ n : ℕ, ‖w n‖ ≤ 1 := by
    intro n
    rw [hw, norm_mul, norm_inv, hnormR, inv_mul_le_one₀ hRpos]
    exact hle n
  have hweyl : Summable fun n : ℕ => ‖w n‖ / (1 + ‖w n‖) := by
    have hpt : (fun n : ℕ => ‖w n‖ / (1 + ‖w n‖))
        = fun n : ℕ => ‖z n‖ / (‖z 0‖ + ‖z n‖) := by
      funext n
      rw [hw, norm_mul, norm_inv, hnormR, ← hR]
      field_simp
    rw [hpt]
    exact hsum
  obtain ⟨j, hj1, hj2, hj3⟩ := turanPowerSum_normalized ε hε w hw0 hwle hweyl
  have hM_eq : (∑' n : ℕ, ‖w n‖ / (1 + ‖w n‖)) = ∑' n : ℕ, ‖z n‖ / (‖z 0‖ + ‖z n‖) := by
    refine tsum_congr ?_
    intro n
    rw [hw, norm_mul, norm_inv, hnormR, ← hR]
    field_simp
  have hwsumm : Summable fun n : ℕ => (w n) ^ j :=
    summablePowOfWeyl w (by intro h; rw [h] at hw0; norm_num at hw0)
      (fun n => by rw [hw0]; exact hwle n) (by simpa [hw0] using hweyl) j hj1
  have hz_eq : (∑' n : ℕ, (z n) ^ j).re = R ^ j * (∑' n : ℕ, (w n) ^ j).re := by
    have h1 : (∑' n : ℕ, (z n) ^ j) = (R : ℂ) ^ j * (∑' n : ℕ, (w n) ^ j) := by
      have hpt : ∀ n : ℕ, (z n) ^ j = ((R : ℂ) ^ j) * (w n) ^ j := by
        intro n
        rw [← hwz n, mul_pow]
      rw [tsum_congr hpt]
      exact Summable.tsum_mul_left _ hwsumm
    rw [h1, Complex.mul_re]
    have h2 : ((R : ℂ) ^ j).re = R ^ j := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have h3 : ((R : ℂ) ^ j).im = 0 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
    rw [h2, h3, zero_mul, sub_zero]
  refine ⟨j, hj1, ?_, ?_⟩
  · rw [← hM_eq]
    exact hj2
  · rw [hz_eq]
    have hRj : 0 ≤ R ^ j := pow_nonneg hRpos.le j
    nlinarith [hj3, hRj, hε]

end Work.LinnikAreas
