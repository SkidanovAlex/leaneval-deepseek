import Mathlib
import Submission.Work.Parab.leftCoord.levelData
import Submission.Work.Parab.leftCoord.wMap_large_estimates
import Submission.Work.FatouCoord.Exist.fatouCoordW_tsum_bound
import Submission.Work.FatouCoord.Exist.fatouCoordW_abel

namespace Work.Parab.leftCoord

open Work.FatouCoord
open Set Filter Metric
open scoped Topology

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem psiC_asymptotic {f h : ℂ → ℂ} {a : ℂ} {r A A' N : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    (hF : Work.Parab.leftCoord.LevelFacts f h a r N)
    (herr : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, N < ‖w‖ →
      (0 < w.re ∨ (0 < w.im ∧ 0 < (Work.FatouCoord.wMap f w).im) ∨
        (w.im < 0 ∧ (Work.FatouCoord.wMap f w).im < 0)) →
      ‖Work.FatouCoord.coordError f (1 - a) w‖ ≤ C / ‖w‖ ^ 2) :
    ∀ ε > 0, ∃ R : ℝ, ∀ W : ℂ,
      W ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap f) → R < ‖W‖ →
      -3 * |W.im| < W.re →
      ‖Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap f)
        (Work.FatouCoord.fatouCoordW f (1 - a)) W - (W - (1 - a) * Complex.log W)‖ < ε := by
  -- ## 0. the constants supplied by the level facts and the error hypothesis
  obtain ⟨K, hKnn, hstep⟩ := hF.step
  obtain ⟨Kts, hKtsnn, htsum⟩ := hF.rem
  obtain ⟨Ccs, hCcsnn, hCerr⟩ := herr
  have hNpos : 0 < N := hF.pos
  have hmono : ∀ x : ℂ, N < ‖x‖ → x.re ≤ (wMap f x).re := by
    intro x hx
    have h := (hstep x hx).2.2.2
    linarith
  have hGN : ∀ x : ℂ, N < x.re → N < (wMap f x).re := by
    intro x hx
    have hxnorm : N < ‖x‖ := lt_of_lt_of_le hx (Complex.re_le_norm x)
    have h := (hstep x hxnorm).2.2.2
    linarith
  have habelN : ∀ x : ℂ, N < x.re →
      fatouCoordW f (1 - a) (wMap f x) = fatouCoordW f (1 - a) x + 1 :=
    fun x hx => hF.abel x hx
  intro ε hε
  -- ## 3. the target level `M`
  set M : ℝ := max (N + 2) (2 * Kts / ε + 1) with hMdef
  have hMgtN : N < M := by
    have h1 : N + 2 ≤ M := by rw [hMdef]; exact le_max_left _ _
    linarith
  have hMpos : 0 < M := lt_trans hNpos hMgtN
  have herr_end : Kts / M < ε / 2 := by
    have h2 : 2 * Kts / ε < M := by
      have h3 : 2 * Kts / ε + 1 ≤ M := by rw [hMdef]; exact le_max_right _ _
      linarith
    have h4 : 2 * Kts < M * ε := by
      rw [div_lt_iff₀ hε] at h2
      linarith
    rw [div_lt_iff₀ hMpos]
    linarith
  -- ## 4. the threshold `R`
  set R : ℝ := 1536 * K + 384 * K * M
    + 384 * Ccs * (2 * M + 2) / ε + 768 * Ccs / ε + 1 with hRdef
  have hnn1 : (0:ℝ) ≤ 1536 * K := by linarith
  have hnn2 : (0:ℝ) ≤ 384 * K * M := by positivity
  have hnn3 : (0:ℝ) ≤ 384 * Ccs * (2 * M + 2) / ε := by positivity
  have hnn4 : (0:ℝ) ≤ 768 * Ccs / ε := by positivity
  have hRnn : 0 < R := by rw [hRdef]; linarith
  have hR1 : 1 ≤ R := by rw [hRdef]; linarith
  have hRa : 384 * K ≤ R := by rw [hRdef]; linarith
  have hRb : 384 * K * M ≤ R := by rw [hRdef]; linarith
  have hRc : 384 * Ccs * (2 * M + 2) / ε ≤ R := by rw [hRdef]; linarith
  have hRd : 768 * Ccs / ε ≤ R := by rw [hRdef]; linarith
  refine ⟨R, ?_⟩
  intro W hWesc hRW hsect
  set m : ℝ := ‖W‖ with hmdef
  have hmpos : 0 < m := lt_trans hRnn hRW
  have hm1 : 1 ≤ m := le_trans hR1 hRW.le
  have hm_ge_384Ke : 384 * K ≤ m := le_trans hRa hRW.le
  have hm_ge_384KeM : 384 * K * M ≤ m := le_trans hRb hRW.le
  have hm_ge_384C : 384 * Ccs * (2 * M + 2) / ε ≤ m := le_trans hRc hRW.le
  have hm_ge_768C : 768 * Ccs / ε ≤ m := le_trans hRd hRW.le
  have hm2KM : 384 * K * M ≤ m ^ 2 := by nlinarith only [hm_ge_384KeM, hm1, hmpos]
  have hm2Kem : 384 * K * m ≤ m ^ 2 := by nlinarith only [hm_ge_384Ke, hmpos]
  have hm2K : 384 * K ≤ m ^ 2 := by nlinarith only [hm_ge_384Ke, hm1, hmpos]
  have hm2C : 384 * Ccs * (2 * M + 2) / ε ≤ m ^ 2 := by nlinarith only [hm_ge_384C, hm1, hmpos]
  have hm2C' : 768 * Ccs / ε ≤ m ^ 2 := by nlinarith only [hm_ge_768C, hm1, hmpos]
  -- ## 5. the orbit and the crossing index
  let w : ℕ → ℂ := fun k => (wMap f)^[k] W
  have hwsucc : ∀ k : ℕ, w (k + 1) = wMap f (w k) := by
    intro k
    show (wMap f)^[k + 1] W = wMap f ((wMap f)^[k] W)
    exact Function.iterate_succ_apply' (wMap f) k W
  have hw0 : w 0 = W := rfl
  have hnormgt : ∀ k : ℕ, N < ‖w k‖ := norm_gt_of_EscC hmono hWesc
  have hgrowth : ∀ k : ℕ, W.re + (k : ℝ) / 2 ≤ (w k).re := by
    intro k
    induction k with
    | zero =>
      show W.re + ((0 : ℕ) : ℝ) / 2 ≤ (w 0).re
      rw [hw0]; norm_num
    | succ k ih =>
      have h3 := (hstep (w k) (hnormgt k)).2.2.2
      rw [hwsucc k]
      push_cast
      linarith
  have hex : ∃ J : ℕ, M < (w J).re := by
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * (M - W.re))
    refine ⟨n₀ + 1, ?_⟩
    have h := hgrowth (n₀ + 1)
    have hc : (((n₀ + 1 : ℕ) : ℝ)) / 2 = (n₀ : ℝ) / 2 + 1 / 2 := by push_cast; ring
    rw [hc] at h
    linarith
  let J : ℕ := Nat.find hex
  have hJbig : M < (w J).re := Nat.find_spec hex
  have hJprev : ∀ k : ℕ, k < J → (w k).re ≤ M := fun k hk => not_lt.mp (Nat.find_min hex hk)
  have hJr : N < (w J).re := lt_trans hMgtN hJbig
  have hJle : (J : ℝ) ≤ 2 * M + 2 * m + 2 := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [h0]; push_cast; linarith [hMpos, hmpos]
    · obtain ⟨J', hJ'⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
      have h1 : J' < J := by omega
      have h2 := hJprev J' h1
      have h3 := hgrowth J'
      have h4 : (J' : ℝ) ≤ 2 * (M - W.re) := by linarith
      have h5 : |W.re| ≤ m := by rw [hmdef]; exact Complex.abs_re_le_norm W
      have h6 : 2 * (M - W.re) ≤ 2 * M + 2 * m := by
        have h7 : -W.re ≤ m := le_trans (neg_le_abs W.re) h5
        linarith
      rw [hJ']
      push_cast
      linarith
  have hdrift_tot : (J : ℝ) * (8 * K / m) ≤ m / 8 := by
    have h8nn : 0 ≤ 8 * K / m := by positivity
    have h1 : (J : ℝ) * (8 * K / m) ≤ (2 * M + 2 * m + 2) * (8 * K / m) :=
      mul_le_mul_of_nonneg_right hJle h8nn
    have h2 : (2 * M + 2 * m + 2) * (8 * K / m) ≤ m / 8 := by
      have h3 : (2 * M + 2 * m + 2) * (8 * K / m) = 8 * K * (2 * M + 2 * m + 2) / m := by ring
      rw [h3, div_le_iff₀ hmpos]
      nlinarith [hm2KM, hm2Kem, hm2K, hmpos]
    linarith
  have hdich : m / 4 ≤ max W.re |W.im| := by
    have hsq : m ^ 2 = W.re ^ 2 + W.im ^ 2 := by
      rw [hmdef, Complex.sq_norm, Complex.normSq_apply]
      ring
    have hmaxnn : 0 ≤ max W.re |W.im| := le_trans (abs_nonneg W.im) (le_max_right _ _)
    have hmax_im : |W.im| ≤ max W.re |W.im| := le_max_right _ _
    have hmax_re : W.re ≤ max W.re |W.im| := le_max_left _ _
    have h3 : m ^ 2 ≤ 16 * (max W.re |W.im|) ^ 2 := by
      rcases le_or_gt 0 W.re with h | h
      · have h1 : W.re ^ 2 ≤ (max W.re |W.im|) ^ 2 := pow_le_pow_left₀ h hmax_re 2
        have h2 : W.im ^ 2 ≤ (max W.re |W.im|) ^ 2 := by
          rw [← sq_abs W.im]
          exact pow_le_pow_left₀ (abs_nonneg _) hmax_im 2
        have hX2 : 0 ≤ (max W.re |W.im|) ^ 2 := sq_nonneg _
        linarith [hsq, h1, h2, hX2]
      · have h5 : |W.re| ≤ 3 * |W.im| := by
          rw [abs_of_neg h]
          linarith [hsect]
        have h6 : |W.re| ≤ 3 * (max W.re |W.im|) := by
          linarith [h5, hmax_im, abs_nonneg W.re]
        have h1 : W.re ^ 2 ≤ (3 * (max W.re |W.im|)) ^ 2 := by
          rw [← sq_abs W.re]
          exact pow_le_pow_left₀ (abs_nonneg _) h6 2
        have h2 : W.im ^ 2 ≤ (max W.re |W.im|) ^ 2 := by
          rw [← sq_abs W.im]
          exact pow_le_pow_left₀ (abs_nonneg _) hmax_im 2
        have hX2 : 0 ≤ (max W.re |W.im|) ^ 2 := sq_nonneg _
        linarith [hsq, h1, h2, hX2]
    have hm4nn : 0 ≤ m / 4 := by linarith
    have h4 : (m / 4) ^ 2 ≤ (max W.re |W.im|) ^ 2 := by nlinarith [h3]
    have h5 := (sq_le_sq.mp h4)
    rwa [abs_of_nonneg hm4nn, abs_of_nonneg hmaxnn] at h5
  -- ## 6. the invariant along the orbit
  have hkey : ∀ k : ℕ, k ≤ J →
      (m / 8 ≤ ‖w k‖ ∧ |(w k).im - W.im| ≤ (k : ℝ) * (8 * K / m) ∧
        W.re + (k : ℝ) / 2 ≤ (w k).re) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨?_, ?_, ?_⟩
      · rw [hw0, ← hmdef]; linarith
      · rw [hw0]; simp
      · rw [hw0]; simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ J := le_trans (Nat.le_succ k) hk
      obtain ⟨hnorm, hdrift, hre⟩ := ih hk'
      have hinc : ‖w (k + 1) - w k - 1‖ ≤ 8 * K / m := by
        have h1 := (hstep (w k) (hnormgt k)).1
        have h2 : K / ‖w k‖ ≤ 8 * K / m := by
          have h3 : K / ‖w k‖ ≤ K / (m / 8) :=
            div_le_div_of_nonneg_left hKnn (by positivity) hnorm
          have h4 : K / (m / 8) = 8 * K / m := by field_simp
          rwa [h4] at h3
        calc ‖w (k + 1) - w k - 1‖ = ‖wMap f (w k) - (w k + 1)‖ := by
              rw [hwsucc k]; ring_nf
          _ ≤ K / ‖w k‖ := h1
          _ ≤ 8 * K / m := h2
      have hre' : W.re + ((k + 1 : ℕ) : ℝ) / 2 ≤ (w (k + 1)).re := by
        have h3 := (hstep (w k) (hnormgt k)).2.2.2
        rw [hwsucc k]
        have h5 : ((k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) / 2 + 1 / 2 := by push_cast; ring
        rw [h5]
        linarith
      have him' : |(w (k + 1)).im - W.im| ≤ ((k + 1 : ℕ) : ℝ) * (8 * K / m) := by
        have h1 : |(w (k + 1)).im - W.im|
            ≤ |(w (k + 1)).im - (w k).im| + |(w k).im - W.im| := by
          have h2 : (w (k + 1)).im - W.im
              = ((w (k + 1)).im - (w k).im) + ((w k).im - W.im) := by ring
          rw [h2]; exact abs_add_le _ _
        have h3 : |(w (k + 1)).im - (w k).im| ≤ 8 * K / m := by
          have h4 : (w (k + 1)).im - (w k).im = (w (k + 1) - w k - 1).im := by
            simp only [Complex.sub_im, Complex.one_im]; ring
          rw [h4]
          exact le_trans (Complex.abs_im_le_norm _) hinc
        have h5 : ((k + 1 : ℕ) : ℝ) * (8 * K / m) = (k : ℝ) * (8 * K / m) + 8 * K / m := by
          push_cast; ring
        rw [h5]
        linarith
      have hnorm_succ : m / 8 ≤ ‖w (k + 1)‖ := by
        have hle : max (w (k + 1)).re |(w (k + 1)).im| ≤ ‖w (k + 1)‖ :=
          max_le (Complex.re_le_norm _) (Complex.abs_im_le_norm _)
        have hmain : m / 8 ≤ max (w (k + 1)).re |(w (k + 1)).im| := by
          rcases le_or_gt (m / 4) W.re with hcase | hcase
          · refine le_trans ?_ (le_max_left _ _)
            have h6 : m / 8 ≤ W.re := by linarith
            have h7 : (0:ℝ) ≤ ((k + 1 : ℕ) : ℝ) / 2 := by positivity
            linarith
          · have hWim : m / 4 ≤ |W.im| := by
              rcases le_or_gt (m / 4) |W.im| with h | h
              · exact h
              · exact absurd (max_lt hcase h) (not_lt.mpr hdich)
            refine le_trans ?_ (le_max_right _ _)
            have h6 : ((k + 1 : ℕ) : ℝ) * (8 * K / m) ≤ m / 8 := by
              have h7 : ((k + 1 : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast hk
              have h8 : 0 ≤ 8 * K / m := by positivity
              calc ((k + 1 : ℕ) : ℝ) * (8 * K / m) ≤ (J : ℝ) * (8 * K / m) :=
                    mul_le_mul_of_nonneg_right h7 h8
                _ ≤ m / 8 := hdrift_tot
            have h9 : |W.im| - ((k + 1 : ℕ) : ℝ) * (8 * K / m) ≤ |(w (k + 1)).im| := by
              have h10 := abs_sub_abs_le_abs_sub W.im (w (k + 1)).im
              rw [abs_sub_comm] at h10
              linarith [him']
            linarith
        linarith
      exact ⟨hnorm_succ, him', hre'⟩
  -- ## 7. the telescoping identity
  have hw_eq : ∀ k : ℕ, (wMap f)^[k] W = w k := fun k => rfl
  have hsum_eq : (∑ k ∈ Finset.range J,
        (approxCoord (1 - a) ((wMap f)^[k + 1] W) - approxCoord (1 - a) ((wMap f)^[k] W) - 1))
      = ∑ k ∈ Finset.range J, coordError f (1 - a) (w k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hw_eq (k + 1), hw_eq k, coordError_apply, ← hwsucc k]
  have hident : PsiC N (wMap f) (fatouCoordW f (1 - a)) W - approxCoord (1 - a) W
      = (∑ k ∈ Finset.range J, coordError f (1 - a) (w k))
        + (fatouCoordW f (1 - a) (w J) - approxCoord (1 - a) (w J)) := by
    rw [Work.Parab.leftCoord.PsiC_sub_approx_eq_sum (N := N) (G := wMap f)
      (ψ := fatouCoordW f (1 - a)) (c := 1 - a) hGN habelN hmono hWesc hJr, hsum_eq]
  -- ## 8. the uniform endgame
  have core : (∀ k : ℕ, k < J → ‖coordError f (1 - a) (w k)‖ ≤ Ccs / ‖w k‖ ^ 2) →
      ‖PsiC N (wMap f) (fatouCoordW f (1 - a)) W - approxCoord (1 - a) W‖ < ε := by
    intro hdef_all
    have hRJ : ‖fatouCoordW f (1 - a) (w J) - approxCoord (1 - a) (w J)‖ < ε / 2 := by
      have h1 : ‖fatouCoordW f (1 - a) (w J) - approxCoord (1 - a) (w J)‖ ≤ Kts / (w J).re :=
        htsum (w J) hJr
      have h2 : Kts / (w J).re ≤ Kts / M :=
        div_le_div_of_nonneg_left hKtsnn hMpos hJbig.le
      linarith [herr_end]
    have hsum : ‖∑ k ∈ Finset.range J, coordError f (1 - a) (w k)‖ < ε / 2 := by
      have h1 : ‖∑ k ∈ Finset.range J, coordError f (1 - a) (w k)‖
          ≤ ∑ k ∈ Finset.range J, ‖coordError f (1 - a) (w k)‖ := norm_sum_le _ _
      have h2 : ∑ k ∈ Finset.range J, ‖coordError f (1 - a) (w k)‖
          ≤ ∑ k ∈ Finset.range J, Ccs / ‖w k‖ ^ 2 :=
        Finset.sum_le_sum (fun k hk => hdef_all k (Finset.mem_range.mp hk))
      have h3 : ∑ k ∈ Finset.range J, Ccs / ‖w k‖ ^ 2
          ≤ ∑ _k ∈ Finset.range J, Ccs / (m / 8) ^ 2 := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk_le : k ≤ J := le_of_lt (Finset.mem_range.mp hk)
        have hwk : m / 8 ≤ ‖w k‖ := (hkey k hk_le).1
        have hsq : (m / 8) ^ 2 ≤ ‖w k‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) hwk 2
        exact div_le_div_of_nonneg_left hCcsnn (by positivity) hsq
      have h4 : ∑ _k ∈ Finset.range J, Ccs / (m / 8) ^ 2 = Ccs / (m / 8) ^ 2 * (J : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      have h5 : Ccs / (m / 8) ^ 2 * (J : ℝ) = 64 * Ccs * (J : ℝ) / m ^ 2 := by
        have hm8 : (m / 8) ^ 2 = m ^ 2 / 64 := by ring
        rw [hm8, div_div_eq_mul_div]
        ring_nf
      have h6 : 64 * Ccs * (J : ℝ) / m ^ 2 ≤ 64 * Ccs * (2 * M + 2 * m + 2) / m ^ 2 := by
        have h7 : 64 * Ccs * (J : ℝ) ≤ 64 * Ccs * (2 * M + 2 * m + 2) :=
          mul_le_mul_of_nonneg_left hJle (by linarith [hCcsnn])
        exact div_le_div_of_nonneg_right h7 (by positivity)
      have h7 : 64 * Ccs * (2 * M + 2 * m + 2) / m ^ 2
          = 64 * Ccs * (2 * M + 2) / m ^ 2 + 128 * Ccs / m := by
        field_simp
        ring
      have h8 : 64 * Ccs * (2 * M + 2) / m ^ 2 ≤ ε / 6 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < m ^ 2)]
        have h9 : 384 * Ccs * (2 * M + 2) ≤ ε * m ^ 2 := by
          have h := (div_le_iff₀ hε).mp hm2C
          linarith
        linarith
      have h9' : 128 * Ccs / m ≤ ε / 6 := by
        rw [div_le_iff₀ hmpos]
        have h10 : 768 * Ccs ≤ ε * m := by
          have h := (div_le_iff₀ hε).mp hm_ge_768C
          linarith
        linarith
      have hchain : ‖∑ k ∈ Finset.range J, coordError f (1 - a) (w k)‖
          ≤ 64 * Ccs * (2 * M + 2 * m + 2) / m ^ 2 := by
        calc ‖∑ k ∈ Finset.range J, coordError f (1 - a) (w k)‖
            ≤ ∑ k ∈ Finset.range J, ‖coordError f (1 - a) (w k)‖ := h1
          _ ≤ ∑ k ∈ Finset.range J, Ccs / ‖w k‖ ^ 2 := h2
          _ ≤ ∑ _k ∈ Finset.range J, Ccs / (m / 8) ^ 2 := h3
          _ = Ccs / (m / 8) ^ 2 * (J : ℝ) := h4
          _ = 64 * Ccs * (J : ℝ) / m ^ 2 := h5
          _ ≤ 64 * Ccs * (2 * M + 2 * m + 2) / m ^ 2 := h6
      rw [h7] at hchain
      linarith
    rw [hident]
    calc ‖(∑ k ∈ Finset.range J, coordError f (1 - a) (w k))
          + (fatouCoordW f (1 - a) (w J) - approxCoord (1 - a) (w J))‖
        ≤ ‖∑ k ∈ Finset.range J, coordError f (1 - a) (w k)‖
          + ‖fatouCoordW f (1 - a) (w J) - approxCoord (1 - a) (w J)‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  -- ## 9. the drift bound at any level
  have hdrift_le : ∀ k : ℕ, k ≤ J → |(w k).im - W.im| ≤ m / 8 := by
    intro k hk
    have h1 := (hkey k hk).2.1
    have h2 : ((k : ℝ)) * (8 * K / m) ≤ m / 8 := by
      have h3 : (k : ℝ) ≤ (J : ℝ) := by exact_mod_cast hk
      have h4 : 0 ≤ 8 * K / m := by positivity
      exact le_trans (mul_le_mul_of_nonneg_right h3 h4) hdrift_tot
    exact le_trans h1 h2
  -- ## 9bis. the three sectors
  by_cases hA : m / 4 ≤ W.re
  · refine core (fun k hk => ?_)
    have hk_le : k ≤ J := le_of_lt hk
    have hre : 0 < (w k).re := by
      have h1 := (hkey k hk_le).2.2
      have h2 : (0:ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith
    exact hCerr (w k) (hnormgt k) (Or.inl hre)
  · have hWim : m / 4 ≤ |W.im| := by
      rcases le_or_gt (m / 4) |W.im| with h | h
      · exact h
      · exact absurd (max_lt (not_le.mp hA) h) (not_lt.mpr hdich)
    by_cases him : 0 < W.im
    · have hWimpos : m / 4 ≤ W.im := by
        rwa [abs_of_pos him] at hWim
      refine core (fun k hk => ?_)
      have hk_le : k ≤ J := le_of_lt hk
      have hk1_le : k + 1 ≤ J := hk
      have himk : 0 < (w k).im := by
        have h5 := hdrift_le k hk_le
        rw [abs_le] at h5
        linarith [h5.1, hWimpos]
      have himk1 : 0 < (w (k + 1)).im := by
        have h5 := hdrift_le (k + 1) hk1_le
        rw [abs_le] at h5
        linarith [h5.1, hWimpos]
      have himk1' : 0 < (wMap f (w k)).im := by
        rw [← hwsucc k]; exact himk1
      exact hCerr (w k) (hnormgt k) (Or.inr (Or.inl ⟨himk, himk1'⟩))
    · have hWimneg : W.im < 0 := by
        have h1 : W.im ≠ 0 := by
          intro h0
          have h2 : |W.im| = 0 := by rw [h0]; simp
          linarith [hWim, hmpos]
        exact lt_of_le_of_ne (not_lt.mp him) h1
      refine core (fun k hk => ?_)
      have hk_le : k ≤ J := le_of_lt hk
      have hk1_le : k + 1 ≤ J := hk
      have hWimneg' : W.im ≤ -(m / 4) := by
        rw [abs_of_neg hWimneg] at hWim
        linarith
      have himk : (w k).im < 0 := by
        have h5 := hdrift_le k hk_le
        rw [abs_le] at h5
        linarith [h5.2, hWimneg']
      have himk1 : (w (k + 1)).im < 0 := by
        have h5 := hdrift_le (k + 1) hk1_le
        rw [abs_le] at h5
        linarith [h5.2, hWimneg']
      have himk1' : (wMap f (w k)).im < 0 := by
        rw [← hwsucc k]; exact himk1
      exact hCerr (w k) (hnormgt k) (Or.inr (Or.inr ⟨himk, himk1'⟩))

end Work.Parab.leftCoord
