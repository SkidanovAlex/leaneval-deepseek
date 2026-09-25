import Mathlib
import Submission.Work.NN.Final.PolarChainDefs
import Submission.Work.CR.Flat.Holder.holderNorm_comp_le_of_contDiffOn

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.PolarChain

open Work.NN.Final

variable {n : ℕ} {ρ : Fin n → ℝ}

/-- The norm of the difference of two `0`-th iterated within-derivatives is the norm of the
difference of the functions. -/
lemma norm_iterFDerivWithin_zero_sub {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : X → F) (Ω : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  have hsub : iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y
      = ContinuousMultilinearMap.uncurry0 ℝ X (f x - f y) := by
    ext m
    simp [ContinuousMultilinearMap.uncurry0_apply, sub_apply]
  rw [hsub, ContinuousMultilinearMap.uncurry0_norm]

/-- The global model of the polar chart agrees with the polar chart on `ε ≤ ‖z j‖`. -/
lemma polarGlob_eq_polarChart_cv {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ j) {z : Fin n → ℂ} (hz : ε ≤ ‖z j‖) :
    polarGlob n ρ j ε z = polarChart n ρ j z := by
  have hr : 0 < ‖z j‖ := lt_of_lt_of_le hε hz
  have hmain : polarLogCoord n ρ j ε z = Real.log (ρ j / ‖z j‖) := by
    rw [polarLogCoord_eq_log hε hρ hz, Real.log_div (ne_of_gt hρ) (ne_of_gt hr)]
  rw [polarGlob_apply, polarChart_apply, hmain]

/-- `cvAnn n ρ j 1` is contained in `cvFlat n ρ j`. -/
lemma cvAnn_one_subset_cvFlat (hρ : ∀ i, 0 < ρ i) (j : Fin n) :
    cvAnn n ρ j 1 ⊆ cvFlat n ρ j := by
  intro z hz
  obtain ⟨h1, ⟨hj1, hj2⟩, h3⟩ := mem_cvAnn.mp hz
  rw [mem_cvFlat]
  refine ⟨h1, ⟨hj1, ?_⟩, h3⟩
  have := mul_lt_mul_of_pos_left Real.exp_one_lt_three (hρ j)
  linarith

/-- The second component of `polarChart` is `> -1` on `cvAnn n ρ j 1`. -/
lemma cvAnn_one_snd_gt (hρ : ∀ i, 0 < ρ i) (j : Fin n) {z : Fin n → ℂ}
    (hz : z ∈ cvAnn n ρ j 1) : -(1 : ℝ) < Real.log (ρ j / ‖z j‖) := by
  obtain ⟨h1, ⟨hj1, hj2⟩, h3⟩ := mem_cvAnn.mp hz
  have hrpos : 0 < ‖z j‖ := by linarith [hρ j, hj1]
  have h1e : 1 / Real.exp 1 < ρ j / ‖z j‖ := by
    rw [div_lt_div_iff₀ (Real.exp_pos 1) hrpos]
    simpa using hj2
  have hexp : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  have hgt : Real.exp (-1) < ρ j / ‖z j‖ := by rw [hexp]; exact h1e
  have := Real.log_lt_log (Real.exp_pos (-1)) hgt
  rwa [Real.log_exp] at this

/-- Norm bound for `polarChart` on `cvAnn n ρ j 1`. -/
lemma norm_polarChart_cvAnn_le (hρ : ∀ i, 0 < ρ i) (j : Fin n) {z : Fin n → ℂ}
    (hz : z ∈ cvAnn n ρ j 1) :
    ‖polarChart n ρ j z‖ ≤ (∑ i : Fin n, 3 * ρ i) + 1 := by
  obtain ⟨h1, ⟨hj1, hj2⟩, h3⟩ := mem_cvAnn.mp hz
  have hjn : (j : ℕ) ≤ n := le_of_lt j.isLt
  have hsum_nn : (0 : ℝ) ≤ ∑ i : Fin n, 3 * ρ i :=
    Finset.sum_nonneg fun i _ => by linarith [hρ i]
  have hzc : ∀ i : Fin n, ‖z i‖ ≤ 3 * ρ i := by
    intro i
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
    · have hh := h1 i hlt
      have hc : chainC n (j : ℕ) < 3 := chainC_lt_three n (j : ℕ) hjn
      nlinarith [hρ i]
    · have hji : i = j := Fin.ext heq
      rw [hji]
      have := mul_lt_mul_of_pos_left Real.exp_one_lt_three (hρ j)
      nlinarith [hj2]
    · have hh := h3 i hgt
      have hd : chainD n (j : ℕ) < 3 := chainD_lt_three n (j : ℕ) hjn
      nlinarith [hρ i]
  have hnorm : ‖z‖ ≤ ∑ i : Fin n, 3 * ρ i :=
    (pi_norm_le_iff_of_nonneg hsum_nn).mpr fun i =>
      le_trans (hzc i) (Finset.single_le_sum (f := fun i : Fin n => 3 * ρ i)
        (fun i _ => by linarith [hρ i]) (Finset.mem_univ i))
  have hlog_ub : Real.log (ρ j / ‖z j‖) < 1 := by
    have hrpos : 0 < ‖z j‖ := lt_trans (by linarith [hρ j] : (0 : ℝ) < ρ j / 2) hj1
    have hlt : ρ j / ‖z j‖ < 2 := by
      rw [div_lt_iff₀ hrpos]; linarith
    have h2 : Real.log (ρ j / ‖z j‖) < Real.log 2 :=
      Real.log_lt_log (div_pos (hρ j) hrpos) hlt
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num)
      linarith
    linarith
  have hlog_lb : -(1 : ℝ) < Real.log (ρ j / ‖z j‖) := cvAnn_one_snd_gt hρ j hz
  have hlogabs : |Real.log (ρ j / ‖z j‖)| ≤ 1 := abs_le.mpr ⟨hlog_lb.le, hlog_ub.le⟩
  rw [polarChart_apply, Prod.norm_def, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · linarith
  · linarith

theorem polarChart_comp_cvAnn {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (j : Fin n) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (u : (Fin n → ℂ) × ℝ → ℂ),
      ContDiffOn ℝ (k : WithTop ENat) u (Set.prod (Work.NN.Final.cvFlat n ρ j) {t : ℝ | -(1:ℝ) < t}) →
      Work.CR.Flat.holderNorm k α (fun z => u (Work.NN.Final.polarChart n ρ j z)) (Work.NN.Final.cvAnn n ρ j 1)
        ≤ ENNReal.ofReal (C k) *
          Work.CR.Flat.holderNorm k α u (Set.prod (Work.NN.Final.cvFlat n ρ j) {t : ℝ | -(1:ℝ) < t}) := by
  classical
  have hρj : 0 < ρ j := hρ j
  set ε : ℝ := ρ j / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  set s : Set (Fin n → ℂ) := cvAnn n ρ j 1 with hs_def
  set t : Set ((Fin n → ℂ) × ℝ) := cvFlat n ρ j ×ˢ {x : ℝ | -(1:ℝ) < x} with ht_def
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) (polarGlob n ρ j ε) := contDiff_polarGlob hε
  obtain ⟨D, hD⟩ := exists_bound_iteratedFDeriv_polarGlob (n := n) (ρ := ρ) (j := j) (ε := ε) hε
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_polarGlob (n := n) (ρ := ρ) (j := j) (ε := ε) hε hΨ D hD
  obtain ⟨E, hE⟩ := exists_holderE_polarGlob (n := n) (ρ := ρ) (j := j) (ε := ε) hε hα0 hα1 hΨ D hD
  have hsopen : IsOpen s := by rw [hs_def]; exact isOpen_cvAnn hρ j 1
  have htopen : IsOpen t := by rw [ht_def]; exact (isOpen_cvFlat hρ j).prod isOpen_Ioi
  have hmem : ∀ z ∈ s, polarGlob n ρ j ε z = polarChart n ρ j z := by
    intro z hz
    rw [hs_def] at hz
    obtain ⟨-, ⟨hj1, -⟩, -⟩ := mem_cvAnn.mp hz
    have hzε : ε ≤ ‖z j‖ := by rw [hε_def]; linarith
    exact polarGlob_eq_polarChart_cv hε hρj hzε
  have hst : Set.MapsTo (polarChart n ρ j) s t := by
    intro z hz
    rw [hs_def] at hz
    rw [ht_def, Set.mem_prod]
    exact ⟨cvAnn_one_subset_cvFlat hρ j hz, cvAnn_one_snd_gt hρ j hz⟩
  have hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) (polarChart n ρ j) s := by
    intro m
    have h1 : ContDiffOn ℝ (m : WithTop ENat) (polarGlob n ρ j ε) s :=
      (hΨ.contDiffOn.of_le (Work.NN.Final.ChartComp.natCast_le_top_nat m)).mono (subset_univ s)
    exact h1.congr fun z hz => (hmem z hz).symm
  have hL' : ∀ x ∈ s, ∀ y ∈ s, ‖polarChart n ρ j x - polarChart n ρ j y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    rw [← hmem x hx, ← hmem y hy]
    exact hL x y
  set M : ℝ := (∑ i : Fin n, 3 * ρ i) + 1 with hM_def
  have hMpos : 0 < M := by
    rw [hM_def]
    have h0 : (0 : ℝ) ≤ ∑ i : Fin n, 3 * ρ i := Finset.sum_nonneg fun i _ => by linarith [hρ i]
    linarith
  have hMb : ∀ z ∈ s, ‖polarChart n ρ j z‖ ≤ M := by
    intro z hz
    rw [hM_def]
    exact norm_polarChart_cvAnn_le hρ j hz
  set D' : ℕ → ℝ := fun k => if k = 0 then M else D k with hD'_def
  have hD'' : ∀ k : ℕ, ∀ z ∈ s,
      ‖iteratedFDerivWithin ℝ k (polarChart n ρ j) s z‖ ≤ D' k := by
    intro k z hz
    rcases eq_or_ne k 0 with hk | hk
    · subst hk
      have hD0 : D' 0 = M := by simp [hD'_def]
      rw [hD0, norm_iteratedFDerivWithin_zero]
      exact hMb z hz
    · have hDk : D' k = D k := by simp [hD'_def, hk]
      rw [hDk]
      have h1 : iteratedFDerivWithin ℝ k (polarChart n ρ j) s z
          = iteratedFDerivWithin ℝ k (polarGlob n ρ j ε) s z :=
        iteratedFDerivWithin_congr (fun w hw => (hmem w hw).symm) hz k
      rw [h1, iteratedFDerivWithin_of_isOpen k hsopen hz]
      exact hD k (Nat.one_le_iff_ne_zero.mpr hk) z
  set E' : ℕ → ℝ := fun k => max (E k) (L * max 1 ((2 * M + 1) ^ (1 - α))) with hE'_def
  have hE'' : ∀ k : ℕ, ∀ x ∈ s, ∀ y ∈ s,
      ‖iteratedFDerivWithin ℝ k (polarChart n ρ j) s x
        - iteratedFDerivWithin ℝ k (polarChart n ρ j) s y‖ ≤ E' k * ‖x - y‖ ^ α := by
    intro k x hx y hy
    have hEk : E k ≤ E' k := by simp only [hE'_def]; exact le_max_left _ _
    have hCα : L * max 1 ((2 * M + 1) ^ (1 - α)) ≤ E' k := by
      simp only [hE'_def]; exact le_max_right _ _
    rcases eq_or_ne k 0 with hk | hk
    · rw [hk] at hCα ⊢
      rw [norm_iterFDerivWithin_zero_sub]
      have hxM : ‖x‖ ≤ M := by
        have h := hMb x hx
        rw [polarChart_apply, Prod.norm_def] at h
        exact le_trans (le_max_left _ _) h
      have hyM : ‖y‖ ≤ M := by
        have h := hMb y hy
        rw [polarChart_apply, Prod.norm_def] at h
        exact le_trans (le_max_left _ _) h
      have hxyM : ‖x - y‖ ≤ 2 * M + 1 := by
        have h := norm_sub_le x y
        linarith
      have hfac : ‖x - y‖ ≤ max 1 ((2 * M + 1) ^ (1 - α)) * ‖x - y‖ ^ α := by
        have hfac' : ‖x - y‖ ^ (1 - α) ≤ max 1 ((2 * M + 1) ^ (1 - α)) := by
          rcases le_or_gt ‖x - y‖ 1 with hle | hlt
          · exact le_trans (Real.rpow_le_one (norm_nonneg _) hle (by linarith)) (le_max_left _ _)
          · exact le_trans (Real.rpow_le_rpow (norm_nonneg _) hxyM (by linarith))
              (le_max_right _ _)
        rcases eq_or_ne ‖x - y‖ 0 with h0 | h0
        · rw [h0, Real.zero_rpow hα0.ne']; simp
        · have hpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
          calc ‖x - y‖ = ‖x - y‖ ^ (1 - α) * ‖x - y‖ ^ α := by
                rw [← Real.rpow_add hpos, show (1 - α) + α = 1 by ring, Real.rpow_one]
            _ ≤ max 1 ((2 * M + 1) ^ (1 - α)) * ‖x - y‖ ^ α :=
                mul_le_mul_of_nonneg_right hfac' (Real.rpow_nonneg (norm_nonneg _) α)
      calc ‖polarChart n ρ j x - polarChart n ρ j y‖
          ≤ L * ‖x - y‖ := hL' x hx y hy
        _ ≤ L * (max 1 ((2 * M + 1) ^ (1 - α)) * ‖x - y‖ ^ α) :=
            mul_le_mul_of_nonneg_left hfac hL0
        _ = L * max 1 ((2 * M + 1) ^ (1 - α)) * ‖x - y‖ ^ α := by ring
        _ ≤ E' 0 * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right hCα (Real.rpow_nonneg (norm_nonneg _) α)
    · have h1 : iteratedFDerivWithin ℝ k (polarChart n ρ j) s x
          = iteratedFDeriv ℝ k (polarGlob n ρ j ε) x := by
        rw [iteratedFDerivWithin_congr (fun w hw => (hmem w hw).symm) hx k,
          iteratedFDerivWithin_of_isOpen k hsopen hx]
      have h2 : iteratedFDerivWithin ℝ k (polarChart n ρ j) s y
          = iteratedFDeriv ℝ k (polarGlob n ρ j ε) y := by
        rw [iteratedFDerivWithin_congr (fun w hw => (hmem w hw).symm) hy k,
          iteratedFDerivWithin_of_isOpen k hsopen hy]
      rw [h1, h2]
      exact (hE k (Nat.one_le_iff_ne_zero.mpr hk) x y).trans
        (mul_le_mul_of_nonneg_right hEk (Real.rpow_nonneg (norm_nonneg _) α))
  obtain ⟨C, hC0, hC⟩ := Work.CR.Flat.Holder.holderNorm_comp_le_of_contDiffOn hst hΦ hsopen
    htopen L hL' α hα0 D' hD'' E' hE''
  exact ⟨C, hC0, fun k u hu => hC k u hu⟩

end Work.NN.PolarChain
