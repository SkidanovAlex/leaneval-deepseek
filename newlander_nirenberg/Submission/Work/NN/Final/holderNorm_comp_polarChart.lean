import Mathlib
import Submission.Work.NN.Final.PolarRegions
import Submission.Work.NN.Final.PolarGlob
import Submission.Work.CR.Flat.Holder.holderNorm_comp_le_of_contDiffOn
import Submission.Work.NN.Final.ChartComp.holderNorm_comp_chartPoint

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

lemma norm_polarChart_le {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hρ : ∀ i, 0 < ρ i)
    (hε : 0 < ε) {z : Fin n → ℂ} (hz : z ∈ outRegion n ρ j ∩ {z : Fin n → ℂ | ε < ‖z j‖}) :
    ‖polarChart n ρ j z‖
      ≤ (∑ i : Fin n, (2 * ρ i + 1)) + max (Real.log 2) |Real.log (ρ j / ε)| + 1 := by
  obtain ⟨hzout, hzj⟩ := hz
  rw [mem_outRegion] at hzout
  obtain ⟨h1, h2, h3⟩ := hzout
  have hr : 0 < ‖z j‖ := lt_trans hε hzj
  have hM₁nn : 0 ≤ ∑ i : Fin n, (2 * ρ i + 1) :=
    Finset.sum_nonneg fun i _ => by linarith [hρ i]
  have hM₂pos : 0 < max (Real.log 2) |Real.log (ρ j / ε)| :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) (le_max_left _ _)
  have hcoord : ‖z‖ ≤ ∑ i : Fin n, (2 * ρ i + 1) := by
    refine (pi_norm_le_iff_of_nonneg hM₁nn).mpr fun i => ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => 2 * ρ i + 1)
      (fun i _ => by linarith [hρ i]) (Finset.mem_univ i))
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h := h1 i hlt; linarith [hρ i]
    · rw [heq]; linarith [hρ j]
    · have h := h3 i hgt; linarith [hρ i]
  have hlog : |Real.log (ρ j / ‖z j‖)| ≤ max (Real.log 2) |Real.log (ρ j / ε)| := by
    have hdown : ρ j / ‖z j‖ > 1 / 2 := by
      rw [gt_iff_lt, lt_div_iff₀ hr]
      linarith
    have hup : ρ j / ‖z j‖ < ρ j / ε := by
      rw [div_lt_div_iff₀ hr hε]
      exact mul_lt_mul_of_pos_left hzj (hρ j)
    have hlowlog : -(Real.log 2) < Real.log (ρ j / ‖z j‖) := by
      have h' := Real.log_lt_log (show (0:ℝ) < 1 / 2 by norm_num) hdown
      have hinv : Real.log ((1:ℝ) / 2) = -Real.log 2 := by
        rw [show ((1:ℝ) / 2) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
      linarith
    have huplog : Real.log (ρ j / ‖z j‖) < Real.log (ρ j / ε) :=
      Real.log_lt_log (by positivity) hup
    rcases le_or_gt 0 (Real.log (ρ j / ‖z j‖)) with hpos | hneg
    · rw [abs_of_nonneg hpos]
      exact le_trans huplog.le (le_trans (le_abs_self _) (le_max_right _ _))
    · rw [abs_of_neg hneg]
      exact le_trans (by linarith) (le_max_left _ _)
  rw [polarChart_apply, Prod.norm_def, Real.norm_eq_abs]
  exact max_le (by linarith) (by linarith)

/-- The global model agrees with the polar chart on the annulus `ε ≤ ‖z j‖`. -/
lemma polarGlob_eq_polarChart {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ j) {z : Fin n → ℂ} (hz : ε ≤ ‖z j‖) :
    polarGlob n ρ j ε z = polarChart n ρ j z := by
  have hr : 0 < ‖z j‖ := lt_of_lt_of_le hε hz
  have hmain : polarLogCoord n ρ j ε z = Real.log (ρ j / ‖z j‖) := by
    rw [polarLogCoord_eq_log hε hρ hz, Real.log_div (ne_of_gt hρ) (ne_of_gt hr)]
  rw [polarGlob_apply, polarChart_apply, hmain]

theorem holderNorm_comp_polarChart {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (j : Fin n) {ε : ℝ} (hε : 0 < ε) (hερ : ε < ρ j) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (u : (Fin n → ℂ) × ℝ → ℂ),
      ContDiffOn ℝ (k : WithTop ENat) u
        (Work.NN.Final.flatRegion n ρ j ε ×ˢ {t : ℝ | -(1:ℝ) < t}) →
      Work.CR.Flat.holderNorm k α (fun z => u (Work.NN.Final.polarChart n ρ j z))
          (Work.NN.Final.outRegion n ρ j ∩ {z | ε < ‖z j‖})
        ≤ ENNReal.ofReal (C k) *
          Work.CR.Flat.holderNorm k α u
            (Work.NN.Final.flatRegion n ρ j ε ×ˢ {t : ℝ | -(1:ℝ) < t}) := by
  classical
  have hρj : 0 < ρ j := hρ j
  set s : Set (Fin n → ℂ) := outRegion n ρ j ∩ {z : Fin n → ℂ | ε < ‖z j‖} with hs_def
  set t : Set ((Fin n → ℂ) × ℝ) := flatRegion n ρ j ε ×ˢ {x : ℝ | -(1:ℝ) < x} with ht_def
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) (polarGlob n ρ j ε) := contDiff_polarGlob hε
  obtain ⟨D, hD⟩ := exists_bound_iteratedFDeriv_polarGlob (n := n) (ρ := ρ) (j := j) (ε := ε) hε
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_polarGlob (n := n) (ρ := ρ) (j := j) (ε := ε) hε hΨ D hD
  obtain ⟨E, hE⟩ := exists_holderE_polarGlob (n := n) (ρ := ρ) (j := j) (ε := ε) hε hα0 hα1 hΨ D hD
  have hsopen : IsOpen s := by
    rw [hs_def]
    exact (isOpen_outRegion n (hρ := hρ) j).inter
      (isOpen_lt continuous_const (continuous_norm.comp (continuous_apply j)))
  have htopen : IsOpen t := by
    rw [ht_def]
    exact (isOpen_flatRegion n (hρ := hρ) j ε).prod isOpen_Ioi
  have hmem : ∀ z ∈ s, polarGlob n ρ j ε z = polarChart n ρ j z := by
    intro z hz
    rw [hs_def] at hz
    exact polarGlob_eq_polarChart hε hρj (le_of_lt hz.2)
  have hst : Set.MapsTo (polarChart n ρ j) s t := by
    intro z hz
    rw [hs_def] at hz
    obtain ⟨hzout, hzj⟩ := hz
    rw [mem_outRegion] at hzout
    obtain ⟨h1, h2, h3⟩ := hzout
    have hr : 0 < ‖z j‖ := lt_trans hε hzj
    rw [ht_def, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · show z ∈ flatRegion n ρ j ε
      rw [mem_flatRegion]
      exact ⟨h1, ⟨hzj, by linarith⟩, h3⟩
    · show -(1:ℝ) < Real.log (ρ j / ‖z j‖)
      have hdown : ρ j / ‖z j‖ > 1 / 2 := by
        rw [gt_iff_lt, lt_div_iff₀ hr]
        linarith
      have hl : Real.log ((1:ℝ) / 2) < Real.log (ρ j / ‖z j‖) :=
        Real.log_lt_log (by norm_num) hdown
      have hinv : Real.log ((1:ℝ) / 2) = -Real.log 2 := by
        rw [show ((1:ℝ) / 2) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
      have h2' : Real.log 2 < 1 := by
        have := Real.log_lt_sub_one_of_pos (show (0:ℝ) < 2 by norm_num) (by norm_num)
        linarith
      linarith
  have hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) (polarChart n ρ j) s := by
    intro m
    have h1 : ContDiffOn ℝ (m : WithTop ENat) (polarGlob n ρ j ε) s :=
      (hΨ.contDiffOn.of_le (ChartComp.natCast_le_top_nat m)).mono (subset_univ s)
    exact h1.congr fun z hz => (hmem z hz).symm
  have hL' : ∀ x ∈ s, ∀ y ∈ s, ‖polarChart n ρ j x - polarChart n ρ j y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    rw [← hmem x hx, ← hmem y hy]
    exact hL x y
  set M : ℝ := (∑ i : Fin n, (2 * ρ i + 1)) + max (Real.log 2) |Real.log (ρ j / ε)| + 1
    with hM_def
  have hMpos : 0 < M := by
    have h2 : 0 ≤ max (Real.log 2) |Real.log (ρ j / ε)| :=
      le_trans (Real.log_nonneg (by norm_num)) (le_max_left _ _)
    have h1 : 0 ≤ ∑ i : Fin n, (2 * ρ i + 1) :=
      Finset.sum_nonneg fun i _ => by linarith [hρ i]
    rw [hM_def]; linarith
  have hMb : ∀ z ∈ s, ‖polarChart n ρ j z‖ ≤ M := by
    intro z hz
    rw [hs_def] at hz
    have := norm_polarChart_le hρ hε hz
    rwa [hM_def]
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
    have hEk : E k ≤ E' k := by
      simp only [hE'_def]
      exact le_max_left _ _
    have hCα : L * max 1 ((2 * M + 1) ^ (1 - α)) ≤ E' k := by
      simp only [hE'_def]
      exact le_max_right _ _
    rcases eq_or_ne k 0 with hk | hk
    · rw [hk] at hCα ⊢
      rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub]
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
  refine ⟨C, hC0, fun k u hu => ?_⟩
  exact hC k u hu

end Work.NN.Final
