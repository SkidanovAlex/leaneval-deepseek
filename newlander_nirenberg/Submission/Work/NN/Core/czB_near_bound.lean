import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmPotential_dCoord_holderNorm_le
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_cz_bound
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

noncomputable section
open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.NN.Core

lemma holderNorm_zero_univ_le_of_bound {n : ℕ} {α : ℝ}
    {g : (Fin n → ℂ) → ℂ} {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hb : ∀ z, ‖g z‖ ≤ A) (hh : ∀ x y, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) :
    Work.CR.Flat.holderNorm 0 α g Set.univ ≤ ENNReal.ofReal (A + K) := by
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ENNReal.ofReal_add hA hK]
  refine add_le_add ?_ ?_
  · rw [Work.CR.Flat.iterDerivNorm_zero]
    exact iSup₂_le fun z _ => ENNReal.ofReal_le_ofReal (hb z)
  · refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    rw [Work.CR.Flat.Cauchy.norm_iteratedFDerivWithin_zero_sub_aux g Set.univ x y]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)]
    exact hh x y

lemma sum_holderNorm_zero_univ_le {n : ℕ} {α : ℝ}
    {F : Fin n → (Fin n → ℂ) → ℂ} {A K : Fin n → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hK : ∀ j, 0 ≤ K j)
    (hb : ∀ j z, ‖F j z‖ ≤ A j) (hh : ∀ j x y, ‖F j x - F j y‖ ≤ K j * ‖x - y‖ ^ α) :
    ∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ
      ≤ ENNReal.ofReal (∑ j, (A j + K j)) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (hA j) (hK j))]
  exact Finset.sum_le_sum fun j _ =>
    holderNorm_zero_univ_le_of_bound (hA j) (hK j) (hb j) (hh j)

theorem czB_near_bound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Fin n → (Fin n → ℂ) → ℂ) (A K : Fin n → ℝ),
      (∀ j, ContDiff ℝ 1 (F j)) →
      (∀ j, 0 ≤ A j) → (∀ j, 0 ≤ K j) →
      (∀ j z, R ≤ ‖z‖ → F j z = 0) →
      (∀ j z, ‖F j z‖ ≤ A j) →
      (∀ j x y, ‖F j x - F j y‖ ≤ K j * ‖x - y‖ ^ α) →
      ∀ i : Fin n,
        (∀ z : Fin n → ℂ, ‖z‖ ≤ 4 * (Real.sqrt n * (R + 1)) + 4 →
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z‖
            ≤ C * ∑ j, (A j + K j)) ∧
        (∀ z z' : Fin n → ℂ, ‖z‖ ≤ 4 * (Real.sqrt n * (R + 1)) + 4 →
          ‖z'‖ ≤ 4 * (Real.sqrt n * (R + 1)) + 4 →
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
            - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
            ≤ C * ‖z - z'‖ ^ α * ∑ j, (A j + K j)) := by
  classical
  set ρ : ℝ := 4 * (Real.sqrt n * (R + 1)) + 4 with hρdef
  set r : Fin n → ℝ := fun _ => 2 * (ρ + 1) with hrdef
  have hsqrt1 : 1 ≤ Real.sqrt n := Work.CR.Flat.Cauchy.one_le_sqrt_nat hn
  have hRρ : R ≤ ρ + 1 := by
    have hnn : (0:ℝ) ≤ R + 1 := by linarith
    have hmul : (R + 1) ≤ Real.sqrt n * (R + 1) := by
      simpa using mul_le_mul_of_nonneg_right hsqrt1 hnn
    rw [hρdef]; linarith
  have hrpos : ∀ j, 0 < r j := by
    intro j
    rw [hrdef]
    have h1 : 0 ≤ Real.sqrt n * (R + 1) :=
      mul_nonneg (Real.sqrt_nonneg n) (by linarith)
    have h2 : (0:ℝ) < ρ + 1 := by rw [hρdef]; linarith
    linarith
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Work.CR.Flat.Cauchy.bmPotential_dCoord_holderNorm_le hn hα0 hα1 hrpos
  refine ⟨C0, hC0pos.le, ?_⟩
  intro F A K hF hA hK hsupp hbnd hholder i
  set hh : (Fin n → ℂ) → ℂ :=
    fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z with hhdef
  have hC0nn : 0 ≤ C0 := hC0pos.le
  have hSnn : 0 ≤ ∑ j, (A j + K j) := Finset.sum_nonneg fun j _ => add_nonneg (hA j) (hK j)
  have hsupp' : ∀ j z, (∃ i, r i / 2 ≤ ‖z i - (0 : Fin n → ℂ) i‖) → F j z = 0 := by
    intro j z ⟨k, hk⟩
    apply hsupp j z
    have hk1 : ρ + 1 ≤ ‖z k‖ := by
      have : r k / 2 = ρ + 1 := by rw [hrdef]; simp only; ring
      simp only [Pi.zero_apply, sub_zero] at hk
      rw [this] at hk; exact hk
    have hzk : ‖z k‖ ≤ ‖z‖ := norm_le_pi_norm z k
    linarith
  have hkey : Work.CR.Flat.holderNorm 0 α hh
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => r j / 2))
      ≤ ENNReal.ofReal C0 * ∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ := by
    rw [hhdef]
    exact hC0 F hF hsupp' i
  have hsum := sum_holderNorm_zero_univ_le hA hK hbnd hholder
  have hmain : Work.CR.Flat.holderNorm 0 α hh
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => r j / 2))
      ≤ ENNReal.ofReal (C0 * ∑ j, (A j + K j)) := by
    calc Work.CR.Flat.holderNorm 0 α hh (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => r j / 2))
        ≤ ENNReal.ofReal C0 * ∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ := hkey
      _ ≤ ENNReal.ofReal C0 * ENNReal.ofReal (∑ j, (A j + K j)) :=
          mul_le_mul_of_nonneg_left hsum bot_le
      _ = ENNReal.ofReal (C0 * ∑ j, (A j + K j)) := (ENNReal.ofReal_mul hC0nn).symm
  have hmem : ∀ z : Fin n → ℂ, ‖z‖ ≤ ρ →
      z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => r j / 2) := by
    intro z hz
    rw [Work.CR.Flat.mem_polydisc]
    intro j
    have hj : r j / 2 = ρ + 1 := by rw [hrdef]; simp only; ring
    simp only [Pi.zero_apply, sub_zero]
    rw [hj]
    have hzj : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
    linarith
  have hρeq : ρ = 4 * (Real.sqrt n * (R + 1)) + 4 := hρdef
  constructor
  · intro z hz
    have h1 : ENNReal.ofReal ‖hh z‖ ≤ ENNReal.ofReal (C0 * ∑ j, (A j + K j)) :=
      le_trans (Work.CR.Flat.norm_apply_le_holderNorm 0 α hh _
        (hmem z (by rw [hρeq]; exact hz))) hmain
    have h2 : ‖hh z‖ ≤ C0 * ∑ j, (A j + K j) :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0nn hSnn)).mp h1
    simpa [hhdef] using h2
  · intro z z' hz hz'
    by_cases hzz : z = z'
    · subst hzz
      simp [sub_self, Real.zero_rpow (ne_of_gt hα0)]
    · have hden : 0 < ‖z - z'‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz)) α
      have hsem : ENNReal.ofReal (‖hh z - hh z'‖ / ‖z - z'‖ ^ α)
          ≤ Work.CR.Flat.holderSeminorm 0 α hh
              (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => r j / 2)) := by
        have h := Work.CR.Flat.le_holderSeminorm 0 α hh
          (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => r j / 2))
          (hmem z (by rw [hρeq]; exact hz)) (hmem z' (by rw [hρeq]; exact hz')) hzz
        rwa [Work.CR.Flat.Cauchy.norm_iteratedFDerivWithin_zero_sub_aux hh _ z z'] at h
      have h1 : ENNReal.ofReal (‖hh z - hh z'‖ / ‖z - z'‖ ^ α)
          ≤ ENNReal.ofReal (C0 * ∑ j, (A j + K j)) :=
        le_trans (le_trans hsem
          (Work.CR.Flat.holderSeminorm_le_holderNorm 0 α hh _ (Nat.zero_le 0))) hmain
      have h2 : ‖hh z - hh z'‖ / ‖z - z'‖ ^ α ≤ C0 * ∑ j, (A j + K j) :=
        (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0nn hSnn)).mp h1
      rw [div_le_iff₀ hden] at h2
      calc ‖hh z - hh z'‖ ≤ (C0 * ∑ j, (A j + K j)) * ‖z - z'‖ ^ α := h2
        _ = C0 * ‖z - z'‖ ^ α * ∑ j, (A j + K j) := by ring

end Work.NN.Core
