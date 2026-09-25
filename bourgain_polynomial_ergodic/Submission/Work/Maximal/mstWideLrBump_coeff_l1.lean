import Mathlib
import Submission.Work.Maximal.mstWideAux
import Submission.Work.BourgainPlan.Maximal.mstHat_sampling_bound

namespace Work.Maximal

theorem mstWideLrBump_coeff_l1 (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) {M E : ℝ}
    (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hbound : ∀ t : ℝ, ‖Work.BourgainPlan.Maximal.mstHat η t‖ ≤ M)
    (hdecay : ∀ t : ℝ, t ≠ 0 → ‖Work.BourgainPlan.Maximal.mstHat η t‖ ≤ E / t ^ 2)
    (hid : ∀ (s : ℕ) (m : ℤ),
      (∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          Work.Maximal.mstWideBump P χ η s ξ * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1)))
        = ((Work.Maximal.mstWideC P s : ℂ))⁻¹
            * Work.BourgainPlan.Maximal.mstHat η ((m : ℝ) / Work.Maximal.mstWideC P s)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℕ,
      Summable (fun m : ℤ => ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          Work.Maximal.mstWideBump P χ η s ξ * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          Work.Maximal.mstWideBump P χ η s ξ * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖) ≤ K := by
  obtain ⟨K, hKpos, hK⟩ :=
    Work.BourgainPlan.Maximal.mstHat_sampling_bound (η := η) hM hE hbound hdecay
  refine ⟨K, hKpos, fun s => ?_⟩
  have hc1 : 1 ≤ mstWideC P s := one_le_mstWideC P s
  have hcpos : 0 < mstWideC P s := lt_of_lt_of_le one_pos hc1
  have hcoe : ∀ m : ℤ,
      ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          mstWideBump P χ η s ξ * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖
      = (mstWideC P s)⁻¹
          * ‖Work.BourgainPlan.Maximal.mstHat η ((m : ℝ) / mstWideC P s)‖ := by
    intro m
    rw [hid s m, norm_mul, norm_inv,
      show ‖((mstWideC P s : ℝ) : ℂ)‖ = |mstWideC P s| from by simp, abs_of_pos hcpos]
  obtain ⟨hsum, htsum⟩ := hK (mstWideC P s) 0 hc1
  simp only [add_zero] at hsum htsum
  refine ⟨hsum.congr (fun m => (hcoe m).symm), ?_⟩
  calc ∑' m : ℤ, ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          mstWideBump P χ η s ξ * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖
      = ∑' m : ℤ, (mstWideC P s)⁻¹
          * ‖Work.BourgainPlan.Maximal.mstHat η ((m : ℝ) / mstWideC P s)‖ :=
        tsum_congr (fun m => hcoe m)
    _ ≤ K := htsum

end Work.Maximal
