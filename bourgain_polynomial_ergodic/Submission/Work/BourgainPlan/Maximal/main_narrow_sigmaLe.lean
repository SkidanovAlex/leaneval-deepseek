import Mathlib
import Submission.Work.BourgainPlan.Maximal.hstep3_msw_uniform
import Submission.Work.IonescuWainger.main_real_of_inputs
import Submission.Work.IonescuWainger.ortho_apply_lower_strata_system_ennreal_uniform
import Submission.Work.IonescuWainger.ortho_apply_upper_pow
import Submission.Work.IonescuWainger.opArc_sigmaLe_eq_sum_strata
import Submission.Work.BourgainPlan.IonescuWainger.erdos_rado_sunflower

namespace Work.BourgainPlan.Maximal

open MeasureTheory ENNReal
open scoped ENNReal BigOperators
open Work.BourgainPlan.IonescuWainger

/-- **Tao's `main` over `Σ_{≤k}(S)` for a general narrow symbol**: the `ℓ^{2r}` endpoint (the case `p = 2r`, `r ≥ 2`) of the Ionescu–Wainger bound over the torsion-arc set `sigmaLeFinset S k`, with a constant `K` uniform in `S`. Route: assemble `Work.IonescuWainger.main_real_of_inputs` with `hstep1` from `ortho_apply_lower_strata_system_ennreal_uniform` (the Erdős–Rado sunflower threshold `M` supplied by `erdos_rado_sunflower`), `hstep3` from `hstep3_msw_uniform` (the multiplier-norm hypothesis of the statement is its hypothesis, and `hεq2` is its strict smallness), and `hstep4` from `ortho_apply_upper_pow` (with the given flat bump `φ`), then rewrite the signed sum over the strata as the unsigned sum over `sigmaLeFinset S k` with `opArc_sigmaLe_eq_sum_strata`. -/
theorem main_narrow_sigmaLe {k r : ℕ} (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∀ {qmax : ℕ} (hqmax : 1 ≤ qmax) {Cφ Mφ : ℝ} (hCφ : 0 ≤ Cφ) (hMφ : 0 ≤ Mφ),
      ∃ K : ℝ, 0 < K ∧
      ∀ {S : Finset ℕ} (h2S : ∀ q ∈ S, 2 ≤ q)
        (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
        (hmax : ∀ q ∈ S, q ≤ qmax)
        {ε η : ℝ} (hε0 : 0 < ε) (hη0 : 0 < η)
        (hεη : ε + η < 1 / (qmax : ℝ) ^ (2 * k)) (hη2 : 2 * η < 1 / (qmax : ℝ) ^ (2 * k))
        (hεq : ε * (qmax : ℝ) ^ k ≤ 1) (hεq2 : ε * (qmax : ℝ) ^ k < 1 / 2)
        (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
        (hψsupp : ∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ε < ‖ξ‖ → ψ ξ = 0)
        (A : ℝ) (hA : 0 ≤ A)
        (hMult : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
          ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
              (fun ξ : ℝ => Work.BourgainPlan.Thm52.circleLift ψ ξ
                * FourierTransform.fourier g ξ) x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume
            ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ)))
              * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume)
        (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
        (hφbd : ∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ‖φ ξ‖ ≤ Mφ)
        (hφsupp : ∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), η < ‖ξ‖ → φ ξ = 0)
        (hφone : ∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ‖ξ‖ ≤ ε → φ ξ = 1)
        {Kφ : ℤ → ℂ} (hKφ : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1)) = Kφ m)
        (hdecayφ : ∀ m : ℤ, ‖Kφ m‖
          ≤ Cφ * η / (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2))
        (hsmallN : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) →
          Work.BourgainPlan.IonescuWainger.HasNonce A →
          2 * (r : ℝ) * ε < 1 / ((∏ j, Work.BourgainPlan.IonescuWainger.QA (A j) : ℕ) : ℝ))
        (hsmallP : ∀ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∀ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
            (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)) →
            2 * (r : ℝ) * ε * ((Work.BourgainPlan.IonescuWainger.QA A₀ *
              (∏ i, Work.BourgainPlan.IonescuWainger.QA ((A i).1)) : ℕ) : ℝ) < 1)
        (f : ℤ →₀ ℂ),
        ∑' n : ℤ, ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc ψ hψ
            (Work.BourgainPlan.IonescuWainger.sigmaLeFinset S k) (⇑f)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) n‖ ^ (2 * r))
          ≤ ENNReal.ofReal (K * A ^ (2 * r)) *
            ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) := by
  intro qmax hqmax Cφ Mφ hCφ hMφ
  classical
  obtain ⟨M₀, hM₀⟩ := Work.BourgainPlan.IonescuWainger.erdos_rado_sunflower k r
  set M : ℕ := max M₀ 2 with hMdef
  have hM2 : 2 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hM0M : M₀ ≤ M := by rw [hMdef]; exact le_max_left _ _
  obtain ⟨C, hCpos, hC⟩ :=
    Work.IonescuWainger.ortho_apply_lower_strata_system_ennreal_uniform k r hr hk
  obtain ⟨C₃, hC₃pos, hC₃⟩ :=
    Work.BourgainPlan.Maximal.hstep3_msw_uniform (k := k) (r := r) hr hk
  set C₁ : ℝ := C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r with hC₁def
  set C₄ : ℝ := ((Mφ ^ 2 * (2 ^ k : ℝ)) ^ (1 / (2 * r : ℝ)) *
      (8 * Cφ * (2 ^ k : ℝ)) ^ (1 - 2 / (2 * r : ℝ))) ^ (2 * r : ℝ) with hC₄def
  have hC₁nn : 0 ≤ C₁ := by rw [hC₁def]; positivity
  have hC₄nn : 0 ≤ C₄ := by rw [hC₄def]; exact Real.rpow_nonneg (by positivity) _
  refine ⟨max 1 (C₁ * C₃ ^ (2 * r) * C₄), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro S h2S hS hmax ε η hε0 hη0 hεη hη2 hεq hεq2
      ψ hψ hψsupp A hA hMult φ hφ hφbd hφsupp hφone Kφ hKφ hdecayφ hsmallN hsmallP f
  have hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A :=
    fun T _ hcard hMle => hM₀ T hcard (hM0M.trans hMle)
  have hstep1 : ∑' x : ℤ, ENNReal.ofReal (‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        (1 : ℂ) * opArc ψ hψ (sigmaStrataFinset A) (⇑f) (memℓp_finsupp f) x‖ ^ (2 * r))
      ≤ ENNReal.ofReal C₁ *
        ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑' x : ℤ, (∑ α ∈ strataCompFinset S k A₀,
              ENNReal.ofReal (‖opArc ψ hψ
                (arcShift (sigmaStrataFinset A₀) α) (⇑f)
                (memℓp_finsupp f) x‖ ^ 2)) ^ (r : ℝ) :=
    hC h2S hS hM2 hsun hε0.le ψ hψ hψsupp hsmallN hsmallP
      (fun _ => (1 : ℂ)) (fun _ => by simp) (⇑f) (memℓp_finsupp f)
  have hpow : (C₃ * A) ^ (2 * (r : ℝ)) = (C₃ * A) ^ (2 * r) := by
    rw [show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hstep3 : ∀ (A₀ : Finset ℕ), A₀ ⊆ S → A₀.card ≤ k →
      ∀ (F : ↥(strataCompFinset S k A₀) → ℤ → ℂ) (hF : ∀ t, Memℓp (F t) 2),
      ∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀),
          ENNReal.ofReal (‖opArc ψ hψ
            (arcShift (sigmaStrataFinset A₀) α.1)
            (F α) (hF α) n‖ ^ 2)) ^ (r : ℝ)
        ≤ ENNReal.ofReal ((C₃ * A) ^ (2 * r)) *
          ∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀),
            ENNReal.ofReal (‖F α n‖ ^ 2)) ^ (r : ℝ) := by
    intro A₀ hA₀S hk₀ F hF
    have h := hC₃ (qmax := qmax) hqmax h2S hS hmax ε hε0 hεq2 ψ hψ hψsupp A hA hMult A₀ hA₀S hk₀ F hF
    rwa [hpow] at h
  have hstep4 : ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
            ENNReal.ofReal (‖opArc φ hφ
              (arcShift (sigmaStrataFinset A₀) α) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ)
      ≤ ENNReal.ofReal C₄ * ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) := by
    have h := Work.IonescuWainger.ortho_apply_upper_pow (S := S) h2S hS hmax hqmax (k := k) (ε := η)
      hη0 hη2 φ hφ (M := Mφ) hMφ hφbd hφsupp (K := Kφ) (C := Cφ) hCφ hKφ hdecayφ
      (r := r) (le_trans (by norm_num) hr) f
    rw [hC₄def]
    exact h
  have hmain := Work.IonescuWainger.main_real_of_inputs (S := S) h2S hS hr hk hmax hqmax hε0 hεη
    ψ φ hψ hφ hψsupp hφsupp hφone (εs := fun _ => (1 : ℂ)) (fun _ => by simp) f
    (C₁ := C₁) (W := (C₃ * A) ^ (2 * r)) (C₄ := C₄) hC₁nn
    (pow_nonneg (mul_nonneg hC₃pos.le hA) _) hC₄nn hstep1 hstep3 hstep4
  have hkey : (∑' n : ℤ, ENNReal.ofReal (‖opArc ψ hψ
        (sigmaLeFinset S k) (⇑f) (memℓp_finsupp f) n‖ ^ (2 * r)))
      = ∑' n : ℤ, ENNReal.ofReal (‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          (1 : ℂ) * opArc ψ hψ (sigmaStrataFinset A) (⇑f) (memℓp_finsupp f) n‖ ^ (2 * r)) := by
    refine tsum_congr (fun n => ?_)
    rw [Work.IonescuWainger.opArc_sigmaLe_eq_sum_strata h2S hS ψ hψ (⇑f) (memℓp_finsupp f)]
    simp only [one_mul, Finset.sum_apply]
  rw [hkey]
  refine hmain.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  calc C₁ * (C₃ * A) ^ (2 * r) * C₄
      = (C₁ * C₃ ^ (2 * r) * C₄) * A ^ (2 * r) := by rw [mul_pow]; ring
    _ ≤ max 1 (C₁ * C₃ ^ (2 * r) * C₄) * A ^ (2 * r) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hA _)

end Work.BourgainPlan.Maximal
