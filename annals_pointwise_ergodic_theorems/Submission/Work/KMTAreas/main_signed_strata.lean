/-
# Tao's Ionescu-Wainger main theorem for an arbitrary *signed* selection of strata

This is the version of `Work.BourgainPlan.Maximal.main_narrow_sigmaLe_uniform` in which the
operator over the strata of a pairwise coprime set `S` is replaced by an arbitrary *signed* sum

  `sum_{A subset S, |A| <= k} es A * Op_{psi;Sigma_A}`,

with coefficients `‖es A‖ <= 1`, and the conclusion is the `l^{2r}` bound for that signed sum (no
longer rewritten as `Op_{psi;Sigma_{<=k}}`).  This is Tao's *superset bound* (arXiv:2008.05066,
Theorem `main` in the form used for a subset of the major arcs): the only step of the proof that
sees the coefficients is `hstep1`, Tao's `ortho-apply`(i), and that step is available for arbitrary
`es` (`Work.IonescuWainger.ortho_apply_lower_strata_system_ennreal_uniform`).

The proof is the proof of `main_narrow_sigmaLe_uniform` verbatim, with `es` threaded through
`hstep1` and the final rewriting step (`opArc_sigmaLe_eq_sum_strata`) dropped.

## Why the signed form is the one needed for Area A1

The workspace's `iwArithFreqs ρ l` is *not* the full arc set `Σ_{<=D+1}(S_l)` of Tao's denominator
set `S_l` of Appendix A of Krause-Mirek-Tao: it is the disjoint union of the strata `Σ_A` over the
*selected* subsets

  `P = {A subset S_l : |A| <= D_ρ + 1, Q_0^{(l)} in A or |A| <= D_ρ}`,

(`Work.KMTAreas.strata_biUnion_eq_iwArithFreqs`).  Taking `εs A = 1` for `A in P` and `εs A = 0`
otherwise turns the signed sum above into `sum_{A in P} Op_{psi;Σ_A}`, which by additivity of the
multiplier over the disjoint strata is `Op_{psi;iwArithFreqs ρ l}` -- the Ionescu-Wainger
projection of Theorem `thm:iw` of Krause-Mirek-Tao.  Since a bound for the *full* arc set does not
control its subsets, this superset/signed form is exactly the statement the bridge needs.
-/
import Mathlib
import Submission.Work.BourgainPlan.Maximal.hstep3_msw_uniform
import Submission.Work.BourgainPlan.IonescuWainger.erdos_rado_sunflower
import Submission.Work.IonescuWainger.ortho_apply_lower_strata_system_ennreal_uniform
import Submission.Work.IonescuWainger.ortho_apply_upper_pow
import Submission.Work.BourgainPlan.Maximal.iw_superset

namespace Work.KMTAreas

open MeasureTheory ENNReal
open scoped ENNReal BigOperators
open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false

/-- **Tao's `main` for a signed selection of strata**: for a pairwise coprime set `S` of integers
`>= 2`, an arbitrary family of coefficients `es` with `‖es A‖ <= 1` and a narrow symbol `ψ` whose
`R`-multiplier norm at the exponent `2r` is at most `A`, the signed sum of the stratum operators
`sum_{A subset S, |A| <= k} es A · Op_{ψ;Σ_A}` satisfies the `l^{2r}` bound with a constant
`K A^{2r}` where `K` does not depend on `S`, `qmax`, `ε`, `η`, `ψ`, `es` or `f`. -/
theorem main_signed_strata_uniform {k r : ℕ} (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∀ {Cφ Mφ : ℝ} (hCφ : 0 ≤ Cφ) (hMφ : 0 ≤ Mφ),
      ∃ K : ℝ, 0 < K ∧
      ∀ {qmax : ℕ} (hqmax : 1 ≤ qmax)
        {S : Finset ℕ} (h2S : ∀ q ∈ S, 2 ≤ q)
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
        (εs : Finset ℕ → ℂ) (hεs : ∀ A, ‖εs A‖ ≤ 1)
        (f : ℤ →₀ ℂ),
        ∑' n : ℤ, ENNReal.ofReal (‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            εs A * Work.BourgainPlan.IonescuWainger.opArc ψ hψ
              (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) (⇑f)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) n‖ ^ (2 * r))
          ≤ ENNReal.ofReal (K * A ^ (2 * r)) *
            ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) := by
  intro Cφ Mφ hCφ hMφ
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
  intro qmax hqmax S h2S hS hmax ε η hε0 hη0 hεη hη2 hεq hεq2
      ψ hψ hψsupp A hA hMult φ hφ hφbd hφsupp hφone Kφ hKφ hdecayφ hsmallN hsmallP εs hεs f
  have hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A :=
    fun T _ hcard hMle => hM₀ T hcard (hM0M.trans hMle)
  have hstep1 : ∑' x : ℤ, ENNReal.ofReal (‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        εs A * opArc ψ hψ (sigmaStrataFinset A) (⇑f) (memℓp_finsupp f) x‖ ^ (2 * r))
      ≤ ENNReal.ofReal C₁ *
        ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑' x : ℤ, (∑ α ∈ strataCompFinset S k A₀,
              ENNReal.ofReal (‖opArc ψ hψ
                (arcShift (sigmaStrataFinset A₀) α) (⇑f)
                (memℓp_finsupp f) x‖ ^ 2)) ^ (r : ℝ) :=
    hC h2S hS hM2 hsun hε0.le ψ hψ hψsupp hsmallN hsmallP εs hεs (⇑f) (memℓp_finsupp f)
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
    ψ φ hψ hφ hψsupp hφsupp hφone (εs := εs) hεs f
    (C₁ := C₁) (W := (C₃ * A) ^ (2 * r)) (C₄ := C₄) hC₁nn
    (pow_nonneg (mul_nonneg hC₃pos.le hA) _) hC₄nn hstep1 hstep3 hstep4
  refine hmain.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  calc C₁ * (C₃ * A) ^ (2 * r) * C₄
      = (C₁ * C₃ ^ (2 * r) * C₄) * A ^ (2 * r) := by rw [mul_pow]; ring
    _ ≤ max 1 (C₁ * C₃ ^ (2 * r) * C₄) * A ^ (2 * r) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hA _)

end Work.KMTAreas
