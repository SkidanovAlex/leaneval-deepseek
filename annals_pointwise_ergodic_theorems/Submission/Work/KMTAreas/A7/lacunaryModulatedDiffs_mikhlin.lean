import Mathlib
import Submission.Work.KMTAreas.A7.varphitildeNt_eq_profile
import Submission.Work.KMTAreas.A7.gProfile_facts
import Submission.Work.KMTAreas.A7.lacModDiff_hasDerivAt
import Submission.Work.KMTAreas.A7.exists_Phi_deriv_bounds
import Submission.Work.KMTAreas.A7.lacModDiff_value_bound
import Submission.Work.KMTAreas.A7.lacModDiff_deriv_bound
import Submission.Work.KMTAreas.A7.lacModDiff_deriv2_bound

set_option autoImplicit false

namespace Work.KMTAreas.A7

noncomputable section

theorem lacunaryModulatedDiffs_mikhlin {Lam del : ℝ} (hLam : 1 < Lam) (hdel : 0 < del)
    {Φ : ℝ → ℂ} (hΦcd : ContDiff ℝ 2 Φ) (hΦsupp : ∀ u : ℝ, 1 ≤ |u| → Φ u = 0)
    (hΦflat : ∀ u : ℝ, |u| ≤ del → Φ u = Φ 0) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ {cbar : ℝ}, 0 ≤ cbar →
      ∀ {sigma : ℕ → ℝ}, (∀ n : ℕ, 0 < sigma n) →
        (∀ n : ℕ, sigma (n + 1) ≥ Lam * sigma n) →
      ∀ {lam : ℕ → ℝ}, (∀ n : ℕ, |lam n| ≤ cbar * sigma n) →
        (∀ n : ℕ, |lam (n + 1) - lam n| ≤ cbar * sigma n) →
      ∀ (K : ℕ) (eps : ℕ → ℂ), (∀ n : ℕ, ‖eps n‖ ≤ 1) →
        MikhlinBound (fun ξ : ℝ => ∑ n ∈ Finset.range K,
          eps n * (Φ (sigma (n + 1) * ξ) * ee (lam (n + 1) * ξ)
            - Φ (sigma n * ξ) * ee (lam n * ξ)))
          (Cc * (1 + cbar) ^ 2) := by
  classical
  -- ### Bounds and vanishing for `Φ`, `deriv Φ` and `iteratedDeriv 2 Φ`
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hΦb, hΦdb, hΦd2b, hΦdsupp, hΦd2supp⟩ :=
    exists_Phi_deriv_bounds hΦcd hΦsupp
  -- ### The three pointwise Mikhlin estimates
  obtain ⟨C4, hC4nn, hC4⟩ := lacModDiff_value_bound hLam hdel hM0 hΦb hΦsupp hΦflat
  obtain ⟨C5, hC5nn, hC5⟩ := lacModDiff_deriv_bound hLam hM0 hM1 hΦb hΦsupp hΦdb hΦdsupp
  obtain ⟨C6, hC6nn, hC6⟩ :=
    lacModDiff_deriv2_bound hLam hM0 hM1 hM2 hΦb hΦsupp hΦdb hΦdsupp hΦd2b hΦd2supp
  -- ### Differentiability of `Φ` and of `deriv Φ`
  have hΦd : ∀ y : ℝ, HasDerivAt Φ (deriv Φ y) y := fun y =>
    (hΦcd.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hΦd2 : ∀ y : ℝ, HasDerivAt (deriv Φ) (iteratedDeriv 2 Φ y) y := by
    intro y
    have hdiff : DifferentiableAt ℝ (iteratedDeriv 1 Φ) y :=
      (ContDiff.differentiable_iteratedDeriv 1 hΦcd (by norm_num)) y
    have h := hdiff.hasDerivAt
    rw [iteratedDeriv_one] at h
    refine h.congr_deriv ?_
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  refine ⟨C4 + C5 + C6, by linarith, ?_⟩
  intro cbar hcbar sigma hspos hstep lam hlam1 hlam2 K eps heps
  let Ψ : ℝ → ℂ := fun ξ : ℝ => ∑ n ∈ Finset.range K,
    eps n * (modBlock Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlock Φ (sigma n) (lam n) ξ)
  change MikhlinBound Ψ ((C4 + C5 + C6) * (1 + cbar) ^ 2)
  have hpos2 : (0 : ℝ) ≤ (1 + cbar) ^ 2 := by positivity
  have hle : ∀ C : ℝ, C ≤ C4 + C5 + C6 →
      C * (1 + cbar) ^ 2 ≤ (C4 + C5 + C6) * (1 + cbar) ^ 2 :=
    fun C hC => mul_le_mul_of_nonneg_right hC hpos2
  have hstep' : ∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1) := fun n => hstep n
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · intro ξ
    exact le_trans (hC4 hcbar hspos hstep' hlam1 hlam2 K eps heps ξ)
      (hle C4 (by linarith))
  · intro ξ
    have hd : deriv Ψ ξ = ∑ n ∈ Finset.range K,
        eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD Φ (sigma n) (lam n) ξ) :=
      (lacModDiff_hasDerivAt hΦd hΦd2 sigma lam eps K).1 ξ |>.deriv
    rw [hd]
    exact le_trans (hC5 hcbar hspos hstep' hlam1 hlam2 K eps heps ξ)
      (hle C5 (by linarith))
  · intro ξ
    have hd2 : HasDerivAt (fun ξ : ℝ => ∑ n ∈ Finset.range K,
        eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD Φ (sigma n) (lam n) ξ))
        (∑ n ∈ Finset.range K,
          eps n * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD2 Φ (sigma n) (lam n) ξ)) ξ :=
      (lacModDiff_hasDerivAt hΦd hΦd2 sigma lam eps K).2 ξ
    have hderiv : deriv Ψ = fun ξ : ℝ => ∑ n ∈ Finset.range K,
        eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD Φ (sigma n) (lam n) ξ) := by
      funext ξ
      exact (lacModDiff_hasDerivAt hΦd hΦd2 sigma lam eps K).1 ξ |>.deriv
    have hiter : iteratedDeriv 2 Ψ ξ = ∑ n ∈ Finset.range K,
        eps n * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD2 Φ (sigma n) (lam n) ξ) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      rw [hderiv]
      exact hd2.deriv
    rw [hiter]
    exact le_trans (hC6 hcbar hspos hstep' hlam1 hlam2 K eps heps ξ)
      (hle C6 (by linarith))

end

end Work.KMTAreas.A7
