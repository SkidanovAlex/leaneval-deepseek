import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.FTS.PhiStar.Series.eFam_zero_moment
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt
import Submission.Work.FTS.PhiStar.Series.BslOp.Setup
import Submission.Work.FTS.PhiStar.Series.BslOp.Bounds
import Submission.Work.FTS.PhiStar.Series.BslOp.Deriv
import Submission.Work.FTS.PhiStar.Series.Deleg.psiAngBounds
import Submission.Work.FTS.PhiStar.Series.bmode_decay15
import Submission.Work.FTS.PhiStar.Series.Deleg.psiExpansion
import Submission.Work.FTS.PhiStar.Series.Deleg.psiRadFacts
import Submission.Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability
import Submission.Work.FTS.PhiStar.Series.Deleg.rpowMajorant
import Submission.Work.FTS.PhiStar.Series.Deleg.termEstimates
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.phiAj_smooth2
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.PhiStar.Radial.radGreenIntended
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled
import Submission.Work.FTS.PhiStar.RadialWAux.radPhi_iteratedDeriv
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_integral_bound
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_contDiffOn
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The mode series solves the elliptic equation.**  This is `psiSeries_bslOp` with the crux
estimates taken as explicit hypotheses. -/
theorem psiSeries_bslOp_of_facts (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : AngModel α ψ)
    (hAng : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |Gegenbauer.eFam m θ| ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ∧
      |deriv (Gegenbauer.eFam m) θ|
        ≤ 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 2 ∧
      |iteratedDeriv 2 (Gegenbauer.eFam m) θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
            * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 4 ∧
      |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 3)
    (hDec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hGamma : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 2 → ∀ z : ℝ, 0 < z →
      |iteratedDeriv k (gammaFun α m) z| ≤ C / Gegenbauer.lam m)
    (hODE : ∀ m : ℕ, 1 ≤ m → ∀ z : ℝ, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (gammaFun α m)) z
        - α * (5 + α) * z * deriv (gammaFun α m) z
        + Gegenbauer.lam m * gammaFun α m z = VocabO.phiA α z)
    (hInt : (∀ m : ℕ, ContinuousOn (fun t => cmode m (RemSource α ψ) t) (Set.Ioi 0)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => cmode m (RemSource α ψ) t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => cmode m (RemSource α ψ) t * t ^ (-(2 * (m : ℝ) / α) - 1))
        (Set.Ioi 1)) ∧
      ContinuousOn (VocabO.phiA α) (Set.Ioi 0) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)))
    (hmaj : ∀ D : ℝ, Summable fun m : ℕ => D * majPow m)
    (hterm : ∀ (Cdec CBz Kφ : ℝ), 0 < Cdec → 0 < CBz → 0 < Kφ → ∀ cθ : ℝ, 0 < cθ →
      ∃ D : ℝ, 0 < D ∧ ∀ m : ℕ, 1 ≤ m →
        let L := (Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)
        (α ^ 2 * Cdec * CBz * Kφ / L * (3 * ((m : ℝ) + 1)) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4)
            ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3)
            ≤ D * majPow m))
    (hExp : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      (∑' m : ℕ, bmode m ψ * Gegenbauer.eFam m θ) = ψ θ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Elliptic.bslOp α (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
        = RemSource α ψ z θ := by
  intro z hz θ hθ hθ2
  obtain ⟨D, hDpos, hB0, hB1, hB2, hB3, hB4, hB5⟩ :=
    mode_bounds α ψ hα hψ.moment hAng hDec hGamma hInt hterm z hz θ hθ hθ2
  obtain ⟨hPz, hPz2, hPt, hPt2, hPtan, hLzero⟩ :=
    deriv_series α ψ hα hInt hmaj z hz θ hθ hθ2 D hB0 hB1 hB2 hB3 hB4 hB5
  rw [Elliptic.bslOp_apply, hLzero, hPz2, hPz, hPt2, hPtan,
    show psiSeries α (RemSource α ψ) z θ
        = ∑' m : ℕ, acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ from rfl]
  -- the mode coefficient of `ψ` vanishes
  have hb0 : bmode 0 ψ = 0 := by
    have hF : Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
      simpa only [Elliptic.Fstar] using hψ.moment
    rw [bmode_eq_cmode 0 ψ 0]
    exact eFam_zero_moment (fun _ θ => ψ θ) hF
  have hac0 : ∀ y : ℝ, acoeff α 0 (RemSource α ψ) y = 0 := by
    intro y
    rw [acoeff_RemSource, hb0]
    ring
  have hdiffA : ∀ m : ℕ,
      (∀ y, 0 < y → HasDerivAt (gammaFun α m) (rgiD1 α m (VocabO.phiA α) y) y) ∧
      (∀ y, 0 < y →
        HasDerivAt (deriv (gammaFun α m)) (deriv (rgiD1 α m (VocabO.phiA α)) y) y) :=
    fun m => hasDerivAt_gammaFun hα m hInt.2.2.2.1 (hInt.2.2.2.2.1 m) (hInt.2.2.2.2.2 m)
  set θu : ℝ := (θ + π / 2) / 2 with hθu
  have hcosθ : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hsum_of : ∀ (E : ℝ) (f : ℕ → ℝ), (∀ m, |f m| ≤ E * majPow m) → Summable f := by
    intro E f hf
    refine Summable.of_norm_bounded (hmaj E) fun m => ?_
    rw [Real.norm_eq_abs]
    exact hf m
  -- the pointwise identity of the summands
  have hpoint : ∀ m : ℕ,
      (-(α ^ 2 * z ^ 2)) * (deriv (deriv (acoeff α m (RemSource α ψ))) z
          * Gegenbauer.eFam m θ)
        + (-(α * (5 + α) * z)) * (deriv (acoeff α m (RemSource α ψ)) z
          * Gegenbauer.eFam m θ)
        + ((-1) * (acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) θ)
            + 1 * (acoeff α m (RemSource α ψ) z
              * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ)
            + (-6) * (acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ))
      = cmode m (RemSource α ψ) z * Gegenbauer.eFam m θ := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hz0 : acoeff α 0 (RemSource α ψ) = fun _ => (0 : ℝ) := funext hac0
      have hd1 : deriv (acoeff α 0 (RemSource α ψ)) = fun _ => (0 : ℝ) := by
        rw [hz0]; simp
      have hd2 : deriv (deriv (acoeff α 0 (RemSource α ψ))) = fun _ => (0 : ℝ) := by
        rw [hd1]; simp
      simp only [hz0, hd1, hd2, cmode_RemSource, hb0, Pi.zero_apply]
      simp
    · have h1 : deriv (acoeff α m (RemSource α ψ)) z
          = α ^ 2 * bmode m ψ * deriv (gammaFun α m) z := by
        rw [deriv_acoeff m (hdiffA m).1 z hz, (hdiffA m).1 z hz |>.deriv]
      have h2 : deriv (deriv (acoeff α m (RemSource α ψ))) z
          = α ^ 2 * bmode m ψ * deriv (deriv (gammaFun α m)) z := by
        rw [deriv_deriv_acoeff m (hdiffA m).1 (hdiffA m).2 z hz, (hdiffA m).2 z hz |>.deriv]
      have h3 : acoeff α m (RemSource α ψ) z = α ^ 2 * bmode m ψ * gammaFun α m z := by
        rw [acoeff_RemSource]
      rw [h1, h2, h3, cmode_RemSource]
      linear_combination (α ^ 2 * bmode m ψ * Gegenbauer.eFam m θ) * hODE m hm z hz
        + (α ^ 2 * bmode m ψ * gammaFun α m z)
          * eFam_lzero_deriv m hcosθ z
  -- summability of the five families
  have hsumF1 : Summable fun m : ℕ =>
      deriv (deriv (acoeff α m (RemSource α ψ))) z * Gegenbauer.eFam m θ :=
    hsum_of D _ (fun m => by rw [abs_mul]; exact hB2 m z hz)
  have hsumF2 : Summable fun m : ℕ =>
      deriv (acoeff α m (RemSource α ψ)) z * Gegenbauer.eFam m θ :=
    hsum_of D _ (fun m => by rw [abs_mul]; exact hB1 m z hz)
  have hsumF3 : Summable fun m : ℕ =>
      acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) θ :=
    hsum_of D _ (fun m => by
      rw [abs_mul]
      exact hB4 m θ (by linarith [hθ]) (by linarith [hθ2]))
  have hsumF4 : Summable fun m : ℕ =>
      acoeff α m (RemSource α ψ) z
        * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ :=
    hsum_of D _ (fun m => by
      rw [abs_mul]
      exact hB5 m θ (by linarith [hθ]) (by linarith [hθ2]))
  have hsumF5 : Summable fun m : ℕ =>
      acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ :=
    hsum_of D _ (fun m => by rw [abs_mul]; exact hB0 m z hz)
  -- normalise the linear combination of sums
  have hnorm : (-(α ^ 2 * z ^ 2)) * (∑' m : ℕ,
          deriv (deriv (acoeff α m (RemSource α ψ))) z * Gegenbauer.eFam m θ)
        - (α * (5 + α) * z) * (∑' m : ℕ,
            deriv (acoeff α m (RemSource α ψ)) z * Gegenbauer.eFam m θ)
        + (-(∑' m : ℕ, acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) θ)
            + (∑' m : ℕ, acoeff α m (RemSource α ψ) z
                * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ)
            - 6 * (∑' m : ℕ, acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ))
      = (-(α ^ 2 * z ^ 2)) * (∑' m : ℕ,
            deriv (deriv (acoeff α m (RemSource α ψ))) z * Gegenbauer.eFam m θ)
          + (-(α * (5 + α) * z)) * (∑' m : ℕ,
              deriv (acoeff α m (RemSource α ψ)) z * Gegenbauer.eFam m θ)
          + ((-1) * (∑' m : ℕ, acoeff α m (RemSource α ψ) z
                * iteratedDeriv 2 (Gegenbauer.eFam m) θ)
              + 1 * (∑' m : ℕ, acoeff α m (RemSource α ψ) z
                  * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ)
              + (-6) * (∑' m : ℕ, acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ)) := by
    ring
  rw [hnorm,
    tsum_lincomb5 (-(α ^ 2 * z ^ 2)) (-(α * (5 + α) * z)) (-1) 1 (-6)
      (fun m => deriv (deriv (acoeff α m (RemSource α ψ))) z * Gegenbauer.eFam m θ)
      (fun m => deriv (acoeff α m (RemSource α ψ)) z * Gegenbauer.eFam m θ)
      (fun m => acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) θ)
      (fun m => acoeff α m (RemSource α ψ) z
        * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ)
      (fun m => acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ)
      hsumF1 hsumF2 hsumF3 hsumF4 hsumF5,
    tsum_congr hpoint]
  -- identify the source
  rw [show (∑' m : ℕ, cmode m (RemSource α ψ) z * Gegenbauer.eFam m θ)
      = (α ^ 2 * VocabO.phiA α z) * (∑' m : ℕ, bmode m ψ * Gegenbauer.eFam m θ) from by
        rw [← tsum_mul_left]
        exact tsum_congr fun m => by rw [cmode_RemSource]; ring]
  rw [hExp θ hθ hθ2]
  rfl

/-- The mode series `psiSeries α (RemSource α ψ)` solves `bslOp α Ψ = RemSource α ψ`. -/
theorem psiSeries_bslOp :
    ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
        Work.Elliptic.bslOp α
            (fun z θ => Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)
            z θ = Work.FTS.PhiStar.RemSource α ψ z θ := by
  intro α ψ hα hα5 hψ
  -- the angular bounds, re-associated
  have hAng : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |Gegenbauer.eFam m θ| ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ∧
      |deriv (Gegenbauer.eFam m) θ|
        ≤ 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 2 ∧
      |iteratedDeriv 2 (Gegenbauer.eFam m) θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
            * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 4 ∧
      |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 3 :=
    fun m θ hθ => ⟨Deleg.psiAngBounds.1 m θ hθ, Deleg.psiAngBounds.2.1 m θ hθ,
      Deleg.psiAngBounds.2.2.1 m θ hθ, Deleg.psiAngBounds.2.2.2 m θ hθ⟩
  -- the coefficient decay
  obtain ⟨Cd, hCdpos, hCd⟩ := bmode_decay15
  have hDec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
    ⟨Cd, hCdpos, fun m hm => hCd α ψ hα hα5 hψ m hm⟩
  -- the integrability of the kernels
  have hInt := Deleg.psiSeriesIntegrability α hα ψ
  -- the radial facts
  obtain ⟨Kφ, hKφ0, hKφ⟩ := (Deleg.psiRadFacts α hα hα5).1
  obtain ⟨Crb, hCrbpos, hRadB⟩ := (Deleg.psiRadFacts α hα hα5).2.1
  have hRadODE := (Deleg.psiRadFacts α hα hα5).2.2
  have hphiAsmooth : ContDiffOn ℝ 22 (VocabO.phiA α) (Set.Ioi 0) :=
    fun z hz => (Work.FTS.PhiStar.contDiffAt_phiA_of α 22 hz).contDiffWithinAt
  have hGamma : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 2 → ∀ z : ℝ, 0 < z →
      |iteratedDeriv k (gammaFun α m) z| ≤ C / Gegenbauer.lam m := by
    refine ⟨Crb * (Kφ + 1), by positivity, fun m hm k hk z hz => ?_⟩
    have h := hRadB m (VocabO.phiA α) Kφ hKφ0 hm hphiAsmooth hKφ k hk z hz
    have h2 : Crb * Kφ / Gegenbauer.lam m ≤ Crb * (Kφ + 1) / Gegenbauer.lam m := by
      refine div_le_div_of_nonneg_right ?_ (le_of_lt (lam_pos hm))
      linarith
    calc |iteratedDeriv k (gammaFun α m) z|
        = |iteratedDeriv k (Radial.radGreen α m (VocabO.phiA α)) z| := rfl
      _ ≤ Crb * Kφ / Gegenbauer.lam m := h
      _ ≤ Crb * (Kφ + 1) / Gegenbauer.lam m := h2
  have hODE : ∀ m : ℕ, 1 ≤ m → ∀ z : ℝ, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (gammaFun α m)) z
        - α * (5 + α) * z * deriv (gammaFun α m) z
        + Gegenbauer.lam m * gammaFun α m z = VocabO.phiA α z := by
    intro m hm z hz
    have h := hRadODE m (VocabO.phiA α) hInt.2.2.2.1 (hInt.2.2.2.2.1 m) (hInt.2.2.2.2.2 m) z hz
    simpa only [gammaFun, Radial.lamR, Gegenbauer.lam] using h
  -- the majorant
  have hmaj : ∀ D : ℝ, Summable fun m : ℕ => D * majPow m := by
    intro D
    exact (Deleg.rpowMajorant.2.1 D).congr (fun m => by rw [majPow])
  -- the arithmetic shapes
  have hterm : ∀ (Cdec CBz Kφ : ℝ), 0 < Cdec → 0 < CBz → 0 < Kφ → ∀ cθ : ℝ, 0 < cθ →
      ∃ D : ℝ, 0 < D ∧ ∀ m : ℕ, 1 ≤ m →
        let L := (Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)
        (α ^ 2 * Cdec * CBz * Kφ / L * (3 * ((m : ℝ) + 1)) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4)
            ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3)
            ≤ D * majPow m) := by
    intro Cdec CBz Kφ h1 h2 h3 cθ h4
    obtain ⟨D, hDpos, hDsh⟩ := Deleg.termEstimates α hα Cdec CBz Kφ h1 h2 h3 cθ h4
    refine ⟨D, hDpos, fun m hm => ?_⟩
    have h := hDsh m hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [majPow]; exact h.1
    · rw [majPow]; exact h.2.1
    · rw [majPow]; exact h.2.2.1
    · rw [majPow]; exact h.2.2.2
  -- the eigen-expansion of ψ
  have hExp : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      (∑' m : ℕ, bmode m ψ * Gegenbauer.eFam m θ) = ψ θ :=
    Deleg.psiExpansion α ψ hα hα5 hψ
      ⟨Cd, hCdpos, fun m hm => hCd α ψ hα hα5 hψ m hm⟩
      (fun m θ hθ => Deleg.psiAngBounds.1 m θ hθ)
  exact psiSeries_bslOp_of_facts α ψ hα hα5 hψ hAng hDec hGamma hODE hInt hmaj hterm hExp

end Work.FTS.PhiStar.Series
