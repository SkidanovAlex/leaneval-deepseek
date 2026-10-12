import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBox.q3NewtonData
import Submission.Work.BoseFixB2.Polar.boxFormB_smul
import Submission.Work.BoseFixR.BoxParamArith
import Submission.Work.BoseFixR.CrudeWordLowerRegime
import Submission.Work.BoseFixR.FibrePartIntegrable
import Submission.Work.BoseFixR.KinFibreMarginal
import Submission.Work.BoseFixR.KinGePDiagHold
import Submission.Work.BoseFixR.PotSplit
import Submission.Work.BoseFixR.WindowBracket
import Submission.Work.BoseFixR.WindowEtaHold
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix

set_option maxHeartbeats 200000000
set_option linter.unusedVariables false
/-! ## 0. Elementary helpers -/

/-- `Adm` is monotone in the diluteness threshold. -/
lemma adm_mono_local {v : ℝ³ → ℝ} {ε ε' μ : ℝ} (h : Adm v ε μ) (hε : ε ≤ ε') : Adm v ε' μ :=
  ⟨h.1, le_trans h.2.1 hε, h.2.2⟩

/-- `cS1` is `2`-homogeneous in the state. -/
lemma cS1_smul_local {N : ℕ} (ℓ c : ℝ) (Φ : X N → ℝ) : cS1 ℓ (c • Φ) = c ^ 2 * cS1 ℓ Φ := by
  unfold cS1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have haP : ∀ x : X N, aP ℓ i (c • Φ) x = c * aP ℓ i Φ x := by
    intro x
    simp only [aP, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul]
    ring
  have hpt : ∀ x : X N, (aP ℓ i (c • Φ) x) ^ 2 = c ^ 2 * (aP ℓ i Φ x) ^ 2 := by
    intro x; rw [haP x]; ring
  trans ∫ x in abox N ℓ, c ^ 2 * (aP ℓ i Φ x) ^ 2
  · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  · rw [integral_const_mul]

/-- The elementary AM–GM `2√(AB) ≤ A + B` for `A, B ≥ 0`. -/
lemma amgm_sqrt_local {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    2 * Real.sqrt (A * B) ≤ A + B := by
  have hsm : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA B
  nlinarith [hsm, sq_nonneg (Real.sqrt A - Real.sqrt B), Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- `wordB` in the analysis-box vocabulary (`Work.BoseFixR.WordBridgeId`). -/
lemma wordB_bridge {v : ℝ³ → ℝ} (h : ScatSol v) (hvrad : _root_.BoseGases.IsRadial v) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < a v) {N : ℕ} {Φ : X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    wordB v h μ N Φ
      = Work.BoseKinLoc.kinFormB N (sideAt μ (a v)) (paramsAt μ (a v)).d (paramsAt μ (a v)).s
          (paramsAt μ (a v)).eT (paramsAt μ (a v)).b Φ
        + qLHSword (N := N) (sideAt μ (a v)) μ (wPairC (sideAt μ (a v)) v)
            (wPairC (sideAt μ (a v)) (g0 v h)) Φ := by
  have hℓ : 0 < sideAt μ (a v) := sideAt_pos hμ hav
  rw [wordB, Work.BoseKinLoc.boxFormB, WordBridgeId h hvrad hℓ hΦ]

/-- `μℓ³` at FS's parameters. -/
lemma mu_ell_cube_sideAt {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    μ * sideAt μ a ^ 3 = (μ * a ^ 3) ^ (-(166 / 323 : ℝ)) := by
  simpa only [sideAt, paramsAt] using mu_ell_cube_fsParams hμ ha

/-- Monotonicity of `μ ↦ μℓ³` in the diluteness: a lower bound at the threshold. -/
lemma mu_ell_cube_ge {μ a θ : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hθ : μ * a ^ 3 ≤ θ) :
    θ ^ (-(166 / 323 : ℝ)) ≤ μ * sideAt μ a ^ 3 := by
  rw [mu_ell_cube_sideAt hμ ha]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hθ (by norm_num)

/-- `θ^{-166/323}` at `θ = 1000^{-323/166}` is `1000`. -/
lemma rpow_1000 : ((1000 : ℝ) ^ (-(323 / 166 : ℝ))) ^ (-(166 / 323 : ℝ)) = 1000 := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1000)]
  norm_num
/-- **The window bound for a normalized state.**  This is the analytic content; the target
`WindowBound` follows by `2`-homogeneity of `wordB`, `cnPlus` and `cS1`. -/
theorem windowBound_normalized {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hav : 0 < a v) :
    ∃ K₁ K₂ ε₀ : ℝ, 1 ≤ K₁ ∧ K₁ ≤ 94 * π ∧ 0 ≤ K₂ ∧ 0 < ε₀ ∧
      ∀ μ : ℝ, Adm v ε₀ μ → ∀ (N : ℕ) (Φ : X N → ℝ),
        2 ≤ N → (N : ℝ) / sideAt μ (a v) ^ 3 ≤ 9 * μ →
        ContDiff ℝ (⊤ : ℕ∞) Φ →
        (∫ x in abox N (sideAt μ (a v)), (Φ x) ^ 2) = 1 →
        0 < cS1 (sideAt μ (a v)) Φ →
        2 * π * (a v) * sideAt μ (a v) ^ 3 * ((N : ℝ) / sideAt μ (a v) ^ 3 - μ) ^ 2
          - 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
          - 94 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
          - K₂ * μ * cnPlus (sideAt μ (a v)) Φ
        ≤ wordB v h μ N Φ := by
  -- the M1 (Newton) data and the three regime thresholds
  obtain ⟨Ct, hCt0, hNewt⟩ := q3NewtonData hR hv hvrad hv_supp h
  obtain ⟨εr, hεr, hreg⟩ := WindowRegime h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εb, hεb, hbr⟩ := WindowBracket h hv hv1 hvrad hR hv_supp hav Ct hCt0
  obtain ⟨εe, hεe, heta⟩ := WindowEtaHold h hv hv1 hvrad hR hv_supp hav Ct hCt0
  have hθpos : (0 : ℝ) < (1000 : ℝ) ^ (-(323 / 166 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hχpos : (0 : ℝ) < Submission.BoseGases.chiSup := Submission.BoseGases.chiSup_pos
  set α₀ : ℝ := (10 : ℝ) ^ 13 * (320 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * (|a v| + 1)
    with hα₀def
  set K₂ : ℝ := α₀ / 2 + 136 * π * |a v| + 91 * |fsqC1 (a v)| + 9 * |fsqC2 (a v)|
      + 9 * |Work.SmallBoxA0.d1C Ct * a v| + 1 with hK₂def
  have hα₀pos : 0 < α₀ := by
    rw [hα₀def]
    have h4 : (0 : ℝ) < 320 * π * Submission.BoseGases.chiSup ^ 2 := by positivity
    positivity
  refine ⟨94 * π, K₂, min (min εr (min εb (min εe 1))) ((1000 : ℝ) ^ (-(323 / 166 : ℝ))),
    ?_, le_refl _, ?_, ?_, ?_⟩
  · nlinarith [Real.pi_gt_three]
  · rw [hK₂def]; positivity
  · exact lt_min (lt_min hεr (lt_min hεb (lt_min hεe one_pos))) hθpos
  · intro μ hAdm N Φ hN2 hwin hΦc hnorm hSc1
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    have hn1 : 1 ≤ n := by omega
    -- the diluteness regime
    have hAdmr : Adm v εr μ := adm_mono_local hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
    have hAdmb : Adm v εb μ := adm_mono_local hAdm
      (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hAdme : Adm v εe μ := adm_mono_local hAdm (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
    have hAdmθ : μ * (a v) ^ 3 ≤ (1000 : ℝ) ^ (-(323 / 166 : ℝ)) :=
      le_trans hAdm.2.1 (min_le_right _ _)
    have hμ0 : 0 < μ := hAdm.1
    obtain ⟨hRℓ, hμℓ3, hdil, hd1⟩ := hreg μ hAdmr
    obtain ⟨ha0, hd0, hs0, heT0, heT1, hb0, hKl0⟩ := paramsAt_facts (a := a v) hμ0 hAdm.2.2
    have hℓ0' : 0 < sideAt μ (a v) := sideAt_pos hμ0 ha0
    have hμℓ3big : 1000 ≤ μ * sideAt μ (a v) ^ 3 := by
      refine le_trans ?_ (mu_ell_cube_ge hμ0 ha0 hAdmθ)
      rw [rpow_1000]
    have hμℓ3pos : 0 < μ * sideAt μ (a v) ^ 3 := by linarith
    have ha0' : 0 ≤ a v := le_of_lt ha0
    -- the state data
    have hΦcont : Continuous Φ := hΦc.continuous
    have hDnn : 0 ≤ g0w0Mass (v := v) h := Work.SmallBoxA0.g0w0Mass_nonneg hR hv hvrad hv_supp h
    have hDle : g0w0Mass (v := v) h ≤ 8 * π * a v :=
      Work.SmallBoxA0.g0w0Mass_le_av hR hv hvrad hv_supp h
    have hcnnn : 0 ≤ cnPlus (sideAt μ (a v)) Φ := cnPlus_nonneg
    have hcs1nn : 0 ≤ cS1 (sideAt μ (a v)) Φ := cS1_nonneg
    have hn_small : ((n + 1 : ℕ) : ℝ) ≤ 9 * μ * sideAt μ (a v) ^ 3 := by
      have h3 : 0 < sideAt μ (a v) ^ 3 := by positivity
      rw [div_le_iff₀ h3] at hwin
      exact hwin
    have hn2_le : ((n : ℝ) + 2) ≤ 10 * μ * sideAt μ (a v) ^ 3 := by
      have h1 : ((n + 1 : ℕ) : ℝ) ≤ 9 * μ * sideAt μ (a v) ^ 3 := hn_small
      have h2 : (1 : ℝ) ≤ μ * sideAt μ (a v) ^ 3 := by linarith
      push_cast at h1 ⊢
      linarith
    -- the M1 data at this box
    obtain ⟨hWfin, hNewton⟩ := hNewt (sideAt μ (a v)) hℓ0' hRℓ
    have hWfin' : MeasureTheory.Integrable
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        wScaled (sideAt μ (a v)) (g0 v h) q.1 * wScaled (sideAt μ (a v)) (g0 v h) q.2
          * (1 / ‖q.1 - q.2‖)) := by
      simpa [one_div] using hWfin
    -- ## (i) the kinetic comparison
    have hkin := KinGePDiagHold (n := n + 1) (ℓ := sideAt μ (a v)) (d := (paramsAt μ (a v)).d)
      (s := (paramsAt μ (a v)).s) (eT := (paramsAt μ (a v)).eT) (b := (paramsAt μ (a v)).b)
      (by omega) hℓ0' hs0 hd0 hd1 heT0 heT1 hb0 hΦc
    -- ## (ii) the Bogoliubov payment (FS lm:appbogolubov)
    have hR1 := Work.BlockBound4.diagW_lm_appbogolubov_explicitC (N := n) (s := sideAt μ (a v))
      (c0 := (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) (Ct := Ct)
      hℓ0' (by positivity) hv hvrad hv1 hR hv_supp h hRℓ hn1 ha0 ?_ hWfin' hCt0 hNewton
    · obtain ⟨C1, hC1eq, hC1nn, hR1body⟩ := hR1
      have hC1d : C1 = Work.SmallBoxA0.d1C Ct := by rw [hC1eq]; rfl
      have hbody := hR1body Φ hΦc hnorm
      simp only [hC1d] at hbody
      -- ## (iii) the potential side
      have hpot := Work.SmallBoxA0.pot_sharp_summary (N := n + 1) (ℓ := sideAt μ (a v)) (μ := μ)
        (v := v) (R := R) hℓ0' hμ0 hv hvrad hv1 hR hv_supp h hRℓ hΦcont hnorm hwin hSc1
      -- ## (iv) the D-square slack
      have hslack := Work.SmallBoxA0.cs2_mass_slack (N := n + 1) (s := sideAt μ (a v)) (μ := μ)
        (D := g0w0Mass (v := v) h) (v := v) hℓ0' hμ0 hDnn hDle ha0'
        (by linarith : 1 ≤ μ * sideAt μ (a v) ^ 3) hwin hΦcont hnorm
      -- ## (v) the Corr residue
      have hcorr := Work.SmallBoxA0.corrWord_sqrt_bound (n := n) (s := sideAt μ (a v)) (R := R)
        (v := v) hℓ0' hR hv hvrad hv_supp h hRℓ hΦcont hnorm
      have hcs1le : cS1 (sideAt μ (a v)) Φ ≤ ((n + 1 : ℕ) : ℝ) := by
        have h1 := cS1_eq_nat_sub_cnPlus (N := n + 1) hℓ0' hΦcont hnorm
        push_cast at h1 ⊢
        linarith
      -- ## (vi) the AM–GM on the Corr residue
      set Cc : ℝ := 32 * π * Submission.BoseGases.chiSup ^ 2 * ((n : ℝ) + 2) * (a v) with hCcdef
      have hCcnn : 0 ≤ Cc := by rw [hCcdef]; positivity
      have hCcLe : Cc ≤ 10 * (32 * π * Submission.BoseGases.chiSup ^ 2 * (a v))
          * (μ * sideAt μ (a v) ^ 3) := by
        rw [hCcdef]
        have h2 : ((n : ℝ) + 2) ≤ 10 * μ * sideAt μ (a v) ^ 3 := hn2_le
        have h3 : (0 : ℝ) ≤ 32 * π * Submission.BoseGases.chiSup ^ 2 * (a v) := by positivity
        nlinarith [h2, h3]
      have hcorr' : 2 * (sideAt μ (a v) ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord (sideAt μ (a v)) h Φ
          ≤ (sideAt μ (a v) ^ 3)⁻¹ * Cc * Real.sqrt (cS1 (sideAt μ (a v)) Φ)
              * Real.sqrt (cnPlus (sideAt μ (a v)) Φ) := by
        have hh := mul_le_mul_of_nonneg_left hcorr
          (by positivity : (0 : ℝ) ≤ (sideAt μ (a v) ^ 3)⁻¹)
        simp only [hCcdef] at hh ⊢
        linarith [hh]
      have hamgm : 2 * (sideAt μ (a v) ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord (sideAt μ (a v)) h Φ
          ≤ (α₀ * μ / 2) * cnPlus (sideAt μ (a v)) Φ
            + (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀)
                * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 := by
        have hU : 0 ≤ (α₀ * μ / 2) * cnPlus (sideAt μ (a v)) Φ := by positivity
        have hV : 0 ≤ 2 * Cc ^ 2 * cS1 (sideAt μ (a v)) Φ
            / (α₀ * μ * (sideAt μ (a v) ^ 3) ^ 2) := by positivity
        have h1 := amgm_sqrt_local hU hV
        have h2 : (α₀ * μ / 2) * cnPlus (sideAt μ (a v)) Φ
              * (2 * Cc ^ 2 * cS1 (sideAt μ (a v)) Φ / (α₀ * μ * (sideAt μ (a v) ^ 3) ^ 2))
            = ((sideAt μ (a v) ^ 3)⁻¹ * Cc * Real.sqrt (cS1 (sideAt μ (a v)) Φ)
                * Real.sqrt (cnPlus (sideAt μ (a v)) Φ)) ^ 2 := by
          have hsq : ((sideAt μ (a v) ^ 3)⁻¹ * Cc * Real.sqrt (cS1 (sideAt μ (a v)) Φ)
                * Real.sqrt (cnPlus (sideAt μ (a v)) Φ)) ^ 2
              = ((sideAt μ (a v) ^ 3)⁻¹) ^ 2 * Cc ^ 2 * (Real.sqrt (cS1 (sideAt μ (a v)) Φ)) ^ 2
                * (Real.sqrt (cnPlus (sideAt μ (a v)) Φ)) ^ 2 := by ring
          rw [hsq, Real.sq_sqrt hcs1nn, Real.sq_sqrt hcnnn]
          field_simp
        have h3 : Real.sqrt ((α₀ * μ / 2) * cnPlus (sideAt μ (a v)) Φ
              * (2 * Cc ^ 2 * cS1 (sideAt μ (a v)) Φ / (α₀ * μ * (sideAt μ (a v) ^ 3) ^ 2)))
            = (sideAt μ (a v) ^ 3)⁻¹ * Cc * Real.sqrt (cS1 (sideAt μ (a v)) Φ)
                * Real.sqrt (cnPlus (sideAt μ (a v)) Φ) := by
          rw [h2, Real.sqrt_sq (by positivity)]
        have h4 : 2 * Cc ^ 2 * cS1 (sideAt μ (a v)) Φ / (α₀ * μ * (sideAt μ (a v) ^ 3) ^ 2)
            ≤ (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀)
                * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 := by
          have h5 : cS1 (sideAt μ (a v)) Φ ≤ ((n + 1 : ℕ) : ℝ) := hcs1le
          have h6 : ((n + 1 : ℕ) : ℝ) ≤ 9 * μ * sideAt μ (a v) ^ 3 := hn_small
          have hB7 : cS1 (sideAt μ (a v)) Φ ≤ 9 * μ * sideAt μ (a v) ^ 3 := le_trans h5 h6
          have h7 : Cc ^ 2 ≤ (10 * (32 * π * Submission.BoseGases.chiSup ^ 2 * (a v))
              * (μ * sideAt μ (a v) ^ 3)) ^ 2 := by
            have := pow_le_pow_left₀ hCcnn hCcLe 2
            simpa using this
          have hprod : Cc ^ 2 * cS1 (sideAt μ (a v)) Φ
              ≤ (10 * (32 * π * Submission.BoseGases.chiSup ^ 2 * (a v))
                  * (μ * sideAt μ (a v) ^ 3)) ^ 2 * (9 * μ * sideAt μ (a v) ^ 3) :=
            mul_le_mul h7 hB7 hcs1nn (by positivity)
          have hcore : 2 * Cc ^ 2 * cS1 (sideAt μ (a v)) Φ
              ≤ (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v|)
                * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * (μ * sideAt μ (a v) ^ 6) := by
            have habs : |a v| = a v := abs_of_nonneg ha0'
            have h2 : (2 : ℝ) * Cc ^ 2 * cS1 (sideAt μ (a v)) Φ
                ≤ 2 * ((10 * (32 * π * Submission.BoseGases.chiSup ^ 2 * a v)
                    * (μ * sideAt μ (a v) ^ 3)) ^ 2 * (9 * μ * sideAt μ (a v) ^ 3)) := by
              have h3 := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
              linarith [h3]
            have hcoefid : (2 : ℝ) * ((10 * (32 * π * Submission.BoseGases.chiSup ^ 2 * a v)
                    * (μ * sideAt μ (a v) ^ 3)) ^ 2 * (9 * μ * sideAt μ (a v) ^ 3))
                = (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v|)
                  * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * (μ * sideAt μ (a v) ^ 6) := by
              rw [habs]; ring
            linarith [h2, hcoefid]
          calc 2 * Cc ^ 2 * cS1 (sideAt μ (a v)) Φ / (α₀ * μ * (sideAt μ (a v) ^ 3) ^ 2)
              ≤ ((1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v|)
                  * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * (μ * sideAt μ (a v) ^ 6))
                / (α₀ * μ * (sideAt μ (a v) ^ 3) ^ 2) :=
                div_le_div_of_nonneg_right hcore (by positivity)
            _ = (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀)
                * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 := by
                have h1 : α₀ ≠ 0 := ne_of_gt hα₀pos
                have h2 : μ ≠ 0 := ne_of_gt hμ0
                have h3 : sideAt μ (a v) ^ 3 ≠ 0 := ne_of_gt (pow_pos hℓ0' 3)
                field_simp
        linarith [h1, h3, h4, hcorr']
      -- ## (vii) the η-step
      have hetaR := heta μ hAdme (n + 1) (by omega) hwin
      have hetaStep : -((1 / 2) * ((1 + Work.SmallBoxA0.d1C Ct * (R / sideAt μ (a v)))
              * (1 + Work.SmallBoxA0.d1C Ct
                  * ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) * a v) - 1)
            * g0w0Mass (v := v) h * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)
            * (sideAt μ (a v) ^ 3)⁻¹)
          ≥ -(μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 + μ * (a v)) := by
        set ηv : ℝ := (1 + Work.SmallBoxA0.d1C Ct * (R / sideAt μ (a v)))
            * (1 + Work.SmallBoxA0.d1C Ct
                * ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) * a v) - 1
          with hηvdef
        have hηeq : Work.BlockBound4.d4Eta Ct R (sideAt μ (a v))
            ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) v = ηv := rfl
        rw [hηeq] at hetaR
        have h7 : ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
          nlinarith
        have hA1 : ηv * g0w0Mass (v := v) h * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)
            ≤ |ηv| * (8 * π * a v) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
          calc ηv * g0w0Mass (v := v) h * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)
              = ηv * (g0w0Mass (v := v) h * (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))) := by
                ring
            _ ≤ |ηv| * ((8 * π * a v) * ((((n + 1 : ℕ) : ℝ) + 1) ^ 2)) := by
                refine mul_le_mul (le_abs_self ηv) ?_ (by positivity) (abs_nonneg ηv)
                exact mul_le_mul hDle h7 (by positivity) (by positivity)
            _ = |ηv| * (8 * π * a v) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by ring
        have h4 : (1 / 2) * ηv * g0w0Mass (v := v) h * ((n + 1 : ℕ) : ℝ)
              * ((n + 1 : ℕ) : ℝ) * (sideAt μ (a v) ^ 3)⁻¹
            ≤ (1 / 2) * |ηv| * (8 * π * a v) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2
                * (sideAt μ (a v) ^ 3)⁻¹ := by
          have hk : (0 : ℝ) ≤ (1 / 2) * (sideAt μ (a v) ^ 3)⁻¹ := by positivity
          calc (1 / 2) * ηv * g0w0Mass (v := v) h * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)
                * (sideAt μ (a v) ^ 3)⁻¹
              = (ηv * g0w0Mass (v := v) h * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))
                * ((1 / 2) * (sideAt μ (a v) ^ 3)⁻¹) := by ring
            _ ≤ (|ηv| * (8 * π * a v) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2)
                * ((1 / 2) * (sideAt μ (a v) ^ 3)⁻¹) := mul_le_mul_of_nonneg_right hA1 hk
            _ = (1 / 2) * |ηv| * (8 * π * a v) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2
                * (sideAt μ (a v) ^ 3)⁻¹ := by ring
        linarith [h4, hetaR]
      -- ## (viii) the bracket bound and the Bogoliubov-error bound
      have hB : Work.BlockBound4.d4Bracket Ct n (sideAt μ (a v))
          ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) v
          ≤ 291 * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 := by
        have h1 := hbr μ hAdmb (n + 1) (by omega) hwin
        have h2 : (n + 1) - 1 = n := Nat.add_sub_cancel n 1
        rw [h2] at h1
        exact h1
      have hE : Work.BlockBound4.d4BogErr Ct n (sideAt μ (a v)) v
          ≤ 9 * Work.SmallBoxA0.d1C Ct * (a v) * μ := by
        have h1 : Work.BlockBound4.d4BogErr Ct n (sideAt μ (a v)) v
            = Work.SmallBoxA0.d1C Ct * (a v) * (((n : ℝ) + 1) / sideAt μ (a v) ^ 3) := rfl
        rw [h1]
        have h2 : ((n : ℝ) + 1) / sideAt μ (a v) ^ 3 ≤ 9 * μ := by
          have h3 := hwin
          push_cast at h3
          exact h3
        have h3 : (0 : ℝ) ≤ Work.SmallBoxA0.d1C Ct * (a v) := by
          have h4 : 0 ≤ Work.SmallBoxA0.d1C Ct := Work.SmallBoxA0.d1C_nonneg Ct
          positivity
        nlinarith [h2, h3]
      have hpn : Work.SmallBoxA0.potNCoeff μ (a v)
          ≤ μ * (64 * π * (a v) + 91 * fsqC1 (a v) + 9 * fsqC2 (a v)) := by
        rw [Work.SmallBoxA0.potNCoeff]
        nlinarith [hμ0.le]
      -- ## (ix) the final arithmetic
      have hKcorr : 1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀ ≤ 1 := by
        have h5 : (0 : ℝ) ≤ (320 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 := sq_nonneg _
        have h7 : (0 : ℝ) < (10 : ℝ) ^ 13 * (320 * π * Submission.BoseGases.chiSup ^ 2) ^ 2
            * (|a v| + 1) := by positivity
        have h9 : (320 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v|
            ≤ (320 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * (|a v| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [le_abs_self (a v)]) h5
        rw [hα₀def, div_le_iff₀ h7]
        nlinarith [h9, h5, abs_nonneg (a v), sq_nonneg (a v),
          sq_nonneg (Submission.BoseGases.chiSup : ℝ)]
      have hK₂ge : 136 * π * (a v) + 91 * fsqC1 (a v) + 9 * fsqC2 (a v)
          + 9 * Work.SmallBoxA0.d1C Ct * (a v) + α₀ / 2 ≤ K₂ := by
        rw [hK₂def]
        have h1 : a v ≤ |a v| := le_abs_self _
        have h2 : fsqC1 (a v) ≤ |fsqC1 (a v)| := le_abs_self _
        have h3 : fsqC2 (a v) ≤ |fsqC2 (a v)| := le_abs_self _
        have h4 : Work.SmallBoxA0.d1C Ct * (a v) ≤ |Work.SmallBoxA0.d1C Ct * (a v)| :=
          le_abs_self _
        have h5 : (0 : ℝ) ≤ π := le_of_lt Real.pi_pos
        have h6 : (0 : ℝ) ≤ |a v| := abs_nonneg _
        have h7 : (0 : ℝ) ≤ |fsqC1 (a v)| := abs_nonneg _
        have h8 : (0 : ℝ) ≤ |fsqC2 (a v)| := abs_nonneg _
        have h9 : (0 : ℝ) ≤ |Work.SmallBoxA0.d1C Ct * (a v)| := abs_nonneg _
        nlinarith [h1, h2, h3, h4, h5, h6, h7, h8, h9]
      have hK₁ : 1 + 291 + 1 + 1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀
          ≤ 94 * π := by
        linarith [hKcorr, Real.pi_gt_d20]
      have hnumsmall : (1 + 148 * π) * (a v) * μ ≤ 1 * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 := by
        have h1 : 1 + 148 * π ≤ 593 := by linarith [Real.pi_lt_four]
        have h2 : (0 : ℝ) ≤ (a v) * μ := by positivity
        have h3 : (1 + 148 * π) * ((a v) * μ) ≤ (593 : ℝ) * ((a v) * μ) :=
          mul_le_mul_of_nonneg_right h1 h2
        have h4 : (593 : ℝ) * ((a v) * μ) ≤ (μ * sideAt μ (a v) ^ 3) * ((a v) * μ) :=
          mul_le_mul_of_nonneg_right (by linarith : (593 : ℝ) ≤ μ * sideAt μ (a v) ^ 3) h2
        nlinarith [h3, h4]
      have hCorrWord_eq : Work.SmallBoxA0.CorrWord (sideAt μ (a v)) h Φ
          = ∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) (sideAt μ (a v)),
              (aP (sideAt μ (a v)) i Φ x)
                * (w1Fibre (sideAt μ (a v)) (wPairC (sideAt μ (a v)) (g0 v h)) (x i))
                * (∑ k : Fin (n + 1), aQ (sideAt μ (a v)) k (aQ (sideAt μ (a v)) i Φ) x) := rfl
      -- ## the chain
      have step1 : (1 / 4 : ℝ) * (((n + 1 : ℕ) : ℝ) / sideAt μ (a v) ^ 3 - μ) ^ 2
                * (8 * π * (a v) * sideAt μ (a v) ^ 3)
            - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * sideAt μ (a v) ^ 3)
            + (1 / 2 : ℝ) * g0w0Mass (v := v) h * (((n + 1 : ℕ) : ℝ) + 1) ^ 2
                * (sideAt μ (a v) ^ 3)⁻¹
            - (72 * π * (a v) * μ) * cnPlus (sideAt μ (a v)) Φ
            - 112 * π * (a v) * μ
            + q4PairWord (ℓ := sideAt μ (a v)) (v := v) h (Φ := Φ)
            - Work.SmallBoxA0.potNCoeff μ (a v) * cnPlus (sideAt μ (a v)) Φ
            - 36 * π * (a v) * μ
            - 2 * (sideAt μ (a v) ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord (sideAt μ (a v)) h Φ
          ≤ qLHSword (N := n + 1) (sideAt μ (a v)) μ (wPairC (sideAt μ (a v)) v)
              (wPairC (sideAt μ (a v)) (g0 v h)) Φ := by
        rw [hCorrWord_eq]
        linarith [hpot, hslack]
      have step2 : (1 / 4 : ℝ) * (((n + 1 : ℕ) : ℝ) / sideAt μ (a v) ^ 3 - μ) ^ 2
                * (8 * π * (a v) * sideAt μ (a v) ^ 3)
            - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * sideAt μ (a v) ^ 3)
            + (1 / 2 : ℝ) * g0w0Mass (v := v) h * (((n + 1 : ℕ) : ℝ) + 1) ^ 2
                * (sideAt μ (a v) ^ 3)⁻¹
            - (72 * π * (a v) * μ) * cnPlus (sideAt μ (a v)) Φ
            - 112 * π * (a v) * μ
            + q4PairWord (ℓ := sideAt μ (a v)) (v := v) h (Φ := Φ)
            - Work.SmallBoxA0.potNCoeff μ (a v) * cnPlus (sideAt μ (a v)) Φ
            - 36 * π * (a v) * μ
            - (α₀ * μ / 2) * cnPlus (sideAt μ (a v)) Φ
            - (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀)
                * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
          ≤ qLHSword (N := n + 1) (sideAt μ (a v)) μ (wPairC (sideAt μ (a v)) v)
              (wPairC (sideAt μ (a v)) (g0 v h)) Φ := by
        linarith [step1, hamgm]
      have step3 : (1 / 4 : ℝ) * (((n + 1 : ℕ) : ℝ) / sideAt μ (a v) ^ 3 - μ) ^ 2
                * (8 * π * (a v) * sideAt μ (a v) ^ 3)
            - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * sideAt μ (a v) ^ 3)
            + (1 / 2 : ℝ) * g0w0Mass (v := v) h * (((n + 1 : ℕ) : ℝ) + 1) ^ 2
                * (sideAt μ (a v) ^ 3)⁻¹
            - (72 * π * (a v) * μ) * cnPlus (sideAt μ (a v)) Φ
            - 112 * π * (a v) * μ
            - Work.SmallBoxA0.potNCoeff μ (a v) * cnPlus (sideAt μ (a v)) Φ
            - 36 * π * (a v) * μ
            - (α₀ * μ / 2) * cnPlus (sideAt μ (a v)) Φ
            - (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀)
                * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
            - (1 / 2 : ℝ) * (1 + Work.SmallBoxA0.d1C Ct * (R / sideAt μ (a v)))
                * (1 + Work.SmallBoxA0.d1C Ct
                    * ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) * a v)
                * g0w0Mass (v := v) h * Work.BlockBound4.d4MassCoeff (n + 1) (sideAt μ (a v))
            - Work.BlockBound4.d4Bracket Ct n (sideAt μ (a v))
                ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) v
            - Work.BlockBound4.d4BogErr Ct n (sideAt μ (a v)) v * cnPlus (sideAt μ (a v)) Φ
          ≤ pDiagForm (sideAt μ (a v))
              (fsKinCoeff (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) Φ
            + qLHSword (N := n + 1) (sideAt μ (a v)) μ (wPairC (sideAt μ (a v)) v)
                (wPairC (sideAt μ (a v)) (g0 v h)) Φ := by
        have hb := hbody
        simp only [Work.BlockBound4.d4Bracket, Work.SmallBoxA0.kinPBracket,
          Work.BlockBound4.d4BogErr, Work.SmallBoxA0.kinPBogErr, one_div] at hb ⊢
        linarith [step2, hb]
      have hmass : (1 / 2 : ℝ) * g0w0Mass (v := v) h * (((n + 1 : ℕ) : ℝ) + 1) ^ 2
                * (sideAt μ (a v) ^ 3)⁻¹
            - (1 / 2 : ℝ) * (1 + Work.SmallBoxA0.d1C Ct * (R / sideAt μ (a v)))
                * (1 + Work.SmallBoxA0.d1C Ct
                    * ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) * a v)
                * g0w0Mass (v := v) h * Work.BlockBound4.d4MassCoeff (n + 1) (sideAt μ (a v))
            ≥ -(μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 + μ * (a v)) := by
        have h3 : Work.BlockBound4.d4MassCoeff (n + 1) (sideAt μ (a v))
            = (((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) * (sideAt μ (a v) ^ 3)⁻¹ := by
          rw [Work.BlockBound4.d4MassCoeff]
        set η : ℝ := (1 + Work.SmallBoxA0.d1C Ct * (R / sideAt μ (a v)))
            * (1 + Work.SmallBoxA0.d1C Ct
                * ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) * a v) - 1
          with hηdef
        have hE : (1 / 2 : ℝ) * (1 + Work.SmallBoxA0.d1C Ct * (R / sideAt μ (a v)))
            * (1 + Work.SmallBoxA0.d1C Ct
                * ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) * a v)
            = (1 / 2) * (η + 1) := by rw [hηdef]; ring
        have hηeq : Work.BlockBound4.d4Eta Ct R (sideAt μ (a v))
            ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) v = η := by
          rw [Work.BlockBound4.d4Eta, Work.SmallBoxA0.kinPeta, ← hηdef]
        have hηnn : 0 ≤ η := by
          rw [hηdef]
          have h1 : 0 ≤ Work.SmallBoxA0.d1C Ct * (R / sideAt μ (a v)) :=
            mul_nonneg (Work.SmallBoxA0.d1C_nonneg Ct) (div_nonneg hR.le hℓ0'.le)
          have h2 : 0 ≤ Work.SmallBoxA0.d1C Ct
              * ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) * a v :=
            mul_nonneg (mul_nonneg (Work.SmallBoxA0.d1C_nonneg Ct)
              (inv_nonneg.mpr (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd0.le) hs0.le) hℓ0'.le)))
              ha0'
          nlinarith [h1, h2]
        have hηinv : (0 : ℝ) ≤ (sideAt μ (a v) ^ 3)⁻¹ :=
          inv_nonneg.mpr (pow_nonneg hℓ0'.le 3)
        have hnn1 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have hnn2 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by linarith
        rw [h3, hE]
        have hid : (1 / 2 : ℝ) * g0w0Mass (v := v) h * (((n + 1 : ℕ) : ℝ) + 1) ^ 2
              * (sideAt μ (a v) ^ 3)⁻¹
            - (1 / 2 : ℝ) * (η + 1) * g0w0Mass (v := v) h
              * ((((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) * (sideAt μ (a v) ^ 3)⁻¹)
            = (1 / 2 : ℝ) * g0w0Mass (v := v) h * (((n + 1 : ℕ) : ℝ) + 1)
                * (sideAt μ (a v) ^ 3)⁻¹
              - (1 / 2 : ℝ) * η * g0w0Mass (v := v) h
                * ((((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) * (sideAt μ (a v) ^ 3)⁻¹) := by
          ring
        have hpos : 0 ≤ (1 / 2 : ℝ) * g0w0Mass (v := v) h * (((n + 1 : ℕ) : ℝ) + 1)
            * (sideAt μ (a v) ^ 3)⁻¹ :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hDnn) hnn2) hηinv
        have hmono : (1 / 2 : ℝ) * η * g0w0Mass (v := v) h
              * ((((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) * (sideAt μ (a v) ^ 3)⁻¹)
            ≤ (1 / 2 : ℝ) * η * g0w0Mass (v := v) h
              * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * (sideAt μ (a v) ^ 3)⁻¹ := by
          have hle : (((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 : ℕ) : ℝ)
              ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by nlinarith [hnn1]
          have hc : 0 ≤ (1 / 2 : ℝ) * η * g0w0Mass (v := v) h :=
            mul_nonneg (mul_nonneg (by norm_num) hηnn) hDnn
          calc (1 / 2 : ℝ) * η * g0w0Mass (v := v) h
                * ((((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) * (sideAt μ (a v) ^ 3)⁻¹)
              = ((1 / 2 : ℝ) * η * g0w0Mass (v := v) h)
                * ((((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 : ℕ) : ℝ)) * (sideAt μ (a v) ^ 3)⁻¹ := by
                ring
            _ ≤ ((1 / 2 : ℝ) * η * g0w0Mass (v := v) h)
                * ((((n + 1 : ℕ) : ℝ) + 1) ^ 2) * (sideAt μ (a v) ^ 3)⁻¹ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hc) hηinv
            _ = (1 / 2 : ℝ) * η * g0w0Mass (v := v) h
                * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * (sideAt μ (a v) ^ 3)⁻¹ := by ring
        have hloss : (1 / 2 : ℝ) * η * g0w0Mass (v := v) h
              * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * (sideAt μ (a v) ^ 3)⁻¹
            ≤ μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 + μ * (a v) := by
          have h1 : (1 / 2 : ℝ) * η * g0w0Mass (v := v) h
                * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * (sideAt μ (a v) ^ 3)⁻¹
              ≤ (1 / 2 : ℝ) * η * (8 * π * (a v))
                * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * (sideAt μ (a v) ^ 3)⁻¹ := by
            have hZ : 0 ≤ (1 / 2 : ℝ) * η * (((n + 1 : ℕ) : ℝ) + 1) ^ 2
                * (sideAt μ (a v) ^ 3)⁻¹ :=
              mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hηnn) (sq_nonneg _)) hηinv
            have hD0 : 0 ≤ g0w0Mass (v := v) h := hDnn
            nlinarith [hZ, hDle, hD0, ha0']
          have h2 := hetaR
          rw [hηeq, abs_of_nonneg hηnn] at h2
          linarith [h1, h2]
        linarith [hid, hpos, hmono, hloss]
      have step4 : (1 / 4 : ℝ) * (((n + 1 : ℕ) : ℝ) / sideAt μ (a v) ^ 3 - μ) ^ 2
                * (8 * π * (a v) * sideAt μ (a v) ^ 3)
            - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * sideAt μ (a v) ^ 3)
            - μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 - μ * (a v)
            - (72 * π * (a v) * μ) * cnPlus (sideAt μ (a v)) Φ
            - 112 * π * (a v) * μ
            - Work.SmallBoxA0.potNCoeff μ (a v) * cnPlus (sideAt μ (a v)) Φ
            - 36 * π * (a v) * μ
            - (α₀ * μ / 2) * cnPlus (sideAt μ (a v)) Φ
            - (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀)
                * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
            - Work.BlockBound4.d4Bracket Ct n (sideAt μ (a v))
                ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) v
            - Work.BlockBound4.d4BogErr Ct n (sideAt μ (a v)) v * cnPlus (sideAt μ (a v)) Φ
          ≤ pDiagForm (sideAt μ (a v))
              (fsKinCoeff (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) Φ
            + qLHSword (N := n + 1) (sideAt μ (a v)) μ (wPairC (sideAt μ (a v)) v)
                (wPairC (sideAt μ (a v)) (g0 v h)) Φ := by
        linarith [step3, hmass]
      -- ## final comparison with the target's normal form
      have key : (1 / 4 : ℝ) * (((n + 1 : ℕ) : ℝ) / sideAt μ (a v) ^ 3 - μ) ^ 2
                * (8 * π * (a v) * sideAt μ (a v) ^ 3)
            - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * sideAt μ (a v) ^ 3)
            - 94 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
            - K₂ * μ * cnPlus (sideAt μ (a v)) Φ
          ≤ pDiagForm (sideAt μ (a v))
              (fsKinCoeff (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) Φ
            + qLHSword (N := n + 1) (sideAt μ (a v)) μ (wPairC (sideAt μ (a v)) v)
                (wPairC (sideAt μ (a v)) (g0 v h)) Φ := by
        have hZ : 1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀
            ≤ 94 * π - 293 := by linarith [hK₁]
        have hZnn : 0 ≤ 1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀ :=
          div_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) hα₀pos.le
        have hnn2 : (0 : ℝ) ≤ μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 :=
          mul_nonneg (mul_nonneg (sq_nonneg μ) ha0') (pow_nonneg hℓ0'.le 3)
        have hii : μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 + (1 + 148 * π) * (a v) * μ
              + 291 * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
              + (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀)
                * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
            ≤ 94 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 := by
          have h4 : (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀)
                * (μ ^ 2 * (a v) * sideAt μ (a v) ^ 3)
              ≤ (94 * π - 293) * (μ ^ 2 * (a v) * sideAt μ (a v) ^ 3) :=
            mul_le_mul_of_nonneg_right hZ hnn2
          have h5 : (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀)
                * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
              = (1800 * (32 * π * Submission.BoseGases.chiSup ^ 2) ^ 2 * |a v| / α₀)
                * (μ ^ 2 * (a v) * sideAt μ (a v) ^ 3) := by ring
          linarith [h4, h5, hB, hnumsmall]
        have hcn1 : 72 * π * (a v) * μ + Work.SmallBoxA0.potNCoeff μ (a v) + α₀ * μ / 2
              + Work.BlockBound4.d4BogErr Ct n (sideAt μ (a v)) v ≤ K₂ * μ := by
          have h1 := mul_le_mul_of_nonneg_right hK₂ge (le_of_lt hμ0)
          linarith [h1, hpn, hE, hμ0]
        have hI' : (72 * π * (a v) * μ + Work.SmallBoxA0.potNCoeff μ (a v) + α₀ * μ / 2
              + Work.BlockBound4.d4BogErr Ct n (sideAt μ (a v)) v)
              * cnPlus (sideAt μ (a v)) Φ ≤ (K₂ * μ) * cnPlus (sideAt μ (a v)) Φ :=
          mul_le_mul_of_nonneg_right hcn1 hcnnn
        linarith [step4, hii, hI', hB]
      -- ## convert and finish
      have heq1 : 2 * π * (a v) * sideAt μ (a v) ^ 3
            * (((n + 1 : ℕ) : ℝ) / sideAt μ (a v) ^ 3 - μ) ^ 2
          = (1 / 4 : ℝ) * (((n + 1 : ℕ) : ℝ) / sideAt μ (a v) ^ 3 - μ) ^ 2
            * (8 * π * (a v) * sideAt μ (a v) ^ 3) := by ring
      have heq2 : 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
          = (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * sideAt μ (a v) ^ 3) := by ring
      have hfin : 2 * π * (a v) * sideAt μ (a v) ^ 3
            * (((n + 1 : ℕ) : ℝ) / sideAt μ (a v) ^ 3 - μ) ^ 2
          - 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
          - 94 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
          - K₂ * μ * cnPlus (sideAt μ (a v)) Φ
          ≤ pDiagForm (sideAt μ (a v))
              (fsKinCoeff (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) Φ
            + qLHSword (N := n + 1) (sideAt μ (a v)) μ (wPairC (sideAt μ (a v)) v)
                (wPairC (sideAt μ (a v)) (g0 v h)) Φ := by
        linarith [key, heq1, heq2]
      calc 2 * π * (a v) * sideAt μ (a v) ^ 3
            * (((n + 1 : ℕ) : ℝ) / sideAt μ (a v) ^ 3 - μ) ^ 2
          - 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
          - 94 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
          - K₂ * μ * cnPlus (sideAt μ (a v)) Φ
          ≤ pDiagForm (sideAt μ (a v))
              (fsKinCoeff (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹) Φ
            + qLHSword (N := n + 1) (sideAt μ (a v)) μ (wPairC (sideAt μ (a v)) v)
                (wPairC (sideAt μ (a v)) (g0 v h)) Φ := hfin
        _ ≤ Work.BoseKinLoc.kinFormB (n + 1) (sideAt μ (a v)) (paramsAt μ (a v)).d
              (paramsAt μ (a v)).s (paramsAt μ (a v)).eT (paramsAt μ (a v)).b Φ
            + qLHSword (N := n + 1) (sideAt μ (a v)) μ (wPairC (sideAt μ (a v)) v)
                (wPairC (sideAt μ (a v)) (g0 v h)) Φ := by linarith [hkin]
        _ = wordB v h μ (n + 1) Φ := by rw [wordB_bridge h hvrad hμ0 hav hΦc]
    · -- the diluteness hypothesis `2 · c₀ · (a v) ≤ 1`
      have hX : (0 : ℝ) < 2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v) := by
        positivity
      rw [show (2 : ℝ) * (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v))⁻¹ * a v
          = (2 * (a v)) / (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * sideAt μ (a v)) by ring]
      rw [div_le_iff₀ hX]
      linarith [hdil]

/-! ## 2. The block splitting of the word -/

/-- The box word is superadditive over the label split `k + j`: both integrals on the left run
over the *same* box side that `wordB` carries (`sideAt μ (a v)`).  The integrability
hypotheses are the marginal integrability of the two fibre words (see
`WordBFibreIntegrable`), which is what makes the Bochner integrals honest. -/
theorem wordB_split {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) {k j : ℕ}
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hintKL : MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
        Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (bfL Φ y))
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
    (hintPL : MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
        ∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v (Submission.BoseGases.g0 v h)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z)
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
    (hintKR : MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
        Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (bfR Φ z))
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
    (hintPR : MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
        ∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v (Submission.BoseGases.g0 v h)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y)
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
    (hvi : MeasureTheory.LocallyIntegrable v)
    (hgi : MeasureTheory.LocallyIntegrable (Submission.BoseGases.g0 v h)) :
    (∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        Work.BoseBoxFix.wordB v h μ k (bfL Φ y))
      + (∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        Work.BoseBoxFix.wordB v h μ j (bfR Φ z))
      ≤ Work.BoseBoxFix.wordB v h μ (k + j) Φ := by
  have hfunL : (fun y : Submission.BoseGases.X j => Work.BoseBoxFix.wordB v h μ k (bfL Φ y))
      = fun y : Submission.BoseGases.X j =>
          Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (bfL Φ y)
          + ∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v (Submission.BoseGases.g0 v h)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z := rfl
  have hfunR : (fun z : Submission.BoseGases.X k => Work.BoseBoxFix.wordB v h μ j (bfR Φ z))
      = fun z : Submission.BoseGases.X k =>
          Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (bfR Φ z)
          + ∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v (Submission.BoseGases.g0 v h)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y := rfl
  have hboxfun : Work.BoseBoxFix.wordB v h μ (k + j) Φ
      = Work.BoseKinLoc.kinFormB (k + j) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b Φ
          + ∫ x in Submission.BoseGases.abox (k + j) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Φ x) ^ 2 * Work.BoseKinLoc.potWordU (k + j) v (Submission.BoseGases.g0 v h)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 x := rfl
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμ hav
  have hkin := KinSplit (k := k) (j := j) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
    (eT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (b := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b) hℓ hΦ
  have hpot := PotSplit (k := k) (j := j) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (μ := μ) hℓ hv hvi hgi hΦ
  rw [hfunL, hfunR, hboxfun, MeasureTheory.integral_add hintKL hintPL,
    MeasureTheory.integral_add hintKR hintPR]
  linarith [hkin, hpot]

/-! ## 3. Auxiliary lemmas -/

/-- The box norm of a state with `cS1 > 0` is positive. -/
lemma sqNorm_pos_of_cS1_pos {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ}
    (hΨ : Continuous Ψ) (h : 0 < cS1 ℓ Ψ) :
    0 < ∫ x in abox N ℓ, (Ψ x) ^ 2 := by
  by_contra hcon
  push_neg at hcon
  have hle : cS1 ℓ Ψ ≤ 0 := by
    have hsum : cS1 ℓ Ψ = ∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2 := rfl
    rw [hsum]
    refine Finset.sum_nonpos fun i _ => ?_
    have hd := sq_norm_decomp (N := N) (ℓ := ℓ) hℓ i hΨ
    have hnn : 0 ≤ ∫ x in abox N ℓ, (aQ ℓ i Ψ x) ^ 2 := integral_nonneg fun x => sq_nonneg _
    linarith
  linarith

/-- The homogenised sector identity `cS1 = N‖Ψ‖² − n₊`. -/
lemma cS1_eq_nat_mul_sqNorm_sub_cnPlus {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ}
    (hΨ : Continuous Ψ) :
    cS1 ℓ Ψ = (N : ℝ) * (∫ x in abox N ℓ, (Ψ x) ^ 2) - cnPlus ℓ Ψ := by
  have hper : ∀ i : Fin N, (∫ x in abox N ℓ, (Ψ x) ^ 2)
      = (∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Ψ x) ^ 2) :=
    fun i => sq_norm_decomp (N := N) (ℓ := ℓ) hℓ i hΨ
  have hsum : ∑ _i : Fin N, (∫ x in abox N ℓ, (Ψ x) ^ 2) = cS1 ℓ Ψ + cnPlus ℓ Ψ := by
    rw [Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_add_distrib]
    simp only [cS1, cnPlus]
  have hconst : ∑ _i : Fin N, (∫ x in abox N ℓ, (Ψ x) ^ 2)
      = (N : ℝ) * (∫ x in abox N ℓ, (Ψ x) ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith [hsum, hconst]

/-- `wordB` is `2`-homogeneous in the state. -/
lemma wordB_smul {v : ℝ³ → ℝ} (h : ScatSol v) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < a v) {N : ℕ} {Φ : X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (c : ℝ) :
    wordB v h μ N (fun x => c * Φ x) = c ^ 2 * wordB v h μ N Φ :=
  Work.BoseFixB2.Polar.boxFormB_smul (sideAt_pos hμ hav) hΦ

/-- `C μ A m ≤ Kc μ²Aℓ³` from `m ≤ k ≤ 9μℓ³` and `9C ≤ Kc`. -/
lemma block_coef_le {C μ A L m k Kc : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (hL : 0 ≤ L) (hKc : 9 * C ≤ Kc) (hmk : m ≤ k) (hk : k ≤ 9 * μ * L ^ 3) :
    C * μ * A * m ≤ Kc * μ ^ 2 * A * L ^ 3 := by
  have h0 : 0 ≤ C * μ * A := mul_nonneg (mul_nonneg hC hμ) hA
  have h1 : C * μ * A * m ≤ C * μ * A * (9 * μ * L ^ 3) := by
    have hm : m ≤ 9 * μ * L ^ 3 := le_trans hmk hk
    calc C * μ * A * m = (C * μ * A) * m := by ring
      _ ≤ (C * μ * A) * (9 * μ * L ^ 3) := mul_le_mul_of_nonneg_left hm h0
      _ = C * μ * A * (9 * μ * L ^ 3) := by ring
  have h2 : C * μ * A * (9 * μ * L ^ 3) = (9 * C) * (μ ^ 2 * A * L ^ 3) := by ring
  have h3 : (9 * C) * (μ ^ 2 * A * L ^ 3) ≤ Kc * (μ ^ 2 * A * L ^ 3) :=
    mul_le_mul_of_nonneg_right hKc (mul_nonneg (mul_nonneg (sq_nonneg μ) hA) (pow_nonneg hL 3))
  calc C * μ * A * m ≤ C * μ * A * (9 * μ * L ^ 3) := h1
    _ = (9 * C) * (μ ^ 2 * A * L ^ 3) := h2
    _ ≤ Kc * (μ ^ 2 * A * L ^ 3) := h3
    _ = Kc * μ ^ 2 * A * L ^ 3 := by ring

/-! ## 4. The homogeneous per-block window bound -/

/-- **The per-block window bound in homogeneous form** — `windowBound_normalized` made
`2`-homogeneous in the state (using `cS1 > 0 ⟹ ‖Ψ‖² > 0`). -/
theorem perBlockWindow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ K₁ K₂ ε₀ : ℝ, 1 ≤ K₁ ∧ K₁ ≤ 94 * π ∧ 0 ≤ K₂ ∧ 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ),
        2 ≤ N → ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (N : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 ≤ 9 * μ →
        0 < Submission.BoseGases.cS1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ →
        (2 * π * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
              * ((N : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2
            - 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
            - 94 * π * μ ^ 2 * (_root_.BoseGases.a v)
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
            * (∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Ψ x) ^ 2)
          - K₂ * μ * Submission.BoseGases.cnPlus
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ
        ≤ Work.BoseBoxFix.wordB v h μ N Ψ := by
  obtain ⟨K₁, K₂, ε₀, hK₁ge, hK₁94, hK₂0, hε₀pos, hmain⟩ :=
    windowBound_normalized h hv hv1 hvrad hR hv_supp hav
  refine ⟨K₁, K₂, ε₀, hK₁ge, hK₁94, hK₂0, hε₀pos, ?_⟩
  intro μ hAdm N Ψ hN2 hΨ hwin hSc1
  obtain ⟨hμ, hAdmDil, hPOK⟩ := hAdm
  have hμ0 : 0 ≤ μ := le_of_lt hμ
  have hLpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμ hav
  have hL3nn : 0 ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := pow_nonneg hLpos.le 3
  set I : ℝ := ∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Ψ x) ^ 2 with hIdef
  have hIpos : 0 < I := sqNorm_pos_of_cS1_pos hLpos hΨ.continuous hSc1
  set c : ℝ := (Real.sqrt I)⁻¹ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcsq : c ^ 2 = I⁻¹ := by rw [hcdef, inv_pow, Real.sq_sqrt hIpos.le]
  have hpt : ∀ x : Submission.BoseGases.X N, ((fun x => c * Ψ x) x) ^ 2 = c ^ 2 * (Ψ x) ^ 2 := by
    intro x; simp only []; ring
  have hnorm : (∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ((fun x => c * Ψ x) x) ^ 2) = 1 := by
    calc (∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((fun x => c * Ψ x) x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            c ^ 2 * (Ψ x) ^ 2 :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = c ^ 2 * I := by rw [MeasureTheory.integral_const_mul]
      _ = 1 := by rw [hcsq, inv_mul_cancel₀ (ne_of_gt hIpos)]
  have hSc : 0 < Submission.BoseGases.cS1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (fun x => c * Ψ x) := by
    rw [show (fun x : Submission.BoseGases.X N => c * Ψ x)
        = c • Ψ from rfl, Submission.BoseGases.cS1_smul]
    exact mul_pos (pow_pos hcpos 2) hSc1
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X N => c * Ψ x) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hΨ.const_smul c
  have hkey := hmain μ ⟨hμ, hAdmDil, hPOK⟩ N (fun x => c * Ψ x) hN2 hwin hcd hnorm hSc
  have hword : Work.BoseBoxFix.wordB v h μ N (fun x => c * Ψ x)
      = c ^ 2 * Work.BoseBoxFix.wordB v h μ N Ψ := wordB_smul h hμ hav hΨ c
  have hcn : Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (fun x => c * Ψ x)
      = c ^ 2 * Submission.BoseGases.cnPlus
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ := by
    rw [show (fun x : Submission.BoseGases.X N => c * Ψ x)
        = c • Ψ from rfl, Submission.BoseGases.cnPlus_smul]
  rw [hword, hcn, hcsq] at hkey
  have hgoal := mul_le_mul_of_nonneg_left hkey hIpos.le
  have hIinv : I * I⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hIpos)
  have hleft : I * (2 * π * (_root_.BoseGases.a v)
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
          * ((N : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2
        - 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
        - 94 * π * μ ^ 2 * (_root_.BoseGases.a v)
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
        - K₂ * μ * (I⁻¹ * Submission.BoseGases.cnPlus
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ))
      = (2 * π * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
            * ((N : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2
          - 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
          - 94 * π * μ ^ 2 * (_root_.BoseGases.a v)
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
          * I
        - K₂ * μ * Submission.BoseGases.cnPlus
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ := by
    rw [mul_sub]
    have h1 : I * (I⁻¹ * Submission.BoseGases.cnPlus
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ)
        = Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ := by
      rw [← mul_assoc, hIinv, one_mul]
    rw [show I * (K₂ * μ * (I⁻¹ * Submission.BoseGases.cnPlus
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ))
        = K₂ * μ * (I * (I⁻¹ * Submission.BoseGases.cnPlus
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ)) by ring]
    rw [h1, mul_comm I _]
  have hright : I * (I⁻¹ * Work.BoseBoxFix.wordB v h μ N Ψ)
      = Work.BoseBoxFix.wordB v h μ N Ψ := by
    rw [← mul_assoc, hIinv, one_mul]
  rw [hleft, hright] at hgoal
  exact hgoal

/-! ## 5. The block induction -/

/-- **The block induction.**  With the per-block window bound `hwin`, the crude bound `hcrude`,
the fibre marginal integrability `hIntI`, and the constant hypotheses `Kc ≥ 9C`,
`Kc ≥ 4π + K₁ + 9K₂'`, `K₂' ≥ K₂`, `K₂' ≥ C·a v`, every smooth box state satisfies
`wordB ≥ −Kc μ²(a v)ℓ³‖·‖² − K₂'μ n₊`. -/
lemma blockInduction {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v)
    {C Kp K₂ Kc K₂' : ℝ} {k : ℕ}
    (hC0 : 0 ≤ C) (hKp1 : 1 ≤ Kp) (hKp94 : Kp ≤ 94 * π) (hK₂0 : 0 ≤ K₂)
    (hK₂'ge : K₂ ≤ K₂') (hK₂'CA : C * _root_.BoseGases.a v ≤ K₂')
    (hKc9 : 9 * C ≤ Kc) (hKcbig : 4 * π + Kp + 9 * K₂' ≤ Kc)
    (hk2 : 2 ≤ k) (hk8 : 8 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 ≤ (k : ℝ))
    (hk4 : (k : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 ≤ 9 * μ)
    (hcrude : ∀ {n : ℕ} {Ψ : Submission.BoseGases.X n → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Ψ →
      -(C * μ * _root_.BoseGases.a v * (n : ℝ)) * Work.BoseBoxFix.normB v μ n Ψ
        ≤ Work.BoseBoxFix.wordB v h μ n Ψ)
    (hwin : ∀ (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ), 2 ≤ N → ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (N : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 ≤ 9 * μ →
        0 < Submission.BoseGases.cS1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ →
      (2 * π * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
            * ((N : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2
          - 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
          - Kp * μ ^ 2 * (_root_.BoseGases.a v)
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
          * Work.BoseBoxFix.normB v μ N Ψ
        - K₂ * μ * Submission.BoseGases.cnPlus
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ
        ≤ Work.BoseBoxFix.wordB v h μ N Ψ)
    (hvi : MeasureTheory.LocallyIntegrable v)
    (hgi : MeasureTheory.LocallyIntegrable (Submission.BoseGases.g0 v h))
    (hIntI : ∀ {p q : ℕ} {Φ : Submission.BoseGases.X (p + q) → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Φ →
      MeasureTheory.Integrable (fun y : Submission.BoseGases.X q =>
          Work.BoseKinLoc.kinFormB p (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (bfL Φ y))
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox q (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
        ∧ MeasureTheory.Integrable (fun y : Submission.BoseGases.X q =>
            ∫ z in Submission.BoseGases.abox p (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU p v (Submission.BoseGases.g0 v h)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z)
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox q (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
        ∧ MeasureTheory.Integrable (fun z : Submission.BoseGases.X p =>
            Work.BoseKinLoc.kinFormB q (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (bfR Φ z))
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox p (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
        ∧ MeasureTheory.Integrable (fun z : Submission.BoseGases.X p =>
            ∫ y in Submission.BoseGases.abox q (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU q v (Submission.BoseGases.g0 v h)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y)
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox p (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) :
    ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      -(Kc * μ ^ 2 * (_root_.BoseGases.a v)
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
          * Work.BoseBoxFix.normB v μ n Ψ
        - K₂' * μ * Submission.BoseGases.cnPlus
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ
      ≤ Work.BoseBoxFix.wordB v h μ n Ψ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind m ih =>
    intro Ψ hΨ
    have hμ0 : 0 ≤ μ := le_of_lt hμ
    have hA0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
    have hLpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      Work.BoseBox.sideAt_pos hμ hav
    have hL3nn : 0 ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := pow_nonneg hLpos.le 3
    have hK₂'0 : 0 ≤ K₂' := le_trans (mul_nonneg hC0 hA0) hK₂'CA
    have hcn0 : 0 ≤ Submission.BoseGases.cnPlus
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ :=
      Submission.BoseGases.cnPlus_nonneg
    by_cases hmk : m ≤ k
    · have hmkR : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
      have hk9 : (k : ℝ) ≤ 9 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
        have h1 : (k : ℝ) = ((k : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
          field_simp
        rw [h1]
        exact mul_le_mul_of_nonneg_right hk4 hL3nn
      have hN0 : 0 ≤ Work.BoseBoxFix.normB v μ m Ψ := by
        rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
        exact integral_nonneg fun x => sq_nonneg _
      have hcrudeM : -(Kc * μ ^ 2 * (_root_.BoseGases.a v)
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) * Work.BoseBoxFix.normB v μ m Ψ
            - K₂' * μ * Submission.BoseGases.cnPlus
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ
          ≤ Work.BoseBoxFix.wordB v h μ m Ψ := by
        have hcr := hcrude (n := m) (Ψ := Ψ) hΨ
        have hcoef := block_coef_le hC0 hμ0 hA0 hLpos.le hKc9 hmkR hk9
        have h1 := mul_le_mul_of_nonneg_right hcoef hN0
        have h2 : 0 ≤ K₂' * μ * Submission.BoseGases.cnPlus
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ :=
          mul_nonneg (mul_nonneg hK₂'0 hμ0) hcn0
        linarith [hcr, h1, h2]
      by_cases hm1 : m ≤ 1
      · exact hcrudeM
      · by_cases hcS : Submission.BoseGases.cS1
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ = 0
        · exact hcrudeM
        · have hSc1 : 0 < Submission.BoseGases.cS1
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ :=
            lt_of_le_of_ne Submission.BoseGases.cS1_nonneg (Ne.symm hcS)
          have hm2 : 2 ≤ m := by omega
          have hm9 : (m : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 ≤ 9 * μ :=
            le_trans (div_le_div_of_nonneg_right hmkR hL3nn) hk4
          have hb := hwin m Ψ hm2 hΨ hm9 hSc1
          have hq : 0 ≤ 2 * π * (_root_.BoseGases.a v)
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
              * ((m : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2 := by
            refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hA0) hL3nn) (sq_nonneg _)
            exact le_of_lt (by positivity : (0 : ℝ) < 2 * π)
          have hbr : -((4 * π + Kp) * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
              ≤ 2 * π * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                  * ((m : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2
                - 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                - Kp * μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by linarith
          have h1 : -((4 * π + Kp) * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) * Work.BoseBoxFix.normB v μ m Ψ
              ≤ (2 * π * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                  * ((m : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2
                - 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                - Kp * μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
                * Work.BoseBoxFix.normB v μ m Ψ :=
            mul_le_mul_of_nonneg_right hbr hN0
          have hA2 : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
            have h4 : (0 : ℝ) ≤ μ ^ 2 * (_root_.BoseGases.a v) := mul_nonneg (sq_nonneg μ) hA0
            calc (0 : ℝ) ≤ (μ ^ 2 * (_root_.BoseGases.a v))
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := mul_nonneg h4 hL3nn
              _ = μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by ring
          have h2 : (4 * π + Kp)
                * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
              ≤ Kc * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) :=
            mul_le_mul_of_nonneg_right (by linarith [hKcbig]) hA2
          have h3 : -(Kc * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
                * Work.BoseBoxFix.normB v μ m Ψ
              ≤ -((4 * π + Kp) * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
                * Work.BoseBoxFix.normB v μ m Ψ := by
            have h4 := mul_le_mul_of_nonneg_right h2 hN0
            linarith [h4]
          have h4 : -K₂' * μ * Submission.BoseGases.cnPlus
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ
              ≤ -K₂ * μ * Submission.BoseGases.cnPlus
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ := by
            have h5 : K₂ * μ * Submission.BoseGases.cnPlus
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ
                ≤ K₂' * μ * Submission.BoseGases.cnPlus
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₂'ge hμ0) hcn0
            linarith [h5]
          linarith [hb, h1, h3, h4]
    · have hkm : k ≤ m := le_of_lt (Nat.lt_of_not_le hmk)
      obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, (Nat.add_sub_cancel' hkm).symm⟩
      have hjlt : j < k + j := by omega
      have hInts := hIntI (p := k) (q := j) (Φ := Ψ) hΨ
      have hsplit := wordB_split (h := h) (hv := hv) (hvrad := hvrad) (hμ := hμ) (hav := hav)
        (k := k) (j := j) (Φ := Ψ) hΨ hInts.1 hInts.2.1 hInts.2.2.1 hInts.2.2.2 hvi hgi
      have hkpt : ∀ y : Submission.BoseGases.X j,
          -K₂' * μ * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (bfL Ψ y)
            ≤ Work.BoseBoxFix.wordB v h μ k (bfL Ψ y) := by
        intro y
        have hcd : ContDiff ℝ (⊤ : ℕ∞) (bfL Ψ y) := contDiff_bfL hΨ y
        have hN0 : 0 ≤ Work.BoseBoxFix.normB v μ k (bfL Ψ y) := by
          rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
          exact integral_nonneg fun z => sq_nonneg _
        have hcn0 : 0 ≤ Submission.BoseGases.cnPlus
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfL Ψ y) :=
          Submission.BoseGases.cnPlus_nonneg
        by_cases hc : Submission.BoseGases.cS1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (bfL Ψ y) = 0
        · have hcr := hcrude (n := k) (Ψ := bfL Ψ y) hcd
          have hcnEq : Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (bfL Ψ y)
              = (k : ℝ) * Work.BoseBoxFix.normB v μ k (bfL Ψ y) := by
            have h1 := cS1_eq_nat_mul_sqNorm_sub_cnPlus (N := k)
              (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) hLpos hcd.continuous
            rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] at ⊢
            linarith
          have hkey : C * μ * (_root_.BoseGases.a v)
                * ((k : ℝ) * Work.BoseBoxFix.normB v μ k (bfL Ψ y))
              ≤ K₂' * μ * ((k : ℝ) * Work.BoseBoxFix.normB v μ k (bfL Ψ y)) := by
            have h1 : C * _root_.BoseGases.a v ≤ K₂' := hK₂'CA
            have h2 : 0 ≤ μ * ((k : ℝ) * Work.BoseBoxFix.normB v μ k (bfL Ψ y)) :=
              mul_nonneg hμ0 (mul_nonneg (Nat.cast_nonneg k) hN0)
            nlinarith [h1, h2]
          rw [hcnEq]
          linarith [hcr, hkey]
        · have hSc : 0 < Submission.BoseGases.cS1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (bfL Ψ y) := lt_of_le_of_ne Submission.BoseGases.cS1_nonneg (Ne.symm hc)
          have hb := hwin k (bfL Ψ y) hk2 hcd hk4 hSc
          have hx8 : 8 * μ ≤ (k : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
            rw [le_div_iff₀ (pow_pos hLpos 3)]
            exact hk8
          have hsq : 49 * μ ^ 2
              ≤ ((k : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2 := by
            nlinarith [hx8, hμ0]
          have hX0 : 0 ≤ 2 * π * (_root_.BoseGases.a v)
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
            have h4 : (0 : ℝ) ≤ 2 * π * (_root_.BoseGases.a v) :=
              mul_nonneg (le_of_lt (by positivity : (0 : ℝ) < 2 * π)) hA0
            calc (0 : ℝ) ≤ (2 * π * (_root_.BoseGases.a v))
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := mul_nonneg h4 hL3nn
              _ = 2 * π * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by ring
          have hmain1 : 2 * π * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 * (49 * μ ^ 2)
              ≤ 2 * π * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                * ((k : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hX0
          have hmain2 : (4 * π + Kp) * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
              ≤ 2 * π * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                * (49 * μ ^ 2) := by
            have h1 : (4 * π + Kp) ≤ 98 * π := by linarith [hKp94]
            have h2 : (0 : ℝ) ≤ μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 :=
              (by nlinarith [sq_nonneg μ, hA0, hL3nn])
            nlinarith [h1, h2]
          have hbr : 0 ≤ 2 * π * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                * ((k : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2
              - 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
              - Kp * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
            linarith [hmain1, hmain2]
          have hnn : 0 ≤ (2 * π * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                  * ((k : ℝ) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 - μ) ^ 2
                - 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                - Kp * μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
              * Work.BoseBoxFix.normB v μ k (bfL Ψ y) := mul_nonneg hbr hN0
          have h3 : -K₂' * μ * Submission.BoseGases.cnPlus
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfL Ψ y)
              ≤ -K₂ * μ * Submission.BoseGases.cnPlus
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfL Ψ y) := by
            have h5 : K₂ * μ * Submission.BoseGases.cnPlus
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfL Ψ y)
                ≤ K₂' * μ * Submission.BoseGases.cnPlus
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfL Ψ y) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₂'ge hμ0) hcn0
            linarith [h5]
          linarith [hb, hnn, h3]
      have hjpt : ∀ z : Submission.BoseGases.X k,
          -(Kc * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
              * Work.BoseBoxFix.normB v μ j (bfR Ψ z)
            - K₂' * μ * Submission.BoseGases.cnPlus
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfR Ψ z)
          ≤ Work.BoseBoxFix.wordB v h μ j (bfR Ψ z) :=
        fun z => ih j hjlt (bfR Ψ z) (contDiff_bfR hΨ z)
      have hWL : MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          Work.BoseBoxFix.wordB v h μ k (bfL Ψ y))
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) := by
        have hfun : (fun y : Submission.BoseGases.X j =>
              Work.BoseBoxFix.wordB v h μ k (bfL Ψ y))
            = (fun y : Submission.BoseGases.X j =>
                Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (bfL Ψ y)
                  + ∫ z in Submission.BoseGases.abox k
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (bfL Ψ y z) ^ 2
                      * Work.BoseKinLoc.potWordU k v (Submission.BoseGases.g0 v h)
                          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z) := rfl
        rw [hfun]
        exact hInts.1.add hInts.2.1
      have hWR : MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          Work.BoseBoxFix.wordB v h μ j (bfR Ψ z))
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) := by
        have hfun : (fun z : Submission.BoseGases.X k =>
              Work.BoseBoxFix.wordB v h μ j (bfR Ψ z))
            = (fun z : Submission.BoseGases.X k =>
                Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (bfR Ψ z)
                  + ∫ y in Submission.BoseGases.abox j
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (bfR Ψ z y) ^ 2
                      * Work.BoseKinLoc.potWordU j v (Submission.BoseGases.g0 v h)
                          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y) := rfl
        rw [hfun]
        exact hInts.2.2.1.add hInts.2.2.2
      have hcnMargL : MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfL Ψ y))
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) := by
        have hfun : (fun y : Submission.BoseGases.X j =>
              Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfL Ψ y))
            = (fun y : Submission.BoseGases.X j => ∑ i : Fin k,
                ∫ z in Submission.BoseGases.abox k
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  (Submission.BoseGases.aQ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) i
                    (bfL Ψ y) z) ^ 2) := rfl
        rw [hfun]
        exact integrable_finsetSum Finset.univ
          (fun i _ => integrableOn_fibre_integral_L hLpos hΨ i)
      have hcnMargR : MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfR Ψ z))
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) := by
        have hfun : (fun z : Submission.BoseGases.X k =>
              Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfR Ψ z))
            = (fun z : Submission.BoseGases.X k => ∑ i : Fin j,
                ∫ y in Submission.BoseGases.abox j
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  (Submission.BoseGases.aQ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) i
                    (bfR Ψ z) y) ^ 2) := rfl
        rw [hfun]
        exact integrable_finsetSum Finset.univ
          (fun i _ => integrableOn_fibre_integral_R hLpos hΨ i)
      have hsqMargR : MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          Work.BoseBoxFix.normB v μ j (bfR Ψ z))
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) := by
        have hbase : MeasureTheory.IntegrableOn
            (fun x : Submission.BoseGases.X (k + j) => (Ψ x) ^ 2)
            (Submission.BoseGases.abox (k + j) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
          integrableOn_abox_of_continuous hLpos (hΨ.continuous.pow 2)
        have h := (integrable_marginal_blockME
          (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) hbase).2
        have hfun : (fun z : Submission.BoseGases.X k => Work.BoseBoxFix.normB v μ j (bfR Ψ z))
            = (fun z : Submission.BoseGases.X k =>
                ∫ y in Submission.BoseGases.abox j
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  (Ψ (Work.BoseFixR.blockME k j (z, y))) ^ 2) := by
          funext z
          rw [show (fun y : Submission.BoseGases.X j =>
                (Ψ (Work.BoseFixR.blockME k j (z, y))) ^ 2)
              = (fun y : Submission.BoseGases.X j => (bfR Ψ z y) ^ 2) from by
            funext y
            rw [show bfR Ψ z y = Ψ (Work.BoseFixR.blockME k j (z, y)) from by
              rw [Work.BoseFixR.bfR_eq_blockME]]]
          rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
        rw [hfun]
        exact h
      have hGL : MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          -K₂' * μ * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (bfL Ψ y))
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :=
        hcnMargL.const_mul _
      have hGR : MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          -(Kc * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
              * Work.BoseBoxFix.normB v μ j (bfR Ψ z)
            - K₂' * μ * Submission.BoseGases.cnPlus
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfR Ψ z))
          (MeasureTheory.volume.restrict
            (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :=
        (hsqMargR.const_mul _).sub (hcnMargR.const_mul _)
      have hmonoL := setIntegral_mono_ae hGL hWL
        (Filter.Eventually.of_forall (fun y => hkpt y))
      have hmonoR := setIntegral_mono_ae hGR hWR
        (Filter.Eventually.of_forall (fun z => hjpt z))
      have htel := FibreTelescope (k := k) (j := j)
        (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) hLpos hΨ
      have hvalL : (∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          -K₂' * μ * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (bfL Ψ y))
          = -K₂' * μ * (∫ y in Submission.BoseGases.abox j
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (bfL Ψ y)) := by
        rw [← MeasureTheory.integral_const_mul]
      have hvalR : (∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          -(Kc * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
              * Work.BoseBoxFix.normB v μ j (bfR Ψ z)
            - K₂' * μ * Submission.BoseGases.cnPlus
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfR Ψ z))
          = -(Kc * μ ^ 2 * (_root_.BoseGases.a v)
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
              * (∫ z in Submission.BoseGases.abox k
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  Work.BoseBoxFix.normB v μ j (bfR Ψ z))
            - K₂' * μ * (∫ z in Submission.BoseGases.abox k
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (bfR Ψ z)) := by
        rw [MeasureTheory.integral_sub (hsqMargR.const_mul _) (hcnMargR.const_mul _),
          ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
      rw [hvalL] at hmonoL
      rw [hvalR] at hmonoR
      have h2 : (∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseBoxFix.normB v μ j (bfR Ψ z))
          = ∫ x in Submission.BoseGases.abox (k + j)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2 :=
        htel.2.1
      have h3 : (∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfL Ψ y))
          + (∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (bfR Ψ z))
          = Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) Ψ := htel.2.2
      rw [h2] at hmonoR
      have hNB2 : Work.BoseBoxFix.normB v μ (k + j) Ψ
          = ∫ x in Submission.BoseGases.abox (k + j)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2 := rfl
      rw [hNB2, ← h3]
      linarith [hmonoL, hmonoR, hsplit]

/-! ## 6. The target -/

theorem BoxWordLower {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ K ε₀ : ℝ, 1 ≤ K ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) (_root_.BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        -(K * μ ^ 2 * _root_.BoseGases.a v * Work.BoseFixR.ell3 v μ)
            * Work.BoseBoxFix.normB v μ n Φ
          ≤ Work.BoseBoxFix.wordB v h μ n Φ := by
  obtain ⟨C, hC0, hcrude⟩ := CrudeWordLowerRegime h hv hv1 hvrad hR hv_supp
  obtain ⟨εχ, hεχpos, hχ⟩ := Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge v hav hR
  obtain ⟨εA, hεApos, harith⟩ := BoxParamArith h hv1 hR hv_supp hav
  obtain ⟨εI, hεIpos, hIntI⟩ := FibrePartIntegrable_of_memLp h hv1 hR hv_supp hav
  obtain ⟨-, K₂, εP, -, -, hK₂0, hεPpos, hper⟩ :=
    perBlockWindow h hv hv1 hvrad hR hv_supp hav
  have hvi : MeasureTheory.LocallyIntegrable v :=
    (MeasureTheory.memLp_one_iff_integrable.mp hv1).locallyIntegrable
  have hgi : MeasureTheory.LocallyIntegrable (Submission.BoseGases.g0 v h) :=
    (Submission.BoseGases.w0_spec h).2.rhs_integrable
  set K₂' : ℝ := max K₂ (C * _root_.BoseGases.a v) with hK₂'def
  set Kc : ℝ := max (9 * C) (4 * π + 94 * π + 9 * K₂') with hKcdef
  refine ⟨max 1 (Kc + K₂'), min 1 (min εχ (min εA (min εI εP))), le_max_left _ _, ?_, ?_⟩
  · exact lt_min one_pos (lt_min hεχpos (lt_min hεApos (lt_min hεIpos hεPpos)))
  · intro μ hAdm hKB n Φ hNB hlow hspec
    obtain ⟨hμ, hdil, hPOK⟩ := hAdm
    have hε1 : min 1 (min εχ (min εA (min εI εP))) ≤ 1 := min_le_left _ _
    have hεχ' : min 1 (min εχ (min εA (min εI εP))) ≤ εχ :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hεA' : min 1 (min εχ (min εA (min εI εP))) ≤ εA :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hεI' : min 1 (min εχ (min εA (min εI εP))) ≤ εI :=
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hεP' : min 1 (min εχ (min εA (min εI εP))) ≤ εP :=
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hAdm1 : Work.BoseBoxFix.Adm v 1 μ := ⟨hμ, le_trans hdil hε1, hPOK⟩
    have hAdmχ : Work.BoseBoxFix.Adm v εχ μ := ⟨hμ, le_trans hdil hεχ', hPOK⟩
    have hAdmA : Work.BoseBoxFix.Adm v εA μ := ⟨hμ, le_trans hdil hεA', hPOK⟩
    have hAdmI : Work.BoseBoxFix.Adm v εI μ := ⟨hμ, le_trans hdil hεI', hPOK⟩
    have hAdmP : Work.BoseBoxFix.Adm v εP μ := ⟨hμ, le_trans hdil hεP', hPOK⟩
    have hRℓ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 :=
      hχ μ hAdmχ
    have har := harith μ hAdmA
    dsimp only at har
    obtain ⟨har1, har2, har3, har4, har5⟩ := har
    have hA0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
    have hLpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      Work.BoseBox.sideAt_pos hμ hav
    have hL3nn : 0 ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := pow_nonneg hLpos.le 3
    have hk8 : 8 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
        ≤ ((Nat.ceil (8 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) : ℕ) : ℝ) :=
      Nat.le_ceil _
    have hmain := blockInduction (h := h) (hv := hv) (hvrad := hvrad) (hμ := hμ) (hav := hav)
      (C := C) (Kp := 94 * π) (K₂ := K₂) (Kc := Kc) (K₂' := K₂')
      (k := Nat.ceil (8 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3))
      hC0 (by linarith [Real.pi_gt_three]) (le_refl _) hK₂0
      (le_max_left _ _) (le_max_right _ _) (le_max_left _ _) (le_max_right _ _)
      har2 hk8 har4
      (fun {n} {Ψ} hΨ => hcrude (n := n) (μ := μ) hμ hAdm1 hRℓ hΨ)
      (fun N Ψ hN hΨ hd hSc => hper μ hAdmP N Ψ hN hΨ hd hSc)
      hvi hgi
      (fun {p q} {Φ} hΦ => hIntI μ hAdmI (k := p) (j := q) (Φ := Φ) hΦ)
    have hres := hmain n (Φ : Submission.BoseGases.X n → ℝ) Φ.contDiff
    -- the spectral input `n₊ ≤ 𝓜‖·‖²` and `𝓜 ≤ μ(a v)ℓ³`
    have h𝓜0 : 0 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v))
        (_root_.BoseGases.a v) μ :=
      (Work.BoseBox.bigM_pos_of_params hμ hav).le
    have hspec' : Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v))
            (_root_.BoseGases.a v) μ * Work.BoseBoxFix.normB v μ n Φ := by
      have h1 := Work.BoseBox.cnPlus_le_of_spectralNPlusLe
        (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) hLpos h𝓜0
        Φ.contDiff.continuous hspec
      simpa [Work.BoseBox.norm2N, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] using h1
    rw [Work.BoseFixR.ell3, Work.BoseFixR.ell]
    have hNB0 : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := le_of_lt hNB
    have hnn : (0 : ℝ) ≤ μ ^ 2 * (_root_.BoseGases.a v)
        * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 :=
      mul_nonneg (mul_nonneg (sq_nonneg μ) hA0) hL3nn
    have hcoef : (Kc + K₂') * μ ^ 2 * (_root_.BoseGases.a v)
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
        ≤ (max 1 (Kc + K₂')) * μ ^ 2 * (_root_.BoseGases.a v)
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
      have h := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (Kc + K₂')) hnn
      nlinarith [h]
    have h1 := mul_le_mul_of_nonneg_right hcoef hNB0
    have hK₂'0 : 0 ≤ K₂' := le_trans (mul_nonneg hC0 hA0) (le_max_right _ _)
    have h2 : K₂' * μ * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Φ : Submission.BoseGases.X n → ℝ)
        ≤ K₂' * μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
          * Work.BoseBoxFix.normB v μ n Φ := by
      have hμK : 0 ≤ K₂' * μ := mul_nonneg hK₂'0 hμ.le
      have hstep1 : K₂' * μ * Submission.BoseGases.cnPlus
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ)
          ≤ K₂' * μ * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v))
              (_root_.BoseGases.a v) μ * Work.BoseBoxFix.normB v μ n Φ) :=
        mul_le_mul_of_nonneg_left hspec' hμK
      have hstep2 : K₂' * μ * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v))
              (_root_.BoseGases.a v) μ * Work.BoseBoxFix.normB v μ n Φ)
          ≤ K₂' * μ * (μ * (_root_.BoseGases.a v)
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
            * Work.BoseBoxFix.normB v μ n Φ := by
        have hM := mul_le_mul_of_nonneg_right har5 hNB0
        have h3 := mul_le_mul_of_nonneg_left hM hμK
        have h4 : K₂' * μ * ((μ * (_root_.BoseGases.a v)
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
              * Work.BoseBoxFix.normB v μ n Φ)
            = K₂' * μ * (μ * (_root_.BoseGases.a v)
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
              * Work.BoseBoxFix.normB v μ n Φ := by ring
        linarith [h3, h4]
      have heq : K₂' * μ * (μ * (_root_.BoseGases.a v)
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
            * Work.BoseBoxFix.normB v μ n Φ
          = K₂' * μ ^ 2 * (_root_.BoseGases.a v)
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
            * Work.BoseBoxFix.normB v μ n Φ := by ring
      linarith [hstep1, hstep2, heq]
    linarith [hres, h1, h2]

end Work.BoseFixR
