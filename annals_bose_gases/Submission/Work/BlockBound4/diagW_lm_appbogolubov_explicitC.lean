import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BlockBound4.d1_log_arith_F
import Submission.Work.BlockBound4.d1_main_arith_F
import Submission.Work.BlockBound4.d1_quart_arith_F
import Submission.Work.BlockBound4.diag_content_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# R1 — FS's `lm:appbogolubov` (`eq:refinedaprioribog`) at the FAITHFUL (one-particle-sum) word

The word is FS's one-particle sum `Σ_i Q_{B,i}χ_{B,i}[√−Δ_i − c]₊²χ_{B,i}Q_{B,i}`, i.e.
`pDiagForm s (fsKinCoeff c₀)` (NOT the square-of-a-sum `kinPWord`): see the module docstring
of `Submission.Work.BlockBound4.Defs` (Door 4) and of `DiagWF`.

The proof routes the faithful word through

* the Cauchy–Schwarz step `pDiagForm ≥ kinPWord/(N̂+1)` (`KinPSuperadd.kinPWord_le_diagWord`);
* the faithful Bogoliubov content integral `diag_content_integral` (FS's `𝒜(p) =
  s³[‖p‖−c]₊²/(N̂+1) + 2K_s a`, whose deficit is EXACTLY `2K_s a s⁻³`);
* the sharp main term `diag_main_term_le_sharp` against `hNewton`;
* the four scalar comparisons `d1_main_arith_F`, `d1_log_arith_F`, `d1_quart_arith_F`,
  `d1_int_arith`; and the `A₁` mass `a1_mass_bound`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Work.BlockBound4

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem diagW_lm_appbogolubov_explicitC {N : ℕ} {s c0 Ct : ℝ} (hs : 0 < s) (hc0 : 0 < c0)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hsR : R ≤ s * chiR0) (hN : 1 ≤ N) (hav : 0 < a v) (hdil : 2 * c0 * (a v) ≤ 1)
    (hWfin : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (1 / ‖q.1 - q.2‖)))
    (hCt : 0 ≤ Ct)
    (hNewton : (1 / (2 * Real.pi) ^ 3) * ∫ q : EuclideanSpace ℝ (Fin 3),
        ((FourierTransform.fourier (fun x : EuclideanSpace ℝ (Fin 3) =>
            (wScaled s (g0 v h) x : ℂ)) ((1 / (2 * Real.pi)) • q)).re) ^ 2 / ‖q‖ ^ 2
      ≤ 2 * (1 + 6 * Ct * (R / s) ^ 2) * g0w0Mass (v := v) h) :
    ∃ C : ℝ, C = d1TargetC Ct chiR0 chiSup d1Ks ∧ 0 ≤ C ∧
      ∀ (Φ : X (N + 1) → ℝ), ContDiff ℝ ∞ Φ →
      (∫ x in abox (N + 1) s, (Φ x) ^ 2) = 1 →
      pDiagForm s (fsKinCoeff c0) Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) ≥
        - (1 / 2 : ℝ) * (1 + C * (R / s)) * (1 + C * c0 * (a v))
            * g0w0Mass (v := v) h * d4MassCoeff (N + 1) s
        - C * ((a v) ^ 2 * c0 * Real.log (1 / (c0 * (a v)))
                  * ((((N : ℝ) + 1) * ((N : ℝ) + 1)) / s ^ 3)
              + (a v) ^ 4 * (1 / c0 ^ 3) * ((((N : ℝ) + 1) / s ^ 3) ^ 3)
                  * (((N : ℝ) + 1) / s ^ 3) * s ^ 3
              + (a v) * c0 ^ 3 * (((N : ℝ) + 1) / s ^ 3) * s ^ 3)
        - C * (a v) * (((N : ℝ) + 1) / s ^ 3) * cnPlus s Φ := by
  cases N with
  | zero => exact absurd hN (by omega)
  | succ n =>
    have hC0 : 0 ≤ d1TargetC Ct chiR0 chiSup d1Ks := by
      unfold d1TargetC
      refine le_trans (by positivity : (0 : ℝ) ≤ 6 * (2 * Real.pi) ^ 3) (le_max_left _ _)
    refine ⟨d1TargetC Ct chiR0 chiSup d1Ks, rfl, hC0, ?_⟩
    intro Φ hΦc hΦnorm
    have hcast : (((Nat.succ n : ℕ) : ℝ) + 1) = ((n : ℝ) + 2) := by
      rw [Nat.cast_succ]; ring
    rw [hcast]
    set M : ℝ := (n : ℝ) + 2 with hMdef
    set C : ℝ := d1TargetC Ct chiR0 chiSup d1Ks with hCdef
    have hd4 : d4MassCoeff (Nat.succ n + 1) s = M * (M + 1) / s ^ 3 := by
      unfold d4MassCoeff
      push_cast
      rw [hMdef]
      ring
    rw [hd4]
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
    have hM2 : (2 : ℝ) ≤ M := by rw [hMdef]; linarith
    have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM1
    -- the explicit constant and its lower bounds
    have hCge1 : 6 * (2 * Real.pi) ^ 3 ≤ C := by
      rw [hCdef]; unfold d1TargetC; exact le_max_left _ _
    have hCge2 : 36 * Ct * (2 * Real.pi) ^ 3 * chiR0 ≤ C := by
      rw [hCdef]; unfold d1TargetC; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hCge3 : 1536 * Real.pi ^ 3 * (1 + Real.log 2) ≤ C := by
      rw [hCdef]; unfold d1TargetC
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have hCge4 : 8 * (16 * Real.pi) ^ 4 * Real.pi / 3 ≤ C := by
      rw [hCdef]; unfold d1TargetC
      exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_max_right _ _)) (le_max_right _ _)
    have hCge5 : 80 * Real.pi ^ 2 / 3 ≤ C := by
      rw [hCdef]; unfold d1TargetC
      exact le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
    have hCge6 : 4 * d1Ks * chiSup ^ 2 ≤ C := by
      rw [hCdef]; unfold d1TargetC
      exact le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
    have hCpos : (0 : ℝ) < C := by nlinarith [hCge1, Real.pi_pos]
    have hC6 : (6 : ℝ) ≤ C := by
      have hp : (1 : ℝ) ≤ (2 * Real.pi) ^ 3 := by nlinarith [Real.pi_gt_three]
      nlinarith [hCge1, hp]
    have hCchi : 6 * Ct * chiR0 ≤ C := by
      have hp : (1 : ℝ) ≤ 6 * (2 * Real.pi) ^ 3 := by nlinarith [Real.pi_gt_three]
      have h0 : 0 ≤ Ct * chiR0 := mul_nonneg hCt (le_of_lt chiR0_pos)
      have hp6 : (6 : ℝ) ≤ 36 * (2 * Real.pi) ^ 3 := by nlinarith [hp]
      have h1 : 6 * Ct * chiR0 ≤ 36 * Ct * (2 * Real.pi) ^ 3 * chiR0 := by
        have hh := mul_le_mul_of_nonneg_right hp6 h0
        nlinarith [hh]
      linarith [hCge2, h1]
    have hCchi2 : 36 * Ct * chiR0 ≤ C ^ 2 := by
      have h1 : 0 ≤ 6 * Ct * chiR0 := mul_nonneg (mul_nonneg (by norm_num) hCt)
        (le_of_lt chiR0_pos)
      have h2 := mul_le_mul hCchi hC6 (by norm_num : (0 : ℝ) ≤ 6) (le_of_lt hCpos)
      nlinarith [h2]
    have hC384 : (384 : ℝ) ≤ C := by
      have hp : (1 : ℝ) ≤ (2 * Real.pi) ^ 3 := by nlinarith [Real.pi_gt_three]
      have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      have h1 : (384 : ℝ) ≤ 1536 * Real.pi ^ 3 * (1 + Real.log 2) := by
        nlinarith [Real.pi_gt_three, hlog]
      linarith [hCge3, h1]
    have hC27 : 27 * ((16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2)) ≤ C := by
      have hpi3 : 27 ≤ 8 * Real.pi ^ 3 := by nlinarith [Real.pi_gt_three]
      have hX : 0 ≤ (16 * Real.pi) ^ 4 := by positivity
      have h1 : 27 * ((16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2))
          ≤ 8 * (16 * Real.pi) ^ 4 * Real.pi / 3 := by
        rw [show 27 * ((16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2))
            = (27 * (16 * Real.pi) ^ 4) / (3 * Real.pi ^ 2) from by ring]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * Real.pi ^ 2)]
        nlinarith [hpi3, hX]
      linarith [hCge4, h1]
    have hCint : 10 / (3 * Real.pi) ≤ C := by
      have h3 : (1 : ℝ) ≤ 8 * Real.pi ^ 3 := by nlinarith [Real.pi_gt_three]
      have h1 : 10 / (3 * Real.pi) ≤ 80 * Real.pi ^ 2 / 3 := by
        have heq : 80 * Real.pi ^ 2 / 3 = (10 / (3 * Real.pi)) * (8 * Real.pi ^ 3) := by
          field_simp; try ring
        rw [heq]
        have h4 : 0 ≤ 10 / (3 * Real.pi) := by positivity
        have h5 := mul_le_mul_of_nonneg_left h3 h4
        linarith [h5]
      linarith [hCge5, h1]
    -- standing facts
    have hRs : R / s ≤ chiR0 := by rw [div_le_iff₀ hs]; linarith [hsR]
    have hRs0 : 0 ≤ R / s := by positivity
    have hAV0 : 0 ≤ a v := le_of_lt hav
    have hCP0 : 0 ≤ cnPlus s Φ := cnPlus_nonneg
    have hGW0 : 0 ≤ g0w0Mass (v := v) h :=
      g0w0Mass_nonneg hR hv_nonneg hvrad hv_supp h
    have hWint : Integrable (fun z : ℝ³ => wScaled s (g0 v h) z) :=
      wScaled_g0_integrable hR hv_supp h hs hsR
    have hW0 : 0 ≤ᵐ[volume] (fun z : ℝ³ => wScaled s (g0 v h) z) :=
      wScaled_g0_nonneg_ae (ℓ := s) hR hv_nonneg hvrad hv_supp h
    have hWfin' : Integrable (fun q : ℝ³ × ℝ³ =>
        wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹) := by
      simpa only [one_div] using hWfin
    have hWmeas : Measurable (d1Bcoef (wScaled s (g0 v h))) := by
      unfold d1Bcoef
      exact (Complex.continuous_re.comp
        ((continuous_cfourier hWint).comp (continuous_const_smul _))).measurable
    have hInt : Integrable (fun q : ℝ³ => (d1Bcoef (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2) :=
      integrable_pairW_sq_div hWint hW0 hWfin'
    have hWb : ∀ q : ℝ³, |d1Bcoef (wScaled s (g0 v h)) q| ≤ 16 * Real.pi * (a v) :=
      fun q => abs_pairW_wScaled_g0_le hR hv_nonneg hvrad hv_supp h hs hsR q
    -- (F1) the diagonal Cauchy-Schwarz step
    have hdiag : kinPWord s c0 Φ / (M + 1) ≤ pDiagForm s (fsKinCoeff c0) Φ := by
      have hint2 := Work.SmallBoxBridge.Cauchy.integrable_cModeForm
        (n := n + 1) (s := s) (c := c0) hs (le_of_lt hc0) hΦc
      have hKS := Work.KinPSuperadd.kinPWord_le_diagWord (n := n + 1) (s := s) (c := c0)
        hs hΦc.continuous hint2
      have hfac : (((((n + 1) + 1 : ℕ)) : ℝ) + 1) = M + 1 := by
        push_cast
        rw [hMdef]
        ring
      rw [hfac] at hKS
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < M + 1)]
      linarith [hKS]
    -- (F2) the faithful content integral
    have hcontent := diag_content_integral (p := n) (s := s) (c0 := c0) hs hc0 hR hsR
      hv_nonneg hvrad hv_supp h hav hWfin' hΦc hΦnorm
    rw [← hMdef] at hcontent
    obtain ⟨PA, hPAeq⟩ : ∃ P : ℝ, P = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
        diagKF s c0 (a v) M (wScaled s (g0 v h)) q * M := ⟨_, rfl⟩
    obtain ⟨AA, hAAeq⟩ : ∃ A : ℝ, A = 2 * d1Ks * (a v) * (s ^ 3)⁻¹ *
        (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
          (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) := ⟨_, rfl⟩
    rw [← hPAeq, ← hAAeq] at hcontent
    -- (F3) the sharp main term
    have hZbd : ((2 * Real.pi) ^ 3)⁻¹
          * (∫ q : ℝ³, (d1Bcoef (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2)
        ≤ 2 * (1 + 6 * Ct * (R / s) ^ 2) * g0w0Mass (v := v) h := by
      simpa only [d1Bcoef, pairW, cfourier, one_div] using hNewton
    have hpB := d1_exterior_bracket_le (c0 := c0) (av := a v) hc0 hav hdil hWmeas hWb hInt
    have hqE := d1_ext_quartF_le (s := s) (c0 := c0) (av := a v) (M := M) hs hc0 hav hM0
      hWmeas hWb
    have hvol : (volume : Measure ℝ³).real (d1Int c0)
        = (4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3 := by
      have h1 : (∫ q in d1Int c0, (1 : ℝ)) = (volume : Measure ℝ³).real (d1Int c0) := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
      rw [← h1]
      exact momentum_ball_integral_one (2 * c0) (by positivity)
    have hCi : (∫ q in d1Int c0, (2 * Real.pi * (a v) + Real.pi / 2 * (a v)))
        ≤ (2 * Real.pi * (a v) + Real.pi / 2 * (a v)) * ((4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
      exact le_of_eq (mul_comm _ _)
    have hmain := diag_main_term_le_sharp (s := s) (c0 := c0) (av := a v) (M := M)
      hs hc0 hav hM0 hWmeas hWb hInt hpB hqE hCi
    have hPA : PA ≤
        M * ((M + 1) / (4 * s ^ 3)) * (1 + 6 * c0 * (a v))
          * (((2 * Real.pi) ^ 3)⁻¹
              * (∫ q : ℝ³, (d1Bcoef (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2))
      + M * ((M + 1) / (4 * s ^ 3))
          * (((2 * Real.pi) ^ 3)⁻¹
              * (6 * c0 * (16 * Real.pi * (a v)) ^ 2
                  * (4 * Real.pi * Real.log ((2 * c0 * (a v))⁻¹))))
      + M * ((2 * Real.pi) ^ 3)⁻¹
          * (((M + 1) ^ 3 / (4 * s ^ 9))
              * (64 * (16 * Real.pi * (a v)) ^ 4
                  * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹)))
      + M * ((2 * Real.pi) ^ 3)⁻¹
          * ((2 * Real.pi * (a v) + Real.pi / 2 * (a v))
              * ((4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3)) := by
      rw [hPAeq]
      refine le_trans hmain (le_of_eq ?_)
      ring
    -- (F4) the four scalar comparisons
    have hb1 : M * ((M + 1) / (4 * s ^ 3)) * (1 + 6 * c0 * (a v))
          * (((2 * Real.pi) ^ 3)⁻¹
              * (∫ q : ℝ³, (d1Bcoef (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2))
        ≤ (1 / 2) * (1 + C * (R / s)) * (1 + C * c0 * (a v)) * (g0w0Mass (v := v) h)
            * (M * (M + 1) / s ^ 3) :=
      d1_main_arith_F (hs := hs) (hM1 := hM1) (hRs := hRs) (hRs0 := hRs0)
        (hav := hAV0) (hc0 := le_of_lt hc0) (hCt := hCt) (hGW := hGW0)
        (hC6 := hC6) (hCchi := hCchi) (hCchi2 := hCchi2) (hZ := hZbd)
    have hb2 : M * ((M + 1) / (4 * s ^ 3))
          * (((2 * Real.pi) ^ 3)⁻¹
              * (6 * c0 * (16 * Real.pi * (a v)) ^ 2
                  * (4 * Real.pi * Real.log ((2 * c0 * (a v))⁻¹))))
        ≤ C * ((a v) ^ 2 * c0 * Real.log (1 / (c0 * (a v))) * (M * M / s ^ 3)) := by
      simpa only [one_div] using
        d1_log_arith_F (hs := hs) (hM1 := hM1) (hc0 := hc0) (hav := hav) (hdil := hdil)
          (hC := hC384)
    have hb3 : M * ((2 * Real.pi) ^ 3)⁻¹
          * (((M + 1) ^ 3 / (4 * s ^ 9))
              * (64 * (16 * Real.pi * (a v)) ^ 4
                  * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹)))
        ≤ C * ((a v) ^ 4 * (1 / c0 ^ 3) * (((M / s ^ 3) ^ 3) * ((M / s ^ 3)) * s ^ 3)) := by
      simpa only [one_div] using
        d1_quart_arith_F (hs := hs) (hM2 := hM2) (hc0 := hc0) (hav := hav) (hC := hC27)
    have hb4 : M * ((2 * Real.pi) ^ 3)⁻¹
          * ((2 * Real.pi * (a v) + Real.pi / 2 * (a v))
              * ((4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3))
        ≤ C * ((a v) * c0 ^ 3 * ((M / s ^ 3) * s ^ 3)) :=
      d1_int_arith (hs := hs) (hc0 := hc0) (hav := hav) (hM0 := hM0) (hC := hCint)
    -- (F5) the `A₁` mass
    have ha1 := a1_mass_bound (s := s) (n := Nat.succ n) (Φ := Φ) hs hΦc
      (Ks := d1Ks) (a := a v) (le_of_lt d1Ks_pos) (le_of_lt hav)
    have hAb : AA ≤ C * (a v) * (M / s ^ 3) * cnPlus s Φ := by
      rw [hAAeq]
      have h1 : 2 * d1Ks * (a v) * (s ^ 3)⁻¹ * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ q : ℝ³, (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ))
          ≤ (4 * d1Ks * chiSup ^ 2) * (a v)
              * ((((Nat.succ n : ℕ) : ℝ) + 1) / s ^ 3) * cnPlus s Φ := ha1
      rw [hcast] at h1
      have h2 : (4 * d1Ks * chiSup ^ 2) * (a v) * (M / s ^ 3) * cnPlus s Φ
          ≤ C * (a v) * (M / s ^ 3) * cnPlus s Φ := by
        have h3 : 0 ≤ (a v) * ((M / s ^ 3) * cnPlus s Φ) :=
          mul_nonneg hAV0 (mul_nonneg (by positivity) hCP0)
        have h4 := mul_le_mul_of_nonneg_right hCge6 h3
        nlinarith [h4]
      linarith [h1, h2]
    linarith [hcontent, hdiag, hPA, hb1, hb2, hb3, hb4, hAb]

end Work.BlockBound4
