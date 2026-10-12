import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.SmallBoxA0.Assembly
import Submission.Work.SmallBoxD1Assembly
import Submission.Work.SmallBoxD1Scalar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SmallBoxA0.lm_appbogolubov_pWord_explicitC`

The **explicit-constant** form of FS's `lm:appbogolubov` (`eq:refinedaprioribog`) in the
corpus's variables: the same per-state lower bound on `kinPWord s c₀ Φ + q4PairWord Φ` as
`Submission.Work.SmallBoxKineticP.lm_appbogolubov_pWord`, but with the Bogoliubov error
constant pinned to the single explicit value

  `d1TargetC Ct chiR0 chiSup d1Ks`

instead of an unspecified witness of an existential.  Consumers (the fixed-`n` small-box
assembly `Work.SmallBoxA0.state_block_bound_of_inputs_kinP`) need the concrete constant,
and the D1 chain (`Submission.Work.SmallBoxD1Final`) produces precisely this value; the
present module re-runs that chain with the constant pinned.

The proof is the D1 bookkeeping: the content bound `d1_content_integral`, the sharp
main-term splitting `d1_main_term_le_sharp` (into the M1 Newtonian-term `hPA` plus the
three error pieces), the `A₁` mass bound `a1_mass_bound`, the four scalar comparisons
`d1_main_arith`/`d1_log_arith`/`d1_quart_arith`/`d1_int_arith` of `SmallBoxD1Scalar`,
and a final `linarith`.  The only role of the explicit constant is that it dominates the
six numerical thresholds by which the four error terms and the main term are controlled.
-/

namespace Work.SmallBoxA0

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The D1 target `lm:appbogolubov` with the explicit constant `d1TargetC Ct chiR0 chiSup d1Ks`.**
Same statement as `Submission.Work.SmallBoxD1Final.lm_appbogolubov_pWord_holds`, with the
existential over the constant replaced by the pinned value. -/
theorem lm_appbogolubov_pWord_explicitC {N : ℕ} {s c0 Ct : ℝ} (hs : 0 < s) (hc0 : 0 < c0)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hsR : R ≤ s * chiR0) (hN : 1 ≤ N) (hav : 0 < a v) (hdil : 2 * c0 * (a v) ≤ 1)
    (hWfin : MeasureTheory.Integrable (fun q : ℝ³ × ℝ³ =>
      wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹))
    (hCt : 0 ≤ Ct)
    (hNewton : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
        ((FourierTransform.fourier (fun x : ℝ³ => (wScaled s (g0 v h) x : ℂ))
            (((2 * Real.pi)⁻¹) • q)).re) ^ 2 / ‖q‖ ^ 2
      ≤ 2 * (1 + 6 * Ct * (R / s) ^ 2) * g0w0Mass (v := v) h) :
    ∃ C : ℝ, C = d1TargetC Ct chiR0 chiSup d1Ks ∧ 0 ≤ C ∧
      ∀ (Φ : X (N + 1) → ℝ), ContDiff ℝ ∞ Φ →
      (∫ x in abox (N + 1) s, (Φ x) ^ 2) = 1 →
      kinPWord s c0 Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) ≥
        - (1 / 2 : ℝ) * (1 + C * (R / s)) * (1 + C * c0 * (a v))
            * g0w0Mass (v := v) h * ((((N : ℝ) + 1) * ((N : ℝ) + 1)) / s ^ 3)
        - C * ((a v) ^ 2 * c0 * Real.log ((c0 * (a v))⁻¹)
                  * ((((N : ℝ) + 1) * ((N : ℝ) + 1)) / s ^ 3)
              + (a v) ^ 4 * (c0 ^ 3)⁻¹ * ((((N : ℝ) + 1) / s ^ 3) ^ 3) * (((N : ℝ) + 1) / s ^ 3) * s ^ 3
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
    have hM0 : (0 : ℝ) < M := by rw [hMdef]; positivity
    have hM2 : 2 ≤ M := by rw [hMdef]; exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hM1' : (1 : ℝ) ≤ M - 1 := by linarith
    have hs3 : (0 : ℝ) < s ^ 3 := by positivity
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
        have h := mul_le_mul_of_nonneg_right hp6 h0
        nlinarith [h]
      linarith [hCge2, h1]
    have hCchi2 : 36 * Ct * chiR0 ≤ C ^ 2 := by
      have h1 : 0 ≤ 6 * Ct * chiR0 := mul_nonneg (mul_nonneg (by norm_num) hCt)
        (le_of_lt chiR0_pos)
      have h2 := mul_le_mul hCchi hC6 (by norm_num : (0 : ℝ) ≤ 6) (le_of_lt hCpos)
      nlinarith [h2]
    have hClogC : 192 * (1 + Real.log 2) ≤ C := by
      have h1 : (192 : ℝ) ≤ 1536 * Real.pi ^ 3 := by nlinarith [Real.pi_gt_three]
      have h2 : 0 ≤ 1 + Real.log 2 := by
        have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        linarith
      nlinarith [hCge3, h1, h2]
    have hCquart : (16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2) ≤ C := by
      have h3 : (1 : ℝ) ≤ 8 * Real.pi ^ 3 := by nlinarith [Real.pi_gt_three]
      have h1 : (16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2)
          ≤ 8 * (16 * Real.pi) ^ 4 * Real.pi / 3 := by
        have heq : 8 * (16 * Real.pi) ^ 4 * Real.pi / 3
            = ((16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2)) * (8 * Real.pi ^ 3) := by
          field_simp; try ring
        rw [heq]
        have h4 : 0 ≤ (16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2) := by positivity
        have h5 := mul_le_mul_of_nonneg_left h3 h4
        linarith [h5]
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
    -- standing facts on the potential
    have hRs : R / s ≤ chiR0 := by rw [div_le_iff₀ hs]; linarith [hsR]
    have hRs0 : 0 ≤ R / s := by positivity
    have hAV0 : 0 ≤ a v := le_of_lt hav
    have hCP0 : 0 ≤ cnPlus s Φ := cnPlus_nonneg
    have hGW0 : 0 ≤ g0w0Mass (v := v) h := g0w0Mass_nonneg hR hv_nonneg hvrad hv_supp h
    -- the test-function toolbox
    have hWint : MeasureTheory.Integrable (fun z : ℝ³ => wScaled s (g0 v h) z) :=
      wScaled_g0_integrable hR hv_supp h hs hsR
    have hW0 : 0 ≤ᵐ[volume] (fun z : ℝ³ => wScaled s (g0 v h) z) :=
      wScaled_g0_nonneg_ae (ℓ := s) hR hv_nonneg hvrad hv_supp h
    have hWfin' : MeasureTheory.Integrable (fun q : ℝ³ × ℝ³ =>
        wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹) := hWfin
    have hWmeas : Measurable (d1Bcoef (wScaled s (g0 v h))) := by
      unfold d1Bcoef
      exact (Complex.continuous_re.comp
        ((continuous_cfourier hWint).comp (continuous_const_smul _))).measurable
    have hInt : MeasureTheory.Integrable
        (fun q : ℝ³ => (d1Bcoef (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2) :=
      integrable_pairW_sq_div hWint hW0 hWfin'
    have hWb : ∀ q : ℝ³, |d1Bcoef (wScaled s (g0 v h)) q| ≤ 16 * Real.pi * (a v) :=
      fun q => abs_pairW_wScaled_g0_le hR hv_nonneg hvrad hv_supp h hs hsR q
    -- the three analytic inputs and the sharp main-term bound
    have hpb := d1_exterior_bracket_le (c0 := c0) (av := a v) hc0 hav hdil hWmeas hWb hInt
    have hqe := d1_exterior_quart_le (s := s) (c0 := c0) (av := a v) (M := M) hs hc0 hav hM2
      hWmeas hWb
    have hci := d1_interior_le (s := s) (c0 := c0) (av := a v) (M := M) hs hc0 hav hM2 hWb
    have hmain := d1_main_term_le_sharp (s := s) (c0 := c0) (av := a v) (M := M) hs hc0 hav hM2
      hWmeas hWb hInt hpb hqe hci
    -- the content bound and the `A₁` bound
    have hcontent := d1_content_integral (p := n) (s := s) (c0 := c0) hs hc0 hR hsR
      hv_nonneg hvrad hv_supp h hav hWfin hΦc hΦnorm
    have ha1 := a1_mass_bound (s := s) (n := Nat.succ n) (Φ := Φ) hs hΦc
      (Ks := d1Ks) (a := a v) (le_of_lt d1Ks_pos) (le_of_lt hav)
    -- opaque names for the two terms of the content bound
    obtain ⟨PA, hPAeq⟩ : ∃ P : ℝ, P = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
        d1Kcoef s c0 (a v) ((n : ℝ) + 2) (wScaled s (g0 v h)) q * ((n : ℝ) + 2) := ⟨_, rfl⟩
    obtain ⟨AA, hAAeq⟩ : ∃ A : ℝ, A = 2 * d1Ks * (a v) * (s ^ 3)⁻¹ *
        (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
          (modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ)) := ⟨_, rfl⟩
    rw [← hPAeq, ← hAAeq] at hcontent
    -- the sharp main-term bookkeeping, split into its four pieces
    have hPA : PA ≤ M * (M / (4 * s ^ 3 * (M - 1))) * (1 + 6 * c0 * (a v))
          * (((2 * Real.pi) ^ 3)⁻¹
              * (∫ q : ℝ³, (d1Bcoef (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2))
        + M * (M / (4 * s ^ 3 * (M - 1)))
            * (((2 * Real.pi) ^ 3)⁻¹
                * (6 * c0 * (16 * Real.pi * (a v)) ^ 2
                    * (4 * Real.pi * Real.log ((2 * c0 * (a v))⁻¹))))
        + M * (((2 * Real.pi) ^ 3)⁻¹
            * ((M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
                * (64 * (16 * Real.pi * (a v)) ^ 4
                    * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹))))
        + M * (((2 * Real.pi) ^ 3)⁻¹
            * ((2 * Real.pi * (a v) + Real.pi / 2 * (a v))
                * ((4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3))) := by
      rw [hPAeq]
      refine le_trans hmain (le_of_eq ?_)
      ring
    -- the M1 input in the form used by `d1_main_arith`
    have hZbd : ((2 * Real.pi) ^ 3)⁻¹
          * (∫ q : ℝ³, (d1Bcoef (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2)
        ≤ 2 * (1 + 6 * Ct * (R / s) ^ 2) * g0w0Mass (v := v) h := by
      simpa only [d1Bcoef, pairW, cfourier] using hNewton
    -- (1) the main term
    have hb1 : M * (M / (4 * s ^ 3 * (M - 1))) * (1 + 6 * c0 * (a v))
          * (((2 * Real.pi) ^ 3)⁻¹
              * (∫ q : ℝ³, (d1Bcoef (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2))
        ≤ (1 / 2) * (1 + C * (R / s)) * (1 + C * c0 * (a v)) * (g0w0Mass (v := v) h)
            * (M * M / s ^ 3) :=
      d1_main_arith (s := s) (M := M) (R := R) (c0 := c0) (Ct := Ct) (av := a v) (C := C)
        (chi0 := chiR0) (GW := g0w0Mass (v := v) h)
        (Z := ((2 * Real.pi) ^ 3)⁻¹
          * (∫ q : ℝ³, (d1Bcoef (wScaled s (g0 v h)) q) ^ 2 / ‖q‖ ^ 2))
        hs hM2 hRs hRs0 hAV0 (le_of_lt hc0) hCt hGW0 hC6 hCchi hCchi2 hZbd
    -- (2) the logarithmic error
    have hb2 : M * (M / (4 * s ^ 3 * (M - 1)))
          * (((2 * Real.pi) ^ 3)⁻¹
              * (6 * c0 * (16 * Real.pi * (a v)) ^ 2
                  * (4 * Real.pi * Real.log ((2 * c0 * (a v))⁻¹))))
        ≤ C * ((a v) ^ 2 * c0 * Real.log ((c0 * (a v))⁻¹) * (M * M / s ^ 3)) :=
      d1_log_arith (s := s) (M := M) (c0 := c0) (av := a v) (C := C) hs hM2 hc0 hav hdil hClogC
    -- (3) the quartic error
    have hb3 : M * (((2 * Real.pi) ^ 3)⁻¹
          * ((M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
              * (64 * (16 * Real.pi * (a v)) ^ 4
                  * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹))))
        ≤ C * ((a v) ^ 4 * (c0 ^ 3)⁻¹ * ((M / s ^ 3) ^ 3) * (M / s ^ 3) * s ^ 3) := by
      have h := d1_quart_arith (s := s) (M := M) (c0 := c0) (av := a v) (C := C)
        hs hM2 hc0 hav hCquart
      linarith [h]
    -- (4) the interior error
    have hb4 : M * (((2 * Real.pi) ^ 3)⁻¹
          * ((2 * Real.pi * (a v) + Real.pi / 2 * (a v))
              * ((4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3)))
        ≤ C * ((a v) * c0 ^ 3 * (M / s ^ 3) * s ^ 3) := by
      have h := d1_int_arith (s := s) (c0 := c0) (av := a v) (M := M) hs hc0 hav (le_of_lt hM0)
        hCint
      linarith [h]
    -- (5) the `A₁` mass
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
    linarith [hcontent, hPA, hb1, hb2, hb3, hb4, hAb]

end Work.SmallBoxA0
