import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BlockBound4.DiagWF
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BlockBound4.diag_content_point` — the pointwise D1 content bound at the
FAITHFUL Bogoliubov coefficients

FS's `lm:appbogolubov` is applied per momentum `q`.  This module records the
POINTWISE step at the faithful coefficients: at `𝒜 = diagAF s c₀ av M q`
(`= s³[‖q‖−c₀]₊²/(M+1) + 2K_s·av`, the `|B|/(N̂+1)` normalisation with `N̂ = M`
the particle number) and `ℬ = d1Bcoef W q`, the per-`q` content is bounded below
by the sharp Bogoliubov payment:

  `−K^F(q)·M − 2K_s·av·s⁻³·(P_u + P_v) ≤ (F(q)/(M+1))·(P_u + P_v) + ℬ(q)s⁻³·R(q)`

with `K^F = diagKF`, `F(q) = fsKinCoeff c₀ ‖q‖` and `P`, `R` the two real modes'
number/pairing forms.  This is the faithful counterpart of the corpus's
`Submission.BoseGases.d1_content_point` (`Work.SmallBoxD1Assembly`), whose
coefficient `d1Acoef = s³F(M−1)/M + 2K_s av` carries the corpus's square-of-a-sum
normalisation instead of FS's `s³F/(M+1)`.

The proof is the per-`q` Bogoliubov interface
`Submission.BoseGases.d1_content_bogoliubov` at `A₀ = diagAF·s⁻³`,
`B₀ = d1Bcoef W q·s⁻³`, `F = fsKinCoeff c₀ ‖q‖/(M+1)`, together with

* the homogeneity `bogoliubov_coeff_smul` (`K(cA,cB) = cK(A,B)`), which converts
  `K(𝒜s⁻³,ℬs⁻³)·s³` back into `diagKF`;
* the window normalisation `integral_chiScale_sq_acube` (`∫_{Λ(s)}χ_s² = s³`)
  and the state normalisation `∫_{abox}Φ² = 1`, which turn the mass term
  `K(A₀,B₀)·(∫χ_s²)·M·(∫Φ²)` into `diagKF·M`;
* the EXACT deficit `diagAF·s⁻³ − F/(M+1) = 2K_s·av·s⁻³` (an algebraic identity
  from the definition of `diagAF`), which is the `A₁`-mass coefficient;
* `|d1Bcoef W q| ≤ diagAF` (`DiagWF.abs_d1Bcoef_le_diagAF`), the hypothesis
  `|B₀| ≤ A₀` of the Bogoliubov interface.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BlockBound4

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem diag_content_point {p : ℕ} {s c0 av M : ℝ} (hs : 0 < s) (hav : 0 < av)
    (hM : M = (p : ℝ) + 2)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWb : ∀ q : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.pairW W q| ≤ 16 * Real.pi * av)
    {Φ : Submission.BoseGases.X (p + 2) → ℝ} (hΦ : Continuous Φ)
    (hΦnorm : (∫ x in Submission.BoseGases.abox (p + 2) s, (Φ x) ^ 2) = 1)
    (q : EuclideanSpace ℝ (Fin 3)) :
    - Work.BlockBound4.diagKF s c0 av M W q * M
      - (2 * Submission.BoseGases.d1Ks * av * (s ^ 3)⁻¹)
          * (Submission.BoseGases.modeP s (Submission.BoseGases.qModeRe s q) Φ
             + Submission.BoseGases.modeP s (Submission.BoseGases.qModeIm s q) Φ)
    ≤ (Submission.BoseGases.fsKinCoeff c0 ‖q‖ / (M + 1))
        * (Submission.BoseGases.modeP s (Submission.BoseGases.qModeRe s q) Φ
           + Submission.BoseGases.modeP s (Submission.BoseGases.qModeIm s q) Φ)
      + (Submission.BoseGases.d1Bcoef W q * (s ^ 3)⁻¹) * Submission.BoseGases.pairR s Φ q := by
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hs3i : (0 : ℝ) < (s ^ 3)⁻¹ := inv_pos.mpr hs3
  -- the two hypotheses of the per-`q` Bogoliubov interface
  have hA : 0 < diagAF s c0 av M q * (s ^ 3)⁻¹ :=
    mul_pos (diagAF_pos (c0 := c0) hs hM0 hav q) hs3i
  have hB : |d1Bcoef W q * (s ^ 3)⁻¹| ≤ diagAF s c0 av M q * (s ^ 3)⁻¹ := by
    rw [abs_mul, abs_of_pos hs3i]
    exact mul_le_mul_of_nonneg_right (abs_d1Bcoef_le_diagAF (c0 := c0) hs hM0 hav hWb q) hs3i.le
  have h := d1_content_bogoliubov (n := p + 1) (s := s)
    (A₀ := diagAF s c0 av M q * (s ^ 3)⁻¹) (B₀ := d1Bcoef W q * (s ^ 3)⁻¹)
    (F := fsKinCoeff c0 ‖q‖ / (M + 1)) hs (p := q) hΦ hA hB
  rw [integral_chiScale_sq_acube hs, hΦnorm] at h
  have hcast : ((p + 1 : ℕ) : ℝ) + 1 = M := by rw [hM]; push_cast; ring
  -- `K(𝒜s⁻³,ℬs⁻³)·s³ = K(𝒜,ℬ)` (homogeneity of the Bogoliubov coefficient)
  have hK : ((diagAF s c0 av M q * (s ^ 3)⁻¹
        - Real.sqrt ((diagAF s c0 av M q * (s ^ 3)⁻¹) ^ 2
            - (d1Bcoef W q * (s ^ 3)⁻¹) ^ 2)) / 2) * s ^ 3
      = (diagAF s c0 av M q - Real.sqrt (diagAF s c0 av M q ^ 2 - d1Bcoef W q ^ 2)) / 2 := by
    rw [show diagAF s c0 av M q * (s ^ 3)⁻¹ = (s ^ 3)⁻¹ * diagAF s c0 av M q from mul_comm _ _,
      show d1Bcoef W q * (s ^ 3)⁻¹ = (s ^ 3)⁻¹ * d1Bcoef W q from mul_comm _ _,
      bogoliubov_coeff_smul (A := diagAF s c0 av M q) (B := d1Bcoef W q)
        (c := (s ^ 3)⁻¹) hs3i]
    field_simp
  -- the mass term of the interface is `−diagKF·M`
  have hKtr : -((diagAF s c0 av M q * (s ^ 3)⁻¹
        - Real.sqrt ((diagAF s c0 av M q * (s ^ 3)⁻¹) ^ 2
            - (d1Bcoef W q * (s ^ 3)⁻¹) ^ 2)) / 2)
        * (s ^ 3 * (((p + 1 : ℕ) : ℝ) + 1) * 1)
      = -diagKF s c0 av M W q * M := by
    rw [hcast, mul_one,
      show -((diagAF s c0 av M q * (s ^ 3)⁻¹
          - Real.sqrt ((diagAF s c0 av M q * (s ^ 3)⁻¹) ^ 2
              - (d1Bcoef W q * (s ^ 3)⁻¹) ^ 2)) / 2) * (s ^ 3 * M)
        = -(((diagAF s c0 av M q * (s ^ 3)⁻¹
          - Real.sqrt ((diagAF s c0 av M q * (s ^ 3)⁻¹) ^ 2
              - (d1Bcoef W q * (s ^ 3)⁻¹) ^ 2)) / 2) * s ^ 3) * M from by ring,
      hK]
    rfl
  rw [hKtr] at h
  -- the EXACT kinetic deficit `𝒜s⁻³ − F/(M+1) = 2K_s·av·s⁻³`
  have hdef : diagAF s c0 av M q * (s ^ 3)⁻¹ - fsKinCoeff c0 ‖q‖ / (M + 1)
      = 2 * d1Ks * av * (s ^ 3)⁻¹ := by
    unfold diagAF
    have hM1 : M + 1 ≠ 0 := by rw [hM]; positivity
    field_simp
    ring
  rw [hdef] at h
  unfold pairR
  linarith [h]

end Work.BlockBound4
