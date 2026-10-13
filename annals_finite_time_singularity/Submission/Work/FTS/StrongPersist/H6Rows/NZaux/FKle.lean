import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Bound
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.NonlinRows.Rl1.starUopBound
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Acf
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `NZaux/FKle` — the angular moment `FK (F_* + f)`

`|FK (F_* + f)(z)| ≤ 100(1+Cag)α^{-1/2}(1+M)` on `z > 0`, from the pointwise bound on `f` and
`|F_*| ≤ 20α·z/(1+z)² ≤ 5α` (via the `ℝ≥0∞`-form of the triangle inequality for the Bochner
integral and `volume Iθ = π/2`).
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The angular moment `FK (F_* + f)` is bounded by `100(1+Cag)α^{-1/2}(1+M)`. -/
theorem FK_le {α M Cag : ℝ} {f : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M)
    (hCag0 : 0 < Cag)
    (hX : Work.FTS.Nonlin.Xn α f ≤ M)
    (hsupf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |f z θ| ≤ Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f)
    {z : ℝ} (hz : 0 < z) :
    |Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
      ≤ 100 * (1 + Cag) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hp0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hC0 : 0 ≤ Cag * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCag0.le hp0
  have hc0 : 0 ≤ 3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) := by
    have : 0 ≤ Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f := mul_nonneg hC0 hX0
    linarith
  -- the integral bound, in `ℝ≥0∞`
  have hstep : ENNReal.ofReal |Work.Construction.FK
        (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
      ≤ ENNReal.ofReal (3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f)
          * (Real.pi / 2)) := by
    have hFK : Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
        = ∫ θ in Work.Spaces.Iθ, (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
            * Work.Spaces.K θ := rfl
    rw [hFK]
    refine (Work.FTS.Nonlinear.Pieces.ofReal_abs_integral_le _ _ _).trans ?_
    have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal |(fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
            * Work.Spaces.K θ|
          ≤ ENNReal.ofReal (3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.Nonlin.Xn α f)) := by
      filter_upwards [Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
        (fun θ hθ => hθ)] with θ hθ
      refine ENNReal.ofReal_le_ofReal ?_
      have hK : |Work.Spaces.K θ| ≤ 3 :=
        Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_abs_le ⟨hθ.1.le, hθ.2.le⟩
      have hF : |Work.Construction.Fstar α z θ| ≤ 5 * α := by
        refine le_trans (Work.FTS.NonlinRows.Rl1.Fstar_pt hα0 hα1 hz
          ⟨hθ.1.le, hθ.2.le⟩) ?_
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (1 - z), hα0]
      have hf := hsupf z θ hz hθ.1 hθ.2
      have h1 : |(fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ| ≤ 5 * α
          + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f :=
        le_trans (abs_add_le _ _) (add_le_add hF hf)
      calc |(fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ * Work.Spaces.K θ|
          = |Work.Spaces.K θ| * |(fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ| := by
            rw [abs_mul]; ring
        _ ≤ 3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) :=
            mul_le_mul hK h1 (abs_nonneg _) (by norm_num)
    refine (MeasureTheory.lintegral_mono_ae hpt).trans ?_
    rw [MeasureTheory.setLIntegral_const, Work.Spaces.Iθ, Real.volume_Icc, sub_zero,
      ← ENNReal.ofReal_mul hc0]
  rw [ENNReal.ofReal_le_ofReal_iff] at hstep
  · refine le_trans hstep ?_
    have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
    have hp1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := one_le_rpow_neg_half hα0 hα1
    have hX1 : Work.FTS.Nonlin.Xn α f ≤ 1 + M := by linarith
    have hM1 : (0 : ℝ) ≤ 1 + M := by linarith
    have hA0 : (0 : ℝ) ≤ 5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f := by
      have := mul_nonneg hC0 hX0
      linarith
    have h1 : 30 * α ≤ 100 * α ^ (-(1 / 2 : ℝ)) := by nlinarith
    have h2 : 6 * (Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f)
        ≤ 100 * Cag * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
      have h := mul_le_mul_of_nonneg_left hX1 hC0
      have h3 := mul_nonneg hC0 hM1
      nlinarith [h, h3]
    calc 3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) * (Real.pi / 2)
        ≤ 3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) * 2 :=
          mul_le_mul_of_nonneg_left hpi (by linarith)
      _ = 30 * α + 6 * (Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ 100 * α ^ (-(1 / 2 : ℝ)) + 100 * Cag * α ^ (-(1 / 2 : ℝ)) * (1 + M) :=
          add_le_add h1 h2
      _ ≤ 100 * α ^ (-(1 / 2 : ℝ)) * (1 + M)
            + 100 * Cag * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
          have h4 : 100 * α ^ (-(1 / 2 : ℝ)) ≤ 100 * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
            nlinarith [hp0, hM0]
          linarith
      _ = 100 * (1 + Cag) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by ring
  · have : 0 ≤ 3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) := hc0
    positivity
