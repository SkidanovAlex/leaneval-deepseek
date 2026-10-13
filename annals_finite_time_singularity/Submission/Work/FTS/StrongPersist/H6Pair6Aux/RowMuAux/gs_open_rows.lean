/-
# `H6Pair6Aux/RowMuAux/gs_open_rows` — the two `gs`-rows of `N` in the open class

The rows `N₄^{gs}`, `N₅^{gs}` are the pieces of `N` whose coefficient is the angular moment
`FK f = ∫_θ f(·,θ)K(θ)dθ` multiplied by the explicit profile `∂_θF_*` resp. `F_*`
(`F_* = Fstar α`).  Their closed-quadrant counterparts are
`Work.FTS.NonlinRows.Rl1.gsRows45` and the pair of row lemmas `row4gs_le`/`row5gs_le` of
`Work.FTS.NonlinRows.Rl1.gssgFKBounds`, all phrased in the envelope
`Env α f = α² + √α·|f|_{ℋ⁴} + α^{-3/2}|f|²_{ℋ⁴}`.

Here the same two rows are proved for the *open* class `SmoothOpen f` + `HkMem α 4 f` — the
class actually available on this route (`H6Adm α f` gives `SmoothOpen`, while the
closed-quadrant class `SmoothQuad` is unavailable) — with the slot data of the datum read off
from `SmoothOpen`+`HkMem` alone by `RowMuAux/SlotDataOpen` (`slotData_open_g`), in place of the
closed-quadrant `slot0`.

The proof is the verbatim open-class version of the two `gs`-halves of `gsRows45`:

* the pointwise angular bounds `N4gs_pt`/`N5gs_pt` (`Work.FTS.NonlinRows.Rl1`) are
  class-independent and give `|K θ·Nᵢ^{gs}| ≤ cᵢ r·|FK f r|` with the explicit profiles
  `c₄ = 40α²r/(1+r)²`, `c₅ = 60αr/(1+r)²`;
* `|FK f r| ≤ 4√(Φ₀ f r)` (`FK_sq_le_sixteen_Phi0`, with the slot integrability from `SlotData`);
* the `r`-step engine `Fa_le_of_profile` then gives
  `Fa Nᵢ^{gs} ≤ ofReal (π/2·4·√(∫Φ₀)·√(∫(r⁻¹cᵢ)²))`, and `profile_data_sq` evaluates the radial
  factor as `≤ 40α²√2` resp. `≤ 60α√2` (`√2 ≤ 2`);
* finally `√(∫Φ₀) ≤ |f|_{ℋ⁴}`, `α²|f|_{ℋ⁴} ≤ Env α f`, `α|f|_{ℋ⁴} ≤ Env α f` absorb the
  rates into the envelope.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
import Submission.Work.FTS.NonlinRows.Rl1.gssgFKBounds
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.Rows45
import Submission.Work.FTS.NonlinRows.Rl1.FaCoefSlot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-- `√2 ≤ 2`. -/
private theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
  rwa [show Real.sqrt (4 : ℝ) = 2 from by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h

/-- `√16 = 4`. -/
private theorem sqrt_sixteen : Real.sqrt (16 : ℝ) = 4 := by
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `|FK f r| ≤ 4√(Φ₀ f r)`, from the slot integrability and strong measurability. -/
private theorem FK_abs_le_four_sqrt {f : Fn} {r : ℝ} (hr : 0 < r)
    (hint : MeasureTheory.IntegrableOn (fun θ => (f r θ) ^ 2) Work.Spaces.Iθ)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun θ => f r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    |Work.Construction.FK f r|
      ≤ 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r) := by
  have hFK := Real.abs_le_sqrt
    (Work.FTS.NonlinRows.Rl1.FK_sq_le_sixteen_Phi0 (g := f) hr hint haesm)
  rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), sqrt_sixteen] at hFK

theorem gs_open_rows : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4gs α f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5gs α f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  refine ⟨1000 * Real.pi + 1, by positivity, ?_⟩
  intro α f hα hα1 hso hmem
  have s0 : Work.FTS.NonlinRows.Rl1.SlotData α f
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (Work.Spaces.HkSq α 4 f) :=
    slotData_open_g (α := α) (f := f) hα hso hmem
  have hEnvn : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg f hα.le
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hsqrtX : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
      Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r) ≤ Work.FTS.Nonlin.Xn α f :=
    Real.sqrt_le_sqrt s0.le
  have hrad2 : Real.sqrt 2 ≤ 2 := sqrt_two_le_two
  have hα2X := Work.FTS.NonlinRows.Rl1.alpha_sq_mul_Xn_le_Env (g := f) hα hα1
  have hαX := Work.FTS.NonlinRows.Rl1.alpha_mul_Xn_le_Env (g := f) hα hα1
  have hKbig : (240 : ℝ) * Real.pi ≤ 1000 * Real.pi + 1 := by nlinarith [Real.pi_pos]
  constructor
  · -- `N₄^{gs} = -(1/2)·sin2θ·FK f·∂_θF_*`
    have hp := Work.FTS.NonlinRows.Rl1.profile_data_sq (d := 40 * α ^ 2) (by positivity)
    have hmain := Work.FTS.NonlinRows.Rl1.Fa_le_of_profile
      (N := Work.FTS.Nonlin.N4gs α f)
      (c := fun r => 40 * α ^ 2 * r / (1 + r) ^ 2)
      (M := fun r => 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r))
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (C := 16)
      (by norm_num)
      (fun r hr => by positivity)
      (fun r => by positivity)
      s0.nonneg s0.meas s0.int hp.1 hp.2.1
      (fun r hr => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (s0.nonneg r)]
        norm_num))
      (fun r hr θ hθ => by
        have hFKabs := FK_abs_le_four_sqrt (f := f) hr (s0.sqint r hr) (s0.aesm r hr)
        have h1 := Work.FTS.NonlinRows.Rl1.N4gs_pt (α := α) (g := f) hα hα1 r hr θ hθ
        have h2 : 40 * α ^ 2 * (r / (1 + r) ^ 2) * |Work.Construction.FK f r|
            ≤ 40 * α ^ 2 * (r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)) :=
          mul_le_mul_of_nonneg_left hFKabs (by positivity)
        have h3 : 40 * α ^ 2 * (r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r))
            = (40 * α ^ 2 * r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)) := by ring
        exact h1.trans (h2.trans (le_of_eq h3)))
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [sqrt_sixteen]
    have h40 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2) ≤ 40 * α ^ 2 * 2 :=
      hp.2.2.2.trans (by nlinarith [Real.sqrt_nonneg 2, hrad2, sq_nonneg α])
    have hAB : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2)
        ≤ Work.FTS.Nonlin.Xn α f * (40 * α ^ 2 * 2) :=
      mul_le_mul hsqrtX h40 (Real.sqrt_nonneg _) hX0
    have hstep : Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2))
        ≤ Real.pi / 2 * (4 * Work.FTS.Nonlin.Xn α f * (40 * α ^ 2 * 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc 4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
              Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
            * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
              (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2)
          = 4 * (Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
              * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2)) := by ring
        _ ≤ 4 * (Work.FTS.Nonlin.Xn α f * (40 * α ^ 2 * 2)) :=
            mul_le_mul_of_nonneg_left hAB (by norm_num)
        _ = 4 * Work.FTS.Nonlin.Xn α f * (40 * α ^ 2 * 2) := by ring
    refine hstep.trans ?_
    have h1 : Real.pi / 2 * (4 * Work.FTS.Nonlin.Xn α f * (40 * α ^ 2 * 2))
        = (160 * Real.pi) * (α ^ 2 * Work.FTS.Nonlin.Xn α f) := by ring
    rw [h1]
    calc (160 * Real.pi) * (α ^ 2 * Work.FTS.Nonlin.Xn α f)
        ≤ (160 * Real.pi) * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul_of_nonneg_left hα2X (by positivity)
      _ ≤ (1000 * Real.pi + 1) * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) hEnvn
  · -- `N₅^{gs} = -sin²θ·FK f·F_*`
    have hp := Work.FTS.NonlinRows.Rl1.profile_data_sq (d := 60 * α) (by positivity)
    have hmain := Work.FTS.NonlinRows.Rl1.Fa_le_of_profile
      (N := Work.FTS.Nonlin.N5gs α f)
      (c := fun r => 60 * α * r / (1 + r) ^ 2)
      (M := fun r => 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r))
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (C := 16)
      (by norm_num)
      (fun r hr => by positivity)
      (fun r => by positivity)
      s0.nonneg s0.meas s0.int hp.1 hp.2.1
      (fun r hr => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (s0.nonneg r)]
        norm_num))
      (fun r hr θ hθ => by
        have hFKabs := FK_abs_le_four_sqrt (f := f) hr (s0.sqint r hr) (s0.aesm r hr)
        have h1 := Work.FTS.NonlinRows.Rl1.N5gs_pt (α := α) (g := f) hα hα1 r hr θ hθ
        have h2 : 60 * α * (r / (1 + r) ^ 2) * |Work.Construction.FK f r|
            ≤ 60 * α * (r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)) :=
          mul_le_mul_of_nonneg_left hFKabs (by positivity)
        have h3 : 60 * α * (r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r))
            = (60 * α * r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)) := by ring
        exact h1.trans (h2.trans (le_of_eq h3)))
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [sqrt_sixteen]
    have h60 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2) ≤ 60 * α * 2 :=
      hp.2.2.2.trans (by nlinarith [Real.sqrt_nonneg 2, hrad2, hα.le])
    have hAB : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2)
        ≤ Work.FTS.Nonlin.Xn α f * (60 * α * 2) :=
      mul_le_mul hsqrtX h60 (Real.sqrt_nonneg _) hX0
    have hstep : Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2))
        ≤ Real.pi / 2 * (4 * Work.FTS.Nonlin.Xn α f * (60 * α * 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc 4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
              Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
            * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
              (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2)
          = 4 * (Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
              * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2)) := by ring
        _ ≤ 4 * (Work.FTS.Nonlin.Xn α f * (60 * α * 2)) :=
            mul_le_mul_of_nonneg_left hAB (by norm_num)
        _ = 4 * Work.FTS.Nonlin.Xn α f * (60 * α * 2) := by ring
    refine hstep.trans ?_
    have h1 : Real.pi / 2 * (4 * Work.FTS.Nonlin.Xn α f * (60 * α * 2))
        = (240 * Real.pi) * (α * Work.FTS.Nonlin.Xn α f) := by ring
    rw [h1]
    calc (240 * Real.pi) * (α * Work.FTS.Nonlin.Xn α f)
        ≤ (240 * Real.pi) * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul_of_nonneg_left hαX (by positivity)
      _ ≤ (1000 * Real.pi + 1) * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul_of_nonneg_right hKbig hEnvn

end

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux
