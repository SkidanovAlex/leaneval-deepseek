import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## Elementary domination and the weighted `L¹`–`L²` bound -/

/-- The elementary AM–GM bound `|x| ≤ (x² + 1)/2`. -/
private theorem abs_le_half_sq_add (X : ℝ → ℝ) (s : ℝ) :
    |X s| ≤ (X s ^ 2 + 1) / 2 := by
  have h : 2 * |X s| ≤ X s ^ 2 + 1 := by
    nlinarith [sq_nonneg (|X s| - 1), sq_abs (X s)]
  linarith

/-- **The weighted `L¹`–`L²` bound for the `KJ`-slot.**  For a slice `X` whose `σ_η`-weighted
square is integrable on `Iθ`,

  `∫_{Iθ} KJ ε θ s · |X s| ≤ 3 (ε sMass)⁻¹ · √(π/2) · √(∫_{Iθ} X² σ_η)`.

`KJ` is nonnegative and bounded by `3 (ε sMass)⁻¹` (`KJ_nonneg`, `KJ_le`), so it may be replaced
by that constant; the `L¹`-mass of `|X|` is then estimated by the weighted Cauchy–Schwarz
inequality `integralAbsLeSqrtWeighted`.  The integrability of `|X|` itself — needed for the
monotonicity step, and *not* implied by the weighted hypothesis alone, which knows only about
`X²σ` — comes from the AM–GM domination `|X| ≤ (X² + 1)/2` together with the fact that
`IntegrableOn (X² σ_η) Iθ` forces `IntegrableOn X² Iθ` (`integrableOn_sq_of_integrableOn`). -/
private theorem kj_slice_bound_aux {X : ℝ → ℝ} {ε θ : ℝ} (hε : 0 < ε)
    (hInt : IntegrableOn (fun s : ℝ => X s ^ 2 * σθ s) Iθ) :
    (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X s|)
      ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
          (Real.sqrt (Real.pi / 2) * Real.sqrt (∫ s in Iθ, X s ^ 2 * σθ s)) := by
  have hsm : 0 < Work.FTS.EllSol.PkgK5.K5c.sMass := Work.FTS.EllSol.PkgK5.K5c.sMass_pos
  have hCnn : 0 ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ := by
    have h : 0 < (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ :=
      inv_pos.mpr (mul_pos hε hsm)
    linarith
  -- ## integrability of `|X|` on `Iθ`
  have hSq : IntegrableOn (fun s : ℝ => X s ^ 2) Iθ :=
    Work.FTS.EllSol.EllPkgAux.integrableOn_sq_of_integrableOn hInt
  have hAbsInt : IntegrableOn (fun s : ℝ => |X s|) Iθ := by
    have haesm : AEStronglyMeasurable (fun s : ℝ => |X s|) (volume.restrict Iθ) :=
      (Real.continuous_sqrt.comp_aestronglyMeasurable
        (Work.FTS.EllSol.EllPkgAux.aesm_sq_of_integrableOn hInt)).congr
        (Eventually.of_forall (fun s => Real.sqrt_sq_eq_abs (X s)))
    have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Iθ :=
      MeasureTheory.integrableOn_const
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    have hhalf : Integrable (fun s : ℝ => (X s ^ 2 + 1) / 2) (volume.restrict Iθ) :=
      (hSq.add h1).div_const 2
    refine Work.FTS.EllSol.EllPkgAux.integrable_of_le haesm
      (Eventually.of_forall (fun s => abs_nonneg (X s))) hhalf
      (Eventually.of_forall (fun s => by positivity)) ?_
    exact Work.FTS.EllSol.EllPkgAux.ae_le_of_forall_mem_Ioo
      (fun s _ => abs_le_half_sq_add X s)
  -- ## replacing `KJ` by its bound
  have hmono : (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X s|)
      ≤ ∫ s in Iθ, (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * |X s| :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall (fun s =>
        mul_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε θ s) (abs_nonneg (X s))))
      (hAbsInt.const_mul _)
      (Eventually.of_forall (fun s =>
        mul_le_mul_of_nonneg_right (Work.FTS.EllSol.EllPkgAux.KJ_le hε θ s) (abs_nonneg (X s))))
  rw [MeasureTheory.integral_const_mul] at hmono
  -- ## the weighted Cauchy–Schwarz bound for the `L¹`-mass of the slice
  have hA2 : IntegrableOn (fun s : ℝ => X s ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2)) := by
    simpa only [Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta, Work.Spaces.eta] using hInt
  have hcs : (∫ s in Iθ, |X s|)
      ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (∫ s in Iθ, X s ^ 2 * σθ s) := by
    simpa only [Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta, Work.Spaces.eta] using
      Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted (h := X) hA2
  calc (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X s|)
      ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ * (∫ s in Iθ, |X s|) := hmono
    _ ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
          (Real.sqrt (Real.pi / 2) * Real.sqrt (∫ s in Iθ, X s ^ 2 * σθ s)) :=
        mul_le_mul_of_nonneg_left hcs hCnn

/-- Angular slice bound for the `D_z`-slot: for a datum `G` that is `C^∞` on the open quadrant with
honestly slice-integrable `D_z`-weighted square, the three-image-kernel weighted `L¹` mass of the
`D_z`-slice on `Iθ` is bounded by the Cauchy–Schwarz bound in terms of the honest functional
`dIntS G w = w(w)² ∫_{Iθ} (D_zG w θ)² sin(2θ)^{-η}`:

  `∫_{Iθ} KJ ε θ s · |D_zG w s| ≤ 3 (ε sMass)⁻¹ · √(π/2) · √(dIntS G w) / w(w)`.

Route: `KJ ε θ s ≤ 3 (ε sMass)⁻¹` pointwise (`Work.FTS.EllSol.EllPkgAux.KJ_le`), then the
weighted Cauchy–Schwarz inequality `Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted`
applied to the slice `s ↦ D_zG w s` (whose `σ_η`-weighted square is `L¹(Iθ)` by the third conjunct
of `SliceHonestOpen G`, after stripping the constant `w(w)²`), and finally
`√(dIntS G w / w(w)²) = √(dIntS G w) / w(w)` since `0 < w(w)`.  The integrability of
`|D_zG w ·|` on `Iθ` needed for the pointwise comparison comes from
`|h| = √(h²) ≤ 1 + h² w(w)² σ_η` a.e. on `Iθ`. -/
theorem slice_kj_bound (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    (hhon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) (ε θ : ℝ) (hε : 0 < ε) :
    ∀ w : ℝ, 0 < w →
      (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |Work.Spaces.Dz G w s|)
        ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
            (Real.sqrt (Real.pi / 2) *
              (Real.sqrt (Work.EllipticEst.Core.dIntS G w) / Work.Spaces.w w)) := by
  intro w hw
  have hww : 0 < Work.Spaces.w w := Work.FTS.EllSol.EllPkgAux.w_pos hw
  have hwwne : Work.Spaces.w w ≠ 0 := ne_of_gt hww
  have hW2ne : (Work.Spaces.w w) ^ 2 ≠ 0 := pow_ne_zero 2 hwwne
  -- ## honesty of the `D_z`-slice, with the constant radial weight stripped off
  have hInt : IntegrableOn (fun s : ℝ => Work.Spaces.Dz G w s ^ 2 * σθ s) Iθ := by
    have h0 := (hhon.2.2 w hw).const_mul (((Work.Spaces.w w) ^ 2)⁻¹)
    refine h0.congr (Filter.Eventually.of_forall (fun s => ?_))
    show ((Work.Spaces.w w) ^ 2)⁻¹
        * (Work.Spaces.Dz G w s ^ 2 * (Work.Spaces.w w) ^ 2 * σθ s)
      = Work.Spaces.Dz G w s ^ 2 * σθ s
    rw [show Work.Spaces.Dz G w s ^ 2 * (Work.Spaces.w w) ^ 2 * σθ s
        = (Work.Spaces.w w) ^ 2 * (Work.Spaces.Dz G w s ^ 2 * σθ s) from by ring]
    rw [← mul_assoc, inv_mul_cancel₀ hW2ne, one_mul]
  -- ## the abstract weighted bound
  have haux := kj_slice_bound_aux (X := fun s : ℝ => Work.Spaces.Dz G w s) (θ := θ) hε hInt
  -- ## `√(∫ ... ) = √(dIntS G w) / w w`
  have hsqrt : Real.sqrt (∫ s in Iθ, Work.Spaces.Dz G w s ^ 2 * σθ s)
      = Real.sqrt (Work.EllipticEst.Core.dIntS G w) / Work.Spaces.w w := by
    rw [show Work.EllipticEst.Core.dIntS G w
        = (Work.Spaces.w w) ^ 2 * (∫ s in Iθ, Work.Spaces.Dz G w s ^ 2 * σθ s) from rfl,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hww]
    rw [eq_div_iff hwwne]
    ring
  calc (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |Work.Spaces.Dz G w s|)
      ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
          (Real.sqrt (Real.pi / 2) *
            Real.sqrt (∫ s in Iθ, Work.Spaces.Dz G w s ^ 2 * σθ s)) := haux
    _ = 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
          (Real.sqrt (Real.pi / 2) *
            (Real.sqrt (Work.EllipticEst.Core.dIntS G w) / Work.Spaces.w w)) := by
        rw [hsqrt]

end Work.FTS.EllSol.EllPkgAux.MollDom
