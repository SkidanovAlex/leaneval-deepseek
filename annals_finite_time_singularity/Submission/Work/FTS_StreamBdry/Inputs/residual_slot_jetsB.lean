import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.StrongPersist.SP6.WlInf6OfFlatW
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS_RegExport.RXR5L.mubarData
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Decay3_leaf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps/E4R3/Decay3_leaf.lean` — the corrected decay chapter `DecayChapter3`

`DecayChapter3 Ce Cs C₀ ρ` requires, for all `α'` below a threshold, all data in `E4Data` and all
`T > 0`, a **single** majorant `Maj` (chosen before the solution) satisfying `AprioriDecayB`:

* `IntegrableOn (Maj · / ·) (0,∞)`;
* for every `ε ∈ (0,1]`, every solution `g` of the projected scheme in the small ball
  `Xn α' (slice (JfamP ρ ε g) τ) ≤ C₀α'²` and every `τ ∈ [0,T]`:
  * `SlotMaj 1 Maj (slice (JfamP ρ ε g) τ)` — the slots of order `≤ 1` of the projected slice,
  * the three elliptic blocks are `≤ 3` on the open quadrant.

The majorant is the explicit

    `Maj z = min 1 (√Ct · C₀α'² · z√z/(1+z)²)`

with `Ct` the constant of the tail bound `Decay3Aux.slot_tail` (uniform in the datum); `Ct` is
`5K` with `K` the constant of the angular-sup bound `RXT.Slots.v2_theta_sup_uniform`.  The slot
bound is `Decay3Aux.slotMaj_of_ball`'s argument with the datum replaced by a general `f`, and the
block bound is `Decay3Aux.blocks_le_three_fixed` fed with the explicit constant
`Cpt α = √(((4/π) + 200/(γ-1))·40)` of `Decay3Aux.slot_crude` (so the chapter threshold `α` can be
chosen as `min 1 (min (1/(448C₀+1)) (1/(4(448Ce⁺C₀ + Cs⁺)+1)))`, using
`Cpt α · α ≤ 448√α`).

Everything here is `sorry`-free.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- `(Cpt α)² · α ≤ 200000` for `α ∈ (0,1]`, where `Cpt α = √(((4/π) + 200/(γ-1))·40)` is the
constant of the crude pointwise bound. -/
private theorem Cpt_sq_mul_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)) ^ 2 * α
      ≤ 200000 := by
  have hgam : Work.Spaces.gam α - 1 = α / 10 := by
    rw [Work.Spaces.gam]; ring
  have hA : 0 ≤ ((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40 := by
    rw [hgam]; positivity
  rw [Real.sq_sqrt hA, hgam]
  have h1 : 100 / (α / 10) = 1000 / α := by
    field_simp
    ring
  rw [h1]
  have hexp : ((4 / Real.pi) + 2 * (1000 / α)) * 40 * α = (4 / Real.pi) * 40 * α + 80000 := by
    have hα0 : α ≠ 0 := ne_of_gt hα
    field_simp
    ring
  rw [hexp]
  have hp : 4 / Real.pi ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  have h3 : (4 / Real.pi) * 40 * α ≤ 80 := by nlinarith [hp, hα.le, hα1]
  linarith

/-- `Cpt α · α ≤ 448√α` for `α ∈ (0,1]`. -/
private theorem Cpt_mul_alpha_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40) * α
      ≤ 448 * Real.sqrt α := by
  have hA : 0 ≤ ((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40 := by
    have hgam : Work.Spaces.gam α - 1 = α / 10 := by rw [Work.Spaces.gam]; ring
    rw [hgam]; positivity
  have hCA : 0 ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40) * α :=
    mul_nonneg (Real.sqrt_nonneg _) hα.le
  have hle : (Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40) * α) ^ 2
      ≤ 200000 * α := by
    calc (Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40) * α) ^ 2
        = ((Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)) ^ 2 * α) * α :=
          by ring
      _ ≤ 200000 * α := mul_le_mul_of_nonneg_right (Cpt_sq_mul_le hα hα1) hα.le
  calc Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40) * α
      = Real.sqrt ((Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40) * α) ^ 2) :=
        (Real.sqrt_sq hCA).symm
    _ ≤ Real.sqrt (200000 * α) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt 200000 * Real.sqrt α := Real.sqrt_mul (by norm_num) α
    _ ≤ 448 * Real.sqrt α := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg α)
        rw [show (448 : ℝ) = Real.sqrt (448 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num)

theorem Decay3_leaf {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → Work.FTS.StrongEps.EpsE4Thr.E4R3.DecayChapter3 Ce Cs C₀ ρ := by
  classical
  refine ⟨1, ?_⟩
  intro C₀ hC₀
  have hC₀0 : (0 : ℝ) ≤ C₀ := le_trans zero_le_one hC₀
  set Ce' : ℝ := max Ce 0 with hCe'def
  set Cs' : ℝ := max Cs 0 with hCs'def
  have hCe'0 : 0 ≤ Ce' := le_max_right _ _
  have hCs'0 : 0 ≤ Cs' := le_max_right _ _
  refine ⟨min 1 (min (1 / (448 * C₀ + 1)) (1 / (4 * (448 * Ce' * C₀ + Cs') + 1))),
    lt_min one_pos (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_⟩
  intro α' hα'
  have hα'0 : 0 < α' := hα'.1
  have hα'A : α' ≤ min 1 (min (1 / (448 * C₀ + 1)) (1 / (4 * (448 * Ce' * C₀ + Cs') + 1))) :=
    hα'.2
  have hα'1 : α' ≤ 1 := le_trans hα'A (min_le_left _ _)
  have hα'a : α' ≤ 1 / (448 * C₀ + 1) :=
    le_trans hα'A (le_trans (min_le_right _ _) (min_le_left _ _))
  have hα'b : α' ≤ 1 / (4 * (448 * Ce' * C₀ + Cs') + 1) :=
    le_trans hα'A (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the two smallness estimates
  have hCptmu : Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40) * α'
      ≤ 448 * Real.sqrt α' := Cpt_mul_alpha_le hα'0 hα'1
  have hcap : Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
      * (C₀ * α' ^ 2) ≤ 1 := by
    have hsqrt1 : Real.sqrt α' ≤ 1 := Real.sqrt_le_one.mpr hα'1
    have hstep : Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
        * (C₀ * α' ^ 2) ≤ 448 * C₀ * α' := by
      calc Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40) * (C₀ * α' ^ 2)
          = (C₀ * α') * (Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
              * α') := by ring
        _ ≤ (C₀ * α') * (448 * Real.sqrt α') := mul_le_mul_of_nonneg_left hCptmu (by positivity)
        _ ≤ 448 * C₀ * α' := by
            have h1 : 448 * Real.sqrt α' ≤ 448 * 1 :=
              mul_le_mul_of_nonneg_left hsqrt1 (by norm_num)
            have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ C₀ * α')
            linarith [h2]
    have hfin : 448 * C₀ * α' ≤ 1 := by
      have hden : 0 < 448 * C₀ + 1 := by linarith
      calc 448 * C₀ * α' ≤ 448 * C₀ * (1 / (448 * C₀ + 1)) :=
            mul_le_mul_of_nonneg_left hα'a (by positivity)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one hden]
            linarith
    exact le_trans hstep hfin
  have hblk : Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
      * (Ce' * (C₀ * α' ^ 2)) + Cs' * α' ≤ 1 / 4 := by
    have hsqrt1 : Real.sqrt α' ≤ 1 := Real.sqrt_le_one.mpr hα'1
    have hstep : Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
        * (Ce' * (C₀ * α' ^ 2)) ≤ 448 * Ce' * C₀ * α' := by
      calc Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
            * (Ce' * (C₀ * α' ^ 2))
          = (Ce' * C₀ * α') * (Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
              * α') := by ring
        _ ≤ (Ce' * C₀ * α') * (448 * Real.sqrt α') :=
            mul_le_mul_of_nonneg_left hCptmu (by positivity)
        _ ≤ 448 * Ce' * C₀ * α' := by
            have h1 : 448 * Real.sqrt α' ≤ 448 * 1 :=
              mul_le_mul_of_nonneg_left hsqrt1 (by norm_num)
            have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ Ce' * C₀ * α')
            linarith [h2]
    have hX : 0 ≤ 448 * Ce' * C₀ + Cs' := by positivity
    have hden : 0 < 4 * (448 * Ce' * C₀ + Cs') + 1 := by linarith
    have hfin : (448 * Ce' * C₀ + Cs') * α' ≤ 1 / 4 := by
      calc (448 * Ce' * C₀ + Cs') * α'
          ≤ (448 * Ce' * C₀ + Cs') * (1 / (4 * (448 * Ce' * C₀ + Cs') + 1)) :=
            mul_le_mul_of_nonneg_left hα'b hX
        _ ≤ 1 / 4 := by
            rw [mul_one_div, div_le_iff₀ hden]
            linarith
    have hsplit : 448 * Ce' * C₀ * α' + Cs' * α' = (448 * Ce' * C₀ + Cs') * α' := by ring
    linarith [hstep, hfin, hsplit]
  intro K Φs E g₀ hdata T hT
  obtain ⟨hK0, hvan, hEll, hstar, hml, hd, h4g, h6g⟩ := hdata
  -- the tail constant and the majorant
  obtain ⟨Ct, hCt0, hCt⟩ := slot_tail (α := α') hα'0 hα'1
  set D : ℝ := Real.sqrt Ct * (C₀ * α' ^ 2) with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  set P : ℝ → ℝ := fun z => z * Real.sqrt z / (1 + z) ^ 2 with hPdef
  have hPnonneg : ∀ z : ℝ, 0 ≤ P z := by
    intro z
    by_cases hz : 0 ≤ z
    · rw [hPdef]
      exact div_nonneg (mul_nonneg hz (Real.sqrt_nonneg z)) (sq_nonneg _)
    · have hs : Real.sqrt z = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hz)
      rw [hPdef]
      show (0 : ℝ) ≤ z * Real.sqrt z / (1 + z) ^ 2
      rw [hs]
      simp
  have hsqrt_id : ∀ z : ℝ, 0 < z → Real.sqrt (z ^ 3 / (1 + z) ^ 4) = P z := by
    intro z hz
    rw [hPdef]
    have h1 : Real.sqrt (z ^ 3) = z * Real.sqrt z := by
      rw [show z ^ 3 = z ^ 2 * z by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hz.le]
    have h2 : Real.sqrt ((1 + z) ^ 4) = (1 + z) ^ 2 := by
      rw [show (1 + z) ^ 4 = ((1 + z) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [Real.sqrt_div (by positivity), h1, h2]
  set Maj : ℝ → ℝ := fun z => min 1 (D * P z) with hMajdef
  have hMaj0 : ∀ z, 0 ≤ Maj z := fun z => le_min zero_le_one (mul_nonneg hD0 (hPnonneg z))
  have hMaj1 : ∀ z, Maj z ≤ 1 := fun z => min_le_left _ _
  have hcontP : ContinuousOn (fun z : ℝ => D * P z) (Set.Ioi 0) := by
    rw [hPdef]
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_id.mul Real.continuous_sqrt.continuousOn
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro z hz
      have h1z : (0 : ℝ) < 1 + z := by linarith [show (0 : ℝ) < z from hz]
      exact pow_ne_zero 2 (ne_of_gt h1z)
  have hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) := by
    refine (Work.FTS.StrongEps.E4R3.Decay3Aux.integrableOn_majProfile D).mono' ?_ ?_
    · have hM : ContinuousOn (fun z : ℝ => min (1 : ℝ) (D * P z)) (Set.Ioi 0) :=
        fun z hz => continuousWithinAt_const.min (hcontP z hz)
      have hcont : ContinuousOn (fun z : ℝ => Maj z / z) (Set.Ioi 0) := by
        rw [hMajdef]
        exact hM.div continuousOn_id (fun z hz => ne_of_gt hz)
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      rw [Real.norm_of_nonneg (div_nonneg (hMaj0 z) hz.le)]
      have h1 : Maj z ≤ D * P z := by
        change min 1 (D * P z) ≤ D * P z
        exact min_le_right _ _
      have h2 : D * P z / z = D * (Real.sqrt z / (1 + z) ^ 2) := by
        rw [hPdef, div_eq_iff (ne_of_gt hz)]
        ring
      calc Maj z / z ≤ D * P z / z := div_le_div_of_nonneg_right h1 hz.le
        _ = D * (Real.sqrt z / (1 + z) ^ 2) := h2
  refine ⟨Maj, hMajint, ?_⟩
  intro ε hε g hsol hreg hball τ hτ
  have hdP : Work.FTS.StrongEps.EpsDatumP α' ρ ε (slice g τ) := hreg.2 τ hτ
  have hCf : Work.FTS.ClassC.ClassC α' (slice (JfamP ρ ε g) τ) := hdP.2.2
  have hf_ball : Work.FTS.Nonlin.Xn α' (slice (JfamP ρ ε g) τ) ≤ C₀ * α' ^ 2 := hball τ hτ
  have hf_off : ∀ z θ : ℝ, θ ∉ Set.Ioo 0 (Real.pi / 2) → slice (JfamP ρ ε g) τ z θ = 0 := by
    intro z θ hθ
    rw [Work.FTS.StrongEps.slice_JfamP]
    exact Work.FTS.StrongEps.EpsE4Thr.Pz_Jeps_eq_zero_of_theta hθ
  have hf_4 : ContDiffOn ℝ 4 (Function.uncurry (slice (JfamP ρ ε g) τ))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hCf.reg 4
  have hf_mem : Work.Spaces.HkMem α' 4 (slice (JfamP ρ ε g) τ) :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α' (by norm_num) hCf.reg hCf.mem
  -- the slot clause
  have hsl : Work.FTS.StrongEps.SlotMaj 1 Maj (slice (JfamP ρ ε g) τ) := by
    refine Work.FTS.StrongEps.EpsE4Thr.slotMaj_of_offquadrant (k := 1) hMaj0 hf_off ?_
    intro z hz θ hθ0 hθ1 j i hji
    have hPz0 : 0 ≤ P z := hPnonneg z
    by_cases hcase : D * P z ≤ 1
    · have hMajeq : Maj z = D * P z := by
        change min 1 (D * P z) = D * P z
        exact min_eq_right hcase
      rw [hMajeq]
      have hsq := hCt (slice (JfamP ρ ε g) τ) hf_4 hf_mem j i hji z θ hz hθ0 hθ1
      have h1 : |Work.Spaces.mixed j i (slice (JfamP ρ ε g) τ) z θ|
          ≤ Real.sqrt (Ct * Work.Spaces.HkSq α' 4 (slice (JfamP ρ ε g) τ)
              * (z ^ 3 / (1 + z) ^ 4)) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hsq
      have h2 : Real.sqrt (Ct * Work.Spaces.HkSq α' 4 (slice (JfamP ρ ε g) τ)
            * (z ^ 3 / (1 + z) ^ 4))
          = Real.sqrt Ct * Work.Spaces.HkNorm α' 4 (slice (JfamP ρ ε g) τ) * P z := by
        rw [Real.sqrt_mul (mul_nonneg hCt0
            (Work.Spaces.HkSq_nonneg α' 4 (slice (JfamP ρ ε g) τ))),
          Real.sqrt_mul hCt0, hsqrt_id z hz]
        rfl
      have h3 : Real.sqrt Ct * Work.Spaces.HkNorm α' 4 (slice (JfamP ρ ε g) τ) * P z
          ≤ D * P z := by
        rw [hDdef]
        have h := mul_le_mul_of_nonneg_right hf_ball hPz0
        calc Real.sqrt Ct * Work.Spaces.HkNorm α' 4 (slice (JfamP ρ ε g) τ) * P z
            = Real.sqrt Ct * (Work.Spaces.HkNorm α' 4 (slice (JfamP ρ ε g) τ) * P z) := by ring
          _ ≤ Real.sqrt Ct * ((C₀ * α' ^ 2) * P z) :=
              mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg Ct)
          _ = Real.sqrt Ct * (C₀ * α' ^ 2) * P z := by ring
      calc |Work.Spaces.mixed j i (slice (JfamP ρ ε g) τ) z θ|
          ≤ Real.sqrt (Ct * Work.Spaces.HkSq α' 4 (slice (JfamP ρ ε g) τ)
              * (z ^ 3 / (1 + z) ^ 4)) := h1
        _ = Real.sqrt Ct * Work.Spaces.HkNorm α' 4 (slice (JfamP ρ ε g) τ) * P z := h2
        _ ≤ D * P z := h3
    · have hcase' : 1 < D * P z := lt_of_not_ge hcase
      have hMajeq : Maj z = 1 := by
        change min 1 (D * P z) = 1
        exact min_eq_left hcase'.le
      rw [hMajeq]
      have hcr := slot_crude (α := α') hα'0 hα'1 (f := slice (JfamP ρ ε g) τ) (j := j) (i := i)
        (by omega) hz hθ0 hθ1 hf_4 hf_mem
      calc |Work.Spaces.mixed j i (slice (JfamP ρ ε g) τ) z θ|
          ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
              * min z 1 * Work.Spaces.HkNorm α' 4 (slice (JfamP ρ ε g) τ) := hcr
        _ ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
              * 1 * (C₀ * α' ^ 2) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (min_le_right z 1) (Real.sqrt_nonneg _))
              hf_ball (Work.Spaces.HkNorm_nonneg α' 4 (slice (JfamP ρ ε g) τ)) (by positivity)
        _ = Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
              * (C₀ * α' ^ 2) := by ring
        _ ≤ 1 := hcap
  -- the block clause
  have hB : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.Construction.Rop α' (Work.Construction.PhiTil α' (slice (JfamP ρ ε g) τ)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3 ∧
      |Work.Construction.Uop α' (Work.Construction.PhiTil α' (slice (JfamP ρ ε g) τ)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ
          / Work.Construction.s2 θ| ≤ 3 ∧
      |Work.Construction.Vop (Work.Construction.PhiTil α' (slice (JfamP ρ ε g) τ)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3 := by
    intro z θ hz hθ
    have hpt : ∀ g' : Fn, ContDiffOn ℝ 4 (Function.uncurry g') Work.FTS.EllipticEst.Q0 →
        Work.Spaces.HkMem α' 4 g' → ∀ b a : ℕ, a + b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' →
          θ' < Real.pi / 2 →
          |Work.Spaces.mixed b a g' z' θ'|
            ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α' - 1))) * 40)
              * min z' 1 * Work.Spaces.HkNorm α' 4 g' :=
      fun g' h4' hmem' b a hba z' θ' hz' hθ0' hθ1' =>
        slot_crude (α := α') hα'0 hα'1 (f := g') (j := b) (i := a) (by omega) hz' hθ0' hθ1' h4' hmem'
    have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α' u →
        Work.FTS.VocabO.EllPkgGo α' Ce' u (E u) ∧ Work.FTS.ClassC.EllPkgK α' 6 Ce' u (E u) :=
      fun u hu => Work.FTS.StrongEps.E4R3.Decay3Aux.ellPkg_mono (le_max_left Ce 0) (hEll u hu)
    have hstar' : Work.FTS.VocabO2.StarPkgo2 α' Cs' Φs :=
      Work.FTS.StrongEps.E4R3.Decay3Aux.starPkg_mono hα'0 (le_max_left Cs 0) hstar
    exact Work.FTS.StrongEps.E4R3.Decay3Aux.blocks_le_three_fixed hα'0 hα'1 hCe'0 hCs'0 hC₀0
      (Real.sqrt_nonneg _) hpt hblk hCf hf_ball hEll' hstar' z θ hz hθ
  exact Work.FTS.StrongEps.EpsE4Thr.EpsDecay_of_Maj (α := α') (ρ := ρ) (Φs := Φs) (E := E)
    (ε := ε) (τ := τ) (g := g) (Maj := Maj) hMaj0 hMaj1 hMajint hsl hB

end Work.FTS.StrongEps.E4R3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Flow5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Flow5.lean` — the flow-regularity class `EpsFlowP` and the E4 chapters over it

curric-46 install 2026-10-12 of `cbc/fts_regularity_interface.{md,lean}` §§1–5, with the review
`cbc/fts_regularity_interface_REVIEW.md` fixes (F1: imports `Apriori4Defs`, NOT `Apriori4`, so the
restated halves `E4R3/Sixth5.lean`/`Fourth5.lean` can import this file without a cycle; F4 wording).

Everything here is PROVED (`[propext, Classical.choice, Quot.sound]`): `EpsFlowP.mono/glue`,
`xn6_continuousOn_of_flow` (L-B `hcont`), `rawE6_hasDerivWithinAt_of_flow`/`rawE6_deriv_of_flow`
(S4), `rawSlice_L12_zero_of_flow` (F6), `aprioriPF_of_halvesBF`, `aprioriChapter5_of_halves`,
`exists_sol_of_localStepF_aprioriF`, `EpsUniformMem_of_partsF`, `EpsE4R5_of_chapters` (⟹ the
unchanged `E4R4.EpsE4R4Stmt`).  LEAF-C (level-4 product rule) is `E4R3/Flow5Leaves/IP4Flow.lean`;
the producer side (LEAF-A + the local step) is `E4R3/Flow5Local.lean`.

`E4R3/Apriori4Leaves/RawE6Deriv`, `RawSliceL12Zero`, `HalvesB` are SUPERSEDED by the `*_of_flow`
lemmas and `aprioriPF_of_halvesBF` (left in place, off the cone).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6 concat)
open Work.FTS.VocabO (HQo)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr
open Work.FTS.StrongEps.EpsE4Thr.E4R4 (rawE6 IP6o)

set_option autoImplicit false
set_option linter.unusedVariables false
/-! ## 1. Seminorm calculus vocabulary -/

/-- the remainder of a first-order expansion of a fake-time curve of profiles. -/
def rem (u : ℝ → Fn) (v : Fn) (s τ : ℝ) : Fn :=
  fun z θ => u s z θ - u τ z θ - (s - τ) * v z θ

/-- **`ℋᵏ`-differentiability within `S` at `τ` with derivative `v`** (junk-proof: the remainder is
required to be honest, `HQo`, before its norm is read). -/
def HkDerivWithin (α : ℝ) (k : ℕ) (u : ℝ → Fn) (v : Fn) (S : Set ℝ) (τ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, |s - τ| < δ →
    HQo α k (rem u v s τ) ∧ Work.Spaces.HkNorm α k (rem u v s τ) ≤ η * |s - τ|

/-- **`ℋᵏ`-continuity within `S` at `τ`** (junk-proof). -/
def HkContWithin (α : ℝ) (k : ℕ) (u : ℝ → Fn) (S : Set ℝ) (τ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, |s - τ| < δ →
    HQo α k (fun z θ => u s z θ - u τ z θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => u s z θ - u τ z θ) ≤ η

/-! ## 2. The flow-regularity class -/

/-- **`EpsFlowP` — what the Volterra–Picard construction produces at fixed `ε`, and what the
a-priori chapter consumes.**  All constants are existential (they may depend on `ε`, on the
solution and on `T`): the a-priori chapter uses this class only *qualitatively* (to differentiate
energies and to run first-crossing arguments); every `ε`-uniform bound still comes from the energy
estimates.

* `rhs`     — the scheme's right-hand side is an honest `ℋ⁶` profile at every fake time;
* `rhsBdd`  — with a bound uniform on `[0,T]`;
* `rhsCont` — and depends `ℋ⁶`-continuously on the fake time;
* `deriv`   — the flow is `ℋ⁶`-differentiable, with derivative the right-hand side
              (the `ℋ⁶`-valued form of `IsEpsSolP`);
* `wp`      — the un-projected mollified pre-right-hand side is honest at level 4 (the `hWm`
              input of the proved `rawSlice_L12_zero_of_uniform`). -/
structure EpsFlowP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) :
    Prop where
  rhs : ∀ τ ∈ Icc 0 T, HQo α 6 (epsRHSP α ρ ε Φs E g τ)
  rhsBdd : ∃ B : ℝ, ∀ τ ∈ Icc 0 T, Work.Spaces.HkNorm α 6 (epsRHSP α ρ ε Φs E g τ) ≤ B
  rhsCont : ∀ τ ∈ Icc 0 T, HkContWithin α 6 (epsRHSP α ρ ε Φs E g) (Icc 0 T) τ
  deriv : ∀ τ ∈ Icc 0 T, HkDerivWithin α 6 (slice g) (epsRHSP α ρ ε Φs E g τ) (Icc 0 T) τ
  wp : ∀ τ ∈ Icc 0 T, Work.Spaces.HkMem α 4 (Jeps ρ ε (epsWP α ρ ε Φs E g τ))

/-- `EpsFlowP` is monotone in the horizon (PROVED). -/
theorem EpsFlowP.mono {α ε T T' : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (h : EpsFlowP α ρ ε T' Φs E g) (hTT' : T ≤ T') : EpsFlowP α ρ ε T Φs E g := by
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 T' := Icc_subset_Icc le_rfl hTT'
  refine ⟨fun τ hτ => h.rhs τ (hsub hτ), ?_, ?_, ?_, fun τ hτ => h.wp τ (hsub hτ)⟩
  · obtain ⟨B, hB⟩ := h.rhsBdd
    exact ⟨B, fun τ hτ => hB τ (hsub hτ)⟩
  · intro τ hτ η hη
    obtain ⟨δ, hδ, hs⟩ := h.rhsCont τ (hsub hτ) η hη
    exact ⟨δ, hδ, fun s hs' hd => hs s (hsub hs') hd⟩
  · intro τ hτ η hη
    obtain ⟨δ, hδ, hs⟩ := h.deriv τ (hsub hτ) η hη
    exact ⟨δ, hδ, fun s hs' hd => hs s (hsub hs') hd⟩

/-- **(G) `EpsFlowP` glues across a restart** — the `EpsFlowP` twin of `StrongEpsP.RegGlueP`.
The junction datum is the *full* slice (`∀ z θ`, as `IsEpsSolP.init` provides), so
`epsRHSP_congr` identifies the two right-hand sides at the junction.  PROVED. -/
theorem EpsFlowP.glue {α ε t δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {G H : Fam}
    (ht : 0 ≤ t) (hδ : 0 < δ)
    (hGr : EpsRegP α ρ ε t G) (hHr : EpsRegP α ρ ε δ H)
    (hG : EpsFlowP α ρ ε t Φs E G) (hH : EpsFlowP α ρ ε δ Φs E H)
    (hval : ∀ z θ, G z θ t = H z θ 0) :
    EpsFlowP α ρ ε (t + δ) Φs E (concat G (shiftFam H t) t) := by
  set F : Fam := concat G (shiftFam H t) t with hFdef
  have hsG : ∀ s, s ≤ t → slice F s = slice G s := fun s hs =>
    Work.FTS.StrongGlobal.slice_concat_of_le hs
  have hsH : ∀ s, t ≤ s → slice F s = slice H (s - t) := by
    intro s hs
    rcases eq_or_lt_of_le hs with heq | hlt
    · rw [← heq, hsG t le_rfl, sub_self]
      funext z θ; exact hval z θ
    · rw [Work.FTS.StrongGlobal.slice_concat_of_gt hlt]; rfl
  have hrG : ∀ s, s ≤ t → epsRHSP α ρ ε Φs E F s = epsRHSP α ρ ε Φs E G s := fun s hs =>
    Work.FTS.StrongEps.StrongEpsP.epsRHSP_congr (hsG s hs)
  have hrH : ∀ s, t ≤ s → epsRHSP α ρ ε Φs E F s = epsRHSP α ρ ε Φs E H (s - t) := fun s hs =>
    Work.FTS.StrongEps.StrongEpsP.epsRHSP_congr (hsH s hs)
  have mG : ∀ s ∈ Icc 0 (t + δ), s ≤ t → s ∈ Icc 0 t := fun s hs h => ⟨hs.1, h⟩
  have mH : ∀ s ∈ Icc 0 (t + δ), t ≤ s → s - t ∈ Icc 0 δ := fun s hs h =>
    ⟨by linarith, by linarith [hs.2]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    rcases le_total τ t with h | h
    · rw [hrG τ h]; exact hG.rhs τ (mG τ hτ h)
    · rw [hrH τ h]; exact hH.rhs (τ - t) (mH τ hτ h)
  · obtain ⟨BG, hBG⟩ := hG.rhsBdd
    obtain ⟨BH, hBH⟩ := hH.rhsBdd
    refine ⟨max BG BH, fun τ hτ => ?_⟩
    rcases le_total τ t with h | h
    · rw [hrG τ h]; exact le_trans (hBG τ (mG τ hτ h)) (le_max_left _ _)
    · rw [hrH τ h]; exact le_trans (hBH (τ - t) (mH τ hτ h)) (le_max_right _ _)
  · -- continuity of the right-hand side
    intro τ hτ η hη
    rcases lt_trichotomy τ t with h | h | h
    · obtain ⟨d, hd, hc⟩ := hG.rhsCont τ (mG τ hτ h.le) η hη
      refine ⟨min d (t - τ), lt_min hd (by linarith), fun s hs hst => ?_⟩
      have hst' : |s - τ| < d := lt_of_lt_of_le hst (min_le_left _ _)
      have hsl : s < t := by
        have := lt_of_lt_of_le hst (min_le_right _ _)
        linarith [le_abs_self (s - τ)]
      rw [hrG s hsl.le, hrG τ h.le]
      exact hc s (mG s hs hsl.le) hst'
    · subst h
      obtain ⟨dG, hdG, hcG⟩ := hG.rhsCont τ (mG τ hτ le_rfl) η hη
      obtain ⟨dH, hdH, hcH⟩ := hH.rhsCont 0 ⟨le_rfl, hδ.le⟩ η hη
      refine ⟨min dG dH, lt_min hdG hdH, fun s hs hst => ?_⟩
      rcases le_total s τ with h' | h'
      · rw [hrG s h', hrG τ le_rfl]
        exact hcG s (mG s hs h') (lt_of_lt_of_le hst (min_le_left _ _))
      · rw [hrH s h', hrH τ le_rfl, sub_self]
        have := hcH (s - τ) (mH s hs h') (by
          rw [sub_zero]; exact lt_of_lt_of_le hst (min_le_right _ _))
        exact this
    · obtain ⟨d, hd, hc⟩ := hH.rhsCont (τ - t) (mH τ hτ h.le) η hη
      refine ⟨min d (τ - t), lt_min hd (by linarith), fun s hs hst => ?_⟩
      have hst' : |s - τ| < d := lt_of_lt_of_le hst (min_le_left _ _)
      have hsl : t < s := by
        have := lt_of_lt_of_le hst (min_le_right _ _)
        linarith [neg_abs_le (s - τ)]
      rw [hrH s hsl.le, hrH τ h.le]
      exact hc (s - t) (mH s hs hsl.le) (by rw [show s - t - (τ - t) = s - τ by ring]; exact hst')
  · -- differentiability of the flow
    have remG : ∀ s τ, s ≤ t → τ ≤ t → ∀ v : Fn, rem (slice F) v s τ = rem (slice G) v s τ := by
      intro s τ hs hτ v; funext z θ; simp only [rem]; rw [hsG s hs, hsG τ hτ]
    have remH : ∀ s τ, t ≤ s → t ≤ τ → ∀ v : Fn,
        rem (slice F) v s τ = rem (slice H) v (s - t) (τ - t) := by
      intro s τ hs hτ v; funext z θ; simp only [rem]; rw [hsH s hs, hsH τ hτ]; ring
    intro τ hτ η hη
    rcases lt_trichotomy τ t with h | h | h
    · obtain ⟨d, hd, hc⟩ := hG.deriv τ (mG τ hτ h.le) η hη
      refine ⟨min d (t - τ), lt_min hd (by linarith), fun s hs hst => ?_⟩
      have hst' : |s - τ| < d := lt_of_lt_of_le hst (min_le_left _ _)
      have hsl : s < t := by
        have := lt_of_lt_of_le hst (min_le_right _ _)
        linarith [le_abs_self (s - τ)]
      rw [hrG τ h.le, remG s τ hsl.le h.le]
      exact hc s (mG s hs hsl.le) hst'
    · subst h
      obtain ⟨dG, hdG, hcG⟩ := hG.deriv τ (mG τ hτ le_rfl) η hη
      obtain ⟨dH, hdH, hcH⟩ := hH.deriv 0 ⟨le_rfl, hδ.le⟩ η hη
      refine ⟨min dG dH, lt_min hdG hdH, fun s hs hst => ?_⟩
      rcases le_total s τ with h' | h'
      · rw [hrG τ le_rfl, remG s τ h' le_rfl]
        exact hcG s (mG s hs h') (lt_of_lt_of_le hst (min_le_left _ _))
      · have hv : epsRHSP α ρ ε Φs E F τ = epsRHSP α ρ ε Φs E H 0 := by
          rw [hrH τ le_rfl, sub_self]
        rw [hv, remH s τ h' le_rfl, sub_self]
        have hlt : |s - τ - 0| < dH := by
          rw [sub_zero]; exact lt_of_lt_of_le hst (min_le_right _ _)
        obtain ⟨h1, h2⟩ := hcH (s - τ) (mH s hs h') hlt
        refine ⟨h1, ?_⟩
        simpa only [sub_zero] using h2
    · obtain ⟨d, hd, hc⟩ := hH.deriv (τ - t) (mH τ hτ h.le) η hη
      refine ⟨min d (τ - t), lt_min hd (by linarith), fun s hs hst => ?_⟩
      have hst' : |s - τ| < d := lt_of_lt_of_le hst (min_le_left _ _)
      have hsl : t < s := by
        have := lt_of_lt_of_le hst (min_le_right _ _)
        linarith [neg_abs_le (s - τ)]
      have he : s - t - (τ - t) = s - τ := by ring
      rw [hrH τ h.le, remH s τ hsl.le h.le]
      obtain ⟨h1, h2⟩ := hc (s - t) (mH s hs hsl.le) (by rw [he]; exact hst')
      exact ⟨h1, by rw [he] at h2; exact h2⟩
  · intro τ hτ
    rcases le_total τ t with h | h
    · have : epsWP α ρ ε Φs E F τ = epsWP α ρ ε Φs E G τ :=
        Work.FTS.StrongEps.StrongEpsP.epsWP_congr (hsG τ h)
      rw [this]; exact hG.wp τ (mG τ hτ h)
    · have : epsWP α ρ ε Φs E F τ = epsWP α ρ ε Φs E H (τ - t) :=
        Work.FTS.StrongEps.StrongEpsP.epsWP_congr (hsH τ h)
      rw [this]; exact hH.wp (τ - t) (mH τ hτ h)

/-! ## 3. Consumer side: what `EpsFlowP` buys (S4, L-B continuity, F6) -/

/-- the `HQo α 6` clause of a regular solution's slices. -/
theorem regHqo {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {g : Fam} (h : EpsRegP α ρ ε T g)
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) : HQo α 6 (slice g τ) :=
  ⟨(h.2 τ hτ).1, (h.2 τ hτ).2.1⟩

theorem hkNorm_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : Fn) :
    Work.Spaces.HkNorm α k (fun z θ => c * f z θ) = |c| * Work.Spaces.HkNorm α k f := by
  unfold Work.Spaces.HkNorm
  rw [Work.FTS.StrongEps.HkSq_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem hkNorm_triangle' {α : ℝ} {k : ℕ} {f g : Fn} (hf : HQo α k f) (hg : HQo α k g) :
    Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g :=
  Work.FTS.StrongEps.EpsE4Thr.HkNorm_triangle α k
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf.1)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hg.1) hf.2 hg.2

/-- the increment splits as remainder plus linear part. -/
theorem incr_eq (u : ℝ → Fn) (v : Fn) (s τ : ℝ) :
    (fun z θ => u s z θ - u τ z θ) = fun z θ => rem u v s τ z θ + (s - τ) * v z θ := by
  funext z θ; simp only [rem]; ring

/-- **The increment is `O(|s-τ|)` in `ℋᵏ`** (from `HkDerivWithin` with `η = 1`). -/
theorem incr_le {α : ℝ} {k : ℕ} {u : ℝ → Fn} {v : Fn} {S : Set ℝ} {τ : ℝ}
    (hv : HQo α k v) (hd : HkDerivWithin α k u v S τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, |s - τ| < δ →
      HQo α k (fun z θ => u s z θ - u τ z θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => u s z θ - u τ z θ)
        ≤ (1 + Work.Spaces.HkNorm α k v) * |s - τ| := by
  obtain ⟨δ, hδ, h⟩ := hd 1 one_pos
  refine ⟨δ, hδ, fun s hs hst => ?_⟩
  obtain ⟨hq, hn⟩ := h s hs hst
  have hv' : HQo α k (fun z θ => (s - τ) * v z θ) := Work.FTS.Open3.HQo_const_mul hv (s - τ)
  rw [incr_eq u v s τ]
  refine ⟨Work.FTS.Open3.HQo_add hq hv', ?_⟩
  calc Work.Spaces.HkNorm α k (fun z θ => rem u v s τ z θ + (s - τ) * v z θ)
      ≤ Work.Spaces.HkNorm α k (rem u v s τ)
          + Work.Spaces.HkNorm α k (fun z θ => (s - τ) * v z θ) := hkNorm_triangle' hq hv'
    _ = Work.Spaces.HkNorm α k (rem u v s τ) + |s - τ| * Work.Spaces.HkNorm α k v := by
        rw [hkNorm_const_mul]
    _ ≤ 1 * |s - τ| + |s - τ| * Work.Spaces.HkNorm α k v := by linarith
    _ = (1 + Work.Spaces.HkNorm α k v) * |s - τ| := by ring

/-- **L-B's `hcont` from `EpsFlowP`** (PROVED): `τ ↦ Xn6 α (slice g τ)` is continuous on `[0,T]`. -/
theorem xn6_continuousOn_of_flow {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (hreg : EpsRegP α ρ ε T g) (hF : EpsFlowP α ρ ε T Φs E g) :
    ContinuousOn (fun τ => Xn6 α (slice g τ)) (Icc 0 T) := by
  intro τ hτ
  rw [Metric.continuousWithinAt_iff]
  intro c hc
  obtain ⟨δ, hδ, h⟩ := incr_le (hF.rhs τ hτ) (hF.deriv τ hτ)
  set A : ℝ := 1 + Work.Spaces.HkNorm α 6 (epsRHSP α ρ ε Φs E g τ) with hA
  have hA0 : 0 < A := by
    have := Work.Spaces.HkNorm_nonneg α 6 (epsRHSP α ρ ε Φs E g τ); linarith
  refine ⟨min δ (c / (2 * A)), lt_min hδ (by positivity), fun s hs hd => ?_⟩
  rw [Real.dist_eq] at hd ⊢
  have hd1 : |s - τ| < δ := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : |s - τ| < c / (2 * A) := lt_of_lt_of_le hd (min_le_right _ _)
  obtain ⟨hq, hn⟩ := h s hs hd1
  have hb := regHqo hreg hτ
  have ha := regHqo hreg hs
  -- `‖a‖ ≤ ‖b‖ + ‖a-b‖` and `‖b‖ ≤ ‖a‖ + ‖a-b‖`
  have e1 : slice g s = fun z θ => slice g τ z θ + (slice g s z θ - slice g τ z θ) := by
    funext z θ; ring
  have e2 : slice g τ = fun z θ => slice g s z θ + (-1) * (slice g s z θ - slice g τ z θ) := by
    funext z θ; ring
  have i1 : Xn6 α (slice g s) ≤ Xn6 α (slice g τ)
      + Work.Spaces.HkNorm α 6 (fun z θ => slice g s z θ - slice g τ z θ) := by
    show Work.Spaces.HkNorm α 6 (slice g s) ≤ _
    conv_lhs => rw [e1]
    exact hkNorm_triangle' hb hq
  have i2 : Xn6 α (slice g τ) ≤ Xn6 α (slice g s)
      + Work.Spaces.HkNorm α 6 (fun z θ => slice g s z θ - slice g τ z θ) := by
    show Work.Spaces.HkNorm α 6 (slice g τ) ≤ _
    conv_lhs => rw [e2]
    refine le_trans (hkNorm_triangle' ha (Work.FTS.Open3.HQo_const_mul hq (-1))) ?_
    rw [hkNorm_const_mul]; norm_num
  have hsmall : Work.Spaces.HkNorm α 6 (fun z θ => slice g s z θ - slice g τ z θ) < c := by
    calc _ ≤ A * |s - τ| := hn
      _ ≤ A * (c / (2 * A)) := mul_le_mul_of_nonneg_left hd2.le hA0.le
      _ = c / 2 := by field_simp
      _ < c := by linarith
  rw [abs_lt]; constructor <;> linarith

/-- **S4 from `EpsFlowP`: the raw level-six energy identity** (the abstract product rule for the
bounded symmetric bilinear form `IP6o` on `HQo α 6`).  It replaces `rawE6_deriv` (whose
hypotheses `IsEpsSolP + EpsRegP + hbdd6` were returned FALSE by six children): no slot-level chain
rule, no domination, no `hbdd6`.  PROVED. -/
theorem rawE6_hasDerivWithinAt_of_flow {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g : Fam} (hα : α ∈ Ioc (0 : ℝ) 1) (hreg : EpsRegP α ρ ε T g)
    (hF : EpsFlowP α ρ ε T Φs E g) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    HasDerivWithinAt (rawE6 α g) (2 * IP6o α (epsRHSP α ρ ε Φs E g τ) (slice g τ))
      (Icc 0 T) τ := by
  obtain ⟨CC, hCC, hcs0⟩ :=
    Work.FTS.StrongPersist.IP6_cs_coeffs 1 1 1 1 1 1 1 1 1 1 (1 : ℝ) one_pos
  have hcs : ∀ f h : Fn, HQo α 6 f → HQo α 6 h →
      |IP6o α f h| ≤ CC * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 h :=
    fun f h hf hh => hcs0 α hα f h hf hh
  have hα0 : 0 < α := hα.1
  obtain ⟨b, hbdef⟩ : ∃ b : Fn, b = slice g τ := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : Fn, v = epsRHSP α ρ ε Φs E g τ := ⟨_, rfl⟩
  have hb : HQo α 6 b := hbdef ▸ regHqo hreg hτ
  have hv : HQo α 6 v := hvdef ▸ hF.rhs τ hτ
  rw [← hbdef, ← hvdef]
  have hDer : HkDerivWithin α 6 (slice g) v (Icc 0 T) τ := hvdef ▸ hF.deriv τ hτ
  -- the algebraic identity behind the product rule
  have key : ∀ s ∈ Icc 0 T, HQo α 6 (rem (slice g) v s τ) →
      rawE6 α g s - rawE6 α g τ - (s - τ) * (2 * IP6o α v b)
        = IP6o α (fun z θ => slice g s z θ - b z θ) (fun z θ => slice g s z θ - b z θ)
          + 2 * IP6o α (rem (slice g) v s τ) b := by
    intro s hs hR
    obtain ⟨d, hddef⟩ : ∃ d : Fn, d = fun z θ => slice g s z θ - b z θ := ⟨_, rfl⟩
    rw [← hddef]
    have hd : HQo α 6 d := hddef ▸ Work.FTS.Open3.HQo_sub (regHqo hreg hs) hb
    have hsv : HQo α 6 (fun z θ => (s - τ) * v z θ) := Work.FTS.Open3.HQo_const_mul hv (s - τ)
    have hbd : HQo α 6 (fun z θ => b z θ + d z θ) := Work.FTS.Open3.HQo_add hb hd
    have e1 : slice g s = fun z θ => b z θ + d z θ := by
      funext z θ; rw [hddef]; ring
    have e2 : d = fun z θ => rem (slice g) v s τ z θ + (s - τ) * v z θ := by
      funext z θ; rw [hddef, hbdef]; simp only [rem]; ring
    have A1 : IP6o α (fun z θ => b z θ + d z θ) (fun z θ => b z θ + d z θ)
        = IP6o α b (fun z θ => b z θ + d z θ) + IP6o α d (fun z θ => b z θ + d z θ) :=
      Work.FTS.StrongPersist.IP6_add 1 1 1 1 1 1 1 1 1 1 α hα0 hb.1 hd.1 hbd.1 hb.2 hd.2 hbd.2
    have A2 : IP6o α b (fun z θ => b z θ + d z θ) = IP6o α b b + IP6o α d b :=
      (Work.FTS.StrongPersist.IP6_symm 1 1 1 1 1 1 1 1 1 1 α b _).trans
        (Work.FTS.StrongPersist.IP6_add 1 1 1 1 1 1 1 1 1 1 α hα0 hb.1 hd.1 hb.1 hb.2 hd.2 hb.2)
    have A3' : IP6o α (fun z θ => b z θ + d z θ) d = IP6o α b d + IP6o α d d :=
      Work.FTS.StrongPersist.IP6_add 1 1 1 1 1 1 1 1 1 1 α hα0 hb.1 hd.1 hd.1 hb.2 hd.2 hd.2
    have Sbd : IP6o α b d = IP6o α d b := Work.FTS.StrongPersist.IP6_symm 1 1 1 1 1 1 1 1 1 1 α b d
    have A3 : IP6o α d (fun z θ => b z θ + d z θ) = IP6o α d b + IP6o α d d := by
      exact ((Work.FTS.StrongPersist.IP6_symm 1 1 1 1 1 1 1 1 1 1 α d
        (fun z θ => b z θ + d z θ)).trans A3').trans (congrArg (· + IP6o α d d) Sbd)
    have A4' : IP6o α (fun z θ => rem (slice g) v s τ z θ + (s - τ) * v z θ) b
        = IP6o α (rem (slice g) v s τ) b + IP6o α (fun z θ => (s - τ) * v z θ) b :=
      Work.FTS.StrongPersist.IP6_add 1 1 1 1 1 1 1 1 1 1 α hα0 hR.1 hsv.1 hb.1 hR.2 hsv.2 hb.2
    have A4'' : IP6o α (fun z θ => (s - τ) * v z θ) b = (s - τ) * IP6o α v b :=
      Work.FTS.StrongPersist.IP6_smul 1 1 1 1 1 1 1 1 1 1 α (s - τ) v b
    have A4 : IP6o α d b = IP6o α (rem (slice g) v s τ) b + (s - τ) * IP6o α v b := by
      rw [e2, A4', A4'']
    have hτb : rawE6 α g τ = IP6o α b b := by rw [hbdef]; rfl
    have hs' : rawE6 α g s = IP6o α (fun z θ => b z θ + d z θ) (fun z θ => b z θ + d z θ) := by
      show IP6o α (slice g s) (slice g s) = _
      rw [e1]
    rw [hs', hτb, A1, A2, A3, A4]
    ring
  -- the little-o estimate
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set nb : ℝ := Work.Spaces.HkNorm α 6 b with hnbdef
  set nv : ℝ := Work.Spaces.HkNorm α 6 v with hnvdef
  have hnb : 0 ≤ nb := Work.Spaces.HkNorm_nonneg α 6 b
  have hnv : 0 ≤ nv := Work.Spaces.HkNorm_nonneg α 6 v
  set η : ℝ := min 1 (c / (4 * CC * (nb + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ c / (4 * CC * (nb + 1)) := min_le_right _ _
  obtain ⟨δ, hδ, hD⟩ := hDer η hη
  set δ₂ : ℝ := c / (2 * CC * (1 + nv) ^ 2 + 1) with hδ₂def
  have hδ₂ : 0 < δ₂ := by positivity
  have hball : Metric.ball τ (min δ δ₂) ∈ 𝓝[Icc 0 T] τ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds τ (lt_min hδ hδ₂))
  filter_upwards [self_mem_nhdsWithin, hball] with s hs hsb
  have hst : |s - τ| < min δ δ₂ := by rwa [Metric.mem_ball, Real.dist_eq] at hsb
  have hst1 : |s - τ| < δ := lt_of_lt_of_le hst (min_le_left _ _)
  have hst2 : |s - τ| < δ₂ := lt_of_lt_of_le hst (min_le_right _ _)
  obtain ⟨hR, hRn⟩ := hD s hs hst1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, key s hs hR]
  -- the increment and its norm
  have hsv : HQo α 6 (fun z θ => (s - τ) * v z θ) := Work.FTS.Open3.HQo_const_mul hv (s - τ)
  have hdq : HQo α 6 (fun z θ => slice g s z θ - b z θ) :=
    Work.FTS.Open3.HQo_sub (regHqo hreg hs) hb
  have hdn : Work.Spaces.HkNorm α 6 (fun z θ => slice g s z θ - b z θ) ≤ (η + nv) * |s - τ| := by
    have eqd : (fun z θ => slice g s z θ - b z θ)
        = fun z θ => rem (slice g) v s τ z θ + (s - τ) * v z θ := by
      funext z θ; rw [hbdef]; simp only [rem]; ring
    rw [eqd]
    calc _ ≤ Work.Spaces.HkNorm α 6 (rem (slice g) v s τ)
          + Work.Spaces.HkNorm α 6 (fun z θ => (s - τ) * v z θ) := hkNorm_triangle' hR hsv
      _ = Work.Spaces.HkNorm α 6 (rem (slice g) v s τ) + |s - τ| * nv := by
          rw [hkNorm_const_mul]
      _ ≤ η * |s - τ| + |s - τ| * nv := by linarith
      _ = (η + nv) * |s - τ| := by ring
  have h1 := hcs _ _ hdq hdq
  have h2 := hcs _ _ hR hb
  set h := |s - τ| with hhdef
  have hh0 : 0 ≤ h := abs_nonneg _
  set nd : ℝ := Work.Spaces.HkNorm α 6 (fun z θ => slice g s z θ - b z θ) with hnddef
  set nR : ℝ := Work.Spaces.HkNorm α 6 (rem (slice g) v s τ) with hnRdef
  have hnd0 : 0 ≤ nd := Work.Spaces.HkNorm_nonneg α 6 _
  have hnR0 : 0 ≤ nR := Work.Spaces.HkNorm_nonneg α 6 _
  have hCC0 : 0 ≤ CC := hCC.le
  -- `|IP(d,d)| ≤ (c/2) h`
  have b1 : CC * nd * nd ≤ c / 2 * h := by
    have hnd' : nd ≤ (1 + nv) * h := le_trans hdn
      (mul_le_mul_of_nonneg_right (by linarith) hh0)
    have hsq : nd * nd ≤ ((1 + nv) * h) * ((1 + nv) * h) := mul_le_mul hnd' hnd' hnd0
      (by positivity)
    have hhδ : (1 + nv) ^ 2 * h * (2 * CC * (1 + nv) ^ 2 + 1) ≤ (1 + nv) ^ 2 * c := by
      have : h * (2 * CC * (1 + nv) ^ 2 + 1) ≤ c := by
        have := hst2.le; rw [hδ₂def, le_div_iff₀ (by positivity)] at this; linarith
      nlinarith [sq_nonneg (1 + nv)]
    have hden : 0 < 2 * CC * (1 + nv) ^ 2 + 1 := by positivity
    calc CC * nd * nd = CC * (nd * nd) := by ring
      _ ≤ CC * (((1 + nv) * h) * ((1 + nv) * h)) := mul_le_mul_of_nonneg_left hsq hCC0
      _ = (CC * (1 + nv) ^ 2 * h) * h := by ring
      _ ≤ c / 2 * h := by
          apply mul_le_mul_of_nonneg_right _ hh0
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
          have h3 : CC * (1 + nv) ^ 2 * h * 2 * (2 * CC * (1 + nv) ^ 2 + 1)
              ≤ c * (2 * CC * (1 + nv) ^ 2 + 1) := by nlinarith
          exact le_of_mul_le_mul_right (by linarith) hden
  -- `2|IP(R,b)| ≤ (c/2) h`
  have b2 : 2 * (CC * nR * nb) ≤ c / 2 * h := by
    have hRh : nR ≤ η * h := hRn
    have hηb : η * (4 * CC * (nb + 1)) ≤ c := by
      rw [le_div_iff₀ (by positivity)] at hη2; linarith
    calc 2 * (CC * nR * nb) ≤ 2 * (CC * (η * h) * nb) := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRh hCC0) hnb
          linarith
      _ = (η * (4 * CC * nb)) * h / 2 := by ring
      _ ≤ (η * (4 * CC * (nb + 1))) * h / 2 := by
          have : η * (4 * CC * nb) ≤ η * (4 * CC * (nb + 1)) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hη.le
          nlinarith
      _ ≤ c * h / 2 := by nlinarith
      _ = c / 2 * h := by ring
  calc |IP6o α (fun z θ => slice g s z θ - b z θ) (fun z θ => slice g s z θ - b z θ)
        + 2 * IP6o α (rem (slice g) v s τ) b|
      ≤ |IP6o α (fun z θ => slice g s z θ - b z θ) (fun z θ => slice g s z θ - b z θ)|
        + |2 * IP6o α (rem (slice g) v s τ) b| := abs_add_le _ _
    _ = |IP6o α (fun z θ => slice g s z θ - b z θ) (fun z θ => slice g s z θ - b z θ)|
        + 2 * |IP6o α (rem (slice g) v s τ) b| := by rw [abs_mul]; norm_num
    _ ≤ CC * nd * nd + 2 * (CC * nR * nb) := by linarith
    _ ≤ c / 2 * h + c / 2 * h := by linarith
    _ = c * h := by ring

/-- S4 in the shape of the old leaf `rawE6_deriv` (PROVED from the previous lemma). -/
theorem rawE6_deriv_of_flow {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (hα : α ∈ Ioc (0 : ℝ) 1) (hreg : EpsRegP α ρ ε T g) (hF : EpsFlowP α ρ ε T Φs E g) :
    ContinuousOn (rawE6 α g) (Icc 0 T) ∧
      ∀ τ ∈ Ioo 0 T, HasDerivAt (rawE6 α g)
        (2 * IP6o α (epsRHSP α ρ ε Φs E g τ) (slice g τ)) τ := by
  refine ⟨fun τ hτ => (rawE6_hasDerivWithinAt_of_flow hα hreg hF hτ).continuousWithinAt,
    fun τ hτ => ?_⟩
  have hτ' : τ ∈ Icc 0 T := Ioo_subset_Icc_self hτ
  exact (rawE6_hasDerivWithinAt_of_flow hα hreg hF hτ').hasDerivAt
    (Icc_mem_nhds hτ.1 hτ.2)



/-! ## 4. The E4 interfaces re-stated over `EpsFlowP` -/

/-- **The local step, flow-carrying**: `LocalStepP` whose solution also carries `EpsFlowP`. -/
def LocalStepPF (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (C₀ : ℝ) : Prop :=
  ∀ M' : ℝ, 0 ≤ M' → ∃ δ : ℝ, 0 < δ ∧ ∀ h₀ : Fn,
    EpsDatumP α ρ ε h₀ →
    Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε h₀)) ≤ C₀ * α ^ 2 →
    Xn6 α h₀ ≤ M' →
    ∃ h : Fam, IsEpsSolP α ρ ε δ Φs E h₀ h ∧ EpsRegP α ρ ε δ h ∧ EpsFlowP α ρ ε δ Φs E h


/-- **The a-priori bound over the flow class**: `AprioriP` quantified only over solutions that
carry `EpsFlowP` (a strictly smaller class — the one the local step produces). -/
def AprioriPF (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ M : ℝ) : Prop :=
  Xn6 α g₀ ≤ M →
    Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2 →
      ∀ T' : ℝ, 0 < T' → T' ≤ T → ∀ g : Fam, IsEpsSolP α ρ ε T' Φs E g₀ g →
        EpsRegP α ρ ε T' g → EpsFlowP α ρ ε T' Φs E g →
        ∀ τ ∈ Icc 0 T', Xn6 α (slice g τ) ≤ M ∧
          Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2


def AprioriPSixthBF (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ E₁ : ℝ) : Prop :=
  ∀ T' : ℝ, 0 < T' → T' ≤ T → ∀ g : Fam, IsEpsSolP α ρ ε T' Φs E g₀ g → EpsRegP α ρ ε T' g →
    EpsFlowP α ρ ε T' Φs E g →
    (∀ τ ∈ Icc 0 T', Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) →
    ∀ τ ∈ Icc 0 T', rawE6 α g τ ≤ E₁

def AprioriPFourthBF (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ M : ℝ) : Prop :=
  Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2 →
    ∀ T' : ℝ, 0 < T' → T' ≤ T → ∀ g : Fam, IsEpsSolP α ρ ε T' Φs E g₀ g →
      EpsRegP α ρ ε T' g → EpsFlowP α ρ ε T' Φs E g → (∀ τ ∈ Icc 0 T', Xn6 α (slice g τ) ≤ M) →
      ∀ τ ∈ Icc 0 T', Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2



/-- Local-step chapter over the flow class. -/
def LocalStepChapter5 (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ → ∀ ε ∈ Ioc (0 : ℝ) 1, LocalStepPF α' ρ ε Φs E C₀

def FourthChapterBF (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ →
    ∀ T M : ℝ, 0 < T → ∃ ε₄ : ℝ, 0 < ε₄ ∧ ε₄ ≤ 1 ∧
      ∀ ε ∈ Ioc 0 ε₄, AprioriPFourthBF α' ρ ε T Φs E g₀ C₀ M

def SixthChapterBF (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ → Work.FTS.StrongPersist.StarPkg6 α' Cs Φs →
    ∀ T : ℝ, 0 < T → ∃ E₁ : ℝ, 0 ≤ E₁ ∧ K ^ 2 ≤ E₁ ∧ ∃ ε₆ : ℝ, 0 < ε₆ ∧ ε₆ ≤ 1 ∧
      ∀ ε ∈ Ioc 0 ε₆, AprioriPSixthBF α' ρ ε T Φs E g₀ C₀ E₁

def AprioriChapter5 (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ → Work.FTS.StrongPersist.StarPkg6 α' Cs Φs →
    ∀ T : ℝ, 0 < T → ∃ M : ℝ, K ≤ M ∧ ∃ ε₂ : ℝ, 0 < ε₂ ∧ ε₂ ≤ 1 ∧
      ∀ ε ∈ Ioc 0 ε₂, AprioriPF α' ρ ε T Φs E g₀ C₀ M

/-! ## 5. Assembly over the flow class (all PROVED) -/

/-- **L-B over the flow class** (PROVED): the copy of `aprioriP_of_halvesB_strict` whose `hcont`
input is now *derived* (`xn6_continuousOn_of_flow`). -/
theorem aprioriPF_of_halvesBF {α ε T C₀ E₁ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} (hα : 0 < α) (hα1 : α ≤ 1) (hE₁ : 0 ≤ E₁)
    (h6 : AprioriPSixthBF α ρ ε T Φs E g₀ C₀ E₁)
    (h4 : AprioriPFourthBF α ρ ε T Φs E g₀ C₀ (Real.sqrt (2 * E₁ + 1)))
    (hstrict : Xn6 α g₀ < Real.sqrt (2 * E₁ + 1)) :
    AprioriPF α ρ ε T Φs E g₀ C₀ (Real.sqrt (2 * E₁ + 1)) := by
  intro _hM hsmall T' hT' hT'le g hsol hreg hflow
  have hdat : ∀ τ ∈ Icc 0 T', EpsDatumP α ρ ε (slice g τ) := hreg.2
  have hslice0 : slice g 0 = g₀ := funext fun z => funext fun θ => hsol.1 z θ
  have hstrict0 : Xn6 α (slice g 0) < Real.sqrt (2 * E₁ + 1) := by rw [hslice0]; exact hstrict
  have hcontg : ContinuousOn (fun τ => Xn6 α (slice g τ)) (Icc 0 T') :=
    xn6_continuousOn_of_flow hreg hflow
  have hP : ∀ τ ∈ Icc 0 T', Xn6 α (slice g τ) ≤ Real.sqrt (2 * E₁ + 1) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨τ₀, hτ₀, hgt⟩ := hcon
    set s : ℝ := sInf {τ : ℝ | τ ∈ Icc 0 T' ∧ Real.sqrt (2 * E₁ + 1) < Xn6 α (slice g τ)}
      with hsdef
    have hsprop := Work.FTS.StrongEps.E4R3.Apriori4Proofs.sInf_crossing
      (f := fun τ => Xn6 α (slice g τ)) (M := Real.sqrt (2 * E₁ + 1)) (T := T') hT' hcontg
      hstrict0 ⟨τ₀, hτ₀, hgt⟩
    rw [← hsdef] at hsprop
    obtain ⟨hspos, hsT', hsval, hsle⟩ := hsprop
    have hsT : s ≤ T := le_trans hsT' hT'le
    have hsolS : IsEpsSolP α ρ ε s Φs E g₀ g := Work.FTS.StrongEps.StrongEpsP.IsEpsSolP.mono hsol hsT'
    have hregS : EpsRegP α ρ ε s g := hreg.mono hsT'
    have hflowS : EpsFlowP α ρ ε s Φs E g := hflow.mono hsT'
    have hQ : ∀ τ ∈ Icc 0 s, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 :=
      h4 hsmall s hspos hsT g hsolS hregS hflowS hsle
    have hraw : ∀ τ ∈ Icc 0 s, rawE6 α g τ ≤ E₁ := h6 s hspos hsT g hsolS hregS hflowS hQ
    have hloop : Work.Spaces.HkSq α 6 (slice g s) ≤ rawE6 α g s := by
      have hd := hdat s ⟨hspos.le, hsT'⟩
      exact Work.FTS.StrongEps.EpsE4Thr.HkSq_le_IP6 (α := α) ⟨hα, hα1⟩ hd.1 hd.2.1
    have hsqrt : Xn6 α (slice g s) ≤ Real.sqrt E₁ := by
      show Real.sqrt (Work.Spaces.HkSq α 6 (slice g s)) ≤ Real.sqrt E₁
      exact le_trans (Real.sqrt_le_sqrt hloop) (Real.sqrt_le_sqrt (hraw s ⟨hspos.le, le_rfl⟩))
    have hcontr : Real.sqrt (2 * E₁ + 1) ≤ Real.sqrt E₁ := by rw [← hsval]; exact hsqrt
    have h21 : 2 * E₁ + 1 ≤ E₁ := (Real.sqrt_le_sqrt_iff hE₁).mp hcontr
    linarith
  intro τ hτ
  exact ⟨hP τ hτ, h4 hsmall T' hT' hT'le g hsol hreg hflow hP τ hτ⟩

/-- **`AprioriChapter5` from its two halves** (PROVED; the strict datum inequality is supplied by
the proved `strict_datum_of_xn6_le`). -/
theorem aprioriChapter5_of_halves {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}
    (h4 : ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → FourthChapterBF Ce Cs C₀ ρ)
    (h6 : ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → SixthChapterBF Ce Cs C₀ ρ) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → AprioriChapter5 Ce Cs C₀ ρ := by
  obtain ⟨C4, h4⟩ := h4
  obtain ⟨C6, h6⟩ := h6
  refine ⟨max C4 C6, fun C₀ hC₀ => ?_⟩
  obtain ⟨a4, ha4, ha41, H4⟩ := h4 C₀ (le_trans (le_max_left _ _) hC₀)
  obtain ⟨a6, ha6, ha61, H6⟩ := h6 C₀ (le_trans (le_max_right _ _) hC₀)
  refine ⟨min a4 a6, lt_min ha4 ha6, le_trans (min_le_left _ _) ha41, ?_⟩
  intro α' hα' K Φs E g₀ hdat hst6 T hT
  have hα'4 : α' ∈ Ioc 0 a4 := ⟨hα'.1, le_trans hα'.2 (min_le_left _ _)⟩
  have hα'6 : α' ∈ Ioc 0 a6 := ⟨hα'.1, le_trans hα'.2 (min_le_right _ _)⟩
  have hα'1 : α' ≤ 1 := le_trans hα'4.2 ha41
  obtain ⟨E₁, hE₁, hKE, ε₆, hε₆, hε₆1, HS⟩ := H6 α' hα'6 hdat hst6 T hT
  obtain ⟨ε₄, hε₄, hε₄1, HF⟩ := H4 α' hα'4 hdat T (Real.sqrt (2 * E₁ + 1)) hT
  have hK0 : 0 ≤ K := hdat.1
  have hKM : K ≤ Real.sqrt (2 * E₁ + 1) := by
    rw [show K = Real.sqrt (K ^ 2) from (Real.sqrt_sq hK0).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hstrict : Xn6 α' g₀ < Real.sqrt (2 * E₁ + 1) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.strict_datum_of_xn6_le hα'.1 hα'1 hK0 hKE
      hdat.2.2.2.2.2.2.2
  refine ⟨Real.sqrt (2 * E₁ + 1), hKM, min ε₄ ε₆, lt_min hε₄ hε₆,
    le_trans (min_le_left _ _) hε₄1, ?_⟩
  intro ε hε
  have hε4 : ε ∈ Ioc 0 ε₄ := ⟨hε.1, le_trans hε.2 (min_le_left _ _)⟩
  have hε6 : ε ∈ Ioc 0 ε₆ := ⟨hε.1, le_trans hε.2 (min_le_right _ _)⟩
  exact aprioriPF_of_halvesBF hα'.1 hα'1 hE₁ (HS ε hε6) (HF ε hε4) hstrict

/-- **The continuation over the flow class** (PROVED; uses the proved `EpsFlowP.glue`): the copy of
`Reduction.exists_sol_of_localStep_apriori` with `LocalStepPF`/`AprioriPF`. -/
theorem exists_sol_of_localStepF_aprioriF {α ε T C₀ M : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn}
    (hT : 0 < T) (hM : 0 ≤ M) (hg₀M : Xn6 α g₀ ≤ M)
    (hsmall₀ : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2)
    (hd : EpsDatumP α ρ ε g₀) (hstep : LocalStepPF α ρ ε Φs E C₀)
    (hapr : AprioriPF α ρ ε T Φs E g₀ C₀ M) :
    ∃ g : Fam, IsEpsSolP α ρ ε T Φs E g₀ g ∧ EpsRegP α ρ ε T g ∧
      ∀ τ ∈ Icc 0 T, Xn6 α (slice g τ) ≤ M ∧
        Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 := by
  obtain ⟨δ, hδpos, hδstep⟩ := hstep M hM
  have hM₀ : (0 : ℝ) ≤ Xn6 α g₀ := Work.Spaces.HkNorm_nonneg α 6 g₀
  obtain ⟨δ₀, hδ₀pos, hδ₀step⟩ := hstep (Xn6 α g₀) hM₀
  set δ' : ℝ := min δ δ₀ with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos hδ₀pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, T ≤ (N : ℝ) * δ' := by
    obtain ⟨N, hN⟩ := exists_nat_gt (T / δ')
    exact ⟨N, by rw [div_lt_iff₀ hδ'pos] at hN; linarith⟩
  let hor : ℕ → ℝ := fun n => min T (((n : ℝ) + 1) * δ')
  have hhor_pos : ∀ n, 0 < hor n := fun n => lt_min hT (by positivity)
  have hhor_le : ∀ n, hor n ≤ T := fun n => min_le_left _ _
  have hpoint : ∀ n : ℕ, ∃ g : Fam, IsEpsSolP α ρ ε (hor n) Φs E g₀ g ∧
      EpsRegP α ρ ε (hor n) g ∧ EpsFlowP α ρ ε (hor n) Φs E g ∧
      ∀ τ ∈ Icc 0 (hor n), Xn6 α (slice g τ) ≤ M ∧
        Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 := by
    intro n
    induction n with
    | zero =>
      have h0 : hor 0 = min T δ' := by
        show min T ((((0 : ℕ) : ℝ) + 1) * δ') = min T δ'
        norm_num
      rw [h0]
      obtain ⟨h, hsol, hreg, hflow⟩ := hδ₀step g₀ hd hsmall₀ le_rfl
      have hle₀ : min T δ' ≤ δ₀ :=
        le_trans (min_le_right T δ') (by rw [hδ'def]; exact min_le_right δ δ₀)
      have hsol' : IsEpsSolP α ρ ε (min T δ') Φs E g₀ h :=
        Work.FTS.StrongEps.StrongEpsP.IsEpsSolP.mono hsol hle₀
      have hreg' : EpsRegP α ρ ε (min T δ') h := EpsRegP.mono hreg hle₀
      have hflow' : EpsFlowP α ρ ε (min T δ') Φs E h := hflow.mono hle₀
      exact ⟨h, hsol', hreg', hflow',
        hapr hg₀M hsmall₀ (min T δ') (lt_min hT hδ'pos) (min_le_left T δ') h hsol' hreg' hflow'⟩
    | succ n ih =>
      obtain ⟨g, hsol, hreg, hflow, hbnd⟩ := ih
      by_cases hcase : T ≤ ((n : ℝ) + 1) * δ'
      · have hcase' : hor n = T := min_eq_left hcase
        have hnext : hor (n + 1) = T := min_eq_left (by push_cast; linarith)
        have hs : hor (n + 1) = hor n := by rw [hnext, hcase']
        refine ⟨g, ?_, ?_, ?_, ?_⟩
        · rw [hs]; exact hsol
        · rw [hs]; exact hreg
        · rw [hs]; exact hflow
        · rw [hs]; exact hbnd
      · have hXn : ((n : ℝ) + 1) * δ' < T := lt_of_not_ge hcase
        have hnn : hor n = ((n : ℝ) + 1) * δ' := min_eq_right (le_of_lt hXn)
        have hnnonneg : 0 ≤ hor n := le_of_lt (hhor_pos n)
        have hdd : EpsDatumP α ρ ε (slice g (hor n)) := hreg.2 (hor n) ⟨hnnonneg, le_rfl⟩
        have hsb : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε (slice g (hor n)))) ≤ C₀ * α ^ 2 := by
          have h2 := (hbnd (hor n) ⟨hnnonneg, le_rfl⟩).2
          rwa [slice_JfamP] at h2
        have hbd : Xn6 α (slice g (hor n)) ≤ M := (hbnd (hor n) ⟨hnnonneg, le_rfl⟩).1
        obtain ⟨H, hHsol, hHreg, hHflow⟩ := hδstep (slice g (hor n)) hdd hsb hbd
        have hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            g z θ (hor n) = H z θ 0 := fun z θ _ _ _ => (hHsol.1 z θ).symm
        set hR : Fn := fun z θ => epsRHSP α ρ ε Φs E g (hor n) z θ with hRdef
        have hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            HasDerivWithinAt (fun s => g z θ s) (hR z θ) (Icc 0 (hor n)) (hor n) := by
          intro z θ hz hθ hθ'
          exact hsol.2 z θ (hor n) hz ⟨hθ, hθ'⟩ ⟨hnnonneg, le_rfl⟩
        have hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            HasDerivWithinAt (fun s => H z θ s) (hR z θ) (Icc 0 δ) 0 := by
          intro z θ hz hθ hθ'
          have h1 := hHsol.2 z θ 0 hz ⟨hθ, hθ'⟩ ⟨le_rfl, le_of_lt hδpos⟩
          have h2 : hR z θ = epsRHSP α ρ ε Φs E H 0 z θ := by
            have h3 : epsRHSP α ρ ε Φs E g (hor n) = epsRHSP α ρ ε Φs E H 0 :=
              Work.FTS.StrongEps.StrongEpsP.epsRHSP_congr
                (W := g) (W' := H) (τ := hor n) (τ' := 0)
                (funext fun z => funext fun θ => (hHsol.1 z θ).symm)
            exact congrFun (congrFun h3 z) θ
          rw [h2]; exact h1
        have hFsol : IsEpsSolP α ρ ε (hor n + δ) Φs E g₀
            (concat g (shiftFam H (hor n)) (hor n)) :=
          Work.FTS.StrongEps.StrongEpsP.SolGlueP hnnonneg hδpos hsol hHsol
        have hFreg : EpsRegP α ρ ε (hor n + δ) (concat g (shiftFam H (hor n)) (hor n)) :=
          Work.FTS.StrongEps.StrongEpsP.RegGlueP (Φs := Φs) (E := E) hnnonneg hδpos
            hreg hHreg hval hderG hderH
        have hFflow : EpsFlowP α ρ ε (hor n + δ) Φs E (concat g (shiftFam H (hor n)) (hor n)) :=
          EpsFlowP.glue hnnonneg hδpos hreg hHreg hflow hHflow (fun z θ => (hHsol.1 z θ).symm)
        have hle : hor (n + 1) ≤ hor n + δ := by
          have hnext : hor (n + 1) = min T (((n : ℝ) + 2) * δ') := by
            show min T ((((n + 1 : ℕ) : ℝ) + 1) * δ') = min T (((n : ℝ) + 2) * δ')
            rw [show (((n + 1 : ℕ) : ℝ) + 1) * δ' = ((n : ℝ) + 2) * δ' by push_cast; ring]
          rw [hnext, hnn]
          refine le_trans (min_le_right _ _) ?_
          have hδ'le : δ' ≤ δ := by rw [hδ'def]; exact min_le_left δ δ₀
          have hmul : ((n : ℝ) + 2) * δ' = ((n : ℝ) + 1) * δ' + δ' := by ring
          rw [hmul]
          linarith
        refine ⟨concat g (shiftFam H (hor n)) (hor n),
          Work.FTS.StrongEps.StrongEpsP.IsEpsSolP.mono hFsol hle, EpsRegP.mono hFreg hle,
          hFflow.mono hle, ?_⟩
        exact hapr hg₀M hsmall₀ (hor (n + 1)) (hhor_pos (n + 1)) (hhor_le (n + 1)) _
          (Work.FTS.StrongEps.StrongEpsP.IsEpsSolP.mono hFsol hle) (EpsRegP.mono hFreg hle)
          (hFflow.mono hle)
  obtain ⟨g, hsol, hreg, -, hbnd⟩ := hpoint N
  have hhorN : hor N = T := by
    show min T ((((N : ℕ) : ℝ) + 1) * δ') = T
    exact min_eq_left (by push_cast; linarith)
  exact ⟨g, by rwa [hhorN] at hsol, by rwa [hhorN] at hreg, by rwa [hhorN] at hbnd⟩

/-- Per-`α` assembly over the flow class (PROVED; copy of `E4R3.EpsUniformMem_of_parts3`). -/
theorem EpsUniformMem_of_partsF {α C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn}
    (hvan : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0)
    (hρ : IsSmoothKernel ρ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K) (h6 : Xn6 α g₀ ≤ K * α ^ 2)
    (hsmall : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioc 0 ε₁,
      Work.FTS.Nonlin.Xn α (Jeps ρ ε g₀) ≤ C₀ * α ^ 2)
    (hd : ∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀)
    (hstep : ∀ ε ∈ Ioc (0 : ℝ) 1, LocalStepPF α ρ ε Φs E C₀)
    (hapr : ∀ T : ℝ, 0 < T → ∃ M : ℝ, K ≤ M ∧ ∃ ε₂ : ℝ, 0 < ε₂ ∧ ε₂ ≤ 1 ∧
      ∀ ε ∈ Ioc 0 ε₂, AprioriPF α ρ ε T Φs E g₀ C₀ M)
    (hdecB : ∀ T : ℝ, 0 < T → ∃ Maj : ℝ → ℝ, AprioriDecayB α ρ T Φs E g₀ C₀ Maj) :
    EpsUniformMem α ρ Φs E g₀ C₀ K := by
  obtain ⟨ε₁, hε₁, hsmallb⟩ := hsmall
  refine ⟨hvan, l12_zero_of_epsDatum ⟨hα, hα1⟩ hρ hd, ?_⟩
  intro T hT
  obtain ⟨M, hKM, ε₂, hε₂, hε₂1, hP⟩ := hapr T hT
  obtain ⟨Maj, hMajint, hMaj⟩ := hdecB T hT
  refine ⟨M, hKM, min ε₁ ε₂, lt_min hε₁ hε₂, Maj, hMajint, ?_⟩
  intro ε hε
  have hεpos : 0 < ε := hε.1
  have hε1' : ε ≤ ε₁ := le_trans hε.2 (min_le_left _ _)
  have hε2' : ε ≤ ε₂ := le_trans hε.2 (min_le_right _ _)
  have hε1 : ε ≤ 1 := le_trans hε2' hε₂1
  have hPz : Pz (Jeps ρ ε g₀) = Jeps ρ ε g₀ :=
    Pz_self_of_l12 (Work.FTS.ClassC.ClassC.l12_zero (hd ε hεpos).2.2)
  have hsmall₀ : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2 := by
    rw [hPz]
    exact hsmallb ε ⟨hεpos, hε1'⟩
  have hg₀M : Xn6 α g₀ ≤ M := by
    have hα2le : α ^ 2 ≤ 1 := pow_le_one₀ hα.le hα1
    calc Xn6 α g₀ ≤ K * α ^ 2 := h6
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hα2le hK
      _ = K := mul_one K
      _ ≤ M := hKM
  obtain ⟨g, hsol, hreg, hbnd⟩ :=
    exists_sol_of_localStepF_aprioriF hT (le_trans hK hKM) hg₀M hsmall₀
      (EpsDatum.toDatumP (hd ε hεpos)) (hstep ε ⟨hεpos, hε1⟩) (hP ε ⟨hεpos, hε2'⟩)
  refine ⟨g, hsol, ?_⟩
  intro τ hτ
  have hdP : EpsDatumP α ρ ε (slice g τ) := hreg.2 τ hτ
  have hCmem : Work.Spaces.HkMem α 7 (slice (JfamP ρ ε g) τ) := hdP.2.2.mem
  have hCsm : Work.FTS.EllipticEst.SmoothOpen (slice (JfamP ρ ε g) τ) := hdP.2.2.reg
  have h4 : Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) τ) :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hCsm hCmem
  exact ⟨hdP.1, h4, hdP.2.1, (hbnd τ hτ).2, (hbnd τ hτ).1, by rw [slice_JfamP]; exact hdP.2.2,
    hreg.1,
    hMaj ε ⟨hεpos, hε1⟩ g hsol hreg (fun σ hσ => (hbnd σ hσ).2) τ hτ⟩

/-- **The E4 statement `EpsE4R4Stmt` (unchanged) from the flow-class chapters** (PROVED). -/
theorem EpsE4R5_of_chapters {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ)
    (hL : ∃ CL : ℝ, ∀ C₀ : ℝ, CL ≤ C₀ → LocalStepChapter5 Ce Cs C₀ ρ)
    (hP : ∃ CP : ℝ, ∀ C₀ : ℝ, CP ≤ C₀ → AprioriChapter5 Ce Cs C₀ ρ)
    (hD : ∃ CD : ℝ, ∀ C₀ : ℝ, CD ≤ C₀ → E4R3.DecayChapter3 Ce Cs C₀ ρ) :
    E4R4.EpsE4R4Stmt Ce Cs ρ := by
  obtain ⟨CL, hL⟩ := hL
  obtain ⟨CP, hP⟩ := hP
  obtain ⟨CD, hD⟩ := hD
  refine ⟨max (max 2 CL) (max CP CD),
    le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_trans (le_max_left 2 CL) (le_max_left _ _)), ?_⟩
  intro C₀ hC₀
  have h2 : 2 ≤ C₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC₀
  have hCL : CL ≤ C₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC₀
  have hCP : CP ≤ C₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC₀
  have hCD : CD ≤ C₀ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC₀
  have hC₀' : 1 < C₀ := lt_of_lt_of_le (by norm_num) h2
  obtain ⟨αL, hαL0, hαL1, hL'⟩ := hL C₀ hCL
  obtain ⟨αP, hαP0, hαP1, hP'⟩ := hP C₀ hCP
  obtain ⟨αD, hαD0, hαD1, hD'⟩ := hD C₀ hCD
  refine ⟨min (min αL αP) (min αD 1), lt_min (lt_min hαL0 hαP0) (lt_min hαD0 one_pos), ?_⟩
  intro α hα
  have hα1 : α ≤ 1 := le_trans hα.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hαL : α ∈ Ioc 0 αL :=
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_left _ _) (min_le_left _ _))⟩
  have hαP : α ∈ Ioc 0 αP :=
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  have hαD : α ∈ Ioc 0 αD :=
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  intro K Φs E g₀ hK hvan hEll hstar hstar6 hml hd h4 h6
  have hdata : E4Data α C₀ K Ce Cs ρ Φs E g₀ :=
    ⟨hK, hvan, hEll, hstar, hml, hd, h4, h6⟩
  exact EpsUniformMem_of_partsF hvan hρ hα.1 hα1 hK h6
    (Jeps_smallBall_one_lt hρ hα.1 hα1 hC₀' hd h4) hd
    (fun ε hε => hL' α hαL hdata ε hε)
    (fun T hT => hP' α hαP hdata hstar6 T hT)
    (fun T hT => hD' α hαD hdata T hT)

end Work.FTS.StrongEps.EpsE4Thr.E4R5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.wlInfMul6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

open MeasureTheory Set Filter

/-- **The `𝒲^{6,∞}`-priced level-six product, in squared-norm form.**  For a coefficient `A` which
is `C^∞` on the open quadrant and `𝒲^{6,∞}` with `WlInf α 6 A ≤ K` (the price carried by the star
fields of `StarPkg6`, e.g. `Rop α (PhiTs α Φs)`, `Vop (PhiTs α Φs)`,
`Uop α (PhiTs α Φs)/sin 2θ` and their `(z+1)/z`-weighted versions) and a datum `P` which is `C^∞`
on the open quadrant and honest in `ℋ⁶`, the level-six energy of the product is linear in the
level-six energy of `P`:
`HkSq α 6 (A·P) ≤ C α^{-1} K² (1 + HkSq α 6 P)`
(the `α^{-1}` is forced by the `(γ-1)^{-1} = 10/α` factor of the majorant; in the application
`K = O(α)` for the star fields, so the net factor is `O(α)`).

Route: the pointwise majorant `H6Rows.WProd6.prod_majorant_winf6`
(`HkIntegrand α 6 (A·P) ≤ (7Cz+49Cm)·(WlInf α 6 A)²·GmajW6 α P`) followed by the integral bound
`H6Rows.WProd6.GmajW6_z_integral_le`
(`∫∫ GmajW6 α P ≤ (1 + 700(1 + 6(γ-1)⁻¹))·HkSq α 6 P`); monotone integration plus `HkSq_nonneg`.
(The membership half is the proved `H6Pair6Aux.HkMem_mul_of_WlInf6`.) -/
theorem wlInfMul6 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A P : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K →
      Work.FTS.EllipticEst.SmoothOpen P → Work.Spaces.HkMem α 6 P →
      Work.Spaces.HkSq α 6 (fun z θ => A z θ * P z θ)
        ≤ C * α ^ (-(1 : ℝ)) * K ^ 2 * (1 + Work.Spaces.HkSq α 6 P) := by
  -- the three slot constants of the `𝒲^{6,∞}`-priced product rule
  obtain ⟨Cz, hCzpos, hZ⟩ := Work.FTS.StrongPersist.H6Rows.wprod6.zslot_le_winf6
  obtain ⟨CB, _hCBpos, hMe⟩ := Work.FTS.StrongPersist.H6Rows.wprod6.dzIter_w_mean_le6
  obtain ⟨Cm, hCmpos, hMx⟩ := Work.FTS.StrongPersist.H6Rows.wprod6.mslot_le_winf6 CB
  set K0 : ℝ := 7 * Cz + 49 * Cm with hK0def
  have hK0pos : 0 < K0 := by rw [hK0def]; linarith
  refine ⟨50000 * K0 + 1, by positivity, ?_⟩
  intro α hα A P K hA hAm hAK hP hPm
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 A := Work.Spaces.WlInf_nonneg α 6 A hAm
  have hKnn : 0 ≤ K := le_trans hWnn hAK
  have hPnn : 0 ≤ Work.Spaces.HkSq α 6 P := Work.Spaces.HkSq_nonneg α 6 P
  -- the pointwise majorant of the `ℋ⁶`-integrand of the product
  have hmajor : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * P z θ) z θ
        ≤ K0 * (Work.Spaces.WlInf α 6 A) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α P z θ := by
    intro z hz θ hθ
    rw [hK0def]
    exact Work.FTS.StrongPersist.H6Rows.WProd6.prod_majorant_winf6 hα0 hα1 hA hAm hP hPm
      hCzpos hCmpos
      (fun i hi z' θ' hz' hθ1 hθ2 => hZ α A P hα0 hα1 hA hAm hP i hi z' θ' hz' hθ1 hθ2)
      (fun I J hI hIJ z' θ' hz' hθ1 hθ2 =>
        hMx α A P hα0 hα1 hA hAm hP hPm
          (fun d hd z'' θ'' hz'' hθ1' hθ2' =>
            hMe α P d hα0 hα1 hP hPm hd z'' θ'' hz'' hθ1' hθ2')
          I J hI hIJ z' θ' hz' hθ1 hθ2)
      z hz θ hθ
  set Kg : ℝ := 1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹) with hKgdef
  -- the angular integral of the majorant at each radius
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => A z θ * P z θ) z θ)
        ≤ (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K0 * (Work.Spaces.WlInf α 6 A) ^ 2)
        * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α P z θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_integrableOn_theta hα0 hα1 hPm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => A z θ * P z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (K0 * (Work.Spaces.WlInf α 6 A) ^ 2)
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α P z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α P z θ)
        ≤ Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z := by
      simpa only [hKgdef] using
        Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_theta_integral_le (α := α) (g := P)
          hα0 hα1 hPm hz
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (fun z θ => A z θ * P z θ) z θ)
        ≤ (K0 * (Work.Spaces.WlInf α 6 A) ^ 2)
            * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α P z θ) := h1
      _ ≤ (K0 * (Work.Spaces.WlInf α 6 A) ^ 2)
            * (Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0pos.le (sq_nonneg _))
      _ = (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z := by ring
  -- monotone integration in `z`
  have hdom : IntegrableOn (fun z => (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg)
      * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z) Work.Spaces.Iz :=
    hPm.2.const_mul _
  have hcongr : (∫ z in Work.Spaces.Iz, (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg)
        * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α P z)
      = (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg) * Work.Spaces.HkSq α 6 P := by
    rw [MeasureTheory.integral_const_mul,
      Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6_z_integral]
  have hstep1 : Work.Spaces.HkSq α 6 (fun z θ => A z θ * P z θ)
      ≤ (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg) * Work.Spaces.HkSq α 6 P := by
    rw [Work.Spaces.HkSq, ← hcongr]
    exact setIntegral_mono_of_nonneg
      (fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      (fun z hz => hbdd z hz) hdom
  -- arithmetic: `K0 * Kg ≤ C α^{-1}`, `|A|²_𝒲 ≤ K²`, `HkSq ≥ 0`
  have hKg_le : Kg ≤ 42701 * α⁻¹ := by
    have hsub : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
    have hinv : (Work.Spaces.gam α - 1)⁻¹ = 10 * α⁻¹ := by
      rw [hsub, inv_div, div_eq_mul_inv]
    rw [hKgdef, hinv]
    have h1 : (1 : ℝ) ≤ α⁻¹ := (one_le_inv₀ hα0).mpr hα1
    nlinarith
  have hCKg : K0 * Kg ≤ (50000 * K0 + 1) * α ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]
    calc K0 * Kg ≤ K0 * (42701 * α⁻¹) := mul_le_mul_of_nonneg_left hKg_le hK0pos.le
      _ = (K0 * 42701) * α⁻¹ := by ring
      _ ≤ (50000 * K0 + 1) * α⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hα0.le)
          nlinarith [hK0pos]
  have hW2K : (Work.Spaces.WlInf α 6 A) ^ 2 ≤ K ^ 2 := by
    have h := mul_self_le_mul_self hWnn hAK
    simpa [sq] using h
  have hfinal : (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg) * Work.Spaces.HkSq α 6 P
      ≤ (50000 * K0 + 1) * α ^ (-(1 : ℝ)) * K ^ 2 * (1 + Work.Spaces.HkSq α 6 P) := by
    have h1 : (Work.Spaces.WlInf α 6 A) ^ 2 * Work.Spaces.HkSq α 6 P
        ≤ K ^ 2 * (1 + Work.Spaces.HkSq α 6 P) :=
      mul_le_mul hW2K (by linarith) hPnn (sq_nonneg K)
    calc (K0 * (Work.Spaces.WlInf α 6 A) ^ 2 * Kg) * Work.Spaces.HkSq α 6 P
        = (K0 * Kg) * ((Work.Spaces.WlInf α 6 A) ^ 2 * Work.Spaces.HkSq α 6 P) := by ring
      _ ≤ ((50000 * K0 + 1) * α ^ (-(1 : ℝ)))
            * (K ^ 2 * (1 + Work.Spaces.HkSq α 6 P)) :=
          mul_le_mul hCKg h1 (mul_nonneg (sq_nonneg _) hPnn)
            (mul_nonneg (by linarith [hK0pos]) (Real.rpow_nonneg hα0.le _))
      _ = (50000 * K0 + 1) * α ^ (-(1 : ℝ)) * K ^ 2
            * (1 + Work.Spaces.HkSq α 6 P) := by ring
  exact le_trans hstep1 hfinal

end Work.FTS.StrongEps.E4R3.RawE6Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `residual_slot_jetsB` — the two residual slots, jets of order `≤ 2`, without the clock

The residual of the modulated stream function at profile exponent `α` is
`Φ̃ = v2_PhiT α Φs E g τ = PhiTil (pExp α) (Ftau (pExp α) (GR α g) τ) (slice (ΦR α Φs E g) τ)`.
This file bounds the order-`≤ 2` mixed jets of the two slots

* `v2_SlotU α Φ̃ = Uop (pExp α) Φ̃ / sin 2θ` and
* `Vop Φ̃`

on the open quadrant, at a single fake time `τ ≥ 0`, by a constant depending only on `τ`.

The argument is the one of `RXT.velVanish2` restricted to these two slots and with the *unused*
clock hypothesis `ClockBd` dropped: split `Φ̃ = Φ̃_* + Φ̃_pert` on the open quadrant
(`v2_phiTil_split`), bound the two halves by `starVop` / `v2_starUop` (`StarPkgo2` with the
explicit fields of the star residual) and by `v2_velPert` (`EllPkgGo` + `EllLimOK3` + `Sol` +
`DynOK'`), and add them with `v2_slot_bound_of_split`.

The main theorem `residual_slot_jetsB` below is the instance `α := a` of the general statement
`v2_slots_jets_aux`.
-/

namespace Work.FTS_StreamBdry.Inputs

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS_RegExport.RXT

/- **The two residual slots, jets of order `≤ 2` bounded** (general profile exponent).  This is
`RXT.velVanish2` for the slots `𝒰/sin 2θ` and `𝒱`, without the (unused) clock hypothesis
`ClockBd`, at a single time `τ ≥ 0`. -/
set_option autoImplicit false in
theorem v2_slots_jets_aux {α Ce C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ τ, 0 ≤ τ → ∃ M : ℝ,
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (v2_SlotU α (v2_PhiT α Φs E g τ)) z θ| ≤ M) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.Construction.Vop (v2_PhiT α Φs E g τ)) z θ| ≤ M) := by
  intro τ hτ
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨CV, hCV0, hCV⟩ := starVop hαG hαG1 hStar
  obtain ⟨CU, hCU0, hCU⟩ := Work.FTS_RegExport.RXT.Slots.v2_starUop hαG hαG1 hStar
  have hS1 : (0 : ℝ) < max τ 1 := lt_of_lt_of_le zero_lt_one (le_max_right τ 1)
  obtain ⟨MP, hMP⟩ := v2_velPert (Φs := Φs) (E := E)
    hα hα13 hEll hEL hSol hOK (max τ 1) hS1
  have hτS : τ ∈ Set.Icc (0 : ℝ) (max τ 1) := ⟨hτ, le_max_left τ 1⟩
  set TOTAL : ℝ := CV * (max Cs 1 * Work.FTS.Regularity.pExp α)
    + CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP with hTOTAL
  have hCVa : 0 ≤ CV * (max Cs 1 * Work.FTS.Regularity.pExp α) :=
    mul_nonneg hCV0 (le_of_lt (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1)) hαG))
  have hCUa : 0 ≤ CU * (max Cs 1 * Work.FTS.Regularity.pExp α) :=
    mul_nonneg hCU0 (le_of_lt (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1)) hαG))
  have key : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotU α (v2_PhiT α Φs E g τ)) z θ| ≤ max TOTAL 0 ∧
      |Work.Spaces.mixed j i (Work.Construction.Vop (v2_PhiT α Φs E g τ)) z θ|
        ≤ max TOTAL 0 := by
    intro j i hji z θ hz hθ hθ2
    -- ## the pointwise split of the stream functions on the quadrant
    have hsplit : ∀ z₁ θ₁ : ℝ, (z₁, θ₁) ∈ Work.FTS.EllipticEst.Q0 →
        v2_PhiT α Φs E g τ z₁ θ₁ = v2_PhiStar α Φs z₁ θ₁ + v2_PhiPert α E g τ z₁ θ₁ :=
      fun z₁ θ₁ hp => v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁ hp
    have hsplitFun : Work.FTS_RegExport.RXR5.AgreeOnQ (v2_PhiT α Φs E g τ)
        (v2_PhiStar α Φs + v2_PhiPert α E g τ) :=
      fun z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
        hsplit z₁ θ₁ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz₁, hθ₁, hθ₁2⟩)
    -- ## regularity of the pieces
    have hPhi3 : ContDiffOn ℝ 3
        (Function.uncurry (slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ))
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs) hEL hStar hOK τ hτ
    have hFK2 : ContDiffOn ℝ 2
        (Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) := by
      obtain ⟨C, _hC0, hC⟩ := Ftau_bounds (Φs := Φs) (E := E) hα hα13 hOK τ hτ
      exact contDiffOn_two_integral_Itheta (φ := Work.Spaces.K) v2_continuousOn_K_Iθ
        (contDiffOn_Ftau_Q0 (Φs := Φs) (E := E) hα hα13 hOK τ hτ)
        (fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => ⟨(hC z₁ θ₁ hz₁ hθ₁ hθ₁2).1, (hC z₁ θ₁ hz₁ hθ₁ hθ₁2).2.1,
          (hC z₁ θ₁ hz₁ hθ₁ hθ₁2).2.2⟩)
    have hL12 : ContDiffOn ℝ 3
        (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) := contDiffOn_three_L12 hFK2
    have hTheta3 : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta
        (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 :=
      velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) hL12
    have hFull3 : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ))
        Work.FTS.EllipticEst.Q0 := hPhi3.sub hTheta3
    have hStar3 : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1.of_le
        (by simp [Work.Stability.smoothOrder])
    have hPert3 : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiPert α E g τ))
        Work.FTS.EllipticEst.Q0 := by
      refine (hFull3.sub hStar3).congr ?_
      intro p hp
      obtain ⟨z₁, θ₁⟩ := p
      simp only [Function.uncurry]
      linarith [hsplit z₁ θ₁ hp]
    have hStarC1 : ContDiffOn ℝ 1 (Function.uncurry (v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 :=
      hStar3.of_le (by norm_num)
    have hPertC1 : ContDiffOn ℝ 1 (Function.uncurry (v2_PhiPert α E g τ))
        Work.FTS.EllipticEst.Q0 := hPert3.of_le (by norm_num)
    -- ## the four slot bounds of the two halves
    have hstarU : ∀ j' i' : ℕ, j' + i' ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ →
        θ₁ < Real.pi / 2 →
        |Work.Spaces.mixed j' i' (v2_SlotU α (v2_PhiStar α Φs)) z₁ θ₁|
          ≤ (CU * (max Cs 1 * Work.FTS.Regularity.pExp α)) * min z₁ 1 :=
      fun j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2 => hCU j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2
    have hstarV : ∀ j' i' : ℕ, j' + i' ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ →
        θ₁ < Real.pi / 2 →
        |Work.Spaces.mixed j' i' (Work.Construction.Vop (v2_PhiStar α Φs)) z₁ θ₁|
          ≤ (CV * (max Cs 1 * Work.FTS.Regularity.pExp α)) * min z₁ 1 :=
      fun j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2 => hCV j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2
    have hpertU : ∀ j' i' : ℕ, j' + i' ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ →
        θ₁ < Real.pi / 2 →
        |Work.Spaces.mixed j' i' (v2_SlotU α (v2_PhiPert α E g τ)) z₁ θ₁| ≤ MP * min z₁ 1 :=
      fun j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
        hMP τ hτS z₁ θ₁ hz₁ hθ₁ hθ₁2 (v2_SlotU α (v2_PhiPert α E g τ))
          (by exact Or.inr (Or.inr rfl)) j' i' hji'
    have hpertV : ∀ j' i' : ℕ, j' + i' ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ →
        θ₁ < Real.pi / 2 →
        |Work.Spaces.mixed j' i' (Work.Construction.Vop (v2_PhiPert α E g τ)) z₁ θ₁|
          ≤ MP * min z₁ 1 :=
      fun j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
        hMP τ hτS z₁ θ₁ hz₁ hθ₁ hθ₁2 (Work.Construction.Vop (v2_PhiPert α E g τ))
          (by exact Or.inr (Or.inl rfl)) j' i' hji'
    -- ## `C²` of the four slot functions
    have hSC2U : ContDiffOn ℝ 2 (Function.uncurry (v2_SlotU α (v2_PhiStar α Φs)))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).2.2.2.2.1.of_le
        (by simp [Work.Stability.smoothOrder])
    have hSC2V : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop (v2_PhiStar α Φs)))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).2.2.1.of_le
        (by simp [Work.Stability.smoothOrder])
    have hPC2U : ContDiffOn ℝ 2 (Function.uncurry (v2_SlotU α (v2_PhiPert α E g τ)))
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_uncurry_div_sin_two (contDiffOn_uncurry_Uop
        (α := Work.FTS.Regularity.pExp α) hPert3)
    have hPC2V : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop (v2_PhiPert α E g τ)))
        Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_Vop hPert3
    -- ## the arithmetic of the `min z 1`-trade-off
    have hmm : (0 : ℝ) ≤ min z 1 := le_min hz.le zero_le_one
    have hM0 : 0 ≤ max TOTAL 0 := le_max_right _ _
    have hstep : ∀ c : ℝ, c ≤ max TOTAL 0 → c * min z 1 ≤ max TOTAL 0 := fun c hc => by
      calc c * min z 1 ≤ max TOTAL 0 * min z 1 := mul_le_mul_of_nonneg_right hc hmm
        _ ≤ max TOTAL 0 * 1 := mul_le_mul_of_nonneg_left (min_le_right z 1) hM0
        _ = max TOTAL 0 := mul_one _
    constructor
    · -- the `𝒰/sin 2θ`-slot
      have heq : Set.EqOn (Function.uncurry (v2_SlotU α (v2_PhiT α Φs E g τ)))
          (Function.uncurry (v2_SlotU α (v2_PhiStar α Φs) + v2_SlotU α (v2_PhiPert α E g τ)))
          Work.FTS.EllipticEst.Q0 := by
        intro p hp
        obtain ⟨z₁, θ₁⟩ := p
        obtain ⟨hz₁, hθ₁, hθ₁2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        simp only [Function.uncurry, Pi.add_apply, v2_SlotU]
        rw [Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
          (h := hsplitFun) (Φ := v2_PhiT α Φs E g τ)
          (Φ' := v2_PhiStar α Φs + v2_PhiPert α E g τ) hz₁ hθ₁ hθ₁2]
        exact v2_uop_div_add_at hStarC1 hPertC1 ⟨hz₁, hθ₁, hθ₁2⟩
      have hres := v2_slot_bound_of_split heq hSC2U hPC2U hstarU hpertU j i hji z θ hz hθ hθ2
      have hA : CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP ≤ max TOTAL 0 := by
        rw [hTOTAL]
        exact le_max_of_le_left (by linarith [hCVa])
      exact le_trans hres (hstep _ hA)
    · -- the `𝒱`-slot
      have heq : Set.EqOn (Function.uncurry (Work.Construction.Vop (v2_PhiT α Φs E g τ)))
          (Function.uncurry (Work.Construction.Vop (v2_PhiStar α Φs)
            + Work.Construction.Vop (v2_PhiPert α E g τ)))
          Work.FTS.EllipticEst.Q0 := by
        intro p hp
        obtain ⟨z₁, θ₁⟩ := p
        obtain ⟨hz₁, hθ₁, hθ₁2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        simp only [Function.uncurry, Pi.add_apply]
        rw [Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ (h := hsplitFun)
          (Φ := v2_PhiT α Φs E g τ)
          (Φ' := v2_PhiStar α Φs + v2_PhiPert α E g τ) hz₁ hθ₁ hθ₁2]
        exact v2_vop_add_at hStarC1 hPertC1 ⟨hz₁, hθ₁, hθ₁2⟩
      have hres := v2_slot_bound_of_split heq hSC2V hPC2V hstarV hpertV j i hji z θ hz hθ hθ2
      have hA : CV * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP ≤ max TOTAL 0 := by
        rw [hTOTAL]
        exact le_max_of_le_left (by linarith [hCUa])
      exact le_trans hres (hstep _ hA)
  exact ⟨max TOTAL 0,
    fun j' i' hji' z θ hz hθ hθ2 => (key j' i' hji' z θ hz hθ hθ2).1,
    fun j' i' hji' z θ hz hθ hθ2 => (key j' i' hji' z θ hz hθ hθ2).2⟩

theorem residual_slot_jetsB {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g) :
    ∀ τ, 0 ≤ τ → ∃ M : ℝ,
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotU a
          (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)) z θ| ≤ M) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.Construction.Vop
          (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)) z θ| ≤ M) :=
  v2_slots_jets_aux ha ha13 hEll hEL hStar hSol hOK

end Work.FTS_StreamBdry.Inputs
end
