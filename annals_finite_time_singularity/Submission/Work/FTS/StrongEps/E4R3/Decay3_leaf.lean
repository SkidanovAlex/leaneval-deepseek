import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Chapters
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.SlotBound
import Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.SlotMaj
import Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.blocks_le_three_fixed
import Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.ellPkg_mono
import Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.starPkg_mono

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
