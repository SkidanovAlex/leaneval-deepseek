import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.H2W.sliceStep4Uniform
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceKit
import Submission.Work.H2W.zeroMeanPoincare
import Submission.Work.FTS.EllipticEst.H2W.weakFirstIter
import Submission.Work.FTS.EllipticEst.H2W.weakHetaBound
import Submission.Work.H2W.slot01Aux
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.DzSliceIdent
import Submission.Work.FTS.EllipticEst.H2W.weakSliceDerivBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

noncomputable section

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- `∂_θ²Ψ(z,·)` in the `deriv`-shape used by `weakSliceDerivBound`. -/
private theorem pthIter_two_eq (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 Ψ z θ = deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ := rfl

/-- `∂_θ³Ψ(z,·)` in the `deriv`-shape used by `sliceStep4Uniform`. -/
private theorem pthIter_three_eq (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 3 Ψ z θ
      = deriv (fun t => deriv (fun t' => deriv (fun θ' => Ψ z θ') t') t) θ := rfl

/-! ## Auxiliary slices

The three lemmas below are the slice inputs of the target, proved here so that the final
estimate depends on nothing unproved. -/

/-- The second `θ`-derivative of the slice `D_zΨ(z,·)` is `z·∂_z∂_θ²Ψ(z,·)`. -/
private theorem deriv_deriv_Dz {Ψ : ℝ → ℝ → ℝ} (hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun θ' => Work.Spaces.Dz Ψ z θ') t) θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ := by
  have h2 : ∀ t : ℝ, deriv (fun θ'' => z * Work.Spaces.pz Ψ z θ'') t
      = z * deriv (fun θ'' => Work.Spaces.pz Ψ z θ'') t := fun t => deriv_const_mul_field z
  have h3 : deriv (fun t => deriv (fun θ'' => z * Work.Spaces.pz Ψ z θ'') t) θ
      = deriv (fun t => z * deriv (fun θ'' => Work.Spaces.pz Ψ z θ'') t) θ := by
    congr 1 with t
    exact h2 t
  show deriv (fun t => deriv (fun θ'' => z * Work.Spaces.pz Ψ z θ'') t) θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
  rw [h3, deriv_const_mul_field z]
  rw [show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ from
    Work.FTS.EllipticEst.remov.pz_pthIter_comm_open Ψ hSΨ 2 z θ hz hθ.1 hθ.2]
  rfl

/-- **The `D_zΨ`-slot.**  For a datum of the weak class and `z > 0`, `(∂_θ(D_zΨ))²σ_γ` is
integrable on `Iθ`. -/
private theorem sliceDzInt {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont := weakSliceContinuousKit α F Ψ hα hα4 h z hz
  have hslots :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
  have hPzSlot : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ) Iθ :=
    hslots.2.2.2.1
  have hDsmooth : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Work.Spaces.Dz Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => contDiffOn_iff_forall_nat_le.mp ((hSΨ.DzIter 1).curry_θ hz) n le_top
  -- the second derivative of the slice is the `(j = 1)`-slot of `∂_θ²Ψ`
  have hD2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Work.Spaces.Dz Ψ z θ') t) θ) ^ 2 * sEta θ) Iθ := by
    have hscaled : MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ) Iθ := by
      refine (hPzSlot.const_mul (z ^ 2)).congr ?_
      filter_upwards with θ
      ring
    refine hscaled.congr ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [deriv_deriv_Dz hSΨ hz hθ]
  obtain ⟨hbd1, -⟩ := Work.FTS.EllipticEst.H2W.weakSliceDerivBound
    (fun θ => Work.Spaces.Dz Ψ z θ) hDsmooth hcont.2 (dz_zero_at_zero h z)
    (dz_zero_at_pi_half h z) hD2
  have hσint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ :=
    (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := 2 - Work.Spaces.gam α)
      (by rw [Work.Spaces.gam]; linarith)).1
  refine Integrable.mono'
    (hσint.const_mul ((∫ θ in Iθ,
          (deriv (fun t => deriv (fun θ' => Work.Spaces.Dz Ψ z θ') t) θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) ?_ ?_
  · refine (((measurable_deriv (fun θ' => Work.Spaces.Dz Ψ z θ')).pow_const 2).mul
      ((Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)).pow_const _)
      ).aestronglyMeasurable
  · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    have hs : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
      sig_nonneg α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hs)]
    exact mul_le_mul_of_nonneg_right (hbd1 θ hθ) hs

/-- **The lower-order slices.**  For a datum of the weak class and `z > 0`, the slices `∂_θΨ`
and `Ψ` of `z` are square-integrable on `Iθ` and their squares are dominated by the
`η`-weighted square of `∂_θ²Ψ`. -/
private theorem sliceLowerOrder {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => Ψ z θ') θ) ^ 2) Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Iθ ∧
    (∫ θ in Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2)
        ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) ∧
    (∫ θ in Iθ, (Ψ z θ) ^ 2) ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont := weakSliceContinuousKit α F Ψ hα hα4 h z hz
  have hslots :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
  have hT2s : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2 * sEta θ) Iθ := by
    have h := hslots.2.2.1
    simp only [pthIter_two_eq] at h
    exact h
  have hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => contDiffOn_iff_forall_nat_le.mp (hSΨ.curry_θ hz) n le_top
  obtain ⟨hbd1, hbd2⟩ := Work.FTS.EllipticEst.H2W.weakSliceDerivBound (fun θ => Ψ z θ) hsmooth
    hcont.1 (h.zero z) (h.pi_half z) hT2s
  -- the `η`-slot in the shape of the statement
  have hT2b : (∫ θ in Iθ, (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2 * sEta θ)
      = (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := rfl
  have hT2nn : 0 ≤ (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hB0nn : 0 ≤ (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ' hθ) _)
  have hB0le : (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) ≤ Real.pi / 2 :=
    (Work.FTS.EllipticEst.integrableOn_sin_two_rpow Work.Spaces.eta_nonneg).2
  have hvol : (volume : Measure ℝ) Iθ ≠ ⊤ := Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top
  have hvolreal : (volume : Measure ℝ).real Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def,
      show (volume : Measure ℝ) Iθ = ENNReal.ofReal (Real.pi / 2) from by
        rw [show Iθ = Set.Icc 0 (Real.pi / 2) from rfl, Real.volume_Icc, sub_zero],
      ENNReal.toReal_ofReal (by positivity)]
  have hconstval (c : ℝ) : (∫ _ in Iθ, c) = (Real.pi / 2) * c := by
    rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul]
  -- ## the two pointwise bounds on `(0,π/2)`
  have hpt1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv (fun θ' => Ψ z θ') θ) ^ 2
        ≤ (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
    intro θ hθ
    have h := hbd1 θ hθ
    rwa [hT2b] at h
  have hpt2 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Ψ z θ| ≤ (Real.pi / 4) * Real.sin (2 * θ)
        * Real.sqrt ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by
    intro θ hθ
    have h := hbd2 θ hθ
    rwa [hT2b] at h
  -- ## `∫(u')²`
  have hC1int : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => Ψ z θ') θ) ^ 2) Iθ := by
    refine Integrable.mono'
      (g := fun _ : ℝ => |(∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))|)
      (integrableOn_const (C := |(∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))|) hvol) ?_ ?_
    · exact ((measurable_deriv (fun θ' => Ψ z θ')).pow_const 2).aestronglyMeasurable
    · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact le_trans (hpt1 θ hθ) (le_abs_self _)
  have hC1le : (∫ θ in Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2)
      ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := by
    have hle : (∫ θ in Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2)
        ≤ (Real.pi / 2) * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by
      rw [← hconstval ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))]
      refine integral_mono_ae hC1int
        (integrableOn_const (C := ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) hvol) ?_
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      exact hpt1 θ hθ
    have h2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    have hπ : (Real.pi / 2) ^ 2 ≤ 4 := by nlinarith [h2]
    have hstep1 : (Real.pi / 2) * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))
        ≤ (Real.pi / 2) * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (Real.pi / 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hB0le hT2nn) (by positivity)
    have hstep2 : (Real.pi / 2) * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (Real.pi / 2))
        = (Real.pi / 2) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := by
      ring
    have hstep3 : (Real.pi / 2) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) :=
      mul_le_mul_of_nonneg_right hπ hT2nn
    linarith [hle, hstep1, hstep2, hstep3]
  -- ## `∫u²`
  have hpt3 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Ψ z θ) ^ 2
        ≤ ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
    intro θ hθ
    have hsI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ' hsI
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hnn : 0 ≤ (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := mul_nonneg hT2nn hB0nn
    have h1 : (Ψ z θ) ^ 2
        ≤ ((Real.pi / 4) * Real.sin (2 * θ)
            * Real.sqrt ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
              * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (Ψ z θ)) (hpt2 θ hθ) 2
      simpa only [sq_abs] using h
    have h2 : ((Real.pi / 4) * Real.sin (2 * θ)
          * Real.sqrt ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) ^ 2
        = ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hnn]
      ring
    have heta0 : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h3 : Real.sin (2 * θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
      have hz : (2 : ℝ) - Work.Spaces.eta ≤ 2 := by linarith [heta0]
      rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2]
      exact Real.rpow_le_rpow_of_exponent_ge hspos hs1 hz
    have h4 : 0 ≤ (Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) :=
      mul_nonneg (by positivity) (mul_nonneg hT2nn hB0nn)
    calc (Ψ z θ) ^ 2
        ≤ ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ 2 := by
          rw [h2] at h1
          exact h1
      _ ≤ ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) :=
          mul_le_mul_of_nonneg_left h3 h4
  have hsint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) Iθ :=
    (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := 2 - Work.Spaces.eta)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hC0int : MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Iθ := by
    refine Integrable.mono'
      (g := fun θ => ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
      (hsint.const_mul ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))) ?_ ?_
    · exact AEStronglyMeasurable.pow (hcont.1.aestronglyMeasurable measurableSet_Icc) 2
    · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt3 θ hθ
  have hC0le : (∫ θ in Iθ, (Ψ z θ) ^ 2)
      ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := by
    have hsle : (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) ≤ Real.pi / 2 :=
      (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := 2 - Work.Spaces.eta)
        (by rw [Work.Spaces.eta]; norm_num)).2
    have hmono : (∫ θ in Iθ, (Ψ z θ) ^ 2)
        ≤ ∫ θ in Iθ, ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
      refine integral_mono_ae hC0int (hsint.const_mul _) ?_
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      exact hpt3 θ hθ
    rw [MeasureTheory.integral_const_mul] at hmono
    have h2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    have h4 : Real.pi ^ 4 ≤ 256 := by nlinarith [h2, Real.pi_pos]
    have hπ : (Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2) ≤ 4 := by
      have hval : (Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2) = Real.pi ^ 4 / 64 := by ring
      rw [hval]
      linarith
    have hstep1 : ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        ≤ ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (Real.pi / 2)))
          * (Real.pi / 2) := by
      have hsnn : 0 ≤ (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) :=
        setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
          Real.rpow_nonneg (sin_two_nonneg_Iθ' hθ) _)
      refine mul_le_mul ?_ hsle hsnn (by positivity)
      have h4 : 0 ≤ (Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (Real.pi / 2)) := by
        have hb : 0 ≤ (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (Real.pi / 2) := mul_nonneg hT2nn (by positivity)
        positivity
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB0le hT2nn) (by positivity)
    have hstep2 : ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (Real.pi / 2))) * (Real.pi / 2)
        = ((Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2))
          * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := by
      ring
    have hstep3 : ((Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2))
          * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) :=
      mul_le_mul_of_nonneg_right hπ hT2nn
    linarith [hmono, hstep1, hstep2, hstep3]
  exact ⟨hC1int, hC0int, hC1le, hC0le⟩

/-- **The source slot.**  `∂_θ(Lzero1 u)` for the slice `u = Ψ(z,·)` is dominated by the three
source slots, `(a+b+c)² ≤ 3(a²+b²+c²)` with `Lzero1 u = F + α²z²∂_z²Ψ + α(5+α)D_zΨ`. -/
private theorem slot01SourceBound {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z)
    (hF : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth F z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ)
    (hA : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1
        (fun t => Ψ z t) θ') θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ ∧
      (∫ θ in Iθ, (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ 3 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the slice equation `Lzero1 u = F + α²z²∂_z²Ψ + α(5+α)D_zΨ` on the open interval
  have hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
        = F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α)) * Work.Spaces.Dz Ψ z θ := by
    intro θ hθ
    have hlt := Work.H2W.Lzero1_slice_eq (α := α) (G := F) (Φ := Ψ) (z := z) (θ := θ)
      (fun θ' h1 h2 => h.eq z hz θ' h1 h2) hθ
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hlt
  -- differentiability on the open interval of the three summands
  have hsm (G : ℝ → ℝ → ℝ) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
      ContDiffOn ℝ 2 (fun θ => G z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_iff_forall_nat_le.mp (hG.curry_θ hz) 2 le_top
  have hdF : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      DifferentiableAt ℝ (fun θ' => F z θ') θ := by
    intro θ hθ
    exact ((hsm F (smoothOpen_source h)).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hdA : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      DifferentiableAt ℝ (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ := by
    intro θ hθ
    have hcd : ContDiffOn ℝ 2 (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
        (Set.Ioo 0 (Real.pi / 2)) :=
      ContDiffOn.mul contDiffOn_const
        (contDiffOn_iff_forall_nat_le.mp ((hSΨ.pzIter 2).curry_θ hz) 2 le_top)
    exact (hcd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hdB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      DifferentiableAt ℝ (fun θ' => Work.Spaces.Dz Ψ z θ') θ := by
    intro θ hθ
    exact (((hSΨ.DzIter 1).curry_θ hz).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  -- the derivative of the slice source
  have hderiv_eq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ
        = Work.Spaces.pth F z θ + α ^ 2 * deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
          + (α * (5 + α)) * deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ := by
    intro θ hθ
    have hfun : (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ')
        =ᶠ[𝓝 θ] (fun θ' => F z θ' + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
            + (α * (5 + α)) * Work.Spaces.Dz Ψ z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
      exact hode x hx
    have hder : HasDerivAt (fun θ' => F z θ' + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
        + (α * (5 + α)) * Work.Spaces.Dz Ψ z θ')
        (Work.Spaces.pth F z θ + α ^ 2 * deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
          + (α * (5 + α)) * deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) θ :=
      ((((hdF θ hθ).hasDerivAt).add (((hdA θ hθ).hasDerivAt).const_mul (α ^ 2))).add
        (((hdB θ hθ).hasDerivAt).const_mul (α * (5 + α))))
    rw [hfun.deriv_eq, hder.deriv]
  -- the pointwise bound
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        ≤ 3 * ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
    intro θ hθ
    have hs : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
      sig_nonneg α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsq := sq_add_three_le (Work.Spaces.pth F z θ)
      (α ^ 2 * deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ)
      ((α * (5 + α)) * deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ)
    rw [hderiv_eq θ hθ]
    calc (Work.Spaces.pth F z θ + α ^ 2 * deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
            + (α * (5 + α)) * deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        ≤ 3 * ((Work.Spaces.pth F z θ) ^ 2
              + (α ^ 2 * deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              + ((α * (5 + α)) * deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
          mul_le_mul_of_nonneg_right hsq hs
      _ = 3 * ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by ring
  -- integrability and the integral bound
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => 3 * ((Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) Iθ :=
    (((hF.add (hA.const_mul (α ^ 4))).add (hB.const_mul ((α * (5 + α)) ^ 2)))).const_mul 3
  constructor
  · refine Integrable.mono' hdom ?_ ?_
    · refine ((measurable_deriv (fun θ' => Work.FTS.EllipticEst.Lzero1
          (fun t => Ψ z t) θ')).pow_const 2).mul
        ((Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)).pow_const _)
        |>.aestronglyMeasurable
    · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      have hnn : 0 ≤ 3 * ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
        have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
          sig_nonneg α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        positivity
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (sig_nonneg α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))]
      exact hpt θ hθ
  · have hmono : (∫ θ in Iθ, (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ ∫ θ in Iθ, 3 * ((Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
      refine integral_mono_of_nonneg ?_ hdom ?_
      · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
        exact mul_nonneg (sq_nonneg _) (sig_nonneg α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
        exact hpt θ hθ
    -- decompose the integral of the dominating function
    have hAint : MeasureTheory.IntegrableOn
        (fun θ => α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) Iθ := hA.const_mul (α ^ 4)
    have hBint : MeasureTheory.IntegrableOn
        (fun θ => (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) Iθ := hB.const_mul ((α * (5 + α)) ^ 2)
    have hABint : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) Iθ :=
      hF.add hAint
    have hIntDom : (∫ θ in Iθ, 3 * ((Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))))
        = 3 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
      have hAB : (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
          = (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
            + (∫ θ in Iθ, (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) :=
        MeasureTheory.integral_add
          (f := fun θ => (Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
          (g := fun θ => (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) hABint hBint
      have hAsplit : (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
          = (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
        have h := MeasureTheory.integral_add
          (f := fun θ => (Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          (g := fun θ => α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) hF hAint
        rw [MeasureTheory.integral_const_mul] at h
        exact h
      have hCsplit : (∫ θ in Iθ, (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
          = (α * (5 + α)) ^ 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
        MeasureTheory.integral_const_mul ((α * (5 + α)) ^ 2) _
      calc (∫ θ in Iθ, 3 * ((Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))))
          = 3 * (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) :=
            MeasureTheory.integral_const_mul 3 _
        _ = 3 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
            + (∫ θ in Iθ, (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) := by rw [hAB]
        _ = 3 * (((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
            + (α * (5 + α)) ^ 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by rw [hAsplit, hCsplit]
        _ = 3 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by ring
    exact le_trans hmono (le_of_eq hIntDom)

theorem slot01SliceBound : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ → ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ K * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ,
                (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Work.Spaces.Iθ,
                (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
  obtain ⟨Cs, hCs0, hCs⟩ := sliceStep4Uniform
  refine ⟨Cs * 16, by positivity, fun α F Ψ hα hα4 h z hz => ?_⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  -- ## the range of `γ`
  have hgam1 : 1 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hgam32 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  -- ## the slice data
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont := weakSliceContinuousKit α F Ψ hα hα4 h z hz
  have hsliceSmooth : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => contDiffOn_iff_forall_nat_le.mp (hSΨ.curry_θ hz) n le_top
  have hslots :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
  -- ## the five integrability inputs of `sliceStep4Uniform`
  -- (1) the left-hand side
  have hL : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ := by
    have hh := integrableOn_pth_mixed01 (f := Work.Spaces.pthIter 2 Ψ) hα hα4 h.memB hz
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hh
  -- (2) the `η`-slot `∫(u'')²sEta`
  have hT2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
      * sEta θ) Iθ := hslots.2.2.1
  -- (3), (4) the lower-order terms `u'`, `u`
  obtain ⟨hC1int, hC0int, hC1le, hC0le⟩ := sliceLowerOrder hα hα4 h hz
  -- (5) the three source slots and the source itself
  have hT1 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth F z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ :=
    integrableOn_pth_mixed01 hα hα4 h.memF hz
  have hT3 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ :=
    integrableOn_pth_mixed01 (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hα hα4
      h.memA hz
  have hT4 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ := sliceDzInt hα hα4 h hz
  obtain ⟨hDint, hDle⟩ := slot01SourceBound hα hα4 h hz hT1 hT3 hT4
  -- ## the one-dimensional Step 4 on the slice
  have hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
        = (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ := fun _ _ => rfl
  have hmain := hCs (Work.Spaces.gam α) (fun θ => Ψ z θ)
    (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ')
    hgam1 hgam32 (hsliceSmooth 3) hcont.1 (h.zero z) (h.pi_half z) hode hL hT2 hC1int hC0int hDint
  -- ## nonnegativity of the four slots
  have hT1nn : 0 ≤ (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (sig_nonneg α hθ))
  have hT2nn : 0 ≤ (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hT3nn : 0 ≤ (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (sig_nonneg α hθ))
  have hT4nn : 0 ≤ (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (sig_nonneg α hθ))
  -- ## absorption of the coefficients
  have hα4le : α ^ 4 ≤ 1 := by nlinarith [hα, hα4]
  have hcoefle : (α * (5 + α)) ^ 2 ≤ 2 := by
    have h5 : 5 + α ≤ 21 / 4 := by linarith
    have hb : α * (5 + α) ≤ 1 / 4 * (21 / 4) :=
      mul_le_mul hα4 h5 (by linarith) (by norm_num)
    have hnn : 0 ≤ α * (5 + α) := by positivity
    calc (α * (5 + α)) ^ 2 ≤ (1 / 4 * (21 / 4)) ^ 2 := pow_le_pow_left₀ hnn hb 2
      _ ≤ 2 := by norm_num
  have hD' : (∫ θ in Iθ, (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ 3 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
    have h1 : α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) ≤
        (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
      mul_le_of_le_one_left hT3nn hα4le
    have h2 : (α * (5 + α)) ^ 2 * (∫ θ in Iθ,
          (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) ≤
        2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
      mul_le_mul_of_nonneg_right hcoefle hT4nn
    linarith [hDle, h1, h2]
  -- ## assembly
  have hstep : (∫ θ in Iθ, (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        + (∫ θ in Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2)
        + (∫ θ in Iθ, (Ψ z θ) ^ 2)
      ≤ 3 * (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 9 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          + 3 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 6 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
    linarith [hD', hC1le, hC0le]
  have hfactor : 3 * (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 9 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          + 3 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 6 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ 16 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
    linarith [hT1nn, hT2nn, hT3nn, hT4nn]
  have hfinal : (∫ θ in Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ Cs * (16 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) := by
    have h1 : Cs * ((∫ θ in Iθ, (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          + (∫ θ in Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2)
          + (∫ θ in Iθ, (Ψ z θ) ^ 2))
        ≤ Cs * (16 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) :=
      mul_le_mul_of_nonneg_left (le_trans hstep hfactor) (le_of_lt hCs0)
    exact le_trans hmain h1
  calc (∫ θ in Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ Cs * (16 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) := hfinal
    _ = Cs * 16 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by ring

end

end Work.H2W
