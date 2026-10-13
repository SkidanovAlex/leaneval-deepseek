import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceFiber
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.lzeroSlicePoleBound
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SliceLocal.integrableOn_sinCos2_Lzero1
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.H2W.PsiSlices.pzIterLevelIdentities
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H2W.PsiSlices.pzIter_dilate

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.PsiSlices

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary comparison facts for the weight `sinθcos²θ` -/

/-- `θ ↦ sinθcos²θ` is continuous. -/
theorem continuous_sinCos2_psi : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2; fun_prop

/-- **The pole weight is dominated by a constant against `sinθcos²θ`**:
`sinθcos²θ·(θ⁻¹ + (π/2-θ)⁻¹) ≤ 1 + π/2` on `(0, π/2)`.  (The first summand is
`θ⁻¹ sinθ·cos²θ ≤ 1`; the second is `(π/2-θ)⁻¹cos²θ·sinθ ≤ π/2` since
`cosθ = sin(π/2-θ) ≤ π/2-θ`.) -/
theorem sinCos2_mul_poleWeight_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Elliptic.sinCos2 θ * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) ≤ 1 + Real.pi / 2 := by
  obtain ⟨h0, h1⟩ := hθ
  have ht : 0 < Real.pi / 2 - θ := by linarith
  have hcos : 0 ≤ Real.cos θ :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩).le
  have hcos_le : Real.cos θ ≤ Real.pi / 2 - θ := by
    have h : Real.sin (Real.pi / 2 - θ) = Real.cos θ := Real.sin_pi_div_two_sub θ
    rw [← h]; exact Real.sin_le ht.le
  -- first summand
  have hA : Work.Elliptic.sinCos2 θ * θ⁻¹ ≤ 1 := by
    rw [Work.Elliptic.sinCos2]
    have h1' : Real.sin θ * θ⁻¹ ≤ 1 := by
      rw [mul_comm, inv_mul_le_iff₀ h0]; simpa using Real.sin_le h0.le
    calc Real.sin θ * Real.cos θ ^ 2 * θ⁻¹
        = (Real.sin θ * θ⁻¹) * Real.cos θ ^ 2 := by ring
      _ ≤ 1 * 1 := mul_le_mul h1' (Real.cos_sq_le_one θ) (sq_nonneg _) (by norm_num)
      _ = 1 := by ring
  -- second summand
  have hB : Work.Elliptic.sinCos2 θ * (Real.pi / 2 - θ)⁻¹ ≤ Real.pi / 2 := by
    rw [Work.Elliptic.sinCos2]
    have hstep : Real.cos θ ^ 2 * (Real.pi / 2 - θ)⁻¹ ≤ Real.pi / 2 - θ := by
      have h2 : Real.cos θ ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 := pow_le_pow_left₀ hcos hcos_le 2
      calc Real.cos θ ^ 2 * (Real.pi / 2 - θ)⁻¹
          ≤ (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ)⁻¹ :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = Real.pi / 2 - θ := by
            rw [sq, mul_assoc, mul_inv_cancel₀ (ne_of_gt ht), mul_one]
    calc Real.sin θ * Real.cos θ ^ 2 * (Real.pi / 2 - θ)⁻¹
        = Real.sin θ * (Real.cos θ ^ 2 * (Real.pi / 2 - θ)⁻¹) := by ring
      _ ≤ 1 * (Real.pi / 2 - θ) :=
          mul_le_mul (Real.sin_le_one θ) hstep (by positivity) (by norm_num)
      _ ≤ Real.pi / 2 := by linarith
  rw [mul_add]
  linarith

/-- `Iθ` and the open interval `(0, π/2)` agree a.e. -/
theorem restrict_Iθ_eq_restrict_Ioo_psi :
    volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
      (b := Real.pi / 2))).symm

/-- **The one-variable bridge.**  For a slice `u` that is `C^∞` on `(0, π/2)`, if its
`Lzero1`-source is integrable against `sinθcos²θ` on `Iθ`, then so is the slice itself.

Proof: `WeakPureAux.lzeroSlicePoleBound` (a weighted-`L¹` source forces the pole bound
`|u θ| ≤ C(θ⁻¹ + (π/2-θ)⁻¹)`), the comparison `sinCos2_mul_poleWeight_le`, and the finiteness
of the measure of `Iθ`.

Contrapositive (the shape used below): *a slice which is not `sinθcos²θ`-integrable has a
non-`sinθcos²θ`-integrable `Lzero1`-source.* -/
theorem sigmaIntegrable_of_sourceIntegrable {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hsrc : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  obtain ⟨C, hC, hbound⟩ := Work.FTS.EllipticEst.H2W.WeakPureAux.lzeroSlicePoleBound u hu hsrc
  have hfin : (volume.restrict Work.Spaces.Iθ) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Work.Spaces.Iθ,
      Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    ⟨lt_top_iff_ne_top.mpr hfin⟩
  have hcont : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hu 1).continuousOn
  have haesm : AEStronglyMeasurable (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have h1 : AEStronglyMeasurable (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      (hcont.mul continuous_sinCos2_psi.continuousOn).aestronglyMeasurable measurableSet_Ioo
    rw [restrict_Iθ_eq_restrict_Ioo_psi]
    exact h1
  rw [MeasureTheory.IntegrableOn]
  refine MeasureTheory.Integrable.of_bound haesm (C * (1 + Real.pi / 2)) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_mul]
  rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
  · rcases lt_or_eq_of_le hθ.2 with hθ1 | hθ1
    · have hσ : 0 ≤ Work.Elliptic.sinCos2 θ := by
        rw [Work.Elliptic.sinCos2]
        exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith [hθ1]))
          (sq_nonneg _)
      have hb := hbound θ ⟨hθ0, hθ1⟩
      rw [abs_of_nonneg hσ]
      calc |u θ| * Work.Elliptic.sinCos2 θ
          ≤ (C * (1 / θ + 1 / (Real.pi / 2 - θ))) * Work.Elliptic.sinCos2 θ :=
            mul_le_mul_of_nonneg_right hb hσ
        _ = C * (Work.Elliptic.sinCos2 θ * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹)) := by
            rw [one_div, one_div]; ring
        _ ≤ C * (1 + Real.pi / 2) :=
            mul_le_mul_of_nonneg_left (sinCos2_mul_poleWeight_le ⟨hθ0, hθ1⟩) hC
    · rw [hθ1, show Work.Elliptic.sinCos2 (Real.pi / 2) = 0 by
            simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two]]
      simp only [abs_zero, mul_zero]
      exact mul_nonneg hC (by linarith [Real.pi_pos])
  · rw [← hθ0, show Work.Elliptic.sinCos2 0 = 0 by simp [Work.Elliptic.sinCos2]]
    simp only [abs_zero, mul_zero]
    exact mul_nonneg hC (by linarith [Real.pi_pos])

/-- The `θ`-slices of the `z`-derivatives of a datum that is `C^∞` on the open quadrant are
`C^∞` on `(0, π/2)`. -/
theorem contDiffOn_slice_pzIter_psi {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) (m : ℕ) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hΨ
  have hcur := (hso.pzIter m).curry_θ hz
  intro n
  exact (contDiffOn_iff_forall_nat_le.mp hcur) n le_top

/-- `sinθcos²θ ≥ 0` on the closed interval `Iθ`. -/
theorem sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [h1, Real.pi_pos]))
    (sq_nonneg _)

/-- `sinθcos²θ ≥ 0` on the open interval. -/
theorem sinCos2_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 θ :=
  sinCos2_nonneg_Iθ ⟨hθ.1.le, hθ.2.le⟩

/-- Almost every angle in `Iθ` is interior. -/
theorem ae_mem_Ioo_Iθ_psi :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [restrict_Iθ_eq_restrict_Ioo_psi]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- **From `σ·f ∈ L¹` to `σ·|f| ∈ L¹`.**  (`σ = sinθcos²θ` is nonnegative on `Iθ`, so the two
integrands agree a.e.) -/
theorem sigmaIntegrable_abs_of_integrable {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |f θ|)
      Work.Spaces.Iθ := by
  have hσ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ Work.Elliptic.sinCos2 θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact sinCos2_nonneg_Iθ hθ
  refine hf.abs.congr ?_
  filter_upwards [hσ] with θ h
  show |f θ * Work.Elliptic.sinCos2 θ| = Work.Elliptic.sinCos2 θ * |f θ|
  rw [abs_mul, abs_of_nonneg h, mul_comm]

/-! ## The level-`0` identity and propagation -/

/-- **The level-`0` slice equation.**  For a weak-class datum, `0 < z` and `θ ∈ (0, π/2)`, the
operator `Lzero1` applied to the slice `Ψ(z,·)` equals the source plus the two radial derivative
terms. -/
theorem lzero1_slice_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ
      = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ := by
  have hb := h.1 z hz θ hθ.1 hθ.2
  rw [Work.Elliptic.bslOp_apply] at hb
  rw [show Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ = Work.Elliptic.Lzero Ψ z θ by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero (fun θ' => Ψ z θ') z]
    simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Work.Spaces.pth]]
  linarith

/-- **The level-`0` propagation.**  For a weak-class datum and every `0 < z`: if the slice
`Ψ(z,·)` is *not* `sinθcos²θ`-integrable, then so is (at least) one of the two neighbouring
slices `∂_zΨ(z,·)`, `∂_z²Ψ(z,·)`.

This is the one place where the regress of the `z`-levels closes without further input: the
level-`0` identity has no `u_0`-term (`γ_0 = 0`), so its source involves only the source `F`
(whose slice is `sinθcos²θ`-integrable for **every** `z`, by `lzeroSliceFiber`) and the two
neighbouring slices. -/
theorem lzeroSlice_bad_of_bad {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {z : ℝ} (hz : 0 < z) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ →
      ¬ MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∨
      ¬ MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
          Work.Spaces.Iθ := by
  intro hbad
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.2.2.2.2.2.2.1
  have hIoo := ae_mem_Ioo_Iθ_psi
  have hFσ : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |F z θ|)
      Work.Spaces.Iθ := by
    refine sigmaIntegrable_abs_of_integrable ?_
    simpa using Work.FTS.EllipticEst.H2W.lzeroSliceFiber α F Ψ hα hα4 h z hz 0 (by norm_num)
  have h2σ : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 2 Ψ z θ|)
      Work.Spaces.Iθ := sigmaIntegrable_abs_of_integrable h2
  have h1σ : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pz Ψ z θ|)
      Work.Spaces.Iθ := sigmaIntegrable_abs_of_integrable h1
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |F z θ|
        + α ^ 2 * z ^ 2 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 2 Ψ z θ|)
        + |α * (5 + α) * z| * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pz Ψ z θ|))
      Work.Spaces.Iθ :=
    (hFσ.add (h2σ.const_mul (α ^ 2 * z ^ 2))).add (h1σ.const_mul |α * (5 + α) * z|)
  have hu2 : ContDiffOn ℝ 2 (fun θ' : ℝ => Ψ z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (contDiffOn_slice_pzIter_psi hsm hz 0) 2
  have hLcont : ContinuousOn (Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Ψ z θ'))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SliceLocal.continuousOn_Lzero1_of_contDiffOn_two _ hu2
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ
        * |Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h2' : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Elliptic.sinCos2 θ
          * |Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ|)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      ((continuous_sinCos2_psi.continuousOn).mul (hLcont.abs)).aestronglyMeasurable
        measurableSet_Ioo
    rw [restrict_Iθ_eq_restrict_Ioo_psi]
    exact h2'
  have hsrc : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ
        * |Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ|)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hIoo] with θ hθ
    have hid := lzero1_slice_eq h hz hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg_Ioo hθ), abs_abs, hid]
    have hA : Work.Elliptic.sinCos2 θ
          * |F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
              + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ|
        ≤ Work.Elliptic.sinCos2 θ * (|F z θ| + α ^ 2 * z ^ 2
            * |Work.Spaces.pzIter 2 Ψ z θ| + |α * (5 + α) * z| * |Work.Spaces.pz Ψ z θ|) := by
      refine mul_le_mul_of_nonneg_left ?_ (sinCos2_nonneg_Ioo hθ)
      calc |F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
              + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ|
          ≤ |F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ|
              + |(α * (5 + α) * z) * Work.Spaces.pz Ψ z θ| := abs_add_le _ _
        _ ≤ (|F z θ| + |α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ|)
              + |(α * (5 + α) * z) * Work.Spaces.pz Ψ z θ| := by
            linarith [abs_add_le (F z θ) (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)]
        _ = |F z θ| + α ^ 2 * z ^ 2 * |Work.Spaces.pzIter 2 Ψ z θ|
              + |α * (5 + α) * z| * |Work.Spaces.pz Ψ z θ| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 2)]
    calc Work.Elliptic.sinCos2 θ
          * |F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
              + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ|
        ≤ Work.Elliptic.sinCos2 θ * (|F z θ| + α ^ 2 * z ^ 2
            * |Work.Spaces.pzIter 2 Ψ z θ| + |α * (5 + α) * z| * |Work.Spaces.pz Ψ z θ|) := hA
      _ = Work.Elliptic.sinCos2 θ * |F z θ|
            + α ^ 2 * z ^ 2 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 2 Ψ z θ|)
            + |α * (5 + α) * z| * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pz Ψ z θ|) := by ring
  have hgood : MeasureTheory.IntegrableOn (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    sigmaIntegrable_of_sourceIntegrable (u := fun θ' : ℝ => Ψ z θ') (by
      have hh := contDiffOn_slice_pzIter_psi hsm hz 0
      intro n
      simpa only [Work.Spaces.pzIter_zero] using hh n) hsrc
  exact hbad hgood

end

/- Datum-side (`Ψ`-side) angular-endpoint statement of the weak class `WeakPos2`: for a.e. `z > 0`,
each angular slice `θ ↦ ∂_z^m Ψ(z,θ)` with `m ≤ 4` is integrable against `sinθcos²θ` on
`Iθ = [0, π/2]`.

What is and is not being asked.  The weight `sinθcos²θ` vanishes like `t²` at `θ = π/2`
(`t = π/2-θ`) and like `θ` at `θ = 0`, so the conclusion tolerates any growth `o(t^{-3})` at
`π/2` and any growth `o(θ^{-2})` at `0` — in particular the genuine `t^{-1}` pole and even
`t^{-1}log^k(1/t)`.  This is *strictly weaker* than the pole bound
`|∂_z^m Ψ| ≤ C(θ⁻¹ + (π/2-θ)⁻¹)` (which is equivalent to *boundedness* of the slices, see
`H2W/WeakPureAux/NOTES_weakPzPoleBound.md` §0).  It is *not* refuted by the
"mixture"/hidden-`t log t`-mode datum of `H2W/NOTES_pzIterSliceGrowth3Loc.md` §3 (a `t^{-1}`
pole whose `t^{-1}` source coefficient is cancelled by a hidden `t log t` indicial mode): that
datum satisfies this statement.

Why it is needed.  It is the single remaining input of `Work.FTS.EllipticEst.H2W.lzeroSliceL1Ae`
(carried there in-file as `pzIterSliceIntegrableInput`), which combines it with the level
identities `Lzero(∂_z^j Ψ) = ∂_z^j F + α²z²∂_z^{j+2}Ψ + α(5+α)(z∂_z^{j+1}Ψ + j∂_z^j Ψ)` and with
the delivered source-side sibling `H2W.lzeroSliceFiber` (slices of `F`, `i ≤ 2`).  The same
statement is the target of `H2W/pzIterSliceIntegrableUpTo4.lean` (whose source no longer
elaborates: module docstring before the `import` block) and it is *also* implied by the pole
bound `H2W.pzIterPoleBoundUpTo4` (whose final declaration is `sorry`).

Ingredients available in the tree.  `H2W.pzSlice.*` — `LzeroSolSpan` (every solution of
`Lzero1 u = 0` is `a·sin 2θ + b·LzeroSing`), `LzeroSingPole`, `VdpDefs`/`vdpSolves` (the
variation-of-parameters solution with the two bounded kernels), `kernelBound`, `lzeroSingBounds`,
`growthOfMinSource` (pole bound from an honest source), all `sorry`-free; the separable case of
the rigidity `H2W/SeparableCase.lean`; the level-0 weak-class slice growth
`H2W/WeakPureAux/sliceGrowth_of_weakPos0.lean` and its two open conjuncts
`weakPzPoleBound`/`weakPzIter2PoleBound`; `Mine/SliceMomentTaylor`
(`∫ f²·sEta < ∞ ⟹ ∫|f|·sinθcos²θ < ∞`, with the accompanying
`Remov.SourceBound.absIntegrableOfSqMulSeta` variants); and the `D_z`-shift
`H2W/shiftWeakClass.lean` (`WeakPos2 ⟹ WeakPos0 (D_z^j F) (D_z^j Ψ)`, `j ≤ 2`, two `sorry`s in
its Ψ-moment clauses).  Note `m ≤ 3` alone follows from the (in-file `sorry`-free)
`H2W.pzIterSliceGrowth3` pole bound, so the genuinely new content is the top level `m = 4`. -/

/-! ## Where the gap exactly is (analysis, not a proof)

The reductions in this file are *sharp*: the `z`-regress of the tower closes downward from the
levels `3, 4` (using the shifted bridges and the source honesty `F_0, F_1, F_2` supplied by
`H2W.lzeroSliceFiber`), and it cannot be started any lower, because a downward step from level
`j` needs the honesty of the *source* `D_z^j F`, which the class provides only for `j ≤ 2`.
Hence the target is *equivalent* to the `sinθcos²θ`-honesty of the two top levels.

Two facts about the obstruction, verified in this session (recorded for the next stretch; both
are stated as prose, neither is used by any declaration below):

* **Compatible profiles have order `≤ 1`.**  Expand a slice near `θ = π/2` in the pure powers
  `t^{-M}` (`t = π/2-θ`).  The tower
  `Lzero1(∂_z^mΨ) = ∂_z^mF + α²z²∂_z^{m+2}Ψ + α(5+α)z∂_z^{m+1}Ψ` becomes, at the order
  `t^{-(M+2)}`,
  `(1-M²)a_M = (6+R)a_{M+2} - (M+1)∑_{j≥1}d_j a_{M+2j} + f_{M+2}`, `R = α²z²∂_z²+5αz∂_z`,
  where `d_j` are the coefficients of `cot t = ∑d_jt^{2j-1}` and `f` the coefficients of `F`.
  `HkMem α 2 F` (per fibre, at *every* `z`) forces `f_M = 0` for `M ≥ 3`, so for `M ≥ 2` the
  coefficient `a_M` is *determined* by the higher ones through a second-order ODE in `z`; if all
  the higher coefficients vanish then `(1-M²)a_M = 0`, i.e. `a_M = 0` for `M ≥ 2`.  The only
  "free" levels are the resonances `M = ±1` (the two kernel elements `sin 2θ`, `LzeroSing`).
  Consequently a slice of order `≥ 2` is *impossible* with finitely many profiles, and any
  counterexample would have to be an *infinite* cascade, whose coefficient functions `a_M(z)`
  are related by repeated applications of the second-order operator `(6+R)^{-1}` (which is
  *unbounded at `z = 0`*, with kernel spanned by `z^{-2/α}, z^{-3/α}`), while the source's
  `HkMem` (a `z`-integrability of `F` against `w² = z^{-4}(1+z)^4` near `0`) constrains how
  badly the cascade may blow up at `z = 0`.  Deciding whether the cascade can be summed to a
  `C^∞` function is exactly the open "Gevrey/cascade" problem of
  `H2W/WeakPureAux/NOTES_cascade.md`, `H2W/WeakPureAux/NOTES_weakPhiPoleBound.md` §K, §U.
* **The a.e.-relaxation does not help.**  The class and the conclusion are both covariant under
  the radial dilations `z ↦ λz` (`H2W.PsiSlices.weakPos2_dilate`, `H2W.PsiSlices.pzIter_dilate`),
  so the a.e.-statement is *equivalent* to the pointwise statement at the single point `z = 1`
  (`pzIterSliceIntegrable_of_at_one_clean`): a counterexample only has to exist at one `z`, and
  a proof only has to work at one `z`.  In particular no null-set argument can replace the
  endpoint rigidity. -/


end Work.FTS.EllipticEst.H2W.PsiSlices
