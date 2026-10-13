import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.ReductionsA

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

/-! ## The `D_z`-shifted propagations

The same argument applies verbatim to every `D_z`-shift of the datum: `(D_z^j F, D_z^j Ψ)` solves
the same equation on the open quadrant (`TT.bslOp_DzIter_eq`), and the shifted source slice is
`sinθcos²θ`-integrable for `j ≤ 2` (`DzIter_source_sigmaIntegrable`, from `lzeroSliceFiber` and
the triangular relation `D_z^j = ∑ z^i ∂_z^i`). -/

/-- The source-side slices of the `D_z`-shifts of a weak-class datum are `sinθcos²θ`-integrable
for `j ≤ 2`. -/
theorem DzIter_source_sigmaIntegrable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {z : ℝ} (hz : 0 < z) (j : ℕ) (hj : j ≤ 2) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.DzIter j F z θ
      * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hD1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.DzIter 1 F z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.H2W.lzeroSliceFiber α F Ψ hα hα4 h z hz 1
        (by norm_num)).const_mul z
      |>.congr (Filter.Eventually.of_forall fun θ => by
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
          Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
        ring)
  interval_cases j
  · simpa using Work.FTS.EllipticEst.H2W.lzeroSliceFiber α F Ψ hα hα4 h z hz 0 (by norm_num)
  · exact hD1
  · have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.2.2.2.2.2.2.1
    have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
      Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
        (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen (α := α)
          (Work.FTS.EllipticEst.smoothOpen_of_forall hsm))
        (fun z' θ hz' hθ0 hθ1 => h.1 z' hz' θ hθ0 hθ1)
    have h2 := Work.FTS.EllipticEst.H2W.lzeroSliceFiber α F Ψ hα hα4 h z hz 2 (by norm_num)
    have hae : (fun θ : ℝ => Work.Spaces.DzIter 2 F z θ * Work.Elliptic.sinCos2 θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        fun θ : ℝ => Work.Spaces.DzIter 1 F z θ * Work.Elliptic.sinCos2 θ
          + z ^ 2 * (Work.Spaces.pzIter 2 F z θ * Work.Elliptic.sinCos2 θ) := by
      filter_upwards [ae_mem_Ioo_Iθ_psi] with θ hθ
      rw [Work.FTS.EllipticEst.H2W.lzsf_DzIter_two_eq F
        (hFsm.hasDerivAt_slice_pzIter 1 hθ hz)]
      ring
    have hsum : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.DzIter 1 F z θ * Work.Elliptic.sinCos2 θ
          + z ^ 2 * (Work.Spaces.pzIter 2 F z θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ := by
      have h : MeasureTheory.IntegrableOn
          ((fun θ : ℝ => Work.Spaces.DzIter 1 F z θ * Work.Elliptic.sinCos2 θ)
            + fun θ : ℝ => z ^ 2 * (Work.Spaces.pzIter 2 F z θ * Work.Elliptic.sinCos2 θ))
          Work.Spaces.Iθ := hD1.add (h2.const_mul (z ^ 2))
      convert h using 1
    exact hsum.congr hae.symm

/-- **The `D_z`-shifted level-`0` slice equation.** -/
theorem lzero1_DzIter_slice_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (j : ℕ) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.DzIter j Ψ z θ') θ
      = Work.Spaces.DzIter j F z θ
        + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
        + (α * (5 + α) * z) * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ := by
  have heq := Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ j h.2.2.2.2.2.2.1 h.1
    z hz θ hθ.1 hθ.2
  rw [Work.Elliptic.bslOp_apply] at heq
  rw [show Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.DzIter j Ψ z θ') θ
      = Work.Elliptic.Lzero (Work.Spaces.DzIter j Ψ) z θ by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero (fun θ' => Work.Spaces.DzIter j Ψ z θ') z]
    simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Work.Spaces.pth]]
  linarith

/-- **The `D_z`-shifted level-`0` propagation.**  For a weak-class datum, `0 < z` and `j ≤ 2`:
if the `j`-th shifted slice `D_z^j Ψ(z,·)` is not `sinθcos²θ`-integrable, then so is one of its
two `z`-derivative neighbours. -/
theorem DzIter_bad_of_bad {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {z : ℝ} (hz : 0 < z) (j : ℕ) (hj : j ≤ 2) :
    ¬ MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ →
      ¬ MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ
            * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∨
      ¬ MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro hbad
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.2.2.2.2.2.2.1
  have hIoo := ae_mem_Ioo_Iθ_psi
  have hFσ : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|)
      Work.Spaces.Iθ := sigmaIntegrable_abs_of_integrable
    (DzIter_source_sigmaIntegrable hα hα4 h hz j hj)
  have h2σ : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ
        * |Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ|)
      Work.Spaces.Iθ := sigmaIntegrable_abs_of_integrable h2
  have h1σ : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ
        * |Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ|)
      Work.Spaces.Iθ := sigmaIntegrable_abs_of_integrable h1
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|
        + α ^ 2 * z ^ 2 * (Work.Elliptic.sinCos2 θ
            * |Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ|)
        + |α * (5 + α) * z| * (Work.Elliptic.sinCos2 θ
            * |Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ|))
      Work.Spaces.Iθ :=
    (hFσ.add (h2σ.const_mul (α ^ 2 * z ^ 2))).add (h1σ.const_mul |α * (5 + α) * z|)
  have huD : ContDiffOn ℝ 2
      (fun θ' : ℝ => Work.Spaces.DzIter j Ψ z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hcur := ((Work.FTS.EllipticEst.smoothOpen_of_forall hsm).DzIter j).curry_θ hz
    exact (contDiffOn_iff_forall_nat_le.mp hcur) 2 le_top
  have hLcont : ContinuousOn
      (Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.DzIter j Ψ z θ'))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SliceLocal.continuousOn_Lzero1_of_contDiffOn_two _ huD
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ
        * |Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.DzIter j Ψ z θ') θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h2' : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Elliptic.sinCos2 θ
          * |Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.DzIter j Ψ z θ') θ|)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      ((continuous_sinCos2_psi.continuousOn).mul (hLcont.abs)).aestronglyMeasurable
        measurableSet_Ioo
    rw [restrict_Iθ_eq_restrict_Ioo_psi]
    exact h2'
  have hsrc : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ
        * |Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.DzIter j Ψ z θ') θ|)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hIoo] with θ hθ
    have hid := lzero1_DzIter_slice_eq h hz hθ j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg_Ioo hθ), abs_abs, hid]
    have hA : Work.Elliptic.sinCos2 θ
          * |Work.Spaces.DzIter j F z θ + α ^ 2 * z ^ 2
              * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
              + (α * (5 + α) * z) * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ|
        ≤ Work.Elliptic.sinCos2 θ * (|Work.Spaces.DzIter j F z θ| + α ^ 2 * z ^ 2
            * |Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ|
            + |α * (5 + α) * z| * |Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ|) := by
      refine mul_le_mul_of_nonneg_left ?_ (sinCos2_nonneg_Ioo hθ)
      calc |Work.Spaces.DzIter j F z θ + α ^ 2 * z ^ 2
              * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
              + (α * (5 + α) * z) * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ|
          ≤ |Work.Spaces.DzIter j F z θ + α ^ 2 * z ^ 2
                * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ|
              + |(α * (5 + α) * z) * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ| :=
            abs_add_le _ _
        _ ≤ (|Work.Spaces.DzIter j F z θ| + |α ^ 2 * z ^ 2
                * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ|)
              + |(α * (5 + α) * z) * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ| := by
            linarith [abs_add_le (Work.Spaces.DzIter j F z θ) (α ^ 2 * z ^ 2
              * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ)]
        _ = |Work.Spaces.DzIter j F z θ| + α ^ 2 * z ^ 2
              * |Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ|
              + |α * (5 + α) * z| * |Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 2)]
    calc Work.Elliptic.sinCos2 θ
          * |Work.Spaces.DzIter j F z θ + α ^ 2 * z ^ 2
              * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
              + (α * (5 + α) * z) * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ|
        ≤ Work.Elliptic.sinCos2 θ * (|Work.Spaces.DzIter j F z θ| + α ^ 2 * z ^ 2
            * |Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ|
            + |α * (5 + α) * z| * |Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ|) := hA
      _ = Work.Elliptic.sinCos2 θ * |Work.Spaces.DzIter j F z θ|
            + α ^ 2 * z ^ 2 * (Work.Elliptic.sinCos2 θ
              * |Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ|)
            + |α * (5 + α) * z| * (Work.Elliptic.sinCos2 θ
              * |Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ|) := by ring
  have hgood : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    sigmaIntegrable_of_sourceIntegrable (u := fun θ' : ℝ => Work.Spaces.DzIter j Ψ z θ') (by
      have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
        Work.FTS.EllipticEst.smoothOpen_of_forall hsm
      have hcur := (hso.DzIter j).curry_θ hz
      intro n
      exact (contDiffOn_iff_forall_nat_le.mp hcur) n le_top) hsrc
  exact hbad hgood

/-! ## The assembly: the target reduces to the *source honesty* of the first two levels

Combining the one-variable bridge with the level identities (`H2W.PsiSlices.pzIterLevelIdentities`)
and the source-side slices (`lzeroSliceFiber`) gives the exact reduction

  `pzIterSliceIntegrable`  ⟸  for a.e. `z`, `Lzero1(∂_zΨ(z,·))` and `Lzero1(∂_z²Ψ(z,·))` are
  `sinθcos²θ`-integrable,

where the hypothesis is the *datum-side endpoint rigidity* of the weak class (the chapter's
documented bottleneck): the level-`m` identity has a `γ_m·∂_z^mΨ` term, so the regress of the
`z`-levels can only be closed by controlling the sources themselves.  Everything else is proved
here. -/

/-- **The target from the source honesty of the two lowest `z`-levels.** -/
theorem pzIterSliceIntegrable_of_sourceHonest
    (hsrc : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ
            * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) ∧
        (MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') θ
            * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∀ m : ℕ, m ≤ 4 →
          MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h
  have hsm := h.2.2.2.2.2.2.1
  obtain ⟨hId1, hId2⟩ := Work.H2W.PsiSlices.pzIterLevelIdentities α F Ψ hα hα4 h
  have hFm : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ m ≤ 2, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pzIter m F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun z hz m hm => Work.FTS.EllipticEst.H2W.lzeroSliceFiber α F Ψ hα hα4 h z hz m hm
  -- dividing out a nonzero constant factor
  have hhelper : ∀ (c : ℝ) (g : ℝ → ℝ), c ≠ 0 →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (c * g θ) * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => g θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    intro c g hc hg
    have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
    refine (hg.const_mul c⁻¹).congr (Filter.Eventually.of_forall fun θ => ?_)
    show c⁻¹ * ((c * g θ) * Work.Elliptic.sinCos2 θ) = g θ * Work.Elliptic.sinCos2 θ
    calc c⁻¹ * ((c * g θ) * Work.Elliptic.sinCos2 θ)
        = (c⁻¹ * c) * (g θ * Work.Elliptic.sinCos2 θ) := by ring
      _ = g θ * Work.Elliptic.sinCos2 θ := by rw [hcc, one_mul]
  filter_upwards [hsrc α F Ψ hα hα4 h, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hzs hz
  have hz0 : 0 < z := hz
  -- levels 1 and 2, from the bridge
  have h1abs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ
        * |Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ|)
      Work.Spaces.Iθ := sigmaIntegrable_abs_of_integrable hzs.1
  have h2abs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ
        * |Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') θ|)
      Work.Spaces.Iθ := sigmaIntegrable_abs_of_integrable hzs.2
  have hu1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    sigmaIntegrable_of_sourceIntegrable (u := fun θ' => Work.Spaces.pzIter 1 Ψ z θ')
      (contDiffOn_slice_pzIter_psi hsm hz0 1) h1abs
  have hu2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    sigmaIntegrable_of_sourceIntegrable (u := fun θ' => Work.Spaces.pzIter 2 Ψ z θ')
      (contDiffOn_slice_pzIter_psi hsm hz0 2) h2abs
  -- level 3, from the level-1 identity
  have hu3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    have hRw : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ
            * Work.Elliptic.sinCos2 θ)
          - (Work.Spaces.pzIter 1 F z θ * Work.Elliptic.sinCos2 θ)
          - (2 * α ^ 2 * z) * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
          - (α * (5 + α)) * (Work.Spaces.pzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ)
          - (α * (5 + α) * z) * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ))
        Work.Spaces.Iθ :=
      (((hzs.1.sub (hFm z hz 1 (by norm_num))).sub (hu2.const_mul (2 * α ^ 2 * z))).sub
        (hu1.const_mul (α * (5 + α)))).sub (hu2.const_mul (α * (5 + α) * z))
    have hcomb : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      hRw.congr (by
        filter_upwards [ae_mem_Ioo_Iθ_psi] with θ hθ
        rw [hId1 z hz0 θ hθ.1 hθ.2]
        ring)
    exact hhelper (α ^ 2 * z ^ 2) (fun θ => Work.Spaces.pzIter 3 Ψ z θ) (by positivity) hcomb
  -- level 4, from the level-2 identity
  have hu4 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pzIter 4 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    have hRw : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') θ
            * Work.Elliptic.sinCos2 θ)
          - (Work.Spaces.pzIter 2 F z θ * Work.Elliptic.sinCos2 θ)
          - (2 * α ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
          - (4 * α ^ 2 * z) * (Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ)
          - (α * (5 + α) * 2) * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
          - (α * (5 + α) * z) * (Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ))
        Work.Spaces.Iθ :=
      ((((hzs.2.sub (hFm z hz 2 (by norm_num))).sub (hu2.const_mul (2 * α ^ 2))).sub
        (hu3.const_mul (4 * α ^ 2 * z))).sub (hu2.const_mul (α * (5 + α) * 2))).sub
        (hu3.const_mul (α * (5 + α) * z))
    have hcomb : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ)
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      hRw.congr (by
        filter_upwards [ae_mem_Ioo_Iθ_psi] with θ hθ
        rw [hId2 z hz0 θ hθ.1 hθ.2]
        ring)
    exact hhelper (α ^ 2 * z ^ 2) (fun θ => Work.Spaces.pzIter 4 Ψ z θ) (by positivity) hcomb
  -- level 0, from the level-0 identity and the bridge
  have hu0 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    have hFσ : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |F z θ|) Work.Spaces.Iθ :=
      sigmaIntegrable_abs_of_integrable (hFm z hz 0 (by norm_num))
    have h2σ : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 2 Ψ z θ|)
        Work.Spaces.Iθ := sigmaIntegrable_abs_of_integrable hu2
    have h1σ : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 1 Ψ z θ|)
        Work.Spaces.Iθ := sigmaIntegrable_abs_of_integrable hu1
    have hdom : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |F z θ|
          + α ^ 2 * z ^ 2 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 2 Ψ z θ|)
          + |α * (5 + α) * z| * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 1 Ψ z θ|))
        Work.Spaces.Iθ :=
      (hFσ.add (h2σ.const_mul (α ^ 2 * z ^ 2))).add (h1σ.const_mul |α * (5 + α) * z|)
    have hu2cd : ContDiffOn ℝ 2 (fun θ' : ℝ => Ψ z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice_pzIter_psi hsm hz0 0) 2
    have hLcont : ContinuousOn (Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Ψ z θ'))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      Work.FTS.EllipticEst.SliceLocal.continuousOn_Lzero1_of_contDiffOn_two _ hu2cd
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
    have hsrc0 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Elliptic.sinCos2 θ
          * |Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ|) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' hdom haesm ?_
      filter_upwards [ae_mem_Ioo_Iθ_psi] with θ hθ
      have hid := lzero1_slice_eq h hz0 hθ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg_Ioo hθ), abs_abs, hid]
      have hA : Work.Elliptic.sinCos2 θ
            * |F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
                + (α * (5 + α) * z) * Work.Spaces.pzIter 1 Ψ z θ|
          ≤ Work.Elliptic.sinCos2 θ * (|F z θ| + α ^ 2 * z ^ 2
              * |Work.Spaces.pzIter 2 Ψ z θ|
              + |α * (5 + α) * z| * |Work.Spaces.pzIter 1 Ψ z θ|) := by
        refine mul_le_mul_of_nonneg_left ?_ (sinCos2_nonneg_Ioo hθ)
        calc |F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
                + (α * (5 + α) * z) * Work.Spaces.pzIter 1 Ψ z θ|
            ≤ |F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ|
                + |(α * (5 + α) * z) * Work.Spaces.pzIter 1 Ψ z θ| := abs_add_le _ _
          _ ≤ (|F z θ| + |α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ|)
                + |(α * (5 + α) * z) * Work.Spaces.pzIter 1 Ψ z θ| := by
              linarith [abs_add_le (F z θ) (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)]
          _ = |F z θ| + α ^ 2 * z ^ 2 * |Work.Spaces.pzIter 2 Ψ z θ|
                + |α * (5 + α) * z| * |Work.Spaces.pzIter 1 Ψ z θ| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2),
                abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 2)]
      calc Work.Elliptic.sinCos2 θ
            * |F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
                + (α * (5 + α) * z) * Work.Spaces.pzIter 1 Ψ z θ|
          ≤ Work.Elliptic.sinCos2 θ * (|F z θ| + α ^ 2 * z ^ 2
              * |Work.Spaces.pzIter 2 Ψ z θ|
              + |α * (5 + α) * z| * |Work.Spaces.pzIter 1 Ψ z θ|) := hA
        _ = Work.Elliptic.sinCos2 θ * |F z θ|
              + α ^ 2 * z ^ 2 * (Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 2 Ψ z θ|)
              + |α * (5 + α) * z| * (Work.Elliptic.sinCos2 θ
                * |Work.Spaces.pzIter 1 Ψ z θ|) := by ring
    exact sigmaIntegrable_of_sourceIntegrable (u := fun θ' => Ψ z θ')
      (contDiffOn_slice_pzIter_psi hsm hz0 0) hsrc0
  intro m hm
  interval_cases m
  · exact hu0
  · exact hu1
  · exact hu2
  · exact hu3
  · exact hu4

end
end Work.FTS.EllipticEst.H2W.PsiSlices
