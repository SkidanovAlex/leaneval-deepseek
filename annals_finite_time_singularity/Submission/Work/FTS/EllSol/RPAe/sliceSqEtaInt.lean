/-
# The trace-free endpoint control of a slice with `η`-weighted second derivative

For `u` of class `C^∞` on the open interval `(0, π/2)` whose second derivative satisfies
`∫_{Iθ} (u'')² sin(2θ)^{-η} < ∞`, the function `u` and its derivative are square integrable
against the same weight `sin(2θ)^{-η}`.  **No** endpoint trace hypothesis is used: the weight
`sin(2θ)^{-η}` is `≥ 1` on the open interval, so `(u'')²` is integrable there, and the classical
fact `bdd_of_integrableOn_deriv` (a function whose derivative is integrable has bounded total
variation) bounds `u'` and then `u` on `(0, π/2)`; boundedness plus the integrability of the
weight give the two conclusions.

This is the extra ingredient of `Work.FTS.EllSol.ropPoincareAe`: it supplies the integrability of
the *top* slice group (`j = 4`, i.e. the pure radial term `(D_z^4 f)² w² sin(2θ)^{-η}`) at those
`z` for which the trace hypothesis is not available.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.H2W.SliceEtaFacts
import Submission.Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv
import Submission.Work.FTS.EllSol.RPAe.Defs
import Submission.Work.FTS.EllSol.VopAux.TraceAux
import Submission.Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW
import Submission.Work.FTS.EllSol.VopAux.sliceGroup_pth_eq_sliceW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.RPAe

set_option autoImplicit false

/-- The open interval `(0, π/2)` has finite Lebesgue measure. -/
theorem volume_Ioo_lt_top : (volume : Measure ℝ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ≠ ⊤ := by
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-- The weight `thEta θ = sin(2θ)^{-η}` is at least `1` on the open interval. -/
theorem one_le_thEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ :=
  Work.FTS.EllipticEst.H2W.one_le_sEta hθ

/-- The weight `thEta` is nonnegative on `Iθ`. -/
theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ :=
  Work.FTS.EllipticEst.thEta_nonneg hθ

/-- The weight `thEta` is continuous on the open interval. -/
theorem continuousOn_thEta : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  fun θ hθ => (Work.FTS.EllipticEst.H2W.continuousAt_sEta hθ).continuousWithinAt

/-- **Trace-free endpoint control.**  If `u` is `C^∞` on the open interval `(0, π/2)` and
`∫_{Iθ} (u'')² sin(2θ)^{-η} < ∞`, then `u² sin(2θ)^{-η}` and `(u')² sin(2θ)^{-η}` are integrable
on `Iθ`. -/
theorem sliceBdd_of_sq_sliceV {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hIoo : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hIooMeas : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have haeMem : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ae_restrict_mem hIooMeas
  -- smoothness of `u'` and of `u''` on the open interval
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ContDiffOn.deriv_of_isOpen (hu 2) isOpen_Ioo (by norm_cast)
  have hd0 : ContDiffOn ℝ 0 (Work.FTS.EllipticEst.sliceV u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h := ContDiffOn.deriv_of_isOpen hd1 isOpen_Ioo (m := 0) (by norm_cast)
    simpa only [Work.FTS.EllipticEst.sliceV] using h
  -- `(u'')²` is integrable on the open interval
  have hA' : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    show MeasureTheory.Integrable _
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    rw [hIoo]
    exact hA
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hA'
      ((hd0.continuousOn.pow 2).aestronglyMeasurable hIooMeas) ?_
    filter_upwards [haeMem] with θ hθ
    have h1 : (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ := one_le_thEta_of_mem_Ioo hθ
    rw [Real.norm_of_nonneg (sq_nonneg (Work.FTS.EllipticEst.sliceV u θ))]
    calc (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        = (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * 1 := by ring
      _ ≤ (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- `u''` is integrable on the open interval
  have hA1 : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.sliceV u)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono'
      (g := fun θ => (1 / 2) * ((Work.FTS.EllipticEst.sliceV u θ) ^ 2 + 1))
      ((hA2.add (integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ))
        volume_Ioo_lt_top)).const_mul (1 / 2))
      (hd0.continuousOn.aestronglyMeasurable hIooMeas) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs]
    have h2 : |Work.FTS.EllipticEst.sliceV u θ|
        ≤ (1 / 2) * ((Work.FTS.EllipticEst.sliceV u θ) ^ 2 + 1) := by
      nlinarith [sq_nonneg (|Work.FTS.EllipticEst.sliceV u θ| - 1),
        sq_abs (Work.FTS.EllipticEst.sliceV u θ)]
    exact h2
  -- `deriv u` is bounded on the open interval
  obtain ⟨C₁, hC₁nn, hC₁⟩ :=
    Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv hpi
      (φ := deriv u)
      (fun θ hθ => (((hd1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt))
      (by simpa only [Work.FTS.EllipticEst.sliceV] using hA1)
  -- hence `(u')² thEta` is integrable
  have hthInt : Integrable (fun θ => C₁ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [hIoo]
    exact Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul (C₁ ^ 2)
  have hD2Ioo : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hthInt
      (((hd1.continuousOn.pow 2).mul continuousOn_thEta).aestronglyMeasurable hIooMeas) ?_
    filter_upwards [haeMem] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (thEta_nonneg_Iθ hθI))]
    have hb : (deriv u θ) ^ 2 ≤ C₁ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC₁ θ hθ) 2
    exact mul_le_mul_of_nonneg_right hb (thEta_nonneg_Iθ hθI)
  have hD2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    show MeasureTheory.Integrable _ (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    rw [← hIoo]
    exact hD2Ioo
  -- `(u')²` and `u'` are integrable on the open interval
  have hD2sq : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hD2Ioo
      ((hd1.continuousOn.pow 2).aestronglyMeasurable hIooMeas) ?_
    filter_upwards [haeMem] with θ hθ
    have h1 : (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ := one_le_thEta_of_mem_Ioo hθ
    rw [Real.norm_of_nonneg (sq_nonneg (deriv u θ))]
    calc (deriv u θ) ^ 2 = (deriv u θ) ^ 2 * 1 := by ring
      _ ≤ (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hD1 : MeasureTheory.IntegrableOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono'
      (g := fun θ => (1 / 2) * ((deriv u θ) ^ 2 + 1))
      ((hD2sq.add (integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ))
        volume_Ioo_lt_top)).const_mul (1 / 2))
      (hd1.continuousOn.aestronglyMeasurable hIooMeas) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs]
    have h2 : |deriv u θ| ≤ (1 / 2) * ((deriv u θ) ^ 2 + 1) := by
      nlinarith [sq_nonneg (|deriv u θ| - 1), sq_abs (deriv u θ)]
    exact h2
  -- `u` is bounded on the open interval
  obtain ⟨C₀, hC₀nn, hC₀⟩ :=
    Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv hpi (φ := u)
      (fun θ hθ => ((((hu 1).differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt)) hD1
  -- hence `u² thEta` is integrable
  have hthInt0 : Integrable (fun θ => C₀ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [hIoo]
    exact Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul (C₀ ^ 2)
  have hU2Ioo : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hthInt0
      ((((hu 0).continuousOn.pow 2).mul continuousOn_thEta).aestronglyMeasurable hIooMeas) ?_
    filter_upwards [haeMem] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (thEta_nonneg_Iθ hθI))]
    have hb : (u θ) ^ 2 ≤ C₀ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC₀ θ hθ) 2
    exact mul_le_mul_of_nonneg_right hb (thEta_nonneg_Iθ hθI)
  refine ⟨?_, hD2⟩
  show MeasureTheory.Integrable _ (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [← hIoo]
  exact hU2Ioo

/-! ## Integrability of the slice groups of `f` and of `∂_θ f`

The `j`-th slice group of `f` is `w(z)² · sliceW (4-j) α u` with `u` the `j`-th slice of `f`
(`VopAux.sliceGroup_eq_sliceW`), that of `∂_θ f` is `w(z)² · sliceW (4-j) α (deriv u)`
(`VopAux.sliceGroup_pth_eq_sliceW`).  For `j ≤ 3` the endpoint traces of the slice `u` are
available and the single-slice estimates `VopAux.sliceF_le_sliceV` /
`VopAux.sliceF_deriv_le_sliceV` deliver the integrability of the two `sliceW`'s; for `j = 4`
(where `sliceW 0` is just the `η`-weighted square) the trace-free lemma
`sliceBdd_of_sq_sliceV` above is used instead.  Both need only the per-`z` integrability of the
`ℋ⁴`-integrand of `∂_θ² f` (`VopAux.integrableOn_sliceV_thEta`,
`VopAux.integrableOn_sliceV_LopIter`). -/

/-- Every slice group vanishes identically at `z = 0`, where `w 0 = 0`. -/
theorem sliceGroup_at_zero (α : ℝ) (k j : ℕ) (F : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.FTS.EllipticEst.sliceGroup α k j F 0 θ = 0 := by
  simp only [Work.FTS.EllipticEst.sliceGroup, Work.Spaces.Wt, Work.Spaces.w]
  simp

/-- **Integrability of the slice groups.**  For `f` of class `C^∞` on the open quadrant whose
`ℋ⁴`-integrand of `∂_θ² f` is integrable on `Iθ` at every `z ∈ Iz`, and whose slices
`θ' ↦ D_z^j f z θ'` have vanishing endpoint traces for `j ≤ 3` and every `z > 0`, the `j`-th
slice group of `f` and of `∂_θ f` is integrable on `Iθ` at every `z ∈ Iz`, for every `j ≤ 4`. -/
theorem sliceGroupIntegrableEasy : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f →
    (∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ)
      Work.Spaces.Iθ) →
    ∀ z ∈ Work.Spaces.Iz, ∀ j : ℕ, j ≤ 4 →
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ)
        Work.Spaces.Iθ := by
  intro α f hα0 hα1 hSO htr hInt z hz j hj
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · -- `z = 0`: both integrands vanish identically
    subst hz0
    constructor
    · refine MeasureTheory.integrableOn_zero.congr ?_
      exact Filter.Eventually.of_forall fun θ => (sliceGroup_at_zero α 4 j f θ).symm
    · refine MeasureTheory.integrableOn_zero.congr ?_
      exact Filter.Eventually.of_forall fun θ =>
        (sliceGroup_at_zero α 4 j (Work.Spaces.pth f) θ).symm
  · have hInt4 := hInt z hz
    set u : ℝ → ℝ := fun θ' => Work.Spaces.DzIter j f z θ' with hu
    have husm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllSol.VopAux.contDiffOn_slice_of_smoothOpen (hSO.DzIter j) hzpos
    have hAj : MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ :=
      Work.FTS.EllSol.VopAux.integrableOn_sliceV_thEta (α := α) (k := 4) (f := f) hSO hzpos hj
        hInt4
    have hBj : ∀ m ∈ Finset.Icc 1 (4 - j), MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
      intro m hm
      have hmj : m + j ≤ 4 := by
        have h2 := (Finset.mem_Icc.mp hm).2
        omega
      exact Work.FTS.EllSol.VopAux.integrableOn_sliceV_LopIter (α := α) (k := 4) (f := f) hSO
        hzpos (Finset.mem_Icc.mp hm).1 hmj hInt4
    rcases le_or_gt j 3 with hj3 | hj3
    · -- `j ≤ 3`: the endpoint traces of the slice are available
      have htrj := htr j hj3 z hzpos
      obtain ⟨h1, h2, -⟩ := RPAe.sliceF_le_sliceV_apply (4 - j) α u hα0 hα1 husm htrj.1 htrj.2
        hAj hBj
      obtain ⟨h1', h2', -⟩ := RPAe.sliceF_deriv_le_sliceV_apply (4 - j) α u hα0 hα1 husm htrj.1
        htrj.2 hAj hBj
      have hWu : MeasureTheory.IntegrableOn
          (fun θ => Work.FTS.EllSol.VopAux.sliceW (4 - j) α u θ) Work.Spaces.Iθ :=
        Work.FTS.EllSol.VopAux.integrableOn_sliceW_of (K := 4 - j) h1 h2
      have hWdu : MeasureTheory.IntegrableOn
          (fun θ => Work.FTS.EllSol.VopAux.sliceW (4 - j) α (deriv u) θ) Work.Spaces.Iθ :=
        Work.FTS.EllSol.VopAux.integrableOn_sliceW_of (K := 4 - j) h1' h2'
      constructor
      · refine MeasureTheory.Integrable.congr
          (MeasureTheory.Integrable.const_mul hWu ((Work.Spaces.w z) ^ 2)) ?_
        refine Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo ?_
        intro θ hθ
        show (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW (4 - j) α u θ
          = Work.FTS.EllipticEst.sliceGroup α 4 j f z θ
        rw [Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW α 4 j f hzpos (fun n => hSO.forall n) θ hθ]
      · refine MeasureTheory.Integrable.congr
          (MeasureTheory.Integrable.const_mul hWdu ((Work.Spaces.w z) ^ 2)) ?_
        refine Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo ?_
        intro θ hθ
        show (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW (4 - j) α (deriv u) θ
          = Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ
        rw [Work.FTS.EllSol.VopAux.sliceGroup_pth_eq_sliceW α 4 j f hzpos
          (fun n => hSO.forall n) θ hθ]
    · -- `j = 4`: no trace is available; use the trace-free `η`-weighted bounds
      have hj4 : j = 4 := by omega
      subst hj4
      obtain ⟨hU2, hD2⟩ := sliceBdd_of_sq_sliceV husm hAj
      have hWu : MeasureTheory.IntegrableOn
          (fun θ => Work.FTS.EllSol.VopAux.sliceW 0 α u θ) Work.Spaces.Iθ := by
        refine hU2.congr ?_
        exact Filter.Eventually.of_forall fun θ => by simp [Work.FTS.EllSol.VopAux.sliceW]
      have hWdu : MeasureTheory.IntegrableOn
          (fun θ => Work.FTS.EllSol.VopAux.sliceW 0 α (deriv u) θ) Work.Spaces.Iθ := by
        refine hD2.congr ?_
        exact Filter.Eventually.of_forall fun θ => by simp [Work.FTS.EllSol.VopAux.sliceW]
      constructor
      · refine MeasureTheory.Integrable.congr
          (MeasureTheory.Integrable.const_mul hWu ((Work.Spaces.w z) ^ 2)) ?_
        refine Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo ?_
        intro θ hθ
        show (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW 0 α u θ
          = Work.FTS.EllipticEst.sliceGroup α 4 4 f z θ
        rw [Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW α 4 4 f hzpos (fun n => hSO.forall n)
          θ hθ]
      · refine MeasureTheory.Integrable.congr
          (MeasureTheory.Integrable.const_mul hWdu ((Work.Spaces.w z) ^ 2)) ?_
        refine Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo ?_
        intro θ hθ
        show (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW 0 α (deriv u) θ
          = Work.FTS.EllipticEst.sliceGroup α 4 4 (Work.Spaces.pth f) z θ
        rw [Work.FTS.EllSol.VopAux.sliceGroup_pth_eq_sliceW α 4 4 f hzpos
          (fun n => hSO.forall n) θ hθ]

end Work.FTS.EllSol.RPAe
