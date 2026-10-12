import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
import Submission.Work.SmallBoxBridge.Resolve.kinKernel_stronglyMeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.FamKernelAux` — shared utilities for the family-form/kernel-form identity

Small reusable facts used by `Work.BSKinetic.familyFormUnproj_eq_kernelForm` and by the
helper lemmas it delegates (the per-`u` kernel identity, the `u`-integral of the window
product, and the integrability of the various family/kernel integrands).

* `integrable_of_compact_support`: a bounded, a.e. strongly measurable function supported in a
  compact set is integrable for a measure finite on compacts.  Needed because the kernel
  `K_F = 𝓕⁻¹F` is only bounded+a.e.-measurable (`…kinKernel_bdd`,
  `…kinKernel_aestronglyMeasurable`), never continuous.
* `HasCompactSupport.exists_norm_le`: the support of a compactly supported function lies in a
  closed ball.
* the support/bound calculus of the big-box window `bsWin ℓ u x = χ((x - ℓ•u)/ℓ)`:
  it vanishes when `‖x - ℓ•u‖ > ℓ/2`, so a nonzero value forces `‖u‖ ≤ (‖x‖ + ℓ/2)/ℓ`;
  and `|bsWin ℓ u x| ≤ chiSup`.
* `abs_convScale_le_one`: `|convScale ℓ z| ≤ 1` (`convScale ℓ z = (χ⋆χ)(z/ℓ)`, `0 ≤ χ⋆χ ≤ 1`).
-/

noncomputable section

open MeasureTheory

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- A bounded, a.e. strongly measurable function supported in a compact set is integrable for
a measure which is finite on compacts. -/
lemma integrable_of_compact_support {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [T2Space α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {f : α → ℝ} (hK : ∃ K : Set α, IsCompact K ∧ ∀ x, f x ≠ 0 → x ∈ K)
    (hm : AEStronglyMeasurable f μ) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Integrable f μ := by
  obtain ⟨K, hKc, hKs⟩ := hK
  obtain ⟨C, hC⟩ := hb
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  have hKtop : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hg : Integrable (K.indicator (fun _ : α => C)) μ := by
    rw [integrable_indicator_iff hKmeas]
    exact integrableOn_const hKtop (by simp)
  refine Integrable.mono' hg hm ?_
  filter_upwards with x
  by_cases hx : x ∈ K
  · simp only [Set.indicator_of_mem hx]
    exact hC x
  · have h0 : f x = 0 := by by_contra h; exact hx (hKs x h)
    simp only [Set.indicator_of_notMem hx, h0, norm_zero, le_refl]

/-- The support of a compactly supported function is contained in a closed ball. -/
lemma HasCompactSupport.exists_norm_le {E : Type*} [NormedAddCommGroup E] {f : E → ℝ}
    (h : HasCompactSupport f) : ∃ R : ℝ, ∀ x, f x ≠ 0 → ‖x‖ ≤ R := by
  obtain ⟨C, hC⟩ := h.isCompact.isBounded.exists_norm_le
  exact ⟨C, fun x hx => hC x (subset_tsupport f (Function.mem_support.mpr hx))⟩

/-- `|χ_ℓ|` is bounded by `chiSup`. -/
lemma abs_bsWin_le (ℓ : ℝ) (u x : ℝ³) :
    |bsWin ℓ u x| ≤ Submission.BoseGases.chiSup :=
  Submission.BoseGases.abs_chiScale_le_chiSup ℓ (x - ℓ • u)

/-- `bsWin ℓ u x` vanishes when `x` is farther than `ℓ/2` from the centre `ℓ•u`. -/
lemma bsWin_eq_zero_of_lt_norm {ℓ : ℝ} (hℓ : 0 < ℓ) (u x : ℝ³)
    (h : ℓ / 2 < ‖x - ℓ • u‖) : bsWin ℓ u x = 0 := by
  rw [bsWin, Submission.BoseGases.chiScale]
  apply Submission.BoseGases.chi_eq_zero_of_half_le_norm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
  have h1 : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
  rw [← h1]
  exact le_of_lt (mul_lt_mul_of_pos_left h (inv_pos.mpr hℓ))

/-- A nonzero value of `bsWin ℓ u x` forces `‖x - ℓ•u‖ ≤ ℓ/2`. -/
lemma bsWin_ne_zero_le_norm {ℓ : ℝ} (hℓ : 0 < ℓ) {u x : ℝ³} (h : bsWin ℓ u x ≠ 0) :
    ‖x - ℓ • u‖ ≤ ℓ / 2 := by
  by_contra hc
  exact h (bsWin_eq_zero_of_lt_norm hℓ u x (lt_of_not_ge hc))

/-- A nonzero value of `bsWin ℓ u x` forces `‖u‖ ≤ (‖x‖ + ℓ/2)/ℓ`. -/
lemma bsWin_ne_zero_norm_le {ℓ : ℝ} (hℓ : 0 < ℓ) {u x : ℝ³} (h : bsWin ℓ u x ≠ 0) :
    ‖u‖ ≤ (‖x‖ + ℓ / 2) / ℓ := by
  have h1 := bsWin_ne_zero_le_norm hℓ h
  have h2 : ‖ℓ • u‖ ≤ ‖x‖ + ℓ / 2 := by
    calc ‖ℓ • u‖ = ‖x - (x - ℓ • u)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - ℓ • u‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + ℓ / 2 := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at h2
  rw [le_div_iff₀ hℓ]
  linarith

/-- `|convScale ℓ z| ≤ 1`. -/
lemma abs_convScale_le_one (ℓ : ℝ) (z : ℝ³) : |Submission.BoseGases.convScale ℓ z| ≤ 1 := by
  rw [abs_le]
  refine ⟨?_, Submission.BoseGases.conv3chi_le_one (ℓ⁻¹ • z)⟩
  rw [Submission.BoseGases.convScale]
  linarith [Submission.BoseGases.conv3chi_nonneg (ℓ⁻¹ • z)]

/-- **The `u`-integral of the product of two big-box windows is the scaled autocorrelation**
`∫_u bsWin ℓ u x · bsWin ℓ u y du = convScale ℓ (x - y)`.  This is the off-diagonal companion of
the `L²`-normalisation `Work.UBBInputs9.B.integral_chiScale_sub_smul_sq`; it is
`Submission.BoseGases.chiU_chiU_integral` rewritten through `bsWin_eq_chiU`. -/
lemma integral_bsWin_mul_bsWin {ℓ : ℝ} (hℓ : 0 < ℓ) (x y : ℝ³) :
    (∫ u : ℝ³, bsWin ℓ u x * bsWin ℓ u y)
      = Submission.BoseGases.convScale ℓ (x - y) := by
  have hne : ℓ ≠ 0 := ne_of_gt hℓ
  have h : (fun u : ℝ³ => bsWin ℓ u x * bsWin ℓ u y)
      = fun u : ℝ³ => Submission.BoseGases.chiU ℓ u x * Submission.BoseGases.chiU ℓ u y := by
    funext u
    rw [bsWin_eq_chiU hne, bsWin_eq_chiU hne]
  rw [h]
  exact Submission.BoseGases.chiU_chiU_integral ℓ hne x y

/-- `convScale ℓ = (χ⋆χ)(·/ℓ)` is continuous (`conv_contDiff`). -/
lemma continuous_convScale (ℓ : ℝ) : Continuous (Submission.BoseGases.convScale ℓ) := by
  unfold Submission.BoseGases.convScale
  exact (Submission.BoseGases.conv_contDiff.continuous).comp (by fun_prop)

/-- `z ↦ kinKernel F (z.1 - z.2)` is a.e. strongly measurable on `ℝ³ × ℝ³`. -/
lemma aestronglyMeasurable_kinKernel_sub {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : ℝ³ => F ‖p‖)) :
    AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => Submission.BoseGases.kinKernel F (z.1 - z.2))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
  (Work.SmallBoxBridge.Resolve.kinKernel_stronglyMeasurable hFi).comp_measurable
    (by fun_prop) |>.aestronglyMeasurable

end Work.BSKinetic
