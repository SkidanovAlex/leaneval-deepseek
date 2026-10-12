import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass.lowMult_sq_le_ae_of_nonpos`

For a non-positive cut-off parameter `κ ≤ 0` (the degenerate case `κ = 0` of the
`Work.BoseFixB3.HighMass` program, where the low-momentum cut-off `κ = (d²ℓ)⁻¹` is replaced by
`0`), the symbol `p ↦ f(‖p‖/κ)` of `Work.BoseBoxFix.LowCut` is identically `1`
(`lowCut_eq_one_of_nonpos`: `‖p‖/κ ≤ 0 ≤ 1` and `LowCut.one`).  The one-slot low-momentum
multiplier therefore reduces to the full inverse Fourier transform of the profile,

`lowMult fc κ ℓ ψ x = (𝓕⁻ (𝓕 (1_Λ ψ)) x).re`

(`lowMult_eq_re_fourierInv`), and the claim follows from the two complementary facts:

* if `𝓕 (1_Λ ψ)` is integrable, the Fourier inversion formula
  (`MeasureTheory.Integrable.fourierInv_fourier_eq`) gives `𝓕⁻(𝓕u) x = u x` at every point of
  continuity of `u = 1_Λ ψ`; these are all points off the null union of the coordinate
  hyperplanes `x_m = ±ℓ/2` (`ae_continuousAt_indicator_acube`), whence `lowMult = ψ x` and
  `(ψ x - ψ x)² ≤ (ψ x)²`;
* if `𝓕 (1_Λ ψ)` is *not* integrable, the integrand of the inverse transform is not integrable
  either (it differs from `𝓕u` by the unimodular character `𝐞 (⟪·,x⟫)`,
  `integrable_fourier_char_smul_iff`), so the Bochner integral is `0` by convention
  (`MeasureTheory.integral_undef`) and `lowMult = 0`; the inequality then holds with equality.

Note that both halves are needed: the multiplier formula is a Bochner integral, so `lowMult` is
*junk-zero* rather than the (non-convergent) inversion integral whenever `𝓕u ∉ L¹`.  In both
cases the requested inequality holds almost everywhere on the box.
-/

noncomputable section

open scoped Real Topology BigOperators FourierTransform
open MeasureTheory Filter Metric

namespace Work.BoseFixB3.HighMass

open _root_.BoseGases Submission.BoseGases
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/- Auxiliary lemmas of this file (private sub-namespace, to avoid clashes with same-named
statements proved elsewhere in the workspace). -/
namespace LowMultAux

/-! ## 1. The non-positive cut-off is trivial -/

/-- For `κ ≤ 0` the cut-off symbol of `LowCut` is identically `1`: `‖p‖/κ ≤ 0 ≤ 1`. -/
lemma lowCut_eq_one_of_nonpos (fc : LowCut) {κ : ℝ} (hκ : κ ≤ 0) (p : ℝ³) :
    fc.f (‖p‖ / κ) = 1 := by
  rcases lt_or_eq_of_le hκ with h | h
  · refine fc.one _ ?_
    have : ‖p‖ / κ ≤ 0 := div_nonpos_of_nonneg_of_nonpos (norm_nonneg p) h.le
    linarith
  · rw [h, div_zero]
    exact fc.one 0 zero_le_one

/-! ## 2. The multiplier is the inverse Fourier transform of the profile -/

/-- **The low-momentum multiplier at `κ ≤ 0` is the inverse Fourier transform of `1_Λψ`.**
Unfolding `lowMult` and inserting `f(‖p‖/κ) = 1`, the substitution `p = 2π w`
(`Measure.integral_comp_smul_of_nonneg`, valid also for non-integrable integrands) turns
`(2π)⁻³ ∫_p e^{i⟪p,x⟫} kinFT u p` into the defining integral of `𝓕⁻(𝓕u) x`. -/
lemma lowMult_eq_re_fourierInv (fc : LowCut) {κ ℓ : ℝ} (hκ : κ ≤ 0) (ψ : ℝ³ → ℝ) (b : ℝ³) :
    lowMult fc κ ℓ ψ b
      = (𝓕⁻ (𝓕 (fun z : ℝ³ => (((acube ℓ).indicator ψ z : ℝ) : ℂ))) b).re := by
  have hcut : ∀ p : ℝ³, fc.f (‖p‖ / κ) = 1 := lowCut_eq_one_of_nonpos fc hκ
  rw [lowMult]
  set u : ℝ³ → ℂ := fun z => (((acube ℓ).indicator ψ z : ℝ) : ℂ) with hu
  have hInt : (∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p b : ℂ)) *
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) * Submission.BoseGases.kinFT u p)
      = ∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p b : ℂ)) *
          Submission.BoseGases.kinFT u p := by
    apply integral_congr_ae
    filter_upwards with p
    rw [hcut p]
    simp
  rw [hInt]
  have hG : (∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p b : ℂ)) *
        Submission.BoseGases.kinFT u p)
      = ∫ p : ℝ³, (fun w : ℝ³ =>
          Complex.exp (↑(2 * Real.pi * (inner ℝ w b)) * Complex.I) * 𝓕 u w)
          ((2 * Real.pi)⁻¹ • p) := by
    apply integral_congr_ae
    filter_upwards with p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    have hExp : Complex.exp (Complex.I * (inner ℝ p b : ℂ))
        = Complex.exp (↑(2 * Real.pi * (inner ℝ ((2 * Real.pi)⁻¹ • p) b)) * Complex.I) := by
      rw [real_inner_smul_left]
      congr 1
      push_cast
      field_simp
    rw [hExp]
  rw [hG, Measure.integral_comp_smul_of_nonneg (volume : Measure ℝ³)
      (fun w : ℝ³ => Complex.exp (↑(2 * Real.pi * (inner ℝ w b)) * Complex.I) * 𝓕 u w)
      ((2 * Real.pi)⁻¹) (hR := by positivity)]
  rw [Real.fourierInv_eq']
  rw [show (∫ v : ℝ³, Complex.exp (↑(2 * Real.pi * (inner ℝ v b)) * Complex.I) • 𝓕 u v)
      = ∫ v : ℝ³, Complex.exp (↑(2 * Real.pi * (inner ℝ v b)) * Complex.I) * 𝓕 u v from by
        apply integral_congr_ae
        filter_upwards with v
        rw [smul_eq_mul]]
  rw [finrank_euclideanSpace, Fintype.card_fin]
  set Z : ℂ := ∫ w : ℝ³, Complex.exp (↑(2 * Real.pi * (inner ℝ w b)) * Complex.I) * 𝓕 u w
    with hZ
  have hK : (((2 * Real.pi)⁻¹ : ℝ) ^ 3)⁻¹ = (2 * Real.pi) ^ 3 := by rw [inv_pow, inv_inv]
  have hA : ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * (((2 * Real.pi) ^ 3 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ^ 3 ≠ 0),
      Complex.ofReal_one]
  have hfin : ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ((((2 * Real.pi)⁻¹ : ℝ) ^ 3)⁻¹ • Z) = Z := by
    rw [Complex.real_smul, hK, ← mul_assoc, hA, one_mul]
  rw [hfin]

/-! ## 3. The inverse-transform integrand of a non-integrable transform -/

/-- **Integrability of the inverse-transform integrand.**  The character `𝐞 (⟪·,b⟫)` is
unimodular, so `v ↦ 𝐞 (⟪v,b⟫) • 𝓕u v` is integrable iff `𝓕u` is
(`Real.fourierIntegral_convergent_iff` at `-b`). -/
lemma integrable_fourier_char_smul_iff {u : ℝ³ → ℂ} (b : ℝ³) :
    Integrable (fun v : ℝ³ => Real.fourierChar (inner ℝ v b) • 𝓕 u v) ↔ Integrable (𝓕 u) := by
  have h := Real.fourierIntegral_convergent_iff (μ := volume) (f := 𝓕 u) (-b)
  simpa using h

/-! ## 4. Auxiliary measure theory of the box `Λ = acube ℓ` -/

/-- A coordinate hyperplane of `ℝ³` is Lebesgue-null: transfer to the coordinate model
`Fin 3 → ℝ` along the measure-preserving `WithLp.ofLp` and use the product-measure
computation `Measure.pi_hyperplane`. -/
lemma volume_coord_eq_zero (m : Fin 3) (c : ℝ) :
    (volume : Measure ℝ³) {x : ℝ³ | x m = c} = 0 := by
  have hmp : MeasurePreserving (WithLp.ofLp : ℝ³ → (Fin 3 → ℝ)) (volume : Measure ℝ³)
      (volume : Measure (Fin 3 → ℝ)) := PiLp.volume_preserving_ofLp (Fin 3)
  have hset : {x : ℝ³ | x m = c} = WithLp.ofLp ⁻¹' {y : Fin 3 → ℝ | y m = c} := rfl
  rw [hset, hmp.measure_preimage (by measurability)]
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) m c

/-- The centred cube `Λ = acube ℓ` is compact: it is the image of the compact coordinate
box `Set.univ.pi (Icc (-ℓ/2) (ℓ/2))` under the continuous map `cgEuc3`. -/
theorem isCompact_acube (ℓ : ℝ) : IsCompact (acube ℓ) := by
  rw [acube_eq_image]
  refine IsCompact.image ?_ ?_
  · rw [acubeF_eq_pi]
    exact isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc)
  · rw [show ⇑cgEuc3 = fun x : Fin 3 → ℝ => WithLp.toLp 2 x from
      funext fun x => MeasurableEquiv.toLp_apply 2 (Fin 3 → ℝ) x]
    fun_prop

/-- `(acube ℓ).indicator ψ` is integrable (as a `ℂ`-valued function): `ψ` is continuous, hence
continuous on the compact `acube ℓ`, so `IntegrableOn ψ (acube ℓ)`, and an indicator of a
measurable set of an integrable-on function is integrable. -/
theorem integrable_indicator_acube {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    Integrable (fun z : ℝ³ => (((acube ℓ).indicator ψ z : ℝ) : ℂ)) := by
  have hψc : Continuous (fun z : ℝ³ => ((ψ z : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hψ
  have h1 : IntegrableOn (fun z : ℝ³ => ((ψ z : ℝ) : ℂ)) (acube ℓ) volume :=
    hψc.continuousOn.integrableOn_compact (isCompact_acube ℓ)
  have h2 : Integrable ((acube ℓ).indicator (fun z : ℝ³ => ((ψ z : ℝ) : ℂ))) volume :=
    (integrable_indicator_iff (acube_measurable ℓ)).mpr h1
  refine h2.congr ?_
  filter_upwards with z
  by_cases hz : z ∈ acube ℓ
  · simp [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz]

/-- The open box `{z | ∀ m, -ℓ/2 < z m < ℓ/2}` is open (finite intersection of preimages of
the open interval under the coordinate projections). -/
lemma isOpen_box_interior (ℓ : ℝ) :
    IsOpen {z : ℝ³ | ∀ m : Fin 3, -ℓ/2 < z m ∧ z m < ℓ/2} := by
  rw [show {z : ℝ³ | ∀ m : Fin 3, -ℓ/2 < z m ∧ z m < ℓ/2}
      = ⋂ m : Fin 3, ((fun z : ℝ³ => z m) ⁻¹' (Set.Ioo (-ℓ/2) (ℓ/2))) by
        ext z
        simp [Set.mem_Ioo, Set.mem_iInter]]
  exact isOpen_iInter_of_finite fun m =>
    IsOpen.preimage (by fun_prop : Continuous fun z : ℝ³ => z m) isOpen_Ioo

/-- **`1_Λψ` is continuous off the coordinate boundary of the cube.**  If no coordinate of `b`
equals `±ℓ/2` then either `b` is strictly inside — where the indicator is `1` on a
neighbourhood and continuity is that of `ψ` — or some coordinate is strictly outside, where the
indicator is `0` on a neighbourhood. -/
lemma continuousAt_indicator_acube_of_boundary {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) {b : ℝ³}
    (hb : ∀ m : Fin 3, b m ≠ -ℓ/2 ∧ b m ≠ ℓ/2) :
    ContinuousAt (fun z : ℝ³ => ((acube ℓ).indicator ψ z : ℝ)) b := by
  by_cases hin : ∀ m : Fin 3, -ℓ/2 < b m ∧ b m < ℓ/2
  · have hO : {z : ℝ³ | ∀ m : Fin 3, -ℓ/2 < z m ∧ z m < ℓ/2} ∈ 𝓝 b :=
      (isOpen_box_interior ℓ).mem_nhds hin
    have hev : ∀ᶠ z in 𝓝 b, z ∈ acube ℓ := by
      filter_upwards [hO] with z hz
      rw [mem_acube_iff]
      exact fun m => ⟨le_of_lt (hz m).1, le_of_lt (hz m).2⟩
    have hcongr : (fun z : ℝ³ => ((acube ℓ).indicator ψ z : ℝ)) =ᶠ[𝓝 b] ψ := by
      filter_upwards [hev] with z hz
      exact Set.indicator_of_mem hz ψ
    exact ContinuousAt.congr hψ.continuousAt hcongr.symm
  · obtain ⟨m, hm⟩ := not_forall.mp hin
    have hm' : b m ≤ -ℓ/2 ∨ ℓ/2 ≤ b m := by
      rcases not_and_or.mp hm with h | h
      · exact Or.inl (le_of_not_gt h)
      · exact Or.inr (le_of_not_gt h)
    have hcase : b m < -ℓ/2 ∨ ℓ/2 < b m :=
      hm'.imp (fun h => lt_of_le_of_ne h (hb m).1)
        (fun h => lt_of_le_of_ne h (Ne.symm (hb m).2))
    rcases hcase with hlt | hgt
    · have hU : {z : ℝ³ | z m < -ℓ/2} ∈ 𝓝 b :=
        (isOpen_lt (by fun_prop : Continuous fun z : ℝ³ => z m) continuous_const).mem_nhds hlt
      have hev : ∀ᶠ z in 𝓝 b, z ∉ acube ℓ := by
        filter_upwards [hU] with z hz hzmem
        have h2 := ((mem_acube_iff ℓ z).mp hzmem) m
        linarith [h2.1]
      have hcongr : (fun z : ℝ³ => ((acube ℓ).indicator ψ z : ℝ)) =ᶠ[𝓝 b] 0 := by
        filter_upwards [hev] with z hz
        exact Set.indicator_of_notMem hz ψ
      exact ContinuousAt.congr (continuous_const : Continuous (fun _ : ℝ³ => (0:ℝ))).continuousAt
        hcongr.symm
    · have hU : {z : ℝ³ | ℓ/2 < z m} ∈ 𝓝 b :=
        (isOpen_lt continuous_const (by fun_prop : Continuous fun z : ℝ³ => z m)).mem_nhds hgt
      have hev : ∀ᶠ z in 𝓝 b, z ∉ acube ℓ := by
        filter_upwards [hU] with z hz hzmem
        have h2 := ((mem_acube_iff ℓ z).mp hzmem) m
        linarith [h2.2]
      have hcongr : (fun z : ℝ³ => ((acube ℓ).indicator ψ z : ℝ)) =ᶠ[𝓝 b] 0 := by
        filter_upwards [hev] with z hz
        exact Set.indicator_of_notMem hz ψ
      exact ContinuousAt.congr (continuous_const : Continuous (fun _ : ℝ³ => (0:ℝ))).continuousAt
        hcongr.symm

/-- **`1_Λψ` is a.e. continuous on `Λ`.**  The only candidate discontinuity points are the
coordinate hyperplanes `x_m = ±ℓ/2`, whose finite union is null
(`volume_coord_eq_zero`). -/
theorem ae_continuousAt_indicator_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    ∀ᵐ b ∂((volume : Measure ℝ³).restrict (acube ℓ)),
      ContinuousAt (fun z : ℝ³ => (((acube ℓ).indicator ψ z : ℝ) : ℂ)) b := by
  set S : Set ℝ³ := ⋃ m : Fin 3, ({x : ℝ³ | x m = -ℓ/2} ∪ {x : ℝ³ | x m = ℓ/2}) with hSdef
  have hS : (volume : Measure ℝ³) S = 0 := by
    rw [hSdef]
    refine measure_iUnion_null fun m => ?_
    exact measure_union_null (volume_coord_eq_zero m (-ℓ/2)) (volume_coord_eq_zero m (ℓ/2))
  have hae : ∀ᵐ x ∂(volume : Measure ℝ³), x ∉ S := compl_mem_ae_iff.mpr hS
  rw [ae_restrict_iff' (acube_measurable ℓ)]
  filter_upwards [hae] with x hxS hxmem
  have hb : ∀ m : Fin 3, x m ≠ -ℓ/2 ∧ x m ≠ ℓ/2 := by
    intro m
    constructor
    · intro h
      exact hxS (by rw [hSdef]; exact Set.mem_iUnion.mpr ⟨m, Or.inl h⟩)
    · intro h
      exact hxS (by rw [hSdef]; exact Set.mem_iUnion.mpr ⟨m, Or.inr h⟩)
  exact Complex.continuous_ofReal.continuousAt.comp
    (continuousAt_indicator_acube_of_boundary hψ hb)

end LowMultAux

open LowMultAux

/-! ## 5. The a.e. bound -/

/-- **The one-slot inequality at `κ ≤ 0`.**  With the trivial cut-off the low-momentum
multiplier is (a.e.) either the identity or the zero operator, and in both cases
`(ψ x - lowMult … ψ x)² ≤ (ψ x)²` holds: `0 ≤ ψ x²` in the first case, equality in the second. -/
theorem lowMult_sq_le_ae_of_nonpos {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : κ ≤ 0) (hℓ : 0 < ℓ)
    {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    ∀ᵐ b ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)),
      (ψ b - Work.BoseBoxFix.lowMult fc κ ℓ ψ b) ^ 2 ≤ (ψ b) ^ 2 := by
  set u : ℝ³ → ℂ := fun z => (((acube ℓ).indicator ψ z : ℝ) : ℂ) with hu
  have hlow : ∀ b : ℝ³, lowMult fc κ ℓ ψ b = (𝓕⁻ (𝓕 u) b).re := by
    intro b
    rw [lowMult_eq_re_fourierInv fc hκ ψ b]
  by_cases hF : Integrable (𝓕 u)
  · -- Case 1: `𝓕 u ∈ L¹`; Fourier inversion at the a.e. points of continuity of `u`.
    have huint : Integrable u := by
      rw [hu]
      exact integrable_indicator_acube hψ
    have hcont : ∀ᵐ b ∂((volume : Measure ℝ³).restrict (acube ℓ)), ContinuousAt u b := by
      rw [hu]
      exact ae_continuousAt_indicator_acube hℓ hψ
    filter_upwards [hcont, ae_restrict_mem (acube_measurable ℓ)] with b hbcont hbmem
    have hinv : 𝓕⁻ (𝓕 u) b = u b := huint.fourierInv_fourier_eq hF hbcont
    have hub : u b = ((ψ b : ℝ) : ℂ) := by
      rw [hu]
      simp [Set.indicator_of_mem hbmem]
    rw [hlow b, hinv, hub, Complex.ofReal_re]
    nlinarith [sq_nonneg (ψ b)]
  · -- Case 2: `𝓕 u ∉ L¹`; the inverse transform vanishes by the junk-value convention.
    have hzero : ∀ b : ℝ³, lowMult fc κ ℓ ψ b = 0 := by
      intro b
      rw [hlow b, Real.fourierInv_eq,
        integral_undef ((integrable_fourier_char_smul_iff (u := u) b).not.mpr hF)]
      simp
    filter_upwards with b
    rw [hzero b]
    simp

end Work.BoseFixB3.HighMass
