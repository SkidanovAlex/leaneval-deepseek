/-
Copyright: work module for the Elgindi finite-time singularity project.

# The first `z`-moment of an honest datum vanishes

`HonFirstMoment`: for honest data `Hon α F Ψ` (Elgindi, Annals **194** (2021), the level-`0`
`η`-weighted elliptic estimate) and every `z > 0`, the angular moment of `∂_zΨ` vanishes:

  `∫_θ ∂_zΨ(z,θ) sinθcos²θ dθ = 0`.

This is the differentiated form of the solvability condition `OrthCond Ψ`
(`Fstar Ψ ≡ 0`), which holds for *every* `z ∈ ℝ`.

## Route

`OrthCond Ψ` says that the totalised moment `M(z) = ∫_θ Ψ(z,θ) sinθcos²θ dθ` is `0` for every
`z`.  `HonSliceL1` shows that for `z > 0` that moment is an *honest* integral
(`memB` gives `∫_θ (∂_θθΨ)²σ < ∞`, hence `∂_θΨ` and `Ψ` bounded on the slice and `Ψ·ψ ∈ L¹`),
so `M(z) - M(z - h) = 0` is a genuine identity.  The fundamental theorem of calculus along the
`z`-direction rewrites it as `∫_θ (Ψ(z,θ) - Ψ(z-h,θ)) ψ θ dθ = 0`, i.e.

  `∫_θ D_h(θ) ψ θ dθ = 0`,   `D_h(θ) = (Ψ(z,θ) - Ψ(z-h,θ))/h`.

Since `∂_zΨ(z,θ)` is the limit of `D_h(θ)` as `h → 0⁺` (`HonDifQuotTendsto`), a
dominated-convergence argument along the filter `𝓝[>] 0` gives `∫_θ ∂_zΨ(z,θ)ψ θ dθ = 0`,
provided the difference quotients are dominated by an `L¹` function of `θ`:
`|D_h(θ)| ≤ |∂_zΨ(z,θ)| + ∫_{z/2}^{z} |∂_zzΨ(u,θ)| du` (`HonDifQuotBound`).
The first term is integrable exactly in the case where the target integral is honest (otherwise
the totalised integral is `0` by definition), and the second one is integrable by
`HonZBoxPsiBound` (Cauchy–Schwarz against `σ` for each `u`, plus the box integrability supplied
by `memA`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonSliceL1
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.EllipticEst.Honest.HonDifQuotBound
import Submission.Work.FTS.EllipticEst.Honest.HonDifQuotTendsto
import Submission.Work.FTS.EllipticEst.Honest.HonZBoxPsiBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Two elementary facts about the angular profile and the slices -/

/-- The `θ`-slices of an honest datum are smooth on the open angular interval. -/
theorem hon_slice_contDiffOn {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z)
    (n : ℕ) : ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have h2 := h.sm n
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
  exact h2.comp (by fun_prop) hmap

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
theorem sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  positivity

/-- The angular profile is continuous. -/
theorem continuous_sinCos2 : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
  rw [show (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 from rfl]
  fun_prop

/-- `sinθcos²θ` vanishes at the two endpoints of `Iθ`. -/
theorem sinCos2_eq_zero_of_endpoints {θ : ℝ} (hθ : θ = 0 ∨ θ = Real.pi / 2) :
    Work.Elliptic.sinCos2 θ = 0 := by
  rcases hθ with h | h
  · rw [h, Work.Elliptic.sinCos2, Real.sin_zero]; ring
  · rw [h, Work.Elliptic.sinCos2, Real.cos_pi_div_two]; ring

/-! ## The signed moment is an honest integral -/

/-- `HonSliceL1` (the `L¹`-integrability of `|Ψ z ·| · sinθcos²θ`) upgraded to the signed
moment, which is what `OrthCond Ψ` computes. -/
theorem hon_psi_moment_integrable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  refine (HonSliceL1 α F Ψ h z hz).mono'
    ((slice_aesm_of_contDiffOn (hon_slice_contDiffOn h hz 1)).mul
      continuous_sinCos2.aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg_Iθ hθ)]

/-- **The moment difference vanishes.**  For `0 < h < z`, the two honest moments
`∫_θ Ψ z θ ψ θ` and `∫_θ Ψ (z-h) θ ψ θ` are both `0` by `OrthCond Ψ`, hence so is their
difference. -/
theorem hon_moment_diff_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    {z hh : ℝ} (hz : 0 < z) (hh0 : 0 < hh) (hhz : hh < z) :
    (∫ θ in Work.Spaces.Iθ, (Ψ z θ - Ψ (z - hh) θ) * Work.Elliptic.sinCos2 θ) = 0 := by
  have hz' : 0 < z - hh := by linarith
  have hI1 := hon_psi_moment_integrable h hz
  have hI2 := hon_psi_moment_integrable h hz'
  have hsplit : (∫ θ in Work.Spaces.Iθ, (Ψ z θ - Ψ (z - hh) θ) * Work.Elliptic.sinCos2 θ)
      = (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Elliptic.sinCos2 θ)
        - (∫ θ in Work.Spaces.Iθ, Ψ (z - hh) θ * Work.Elliptic.sinCos2 θ) := by
    rw [show (fun θ => (Ψ z θ - Ψ (z - hh) θ) * Work.Elliptic.sinCos2 θ)
        = (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ
            - Ψ (z - hh) θ * Work.Elliptic.sinCos2 θ) from by funext θ; ring]
    exact MeasureTheory.integral_sub hI1 hI2
  have h1 : (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 := by
    simpa only [Work.Elliptic.Fstar] using h.orthΨ z
  have h2 : (∫ θ in Work.Spaces.Iθ, Ψ (z - hh) θ * Work.Elliptic.sinCos2 θ) = 0 := by
    simpa only [Work.Elliptic.Fstar] using h.orthΨ (z - hh)
  rw [hsplit, h1, h2]
  ring

/-! ## The main theorem -/

theorem HonFirstMoment (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (h : Hon α F Ψ) :
    ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 := by
  intro z hz
  by_cases hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ
  swap
  · -- the totalised integral of a non-integrable function is `0`
    exact MeasureTheory.integral_undef hint
  -- ## the integrability of the dominating function
  have hψaesm : AEStronglyMeasurable (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    continuous_sinCos2.aestronglyMeasurable
  have habs : MeasureTheory.Integrable
      (fun θ : ℝ => |Work.Spaces.pz Ψ z θ| * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (hint.norm).mono' ?_ ?_
    · refine (hint.aestronglyMeasurable.norm).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg_Iθ hθ)]
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have h1 : ‖|Work.Spaces.pz Ψ z θ| * Work.Elliptic.sinCos2 θ‖
          = |Work.Spaces.pz Ψ z θ| * Work.Elliptic.sinCos2 θ :=
        Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hθ))
      have h2 : ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖
          = |Work.Spaces.pz Ψ z θ| * Work.Elliptic.sinCos2 θ := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg_Iθ hθ)]
      rw [h1, h2]
  have hK : MeasureTheory.Integrable
      (fun θ : ℝ => (∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ|)
        * Work.Elliptic.sinCos2 θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    HonZBoxPsiBound α F Ψ h z hz
  have hdom : MeasureTheory.Integrable
      (fun θ : ℝ => (|Work.Spaces.pz Ψ z θ|
          + ∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ|)
        * Work.Elliptic.sinCos2 θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h2 := habs.add hK
    refine h2.congr ?_
    filter_upwards with θ
    simp only [Pi.add_apply]
    ring
  -- ## the eventual smallness of the step
  have hev : ∀ᶠ hh : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), hh ∈ Set.Ioo 0 (z / 2) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Iio.mem_nhds (show (0 : ℝ) < z / 2 by linarith)] with hh hhlt hhpos
    exact ⟨hhpos, hhlt⟩
  -- ## the difference quotients: measurability, domination, convergence
  have hmeas : ∀ᶠ hh : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), AEStronglyMeasurable
      (fun θ : ℝ => ((Ψ z θ - Ψ (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hev] with hh hhh
    have hhz : hh < z := by linarith [hhh.2, hz]
    have h1 : AEStronglyMeasurable (fun θ : ℝ => Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      slice_aesm_of_contDiffOn (hon_slice_contDiffOn h hz 1)
    have h2 : AEStronglyMeasurable (fun θ : ℝ => Ψ (z - hh) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      slice_aesm_of_contDiffOn (hon_slice_contDiffOn h (by linarith : 0 < z - hh) 1)
    have h3 : AEStronglyMeasurable
        (fun θ : ℝ => ((Ψ z θ - Ψ (z - hh) θ) * (1 / hh)) * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((h1.sub h2).mul_const (1 / hh)).mul hψaesm
    refine h3.congr ?_
    filter_upwards with θ
    rw [div_eq_mul_inv]
    ring
  have hbound : ∀ᶠ hh : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖((Ψ z θ - Ψ (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ‖
        ≤ (|Work.Spaces.pz Ψ z θ| + ∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ|)
            * Work.Elliptic.sinCos2 θ := by
    filter_upwards [hev] with hh hhh
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards with θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [sinCos2_eq_zero_of_endpoints (Or.inl rfl), mul_zero]
      simp
    · rcases eq_or_lt_of_le hθ.2 with h2 | h2
      · subst h2
        rw [sinCos2_eq_zero_of_endpoints (Or.inr rfl), mul_zero]
        simp
      · have hb := HonDifQuotBound α F Ψ h z hz hh hhh.1 hhh.2 θ h0 h2
        have hψ0 := sinCos2_nonneg_Iθ hθ
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hψ0]
        have htri : |(Ψ z θ - Ψ (z - hh) θ) / hh|
            ≤ |Work.Spaces.pz Ψ z θ|
              + ∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ| := by
          have h1 : |(Ψ z θ - Ψ (z - hh) θ) / hh|
              ≤ |Work.Spaces.pz Ψ z θ|
                + |(Ψ z θ - Ψ (z - hh) θ) / hh - Work.Spaces.pz Ψ z θ| := by
            have hab := abs_add_le (Work.Spaces.pz Ψ z θ)
              ((Ψ z θ - Ψ (z - hh) θ) / hh - Work.Spaces.pz Ψ z θ)
            calc |(Ψ z θ - Ψ (z - hh) θ) / hh|
                = |Work.Spaces.pz Ψ z θ
                    + ((Ψ z θ - Ψ (z - hh) θ) / hh - Work.Spaces.pz Ψ z θ)| := by
                  ring_nf
              _ ≤ _ := hab
          linarith [hb]
        exact mul_le_mul_of_nonneg_right htri hψ0
  have hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun hh : ℝ => ((Ψ z θ - Ψ (z - hh) θ) / hh)
        * Work.Elliptic.sinCos2 θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)) := by
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards with θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [sinCos2_eq_zero_of_endpoints (Or.inl rfl), mul_zero]
      simp only [mul_zero]
      exact tendsto_const_nhds
    · rcases eq_or_lt_of_le hθ.2 with h2 | h2
      · subst h2
        rw [sinCos2_eq_zero_of_endpoints (Or.inr rfl), mul_zero]
        simp only [mul_zero]
        exact tendsto_const_nhds
      · exact (HonDifQuotTendsto α F Ψ h z hz θ h0 h2).mul_const _
  -- ## the integrals of the difference quotients vanish
  have hint_zero : ∀ᶠ hh : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∫ θ, ((Ψ z θ - Ψ (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) = 0 := by
    filter_upwards [hev] with hh hhh
    have hm := hon_moment_diff_zero h hz hhh.1 (by linarith [hhh.2])
    rw [show (fun θ : ℝ => ((Ψ z θ - Ψ (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ)
        = (fun θ : ℝ => (1 / hh)
            * ((Ψ z θ - Ψ (z - hh) θ) * Work.Elliptic.sinCos2 θ)) from by
      funext θ; rw [div_eq_mul_inv]; ring]
    rw [MeasureTheory.integral_const_mul, hm, mul_zero]
  -- ## dominated convergence along `𝓝[>] 0`
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (F := fun hh θ => ((Ψ z θ - Ψ (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ)
    (f := fun θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
    (fun θ => (|Work.Spaces.pz Ψ z θ| + ∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ|)
      * Work.Elliptic.sinCos2 θ)
    hmeas hbound hdom hlim
  have hzero : Filter.Tendsto
      (fun hh : ℝ => ∫ θ, ((Ψ z θ - Ψ (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hint_zero] with hh hh0
    exact hh0.symm
  exact tendsto_nhds_unique hDCT hzero

end Work.FTS.EllipticEst.Honest
