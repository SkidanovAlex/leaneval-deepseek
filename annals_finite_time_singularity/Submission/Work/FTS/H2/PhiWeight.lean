import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.H2

/-! ## The two auxiliary facts behind `PhiWeight`

The pointwise Hardy-weight comparison (on the open quadrant `z > 0`, `0 < θ < π/2`) and the
a.e. strong measurability of the weighted angular energy on `(0,∞)`. -/

/-- **Pointwise Hardy-weight comparison.**  On the open quadrant `z > 0`, `0 < θ < π/2` one has
`0 < sin(2θ) ≤ 1`, so `1/sin(2θ)^{η/2} ≥ 1`; since the radial weight `w z = (1+z)²/z²` satisfies
`w z ≥ 1` for `z > 0`, the Hardy weight `((1+z)/z)² = w z` applied to `f²` is dominated by the
`i = 0` summand of the `ℋ^k`-integrand, hence by the whole integrand:
`(f z θ)² * ((1+z)/z)² ≤ HkIntegrand α k f z θ`.  The boundary of the quadrant (where the weight
vanishes) is a null set, which is why this is applied a.e. on `Iθ`. -/
private theorem phiWeight_pointwise (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      (f z θ) ^ 2 * ((1 + z) / z) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  intro z hz θ hθ hθ2
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- `w z ≤ (w z / sin(2θ)^{η/2})²`, using `0 < sin(2θ)^{η/2} ≤ 1` and `1 ≤ w z`
  have hchain : Work.Spaces.w z ≤
      (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
    have hSpos : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hsin _
    have hSle : S ≤ 1 := by
      rw [hSdef]
      exact Real.rpow_le_one (le_of_lt hsin) (Real.sin_le_one _)
        (by norm_num [Work.Spaces.eta])
    have hw1 : 1 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
      nlinarith
    have hw0 : 0 ≤ Work.Spaces.w z := le_trans zero_le_one hw1
    rw [div_pow, le_div_iff₀ (pow_pos hSpos 2)]
    have hS2 : S ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt hSpos) hSle
    calc Work.Spaces.w z * S ^ 2 ≤ Work.Spaces.w z * 1 := mul_le_mul_of_nonneg_left hS2 hw0
      _ ≤ Work.Spaces.w z * Work.Spaces.w z := by
          rw [mul_one]; exact le_mul_of_one_le_left hw0 hw1
      _ = Work.Spaces.w z ^ 2 := (pow_two _).symm
  -- the `i = 0` summand of the integrand
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α k f z θ 0 (Nat.zero_le k)
  simp only [Work.Spaces.DzIter_zero] at hkey
  calc (f z θ) ^ 2 * ((1 + z) / z) ^ 2
      = (f z θ) ^ 2 * Work.Spaces.w z := by rw [Work.Spaces.w, div_pow]
    _ ≤ (f z θ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hchain (sq_nonneg _)
    _ = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        ring
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := hkey

/-- **Measurability of the weighted angular energy.**  For `f` smooth on an open neighbourhood
of the closed quadrant, `r ↦ (∫_θ f(r,θ)²) * ((1+r)/r)²` is a.e. strongly measurable for
`volume.restrict (Ioi 0)`.

`(r,θ) ↦ (f r θ)²` is continuous on the closed quadrant `Iz ×ˢ Iθ` (by `SmoothNbhd` and
`Iz ×ˢ Iθ ⊆ Ioi (-1) ×ˢ Ioo (-1) (π/2+1)`), hence a.e. strongly measurable for
`(volume.restrict Iz).prod (volume.restrict Iθ)`: that measure is `(volume.prod volume)` restricted
to the quadrant (`MeasureTheory.Measure.prod_restrict`), on which continuity gives a.e. strong
measurability.  `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` integrates out the
angle, and `AEStronglyMeasurable.mono_measure` with `Measure.restrict_mono_set` moves the
statement from `Iz` to the smaller `Ioi 0`.  The Hardy weight `r ↦ ((1+r)/r)²` is continuous on
`(0,∞)`, hence a.e. strongly measurable there. -/
private theorem phiWeight_aesm (f : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd f) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  -- joint a.e. strong measurability of `(r,θ) ↦ (f r θ)²` on `Iz × Iθ`
  have hquad : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hsub : Work.Spaces.Iz ×ˢ Work.Spaces.Iθ ⊆
        Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (π / 2 + 1) := by
      intro p hp
      rw [Set.mem_prod] at hp ⊢
      refine ⟨?_, ?_⟩
      · rw [Work.Spaces.Iz, Set.mem_Ici] at hp
        rw [Set.mem_Ioi]; linarith [hp.1]
      · rw [Work.Spaces.Iθ, Set.mem_Icc] at hp
        rw [Set.mem_Ioo]
        exact ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      (hsm.continuousOn.mono hsub).pow 2
    have hmeas : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      measurableSet_Ici.prod measurableSet_Icc
    have h1 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hcont.aestronglyMeasurable hmeas
    rwa [← MeasureTheory.Measure.prod_restrict] at h1
  -- integrate out the angle
  have hslicemeas : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hquad
  have hmono : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) ≤
      MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self
  have hslicemeas' : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hslicemeas.mono_measure hmono
  -- the Hardy weight is continuous on `(0,∞)`
  have hw : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : ContinuousOn (fun r : ℝ => (1 + r) / r) (Set.Ioi (0 : ℝ)) :=
      (continuousOn_const.add continuousOn_id).div continuousOn_id
        (fun r hr => ne_of_gt (Set.mem_Ioi.mp hr))
    exact (h1.pow 2).aestronglyMeasurable measurableSet_Ioi
  exact hslicemeas'.mul hw

/-- The weight comparison behind `|L₁₂(f)(0)| ≤ C|f|_{ℋ⁴}` (Elgindi, Proposition
`muestimate`): for a function smooth on an open neighbourhood of the closed quadrant and in
`ℋ⁴` (`Work.Spaces.HkMem α 4 f`), the "Hardy weight" `((1+r)/r)²` applied to the angular
energy of a slice is integrable on `(0,∞)` and its integral is at most the full `ℋ⁴` energy:
`∫_{r>0} (∫_θ f(r,θ)²) ((1+r)/r)² dr ≤ |f|²_{ℋ⁴}`
(`Work.Spaces.HkSq α 4 f`).

Intended proof, for each `r > 0`, a.e. in `θ`: the `i = 0` summand of
`Work.Spaces.HkIntegrand α 4 f r θ` is `(f r θ · w(r)/sin(2θ)^{η/2})²` with
`w(r) = (1+r)²/r²` (`Work.Spaces.w`); on `0 < θ < π/2` one has `0 < sin(2θ) ≤ 1`, so
`1/sin(2θ)^{η/2} ≥ 1` and
`(f r θ)² ((1+r)/r)² ≤ (f r θ)² w(r)² ≤ (f r θ · w(r)/sin(2θ)^{η/2})² ≤ HkIntegrand α 4 f r θ`
(use `Work.Spaces.sq_le_HkIntegrand_z` with `i = 0`; the angular boundary points
`θ = 0, π/2`, where the weight vanishes, form a null set — rewrite with
`MeasureTheory.Ioo_ae_eq_Icc`).  Multiplying by the constant `((1+r)/r)²`
(`MeasureTheory.integral_const_mul`) and integrating the a.e. slice bound over `Iθ` with
`MeasureTheory.integral_mono_of_nonneg` (the majorant `θ ↦ HkIntegrand α 4 f r θ` is integrable
by the first component of `HkMem`) gives the slice bound.  The majorant
`r ↦ ∫_θ HkIntegrand α 4 f r θ` is integrable on `Ioi 0` because it is integrable on
`Iz ⊇ Ioi 0` (second component of `HkMem`, `MeasureTheory.Integrable.mono_measure` with
`MeasureTheory.Measure.restrict_mono_set`); `MeasureTheory.integral_mono_of_nonneg` over `r`,
`MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici 0).symm` and the definition
`HkSq α 4 f = ∫_{z ∈ Iz} ∫_θ HkIntegrand α 4 f z θ` finish.  The integrability of the integrand
on `Ioi 0` follows from the same slice bound by `MeasureTheory.Integrable.mono'` together with
the a.e. strong measurability of `r ↦ (∫_θ f r θ²)((1+r)/r)²`. -/
theorem PhiWeight (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd f)
    (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn
        (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
        (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ),
          (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f := by
  have hIo_meas : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
  -- `(0,π/2)` and `Iθ` carry the same measure
  have hrestrict : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) =
      MeasureTheory.volume.restrict Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := π / 2))
  -- the pointwise bound holds on the open quadrant
  have hpoint : ∀ r : ℝ, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (f r θ) ^ 2 * ((1 + r) / r) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ :=
    fun r hr θ hθ => phiWeight_pointwise α 4 f r hr θ hθ.1 hθ.2
  -- the slice bound for fixed `r > 0`
  have hslice_le : ∀ r : ℝ, 0 < r →
      (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ := by
    intro r hr
    have hrw : (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 =
        ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2 * ((1 + r) / r) ^ 2 :=
      (MeasureTheory.integral_mul_const (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (((1 + r) / r) ^ 2) (fun θ => (f r θ) ^ 2)).symm
    rw [hrw]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 r hr.le) ?_
    · exact Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
        rw [← hrestrict]
        exact self_mem_ae_restrict measurableSet_Ioo
      filter_upwards [hae] with θ hθ
      exact hpoint r hr θ hθ
  -- the majorant is integrable on `(0,∞)`
  have hK : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Ioi (0 : ℝ)) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  -- comparison of the two radial functions a.e.
  have hF_le : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ := by
    filter_upwards [self_mem_ae_restrict hIo_meas] with r hr
    exact hslice_le r hr
  constructor
  · -- integrability, by domination by the majorant
    refine hK.mono' (phiWeight_aesm f hsm) ?_
    have hnn : ∀ r : ℝ,
        0 ≤ (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 := fun r =>
      mul_nonneg (integral_nonneg fun θ => sq_nonneg _) (sq_nonneg _)
    filter_upwards [hF_le] with r hr
    rw [Real.norm_of_nonneg (hnn r)]
    exact hr
  · -- the numerical bound
    refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hK hF_le) ?_
    · exact Filter.Eventually.of_forall fun r =>
        mul_nonneg (integral_nonneg fun θ => sq_nonneg _) (sq_nonneg _)
    · rw [MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
      rfl

end Work.FTS.H2
