/-
# `Submission/Work/FTS_MuLipC/RowN/FaSlice.lean` — a.e. `θ`-slice integrability from `Fa < ⊤`

`Work.FTS.Nonlinear.Pieces.Fa f = ∫⁻_{r>0} r⁻¹ ∫⁻_{θ ∈ Iθ} |K θ · f r θ|` is the
`L¹(r⁻¹dr)`-density functional that dominates `|L₁₂(f)(0)|`
(`Work.FTS.Nonlinear.Pieces.ofReal_L12_le`); its finiteness is what the row estimates of the
`μ`-row control.  The present lemma extracts from `Fa f < ⊤` the pointwise consequence needed
downstream: for almost every radius `r > 0`, the angular slice `θ ↦ K θ · f r θ` is integrable
on `Iθ`.  This is the shape in which the slices are consumed by
`Submission/Work/FTS_MuLipC/RowN/_work1.lean` (via `IntegrableOn.congr_fun` and
`div_eq_inv_mul`, which turns `K θ · f r θ` into the `L₁₂dens`-integrand `K θ · f r θ / r`).

## The proof

Two almost-everywhere facts, intersected:

* *measurability of the slices.*  `haesm` is the joint a.e. strong measurability of
  `uncurry f` for the product `volume.restrict (Ioi 0) × volume.restrict Iθ`; Mathlib's
  `AEStronglyMeasurable.prodMk_left` turns it into a.e. (in `r`) strong measurability of
  `θ ↦ f r θ`.
* *finiteness of the slices.*  The integrand of `Fa f` is
  `F r = ofReal r⁻¹ · ∫⁻_{θ ∈ Iθ} ofReal |K θ · f r θ|`, an ENNReal-valued function of `r`.
  It is `AEMeasurable`: `r ↦ ofReal r⁻¹` is measurable, and the inner lintegral is
  `AEMeasurable` by `AEMeasurable.lintegral_prod_right'` applied to the jointly a.e. measurable
  `(r,θ) ↦ ofReal |K θ · f r θ|` (built from `haesm.aemeasurable`, the measurability of `K`,
  `AEMeasurable.abs` and `AEMeasurable.ennreal_ofReal`).  Hence `ae_lt_top'` gives
  `F r < ⊤` a.e.; and for `r ∈ Ioi 0` the factor `ofReal r⁻¹` is neither `0` nor `⊤`, so
  `F r = ⊤` would force `∫⁻_{θ ∈ Iθ} ofReal |K θ · f r θ| = ⊤` — contrapositive.

On the intersection, `Integrable` is assembled from `AEStronglyMeasurable.mul` (with the
continuous, hence measurable, weight `K`) and `hasFiniteIntegral_iff_norm`
(`‖·‖ = |·|` on `ℝ`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.Nonlinear.Pieces.rl1Bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

set_option autoImplicit false

/-- **A.e. slice integrability from the finiteness of `Fa`.**  If `uncurry f` is a.e. strongly
measurable for `volume.restrict (Ioi 0) × volume.restrict Iθ` and `Fa f < ⊤`, then for almost
every `r > 0` the angular slice `θ ↦ K θ · f r θ` is integrable on `Iθ`. -/
theorem FaSlice {f : ℝ → ℝ → ℝ}
    (haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hfa : Work.FTS.Nonlinear.Pieces.Fa f < ⊤) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ := by
  -- ## the a.e. strong measurability of the slices
  have hslice : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.AEStronglyMeasurable (fun θ => f r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    simpa only [Function.uncurry_apply_pair] using haesm.prodMk_left
  -- ## the a.e. finiteness of the angular lintegral
  have hB : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f r θ|) < ⊤ := by
    have hmeas1 : AEMeasurable (Function.uncurry f)
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := haesm.aemeasurable
    have hKp : Measurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
      unfold Work.Spaces.K; fun_prop
    have hprod : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry f p)
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      hKp.aemeasurable.mul hmeas1
    have habs : AEMeasurable
        (fun p : ℝ × ℝ => ENNReal.ofReal |Work.Spaces.K p.2 * Function.uncurry f p|)
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      hprod.abs.ennreal_ofReal
    have hB_aem : AEMeasurable (fun r : ℝ =>
        ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f r θ|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      simpa only [Function.uncurry_apply_pair] using habs.lintegral_prod_right'
    have hFinv_aem : AEMeasurable (fun r : ℝ => ENNReal.ofReal r⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ENNReal.measurable_ofReal.comp measurable_inv).aemeasurable
    have hF_aem : AEMeasurable (fun r : ℝ => ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f r θ|))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      hFinv_aem.mul hB_aem
    have hlt : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f r θ|)) < ⊤ := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hfa
    filter_upwards [MeasureTheory.ae_lt_top' hF_aem (ne_of_lt hlt),
      MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr hrI
    by_contra hBtop
    have hBeq : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * f r θ|) = ⊤ :=
      le_antisymm le_top (not_lt.mp hBtop)
    have hne : ENNReal.ofReal r⁻¹ ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hrI))
    have hthis : ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * f r θ|) = ⊤ := by
      rw [hBeq, ENNReal.mul_eq_top]
      exact Or.inl ⟨hne, rfl⟩
    exact absurd hr (by rw [hthis]; exact not_lt.mpr le_top)
  -- ## assembly: `Integrable = AEStronglyMeasurable ∧ HasFiniteIntegral`
  have hKmeas : Measurable Work.Spaces.K := by unfold Work.Spaces.K; fun_prop
  filter_upwards [hslice, hB] with r hr hm
  refine ⟨?_, ?_⟩
  · exact hKmeas.aestronglyMeasurable.mul hr
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs] using hm

end Work.FTS_MuLipC.RowN
