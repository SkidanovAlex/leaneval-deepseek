/-
Copyright: work module for the Elgindi finite-time singularity project.

# Measurability of the `J_ε` pair integrand against the angular slice measure

The `JepsHkMem` chapter controls the `H^k`-weighted norms of `J_ε`; every such estimate
integrates an explicit integrand in the variables `(θ, p) ∈ ℝ × (ℝ × ℝ)` against the measure
`(volume.restrict Iθ).prod volume`, where `θ` is the *base* angle and `p` is the *shift*, and the
profile is evaluated at the shifted point

  `q ↦ (zShift z p₁, thShift θ p₂)`,   `q = (θ, p)`.

The present lemma is the measurability of that integrand: the kernel factor `Jker ρ ε p` is
continuous as soon as `ρ` is (no support/mass/nonnegativity hypothesis is needed for
measurability), the exponential weight `exp (2c(|p₁| + |p₂|))` is continuous, and the only
content is the profile factor: `H` is assumed only `ContinuousOn Quad`, and for `θ ∈ (0, π/2)`
the shifted point lies in `Quad` (the base `z` is strictly positive by hypothesis).  The set
`{q | q.1 ∈ (0, π/2)}` is conull for `(volume.restrict Iθ).prod volume`, so the standard
"a.e. continuous ⟹ a.e. measurable" argument applies.
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_pair

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.JepsHkMem

open Work.FTS.StrongEps

/-! ## Elementary facts about `Jker`, the shifts and the angular interval -/

/-- `Jker ρ ε` is continuous as soon as `ρ` is: no support/mass/nonnegativity hypothesis is
needed for measurability. -/
private lemma continuous_Jker_of_continuous (ρ : ℝ × ℝ → ℝ) (hρc : Continuous ρ) (ε : ℝ) :
    Continuous (Jker ρ ε) := by
  have h : Jker ρ ε = fun p : ℝ × ℝ => ε⁻¹ ^ 2 * ρ (ε⁻¹ • p) := by
    funext p; simp only [Jker]
  rw [h]
  exact continuous_const.mul (hρc.comp (continuous_const_smul ε⁻¹))

/-- The endpoints `θ = 0`, `θ = π/2` are null for `volume.restrict Iθ`. -/
private lemma measure_Iθ_compl_Ioo :
    (volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  have h0 : (volume : Measure ℝ) ({0} ∪ {π / 2}) = 0 :=
    measure_union_null (measure_singleton 0) (measure_singleton (π / 2))
  refine measure_mono_null ?_ h0
  intro x hx
  simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
    Set.mem_union, Set.mem_singleton_iff] at hx ⊢
  obtain ⟨hxn, hxI⟩ := hx
  rcases lt_or_ge (0 : ℝ) x with h | h
  · rcases lt_or_ge x (π / 2) with h2 | h2
    · exact absurd ⟨h, h2⟩ hxn
    · exact Or.inr (le_antisymm hxI.2 h2)
  · exact Or.inl (le_antisymm h hxI.1)

/-- The complement of `{q | q.1 ∈ (0, π/2)}` is null for `(volume.restrict Iθ).prod volume`. -/
private lemma measure_compl_Ioo_prod :
    ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ)))
      ({q : ℝ × (ℝ × ℝ) | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)}ᶜ) = 0 := by
  have hset : ({q : ℝ × (ℝ × ℝ) | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)}ᶜ :
      Set (ℝ × (ℝ × ℝ))) = (Set.Ioo (0 : ℝ) (π / 2))ᶜ ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
    ext q; simp
  rw [hset, Measure.prod_prod, measure_Iθ_compl_Ioo]
  simp

/-- The `θ`-shift, as a function of the angular coordinate, is continuous on `(0, π/2)`. -/
private lemma continuousOn_thShift_slice :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => thShift q.1 q.2.2)
      {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by
  have htan : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Real.tan q.1)
      {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by
    refine Real.continuousOn_tan.comp continuous_fst.continuousOn (fun q hq => ?_)
    simp only [Set.mem_ofPred_eq] at hq
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hq.1], hq.2⟩).ne'
  have h1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Real.tan q.1 * Real.exp (-q.2.2))
      {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} :=
    htan.mul (Real.continuous_exp.comp_continuousOn (continuous_snd.snd.neg).continuousOn)
  have h2 := Real.continuous_arctan.comp_continuousOn h1
  simpa only [thShift, Function.comp_def] using h2

/-- The `z`-shift of the base `z` is continuous (in the shift variable). -/
private lemma continuousOn_zShift_theta (z : ℝ) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => zShift z q.2.1)
      {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by
  simp only [zShift]
  exact (continuous_const.mul (Real.continuous_exp.comp (continuous_snd.fst.neg))).continuousOn

/-- The shifted point, as a function of `(θ, p)`, is continuous on `{θ ∈ (0, π/2)}`. -/
private lemma continuousOn_shift_pair_theta (z : ℝ) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (zShift z q.2.1, thShift q.1 q.2.2))
      {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} :=
  ContinuousOn.prodMk (continuousOn_zShift_theta z) continuousOn_thShift_slice

/-- For `θ ∈ (0, π/2)` and `z > 0`, the shifted point lies in the quadrant. -/
private lemma shift_mem_Quad_theta {z : ℝ} (hz : 0 < z) {q : ℝ × (ℝ × ℝ)}
    (hq : q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (zShift z q.2.1, thShift q.1 q.2.2) ∈ Quad :=
  ⟨zShift_pos hz, thShift_mem hq⟩

/-! ## The target -/

theorem aemeasurable_pair_slice {H : ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2) Work.FTS.StrongEps.Quad)
    {ρ : ℝ × ℝ → ℝ} (hρc : Continuous ρ) {ε c z : ℝ} (hz : 0 < z) :
    AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (Work.FTS.StrongEps.Jker ρ ε q.2)
          * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
          * ENNReal.ofReal (H (Work.FTS.StrongEps.zShift z q.2.1)
              (Work.FTS.StrongEps.thShift q.1 q.2.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume) := by
  classical
  set S : Set (ℝ × (ℝ × ℝ)) := {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} with hSdef
  -- `S` is measurable and conull.
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact (isOpen_Ioo.preimage continuous_fst).measurableSet
  have hnull : ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) Sᶜ = 0 := by
    rw [hSdef]
    exact measure_compl_Ioo_prod
  -- On `S`, the composed profile is continuous.
  have hcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      H (zShift z q.2.1) (thShift q.1 q.2.2)) S := by
    rw [hSdef]
    exact hH.comp (continuousOn_shift_pair_theta z)
      (fun q hq => shift_mem_Quad_theta hz hq)
  have hA : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      H (zShift z q.2.1) (thShift q.1 q.2.2))
      (Measure.restrict
        ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) S) :=
    hcont.aemeasurable hSmeas
  -- Multiply by the indicator of `S` and remove it again using conullity.
  have hind : AEMeasurable (S.indicator (fun q : ℝ × (ℝ × ℝ) =>
      H (zShift z q.2.1) (thShift q.1 q.2.2)))
      ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) :=
    (aemeasurable_indicator_iff hSmeas).mpr hA
  have hcongr : (fun q : ℝ × (ℝ × ℝ) => H (zShift z q.2.1) (thShift q.1 q.2.2))
      =ᵐ[((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ)))]
      S.indicator (fun q : ℝ × (ℝ × ℝ) => H (zShift z q.2.1) (thShift q.1 q.2.2)) := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq
    simp only [Set.mem_compl_iff, not_not] at hq
    exact (Set.indicator_of_mem hq
      (fun q : ℝ × (ℝ × ℝ) => H (zShift z q.2.1) (thShift q.1 q.2.2))).symm
  have hHae : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      H (zShift z q.2.1) (thShift q.1 q.2.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) :=
    hind.congr hcongr.symm
  have hHenn : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (H (zShift z q.2.1) (thShift q.1 q.2.2)))
      ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hHae
  -- The kernel factor.
  have hJ : AEMeasurable (fun q : ℝ × (ℝ × ℝ) => ENNReal.ofReal (Jker ρ ε q.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuous_Jker_of_continuous ρ hρc ε).comp continuous_snd).aemeasurable)
  -- The exponential weight factor.
  have hEcont : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      Real.exp (2 * c * (|q.2.1| + |q.2.2|))) :=
    Real.continuous_exp.comp (continuous_const.mul
      ((continuous_snd.fst.abs).add (continuous_snd.snd.abs)))
  have hE : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|))))
      ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hEcont.aemeasurable
  exact (hJ.mul hE).mul hHenn

end Work.FTS.StrongEps.JepsHkMem
