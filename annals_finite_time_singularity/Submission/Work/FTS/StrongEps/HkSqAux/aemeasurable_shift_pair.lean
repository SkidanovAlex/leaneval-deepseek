/-
Copyright: work module for the Elgindi finite-time singularity project.

# Measurability of the shifted kernel pair

`HkSq_Jeps_le` (E1 of the `StrongEps` design) bounds the weighted `L²` norm of `J_ε` by a
constant times the norm of the profile; the first step of any such estimate is that the
integrand is measurable as a function of the pair
`(x, θ) ∈ (ℝ × ℝ) × (ℝ × ℝ)`, namely the pair of *base point* `q.1 = (z, θ)` and
*shift* `q.2 = p`, evaluated at the shifted point
`(zShift z p.1, thShift θ p.2) ∈ Quad`.

The kernel factor `Jker ρ ε q.2` is continuous as soon as `ρ` is (no support/mass/nonnegativity
hypothesis is needed for measurability), so the only content of the present lemma is the
profile factor: `G` is assumed only `ContinuousOn Quad`, and the shift map lands in `Quad`
for every base point in `Quad` — a conull set for the measure
`(volume.restrict Iz × volume.restrict Iθ) × volume`, the complement being the union of the
two coordinate hyperplanes `z = 0`, `θ = 0`, `θ = π/2`, which is null.

The proof is the standard "a.e. continuous ⟹ a.e. measurable" argument: on the conull set
`S = {q | q.1 ∈ Quad}` the composite is continuous (the only point needing care is
`Real.tan`, which is continuous on `{x | cos x ≠ 0} ⊇ (0, π/2)`, whence
`Real.continuousOn_tan`), so it is `AEMeasurable` for `μ.restrict S`; multiplying by the
indicator of `S` (measurable set) and using that `S` is conull gives `AEMeasurable` for `μ`.
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

open Work.FTS.StrongEps
open Work.Spaces

/-! ## Elementary facts about `Jker`, the shifts and the quadrant -/

/-- `Jker ρ ε` is continuous as soon as `ρ` is: no support/mass hypothesis is needed here. -/
private lemma continuous_Jker_of_continuous (ρ : ℝ × ℝ → ℝ) (hρc : Continuous ρ) (ε : ℝ) :
    Continuous (Jker ρ ε) := by
  have h : Jker ρ ε = fun p : ℝ × ℝ => ε⁻¹ ^ 2 * ρ (ε⁻¹ • p) := by
    funext p; simp only [Jker]
  rw [h]
  exact continuous_const.mul (hρc.comp (continuous_const_smul ε⁻¹))

/-- On the quadrant, `cos` does not vanish, so `tan` is continuous there. -/
private lemma cos_ne_zero_of_mem_quad {q : (ℝ × ℝ) × (ℝ × ℝ)} (hq : q.1 ∈ Quad) :
    Real.cos q.1.2 ≠ 0 := by
  have h2 : q.1.2 ∈ Set.Ioo 0 (π / 2) := hq.2
  exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h2.1], h2.2⟩).ne'

/-- The `θ`-shift map is continuous on the set of base points in the quadrant
(the monotone `tan` factor is harmless there because `cos ≠ 0`). -/
private lemma continuousOn_tan_quad :
    ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => Real.tan q.1.2) {q | q.1 ∈ Quad} :=
  Real.continuousOn_tan.comp (by fun_prop) (fun q hq => cos_ne_zero_of_mem_quad hq)

/-- The `θ`-shift is continuous on the set of base points in the quadrant. -/
private lemma continuousOn_thShift_quad :
    ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => thShift q.1.2 q.2.2) {q | q.1 ∈ Quad} := by
  have h1 : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.tan q.1.2 * Real.exp (-q.2.2)) {q | q.1 ∈ Quad} :=
    continuousOn_tan_quad.mul (Real.continuous_exp.comp_continuousOn (by fun_prop))
  have := Real.continuous_arctan.comp_continuousOn h1
  simpa only [thShift, Function.comp_def] using this

/-- The pair of shifts is continuous on the set of base points in the quadrant. -/
private lemma continuousOn_shift_quad :
    ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      (zShift q.1.1 q.2.1, thShift q.1.2 q.2.2)) {q | q.1 ∈ Quad} := by
  refine ContinuousOn.prodMk ?_ continuousOn_thShift_quad
  simp only [zShift]
  fun_prop

/-- The shifted point of a base point of the quadrant lies again in the quadrant. -/
private lemma shift_mem_Quad {q : (ℝ × ℝ) × (ℝ × ℝ)} (hq : q.1 ∈ Quad) :
    (zShift q.1.1 q.2.1, thShift q.1.2 q.2.2) ∈ Quad :=
  ⟨zShift_pos hq.1, thShift_mem hq.2⟩

/-! ## The two null sets of the boundary -/

/-- `z = 0` is null for `volume.restrict Iz` with `Iz = [0, ∞)`. -/
private lemma measure_Iz_compl_Ioi : (volume.restrict Iz) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioi.compl]
  refine measure_mono_null ?_ (measure_singleton (0 : ℝ))
  intro x hx
  simp only [Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff, Set.mem_Ioi,
    Set.mem_singleton_iff] at hx ⊢
  exact le_antisymm (not_lt.mp hx.1) hx.2

/-- `θ = 0` and `θ = π/2` are null for `volume.restrict Iθ` with `Iθ = [0, π/2]`. -/
private lemma measure_Iθ_compl_Ioo : (volume.restrict Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  have h0 : (volume : Measure ℝ) ({0} ∪ {π / 2}) = 0 :=
    measure_union_null (measure_singleton 0) (measure_singleton (π / 2))
  refine measure_mono_null ?_ h0
  intro x hx
  simp only [Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
    Set.mem_union, Set.mem_singleton_iff] at hx ⊢
  obtain ⟨hxn, hxI⟩ := hx
  rcases lt_or_ge (0 : ℝ) x with h | h
  · rcases lt_or_ge x (π / 2) with h2 | h2
    · exact absurd ⟨h, h2⟩ hxn
    · exact Or.inr (le_antisymm hxI.2 h2)
  · exact Or.inl (le_antisymm h hxI.1)

/-- The complement of the quadrant is null for `(volume.restrict Iz).prod (volume.restrict Iθ)`:
it is contained in the union of the two coordinate hyperplanes. -/
private lemma measure_quad_compl :
    (volume.restrict Iz).prod (volume.restrict Iθ) Quadᶜ = 0 := by
  have hsub : Quadᶜ ⊆ (Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ := by
    intro x hx
    simp only [Quad, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, not_and,
      Set.mem_union, Set.mem_univ, and_true, true_and] at hx ⊢
    tauto
  have h1 : (volume.restrict Iz).prod (volume.restrict Iθ)
      ((Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
        (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ) = 0 := by
    rw [measure_union_null_iff]
    constructor
    · rw [Measure.prod_prod, measure_Iz_compl_Ioi, zero_mul]
    · rw [Measure.prod_prod, measure_Iθ_compl_Ioo, mul_zero]
  exact measure_mono_null hsub h1

/-- The set of pairs whose base point is *not* in the quadrant is null for the full
three-dimensional measure `((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume`. -/
private lemma measure_compl_quad_prod :
    (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume)
      ({q : (ℝ × ℝ) × (ℝ × ℝ) | q.1 ∈ Quad}ᶜ) = 0 := by
  have hset : ({q : (ℝ × ℝ) × (ℝ × ℝ) | q.1 ∈ Quad}ᶜ : Set ((ℝ × ℝ) × (ℝ × ℝ))) =
      Quadᶜ ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
    ext q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
  rw [hset, Measure.prod_prod, measure_quad_compl]
  simp

/-! ## The target -/

theorem aemeasurable_shift_pair {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (fun q : ℝ × ℝ => G q.1 q.2) Work.FTS.StrongEps.Quad)
    (ρ : ℝ × ℝ → ℝ) (hρc : Continuous ρ) (ε : ℝ) :
    AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Work.FTS.StrongEps.Jker ρ ε q.2) *
          ENNReal.ofReal (G (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
            (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
  classical
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {q | q.1 ∈ Quad} with hSdef
  -- `S` is the (measurable) set of base points in the quadrant, and it is conull.
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact ((isOpen_Ioi.prod isOpen_Ioo).preimage continuous_fst).measurableSet
  have hnull : (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) Sᶜ = 0 := by
    rw [hSdef]
    exact measure_compl_quad_prod
  -- On `S` the composed profile is continuous.
  have hcont : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2)) S := by
    rw [hSdef]
    exact hG.comp continuousOn_shift_quad (fun q hq => shift_mem_Quad hq)
  have hA : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2))
      (Measure.restrict (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) S) :=
    hcont.aemeasurable hSmeas
  -- Multiplication by the indicator of `S`, and removal of the indicator with the conullity.
  have hind : AEMeasurable (S.indicator (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2)))
      (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) :=
    (aemeasurable_indicator_iff hSmeas).mpr hA
  have hcongr : (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2)) =ᵐ[
        (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume)]
      S.indicator (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2)) := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq
    simp only [Set.mem_compl_iff, not_not] at hq
    exact (Set.indicator_of_mem hq (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2))).symm
  have hGae : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2))
      (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) :=
    hind.congr hcongr.symm
  -- `ENNReal.ofReal` preserves a.e. measurability, as does the pointwise product.
  have hGenn : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2)))
      (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hGae
  have hJnn : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (Jker ρ ε q.2))
      (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuous_Jker_of_continuous ρ hρc ε).comp continuous_snd).aemeasurable)
  exact hJnn.mul hGenn

end Work.FTS.StrongEps.HkSqAux
