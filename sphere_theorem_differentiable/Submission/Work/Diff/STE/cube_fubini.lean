import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CubeSplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fubini for the unit cube: splitting off one coordinate

This file proves `Work.Diff.STE.cube_fubini`: for a continuous `F : (ι → ℝ) → ℂ` and a fixed
index `i : ι`,

`∫ x in unitCube ι, F x = ∫ y in unitCube {j // j ≠ i}, ∫ t in (0,1], F (insertAt i t y)`,

i.e. the integral over the half-open unit cube `(0,1]^ι` is the iterated integral where the
`i`-th coordinate is integrated innermost and the remaining coordinates are collected in the
subtype `{j : ι // j ≠ i}`.

The proof is measure theoretic:

* `restrict_unitCube_measure`: Lebesgue measure restricted to the cube is the product of the
  restricted one dimensional Lebesgue measures `unitIoc = volume.restrict (0,1]`
  (this is `Measure.restrict_pi_pi`).
* `measurePreserving_insertAt`: the "insert the `i`-th coordinate" map
  `(y, t) ↦ insertAt i t y` is a measure preserving map from
  `(Measure.pi fun _ : {j // j ≠ i} => unitIoc).prod unitIoc` to `Measure.pi fun _ : ι => unitIoc`.
  This is proved by `Measure.pi_eq`, i.e. by computing the measure of an arbitrary measurable
  rectangle `Set.pi univ s`: the preimage of such a rectangle is the product of the
  corresponding rectangle in the remaining coordinates with `s i`, and
  `Measure.pi_pi` together with `Fintype.prod_subtype_mul_prod_subtype` identifies
  `(∏ j : {j // j ≠ i}, ν (s j)) * ν (s i)` with `∏ j : ι, ν (s j)`.
* the transfer of the integral along this measure preserving map (`integral_map`) and
  Fubini on the product space (`integral_prod`); the integrability side condition follows from
  the continuity of `F` on the compact cube `[0,1]^ι`.
-/

noncomputable section

open MeasureTheory

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lebesgue measure restricted to the half open unit interval `(0,1]`. -/
def unitIoc : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)

instance instSigmaFiniteUnitIoc : SigmaFinite unitIoc := by rw [unitIoc]; infer_instance

omit [DecidableEq ι] in
/-- Lebesgue measure restricted to the unit cube is the product of the restricted one
dimensional Lebesgue measures. -/
lemma restrict_unitCube_measure :
    (volume : Measure (ι → ℝ)).restrict unitCube = Measure.pi (fun _ : ι => unitIoc) := by
  rw [unitCube, MeasureTheory.volume_pi]
  exact Measure.restrict_pi_pi (μ := fun _ : ι => (volume : Measure ℝ)) (fun _ => Set.Ioc (0 : ℝ) 1)

/-- The map `(y, t) ↦ insertAt i t y` is measurable. -/
lemma measurable_insertAt_pair (i : ι) :
    Measurable (fun p : ({j : ι // j ≠ i} → ℝ) × ℝ => insertAt i p.2 p.1) := by
  rw [measurable_pi_iff]
  intro j
  by_cases h : j = i
  · have hfun : (fun p : ({j : ι // j ≠ i} → ℝ) × ℝ => (insertAt i p.2 p.1) j)
        = fun p => p.2 := by
      funext p; rw [h]; simp
    rw [hfun]
    exact measurable_snd
  · have hfun : (fun p : ({j : ι // j ≠ i} → ℝ) × ℝ => (insertAt i p.2 p.1) j)
        = fun p => p.1 ⟨j, h⟩ := by
      funext p; exact insertAt_of_ne h p.2 p.1
    rw [hfun]
    exact (measurable_pi_apply (⟨j, h⟩ : {j : ι // j ≠ i})).comp measurable_fst

/-- The preimage of a rectangle under `(y, t) ↦ insertAt i t y`. -/
lemma insertAt_preimage (i : ι) (s : ι → Set ℝ) :
    (fun p : ({j : ι // j ≠ i} → ℝ) × ℝ => insertAt i p.2 p.1) ⁻¹' (Set.pi Set.univ s)
      = (Set.pi Set.univ fun j : {j : ι // j ≠ i} => s j) ×ˢ s i := by
  ext p
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
  constructor
  · intro h
    exact ⟨fun j => by simpa [insertAt_of_ne j.2] using h j.1, by simpa using h i⟩
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j = i
    · rw [hj]; simpa using h2
    · rw [insertAt_of_ne hj]; simpa using h1 ⟨j, hj⟩

/-- Inserting the `i`-th coordinate is a measure preserving map from the product of the
remaining coordinates and `ℝ` (both carrying the restricted Lebesgue measure `unitIoc`) to
the cube, carrying the product measure `Measure.pi (fun _ : ι => unitIoc)`. -/
lemma measurePreserving_insertAt (i : ι) :
    MeasurePreserving (fun p : ({j : ι // j ≠ i} → ℝ) × ℝ => insertAt i p.2 p.1)
      ((Measure.pi fun _ : {j : ι // j ≠ i} => unitIoc).prod unitIoc)
      (Measure.pi fun _ : ι => unitIoc) := by
  refine ⟨measurable_insertAt_pair i, ?_⟩
  refine (Measure.pi_eq (μ := fun _ : ι => unitIoc) fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_insertAt_pair i) (MeasurableSet.univ_pi hs),
    insertAt_preimage i s,
    Measure.prod_prod _ _,
    Measure.pi_pi]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j => j = i) (fun j => unitIoc (s j))]
  rw [mul_comm]
  congr 1
  rw [← Finset.prod_subtype ({i} : Finset ι) (fun x => by simp) (fun j => unitIoc (s j))]
  simp

/-- **Fubini for the unit cube.** The integral over `(0,1]^ι` is the iterated integral over
`(0,1]^{ι \ {i}}` and `(0,1]` in the `i`-th coordinate. -/
theorem cube_fubini {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (F : (ι → ℝ) → ℂ) (hF : Continuous F) :
    ∫ x in unitCube (ι := ι), F x
      = ∫ y in unitCube (ι := {j : ι // j ≠ i}),
          ∫ t in Set.Ioc (0 : ℝ) 1, F (insertAt i t y) := by
  have hL : (∫ x in unitCube (ι := ι), F x)
      = ∫ x, F x ∂(Measure.pi fun _ : ι => unitIoc) := by
    rw [restrict_unitCube_measure]
  have hR : (∫ y in unitCube (ι := {j : ι // j ≠ i}),
        ∫ t in Set.Ioc (0 : ℝ) 1, F (insertAt i t y))
      = ∫ y, (∫ t, F (insertAt i t y) ∂unitIoc)
          ∂(Measure.pi fun _ : {j : ι // j ≠ i} => unitIoc) := by
    rw [restrict_unitCube_measure]
    rfl
  have hIntF : Integrable F (Measure.pi fun _ : ι => unitIoc) := by
    rw [← restrict_unitCube_measure]
    exact IntegrableOn.mono_set
      (hF.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc))
      (fun x hx j _ => ⟨(hx j trivial).1.le, (hx j trivial).2⟩)
  have hInt : Integrable (fun p : ({j : ι // j ≠ i} → ℝ) × ℝ => F (insertAt i p.2 p.1))
      ((Measure.pi fun _ : {j : ι // j ≠ i} => unitIoc).prod unitIoc) :=
    (measurePreserving_insertAt i).integrable_comp_of_integrable hIntF
  rw [hL, hR, ← (measurePreserving_insertAt i).map_eq,
    integral_map (measurable_insertAt_pair i).aemeasurable hF.aestronglyMeasurable,
    ← integral_prod (fun p : ({j : ι // j ≠ i} → ℝ) × ℝ => F (insertAt i p.2 p.1)) hInt]

end Work.Diff.STE
