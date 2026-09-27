import Mathlib
import Submission.Work.EKLC7.Defs

/-!
# C7: collapsing two product formulae into a triple product formula

`TripleA` and `TripleB` (`Submission/Work/EKLC7/Defs.lean`) write the leafwise measure `νN` of the
Heisenberg group `Heis3 = ⟨U_ij, U_jk, U_ik⟩` as a *triple* product of the leafwise measures
`νij`, `νjk`, `νik` in the two orders, given the two-step decompositions
`Heis3 = U_ij ⋉ VjkIk`, `VjkIk = U_jk ⋉ U_ik` (whence `VjkIk = U_jk ⊔ U_ik`) resp.
`Heis3 = U_jk ⋉ VijIk`, `VijIk = U_ij ⋉ U_ik`.

The present file supplies the elementary associativity step: if

* `νN` is the image of `μ₁ ⊗ νV` under the multiplication map `(x, y) ↦ x * y`, with constant
  `c₁`, and
* `νV` is the image of `μ₂ ⊗ μ₃` under the multiplication map, with constant `c₂`,

then `νN` is the image of `μ₁ ⊗ μ₂ ⊗ μ₃` under the triple product, with constant `c₁ * c₂`.
The only mathematical content is the associativity of the group law together with the fact that
left translations act on compactly supported continuous functions (so that the second product
formula may be applied to the shifted test function `v ↦ f (x * v)`); the nested integrals are
congruent *termwise*, so no Fubini theorem and no σ-finiteness of the measures is needed.
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

noncomputable section

namespace Work.EKLC7

open MeasureTheory
open Work.EKLContract

/-- The left translate `v ↦ f (g * v)` of a compactly supported continuous function `f`, which is
again continuous with compact support, since left translation by `g` is a homeomorphism of the
group. -/
noncomputable def mulLeftTranslate (f : CompactlySupportedContinuousMap SL3 ℝ) (g : SL3) :
    CompactlySupportedContinuousMap SL3 ℝ :=
  f.comp (Homeomorph.toCocompactMap (Homeomorph.mulLeft g))

@[simp]
theorem mulLeftTranslate_apply (f : CompactlySupportedContinuousMap SL3 ℝ) (g v : SL3) :
    mulLeftTranslate f g v = f (g * v) := by
  simp [mulLeftTranslate]

/-- **Associativity of product formulae.**  If the measure `μN` is the image of `μ₁ ⊗ μV` under
multiplication (up to the constant `c₁`) and `μV` is the image of `μ₂ ⊗ μ₃` under multiplication
(up to the constant `c₂`), then `μN` is the image of `μ₁ ⊗ μ₂ ⊗ μ₃` under the triple product,
up to the constant `c₁ * c₂`. -/
theorem triple_formula {μ₁ μ₂ μ₃ μN μV : Measure SL3} {c₁ c₂ : ℝ}
    (hV : ∀ φ : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ x, φ x ∂μV = c₂ * ∫ x, (∫ y, φ (x * y) ∂μ₃) ∂μ₂)
    (hN : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ x, f x ∂μN = c₁ * ∫ x, (∫ y, f (x * y) ∂μV) ∂μ₁) :
    ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ x, f x ∂μN
        = (c₁ * c₂) * ∫ x, (∫ y, (∫ z, f (x * y * z) ∂μ₃) ∂μ₂) ∂μ₁ := by
  intro f
  -- the second product formula, applied to the left translate `v ↦ f (x * v)` of `f`
  have hstep : ∀ x, ∫ y, f (x * y) ∂μV
      = c₂ * ∫ y, (∫ z, f (x * (y * z)) ∂μ₃) ∂μ₂ := by
    intro x
    have h := hV (mulLeftTranslate f x)
    simpa only [mulLeftTranslate_apply] using h
  -- reassociate the innermost product
  have hfun : (fun x => ∫ y, f (x * y) ∂μV)
      = fun x => c₂ * ∫ y, (∫ z, f (x * y * z) ∂μ₃) ∂μ₂ := by
    funext x
    rw [hstep x]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [mul_assoc]
  -- pull the constants out of the integrals and collect them
  calc ∫ x, f x ∂μN
      = c₁ * ∫ x, (∫ y, f (x * y) ∂μV) ∂μ₁ := hN f
    _ = c₁ * (c₂ * ∫ x, (∫ y, (∫ z, f (x * y * z) ∂μ₃) ∂μ₂) ∂μ₁) := by
          rw [hfun, integral_const_mul]
    _ = (c₁ * c₂) * ∫ x, (∫ y, (∫ z, f (x * y * z) ∂μ₃) ∂μ₂) ∂μ₁ := by
          ring

theorem TripleCollapse {νN νij νjk νik νV1 νV2 : MeasureTheory.Measure Work.EKLContract.SL3}
    (hA : ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      ∫ g, f g ∂νN = c * ∫ g, (∫ u, f (g * u) ∂νV1) ∂νij)
    (hA' : ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      ∫ g, f g ∂νV1 = c * ∫ g, (∫ u, f (g * u) ∂νik) ∂νjk)
    (hB : ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      ∫ g, f g ∂νN = c * ∫ g, (∫ u, f (g * u) ∂νV2) ∂νjk)
    (hB' : ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      ∫ g, f g ∂νV2 = c * ∫ g, (∫ u, f (g * u) ∂νik) ∂νij) :
    (∃ cA : ℝ, 0 < cA ∧ Work.EKLC7.TripleA νN νij νjk νik cA) ∧
    (∃ cB : ℝ, 0 < cB ∧ Work.EKLC7.TripleB νN νij νjk νik cB) := by
  obtain ⟨cA, hcA, hAeq⟩ := hA
  obtain ⟨cA', hcA', hA'eq⟩ := hA'
  obtain ⟨cB, hcB, hBeq⟩ := hB
  obtain ⟨cB', hcB', hB'eq⟩ := hB'
  refine ⟨⟨cA * cA', mul_pos hcA hcA', ?_⟩, ⟨cB * cB', mul_pos hcB hcB', ?_⟩⟩
  · -- `νN ← (νij, νV1)` and `νV1 ← (νjk, νik)`
    exact triple_formula hA'eq hAeq
  · -- `νN ← (νjk, νV2)` and `νV2 ← (νij, νik)`
    exact triple_formula hB'eq hBeq

end Work.EKLC7
