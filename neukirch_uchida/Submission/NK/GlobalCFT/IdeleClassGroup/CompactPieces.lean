/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup.CompactDefs
import Submission.NK.GlobalCFT.LocalField.Topology

/-!
# The local pieces of the bounded norm-one idèles

For a number field `K`, a finite set `S` of nonarchimedean places and a constant `C`, the set
`NK.GlobalCFT.IdeleClassGroup.normOneBounded K S C` of norm-one idèles which are locally
bounded is cut out, place by place, by the conditions

* at a nonarchimedean place `q ∈ S`: `C⁻¹ ≤ ‖y‖ ≤ 1`,
* at a nonarchimedean place `q ∉ S`: `y` is a local unit (equivalently `‖y‖ = 1`),
* at an archimedean place `w`: `C⁻¹ ≤ ‖y‖ ≤ C`.

This file defines the corresponding family of local sets `localPiece K S C`.

## Main definitions

* `NK.GlobalCFT.IdeleClassGroup.localPiece`

## Main results

* `NK.GlobalCFT.IdeleClassGroup.mem_localUnits_ofFinite_of_norm_eq_one`: at a nonarchimedean
  place, an element of norm `1` is a local unit;
* `NK.GlobalCFT.IdeleClassGroup.localPiece_subset_localUnits`: away from `S` the local piece is
  contained in the local units, which is what makes the restricted-product description work.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- **The local pieces of the bounded idèles.**  The family of local conditions whose (restricted)
product describes the locally bounded idèles. -/
noncomputable def localPiece (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (C : ℝ) :
    (v : Place K) → Set ((Place.localField K v)ˣ)
  | Sum.inl w => {z : w.Completionˣ | C⁻¹ ≤ ‖(z : w.Completion)‖ ∧ ‖(z : w.Completion)‖ ≤ C}
  | Sum.inr q => by
      classical
      exact if q ∈ S then
        {y : (q.adicCompletion K)ˣ | C⁻¹ ≤ ‖(y : q.adicCompletion K)‖ ∧
          ‖(y : q.adicCompletion K)‖ ≤ 1}
      else (Place.localUnits K (Place.ofFinite q) : Set _)

@[simp]
theorem localPiece_ofInfinite (S : Finset (HeightOneSpectrum (𝓞 K))) (C : ℝ)
    (w : InfinitePlace K) :
    localPiece K S C (Place.ofInfinite w) =
      {z : w.Completionˣ | C⁻¹ ≤ ‖(z : w.Completion)‖ ∧ ‖(z : w.Completion)‖ ≤ C} := rfl

theorem localPiece_ofFinite_of_mem {S : Finset (HeightOneSpectrum (𝓞 K))} {C : ℝ}
    {q : HeightOneSpectrum (𝓞 K)} (hq : q ∈ S) :
    localPiece K S C (Place.ofFinite q) =
      {y : (q.adicCompletion K)ˣ | C⁻¹ ≤ ‖(y : q.adicCompletion K)‖ ∧
        ‖(y : q.adicCompletion K)‖ ≤ 1} := by
  classical
  simp only [localPiece]
  rw [if_pos hq]

theorem localPiece_ofFinite_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 K))} {C : ℝ}
    {q : HeightOneSpectrum (𝓞 K)} (hq : q ∉ S) :
    localPiece K S C (Place.ofFinite q) = (Place.localUnits K (Place.ofFinite q) : Set _) := by
  classical
  simp only [localPiece]
  rw [if_neg hq]

/-- Away from the finite set `S`, the local piece is contained in the local units.  Since the
local units at an archimedean place are everything, this holds at every place which is not of
the form `ofFinite q` with `q ∈ S`. -/
theorem localPiece_subset_localUnits {S : Finset (HeightOneSpectrum (𝓞 K))} {C : ℝ}
    {v : Place K} (hv : ∀ q ∈ S, v ≠ Place.ofFinite q) :
    localPiece K S C v ⊆ (Place.localUnits K v : Set _) := by
  classical
  rcases v with w | q
  · intro z hz
    simp [Place.localUnits_ofInfinite]
  · rw [localPiece_ofFinite_of_not_mem (K := K) (S := S) (C := C) (fun hq => hv q hq rfl)]

/-- At a nonarchimedean place, an element of `K_qˣ` of norm `1` is a local unit: the local units
are exactly the elements of valuation `1`, and `‖y‖ = 1` is equivalent to `v y = 1`. -/
theorem mem_localUnits_ofFinite_of_norm_eq_one {q : HeightOneSpectrum (𝓞 K)}
    {y : (q.adicCompletion K)ˣ} (h : ‖(y : q.adicCompletion K)‖ = 1) :
    y ∈ Place.localUnits K (Place.ofFinite q) := by
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  refine le_antisymm ?_ ?_
  · rw [← Valued.toNormedField.norm_le_one_iff, h]
  · rw [← Valued.toNormedField.one_le_norm_iff, h]

/-- The local piece at a nonarchimedean place away from `S` is the set of local units, phrased
as the set of elements of norm `1`. -/
theorem localPiece_ofFinite_of_not_mem_eq_norm_eq_one {S : Finset (HeightOneSpectrum (𝓞 K))}
    {C : ℝ} {q : HeightOneSpectrum (𝓞 K)} (hq : q ∉ S) :
    localPiece K S C (Place.ofFinite q) =
      {y : (q.adicCompletion K)ˣ | ‖(y : q.adicCompletion K)‖ = 1} := by
  rw [localPiece_ofFinite_of_not_mem hq]
  ext y
  exact ⟨norm_eq_one_of_mem_localUnits_ofFinite, mem_localUnits_ofFinite_of_norm_eq_one⟩

/-- The complement form of `localPiece_subset_localUnits`: away from the image of `S` under
`Place.ofFinite` the local piece is contained in the local units. -/
theorem localPiece_subset_localUnits_of_notMem_image {S : Finset (HeightOneSpectrum (𝓞 K))}
    {C : ℝ} {v : Place K}
    (hv : v ∉ Place.ofFinite '' (S : Set (HeightOneSpectrum (𝓞 K)))) :
    localPiece K S C v ⊆ (Place.localUnits K v : Set _) :=
  localPiece_subset_localUnits fun q hq hqv => hv ⟨q, Finset.mem_coe.mpr hq, hqv.symm⟩

end NK.GlobalCFT.IdeleClassGroup
