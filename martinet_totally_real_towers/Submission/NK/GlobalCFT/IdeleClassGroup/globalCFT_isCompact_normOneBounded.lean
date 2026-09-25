import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup.CompactDefs
import Submission.NK.GlobalCFT.IdeleClassGroup.CompactPieces
import Submission.NK.GlobalCFT.IdeleClassGroup.isCompact_annulus_infinite
import Submission.NK.GlobalCFT.IdeleClassGroup.isCompact_annulus_finite
import Submission.NK.GlobalCFT.IdeleClassGroup.isClosed_normOne

/-!
# The bounded norm-one idèles are compact

For a number field `K`, a finite set `S` of nonarchimedean places and a constant `C ≥ 1`, the set

`normOneBounded K S C = {x ∈ 𝕀¹ K | x` is a local unit outside `S`, is bounded by `C⁻¹` below at
the places of `S`, and has all archimedean components in the annulus `[C⁻¹, C]`}`

is compact.  This is the compactness half of the finiteness theorem for the idèle class group:
the bounded idèles form a product of compact local pieces inside the restricted product `𝕀 K`, and
the norm-one condition cuts out a closed subset of it.

The proof follows the standard shape of the compactness of unitary idèles
(`NK.GlobalCFT.Ideles.globalCFT_unityIdeles_isCompact`).  Let `Sᶜ` be the set of places which are
not of the form `ofFinite q` with `q ∈ S`.  The restricted product with respect to the principal
filter `𝓟 Sᶜ` is embedded in `𝕀 K` by `RestrictedProduct.inclusion`; inside it the product
`∏_v C_v` of the local pieces `C_v = localPiece K S C v` is compact by Tychonoff's theorem, its
image in `𝕀 K` is therefore compact, and the norm-one idèles which are locally bounded are exactly
its intersection with the closed subgroup `𝕀¹ K` of idèles of content one.

## Main result

* `NK.GlobalCFT.IdeleClassGroup.globalCFT_isCompact_normOneBounded`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct Filter
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- **The local pieces are compact.**  At an archimedean place the local piece is the compact
annulus `{C⁻¹ ≤ ‖z‖ ≤ C}`, at a nonarchimedean place of `S` it is the compact annulus
`{C⁻¹ ≤ ‖y‖ ≤ 1}` and at a nonarchimedean place outside `S` it is the compact group `𝒪_qˣ` of
local units. -/
private theorem isCompact_localPiece {S : Finset (HeightOneSpectrum (𝓞 K))} {C : ℝ}
    (hC : 0 < C) (v : Place K) : IsCompact (localPiece K S C v) := by
  rcases v with w | q
  · rw [localPiece_ofInfinite]
    exact isCompact_annulus_infinite w hC
  · by_cases hq : q ∈ S
    · rw [localPiece_ofFinite_of_mem hq]
      exact isCompact_annulus_finite q hC
    · rw [localPiece_ofFinite_of_not_mem hq]
      exact NK.GlobalCFT.LocalField.globalCFT_localUnits_isCompact_finite q

/-- **Compactness of a product of local pieces inside a restricted product.**  Let
`C i ⊆ A i` for `i ∈ s` and let every `C i` be compact; then the image, under the inclusion of the
piece `Πʳ i, [R i, A i]_[𝓟 s]` into `Πʳ i, [R i, A i]_[𝓕]`, of the product `∏_i C i` is compact.
This is Tychonoff's theorem together with the fact that `Πʳ i, [R i, A i]_[𝓟 s]` carries the
subspace topology of the full product `∏_i R i`. -/
theorem isCompact_inclusion_image_pi {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    {A : (i : ι) → Set (R i)} {C : (i : ι) → Set (R i)} {s : Set ι}
    {𝓕 : Filter ι} (h : 𝓕 ≤ 𝓟 s) (hCsub : ∀ i ∈ s, C i ⊆ A i) (hC : ∀ i, IsCompact (C i)) :
    IsCompact (RestrictedProduct.inclusion R A h '' ((↑) ⁻¹' (Set.univ.pi C) :
      Set (Πʳ i, [R i, A i]_[𝓟 s]))) := by
  have hW : IsCompact ((↑) ⁻¹' (Set.univ.pi C) : Set (Πʳ i, [R i, A i]_[𝓟 s])) := by
    refine (RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
      (S := s)).isInducing.isCompact_preimage' (isCompact_univ_pi hC) ?_
    intro x hx
    rw [RestrictedProduct.range_coe_principal]
    intro i hi
    exact hCsub i hi (Set.mem_univ_pi.mp hx i)
  exact hW.image (RestrictedProduct.continuous_inclusion h)

theorem globalCFT_isCompact_normOneBounded {K : Type*} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {C : ℝ}
    (hC : 1 ≤ C) : IsCompact (NK.GlobalCFT.IdeleClassGroup.normOneBounded K S C) := by
  classical
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  -- the places where the local piece is not the group of local units
  set s : Set (Place K) := (Place.ofFinite '' (S : Set (HeightOneSpectrum (𝓞 K))))ᶜ with hs
  have hsfin : sᶜ.Finite := by
    rw [hs]
    simpa using (S.finite_toSet).image Place.ofFinite
  have hle : Filter.cofinite ≤ 𝓟 s :=
    Filter.le_principal_iff.mpr (Filter.mem_cofinite.mpr hsfin)
  -- the compact piece of the restricted product, and its image in the idèles
  set Kset : Set (Idele K) := RestrictedProduct.inclusion
    (fun v : Place K => (Place.localField K v)ˣ)
    (fun v : Place K => (Place.localUnits K v : Set _)) hle ''
    ((↑) ⁻¹' (Set.univ.pi (localPiece K S C)) :
      Set (Πʳ v : Place K, [(Place.localField K v)ˣ, Place.localUnits K v]_[𝓟 s])) with hKset
  have hKset_compact : IsCompact Kset := by
    rw [hKset]
    refine isCompact_inclusion_image_pi hle (fun v hv => ?_) (isCompact_localPiece hCpos)
    rw [hs] at hv
    exact localPiece_subset_localUnits_of_notMem_image hv
  -- every locally bounded norm-one idèle lies in the compact piece
  have hsub : normOneBounded K S C ⊆ Kset := by
    intro x hx
    obtain ⟨hxloc, hxnorm⟩ := hx
    rw [hKset]
    refine ⟨RestrictedProduct.mk (fun v => x.1 v) ?_, ?_, ?_⟩
    · rw [Filter.eventually_principal]
      intro v hv
      rw [hs] at hv
      rcases v with w | q
      · exact Subgroup.mem_top _
      · exact mem_localUnits_ofFinite_of_norm_eq_one
          (hxloc.1.1 q (fun hq => hv ⟨q, Finset.mem_coe.mpr hq, rfl⟩))
    · rw [Set.mem_preimage, Set.mem_univ_pi]
      intro v
      simp only [RestrictedProduct.mk_apply]
      rcases v with w | q
      · exact hxloc.2 w
      · by_cases hq : q ∈ S
        · rw [localPiece_ofFinite_of_mem hq]
          exact hxloc.1.2 q hq
        · rw [localPiece_ofFinite_of_not_mem hq]
          exact mem_localUnits_ofFinite_of_norm_eq_one (hxloc.1.1 q hq)
    · ext v
      rfl
  -- conversely, a norm-one idèle in the compact piece is locally bounded
  have hsub' : Kset ∩ (Idele.normOne K : Set (Idele K)) ⊆ normOneBounded K S C := by
    rintro x ⟨hxK, hxnorm⟩
    rw [hKset] at hxK
    obtain ⟨y, hyW, rfl⟩ := hxK
    have hyv : ∀ v : Place K, y v ∈ localPiece K S C v :=
      fun v => Set.mem_univ_pi.mp hyW v
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hxnorm⟩
    · intro q hq
      have h := hyv (Place.ofFinite q)
      rw [localPiece_ofFinite_of_not_mem hq] at h
      change ‖(y (Place.ofFinite q) : q.adicCompletion K)‖ = 1
      exact norm_eq_one_of_mem_localUnits_ofFinite h
    · intro q hq
      have h := hyv (Place.ofFinite q)
      rw [localPiece_ofFinite_of_mem hq] at h
      change C⁻¹ ≤ ‖(y (Place.ofFinite q) : q.adicCompletion K)‖ ∧
        ‖(y (Place.ofFinite q) : q.adicCompletion K)‖ ≤ 1
      exact h
    · intro w
      have h := hyv (Place.ofInfinite w)
      rw [localPiece_ofInfinite] at h
      change C⁻¹ ≤ ‖(y (Place.ofInfinite w) : w.Completion)‖ ∧
        ‖(y (Place.ofInfinite w) : w.Completion)‖ ≤ C
      exact h
  rw [show normOneBounded K S C = Kset ∩ (Idele.normOne K : Set (Idele K)) from
    Set.Subset.antisymm (fun x hx => ⟨hsub hx, hx.2⟩) hsub']
  exact hKset_compact.inter_right isClosed_normOne

end NK.GlobalCFT.IdeleClassGroup

