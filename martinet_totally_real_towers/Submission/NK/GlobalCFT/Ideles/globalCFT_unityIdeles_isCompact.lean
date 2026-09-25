import Mathlib
import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.LocalField.globalCFT_localUnits_isCompact_finite

/-!
# The group of unitary idèles is compact

For a number field `K` the idèle group `𝕀 K` is the restricted product of the local unit
groups `K_vˣ`, over the places `v` of `K`, with respect to the groups `𝒪_vˣ` of local units
(which are all of `K_vˣ` at an archimedean place).  The subgroup
`NK.GlobalCFT.Idele.unityIdeles K ≤ 𝕀 K` of **unitary idèles** consists of the idèles which
are `1` at every archimedean place and local units at every nonarchimedean place, i.e. it is the
product `∏_{v finite} 𝒪_vˣ`.  Here we prove that it is compact.

The proof is an application of Tychonoff's theorem in the "product-piece" of the restricted
product.  Let `R v = K_vˣ`, `A v = 𝒪_vˣ` and consider the principal piece
`Πʳ v, [R v, A v]_[⊤]` of the idèle group, whose topology is the product topology of
`∏_v K_vˣ`.  The natural inclusion `inc` of this piece in `𝕀 K` is continuous.  Inside the
piece the unitary idèles are cut out by the conditions `y v ∈ C v`, where `C v = {1}` at the
archimedean places and `C v = A v` at the nonarchimedean ones.  Each `C v` is compact — `{1}` is
a singleton, and `𝒪_vˣ` is compact at a finite place by
`NK.GlobalCFT.LocalField.globalCFT_localUnits_isCompact_finite` — so `∏_v C v` is compact by
Tychonoff, and `unityIdeles K` is the continuous image of it under `inc`.

## Main result

* `NK.GlobalCFT.Ideles.globalCFT_unityIdeles_isCompact`: the unitary idèles are compact.
-/

set_option autoImplicit false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Ideles

open NK.GlobalCFT

/-- **The group of unitary idèles of a number field is compact.**

The unitary idèles `∏_{v finite} 𝒪_vˣ` are the image, under the continuous inclusion of the
"local units everywhere" piece `Πʳ v, [K_vˣ, 𝒪_vˣ]_[⊤]` into the idèles, of the compact product
`∏_v C v` with `C v = {1}` at the archimedean places and `C v = 𝒪_vˣ` at the finite ones; each
`C v` is compact and the topology of the piece is the product topology, so Tychonoff applies. -/
theorem globalCFT_unityIdeles_isCompact {K : Type*} [Field K] [NumberField K] :
    IsCompact ((NK.GlobalCFT.Idele.unityIdeles K : Subgroup (NK.GlobalCFT.Idele K)) :
      Set (NK.GlobalCFT.Idele K)) := by
  classical
  -- The family of "unitary" local conditions: trivial at the archimedean places, local units
  -- at the nonarchimedean ones.
  set C : (v : Place K) → Set ((Place.localField K v)ˣ) :=
    fun v => if Place.IsInfinite v then {1} else (Place.localUnits K v : Set _) with hC
  -- Membership in `C v`, split into the archimedean and nonarchimedean cases.
  have hCmem : ∀ (v : Place K) (y : (Place.localField K v)ˣ),
      (y ∈ C v) ↔ (Place.IsInfinite v → y = 1) ∧
        (Place.IsFinite v → y ∈ Place.localUnits K v) := by
    intro v y
    by_cases h : Place.IsInfinite v
    · obtain ⟨w, rfl⟩ := Place.isInfinite_iff.mp h
      simp [hC]
    · obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp h
      simp [hC]
  -- `C v` is contained in the family defining the restricted product.
  have hCsub : ∀ v, C v ⊆ (Place.localUnits K v : Set ((Place.localField K v)ˣ)) := by
    intro v
    by_cases h : Place.IsInfinite v
    · obtain ⟨w, rfl⟩ := Place.isInfinite_iff.mp h
      simp [hC]
    · obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp h
      simp [hC]
  -- Each `C v` is compact: a singleton at an archimedean place, the compact group of local
  -- units at a nonarchimedean one.
  have hCcompact : ∀ v, IsCompact (C v) := by
    intro v
    by_cases h : Place.IsInfinite v
    · obtain ⟨w, rfl⟩ := Place.isInfinite_iff.mp h
      have hw : C (Place.ofInfinite w) = {1} := by simp [hC]
      rw [hw]
      exact isCompact_singleton
    · obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp h
      have hq : C (Place.ofFinite q) =
          (Place.localUnits K (Place.ofFinite q) : Set ((q.adicCompletion K)ˣ)) := by simp [hC]
      rw [hq]
      exact NK.GlobalCFT.LocalField.globalCFT_localUnits_isCompact_finite q
  -- The product `∏_v C v`, pulled back to the "local units everywhere" piece, is compact.
  have hW : IsCompact ((↑) ⁻¹' (Set.univ.pi C) :
      Set (Πʳ v : Place K, [(Place.localField K v)ˣ, Place.localUnits K v]_[⊤])) := by
    refine (RestrictedProduct.isEmbedding_coe_of_top
      (R := fun v : Place K => (Place.localField K v)ˣ)
      (A := fun v : Place K => (Place.localUnits K v : Set _))).isInducing.isCompact_preimage'
      (isCompact_univ_pi hCcompact) ?_
    intro x hx
    rw [RestrictedProduct.range_coe]
    intro v
    exact hCsub v (Set.mem_univ_pi.mp hx v)
  -- The unitary idèles are exactly the image of that compact set under the inclusion.
  have hZ : ((NK.GlobalCFT.Idele.unityIdeles K : Subgroup (NK.GlobalCFT.Idele K)) :
      Set (NK.GlobalCFT.Idele K)) =
      RestrictedProduct.inclusion (fun v : Place K => (Place.localField K v)ˣ)
        (fun v : Place K => (Place.localUnits K v : Set _)) (le_top : Filter.cofinite ≤ ⊤)
        '' ((↑) ⁻¹' (Set.univ.pi C) :
          Set (Πʳ v : Place K, [(Place.localField K v)ˣ, Place.localUnits K v]_[⊤])) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := NK.GlobalCFT.Idele.mem_unityIdeles.mp hx
      refine ⟨RestrictedProduct.mk x.1 ?_, ?_, ?_⟩
      · rw [Filter.eventually_top]
        exact fun v => hCsub v ((hCmem v (x v)).mpr ⟨hx1 v, hx2 v⟩)
      · rw [Set.mem_preimage, Set.mem_univ_pi]
        exact fun v => (hCmem v (x v)).mpr ⟨hx1 v, hx2 v⟩
      · rfl
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_preimage, Set.mem_univ_pi] at hy
      exact NK.GlobalCFT.Idele.mem_unityIdeles.mpr
        ⟨fun v hv => ((hCmem v (y v)).mp (hy v)).1 hv,
         fun v hv => ((hCmem v (y v)).mp (hy v)).2 hv⟩
  rw [hZ]
  exact hW.image (RestrictedProduct.continuous_inclusion (le_top : Filter.cofinite ≤ ⊤))

end NK.GlobalCFT.Ideles

end
