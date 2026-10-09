import Mathlib
import Submission.Work.SSGRoute.E1aClean.levelChange_lift_transport
import Submission.Work.SSGRoute.ExtChain.galOMulEquiv_continuous

/-!
# The Krull topology is functorial: `AlgEquiv.restrictScalars` is continuous

For an intermediate field `L` of `Ω/k`, the "inclusion" of Galois groups

    Gal(Ω/↥L) → Gal(Ω/k),   σ ↦ AlgEquiv.restrictScalars k σ

is continuous for the Krull topologies.  Both groups consist of automorphisms of `Ω` over a base
field, and the map is the identity on underlying functions; the point is that a basic Krull
neighbourhood of `1` in `Gal(Ω/k)` is the fixing subgroup of a *finite* `F/k`, whose preimage in
`Gal(Ω/↥L)` is the fixing subgroup of `L(F)` — a finitely generated (hence finite) extension of `L`.
The rank estimate for the compositum is `IntermediateField.adjoin_rank_le_of_isAlgebraic_right`.

This is the general form of the hypothesis `hψc` of
`Work.SSGRoute.E1aClean.levelChange_mem_Z1`: the *specialisation* `L = decompField k Ω A` is
`restrictScalars_decompField_continuous` below.  The proof follows the pattern of
`Work.SSGRoute.ExtChain.continuous_galOIncl` (`ExtChain/galOMulEquiv_continuous.lean`), which is the
same statement under the extra (and here unused) hypothesis `L ≤ K` with `K/k` finite; the
`IntermediateField.adjoin_rank_le_of_isAlgebraic_right` estimate it uses is the reason the statement
holds for an arbitrary `L`.
-/

namespace Work.SSGRoute.E1aClean

open IntermediateField
open scoped Topology

noncomputable section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The "inclusion" of Galois groups `Gal(Ω/↥L) → Gal(Ω/k)` is continuous** for the Krull
topologies. -/
theorem restrictScalars_continuous (L : IntermediateField k Ω) :
    Continuous (fun σ : Ω ≃ₐ[↥L] Ω => (AlgEquiv.restrictScalars k σ : Ω ≃ₐ[k] Ω)) := by
  let f : (Ω ≃ₐ[↥L] Ω) →* (Ω ≃ₐ[k] Ω) :=
    { toFun := fun σ => AlgEquiv.restrictScalars k σ
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  have hf : (fun σ : Ω ≃ₐ[↥L] Ω => (AlgEquiv.restrictScalars k σ : Ω ≃ₐ[k] Ω))
      = (f : (Ω ≃ₐ[↥L] Ω) → (Ω ≃ₐ[k] Ω)) := rfl
  rw [hf]
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, f.map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff k Ω] at hU
  obtain ⟨F, hFfin, hFU⟩ := hU
  haveI : FiniteDimensional k F := hFfin
  let E : IntermediateField ↥L Ω := IntermediateField.adjoin ↥L (F : Set Ω)
  have hEfin : FiniteDimensional ↥L E := by
    have hle := IntermediateField.adjoin_rank_le_of_isAlgebraic_right (F := k) (E := ↥L)
      (K := Ω) F
    have hfin : Module.rank k ↥F < Cardinal.aleph0 := Module.rank_lt_aleph0 k ↥F
    have : Module.rank ↥L ↥E < Cardinal.aleph0 := lt_of_le_of_lt hle hfin
    exact Module.rank_lt_aleph0_iff.mp this
  have hopen : IsOpen (E.fixingSubgroup : Set (Ω ≃ₐ[↥L] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen E
  refine Filter.mem_of_superset (hopen.mem_nhds (by simp)) ?_
  intro σ hσ
  have hfix : ∀ y ∈ (E : Set Ω), σ y = y :=
    (IntermediateField.mem_fixingSubgroup_iff (K := E) σ).mp hσ
  apply hFU
  exact (IntermediateField.mem_fixingSubgroup_iff (K := F)
      (AlgEquiv.restrictScalars k σ : Ω ≃ₐ[k] Ω)).mpr
    (fun y hy => hfix y (IntermediateField.subset_adjoin ↥L (F : Set Ω) hy))

/-- **The specialisation to the decomposition field** — this is the hypothesis `hψc` of
`Work.SSGRoute.E1aClean.levelChange_mem_Z1` (the `E1aClean` level-change datum). -/
theorem restrictScalars_decompField_continuous {k : Type} [Field k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω) :
    Continuous (fun g : Ω ≃ₐ[↥(decompField k Ω A)] Ω =>
      (AlgEquiv.restrictScalars k g : Ω ≃ₐ[k] Ω)) :=
  restrictScalars_continuous (decompField k Ω A)

/-- **The unconditional form of the level-change `Z¹`-transfer** (`levelChange_mem_Z1` with its
continuity hypothesis discharged by `restrictScalars_decompField_continuous`).

The level-`1` `1`-cocycle, read with the same values in the level-`2` coefficient
(`homCoind ↥k^h Ω K^h (Rep.res φ R)`, which has the same underlying type `R.V →+ Additive Ωˣ`), is a
level-`2` `1`-cocycle. -/
theorem levelChange_mem_Z1_uncond {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (φ : (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) →*
      (K ≃ₐ[k] K))
    [CharZero ↥(decompField k Ω A)] [IsAlgClosure ↥(decompField k Ω A) Ω]
    [FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      φ (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R))) :
    (fun g : Ω ≃ₐ[↥(decompField k Ω A)] Ω => c.1 (AlgEquiv.restrictScalars k g))
      ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
          (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω
            (henselOverDecomp k Ω K A) (Rep.res φ R)) :=
  levelChange_mem_Z1 A R φ hφres (restrictScalars_decompField_continuous A) c

end

end Work.SSGRoute.E1aClean
