import Submission.Work.Tubular.ThomComparison
import Submission.Work.Tubular.onePoint_homology_relChains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The metric-free comparison `H^n(E⁺) ≅ H^n(E, E∖0)` for a general real bundle

For an **arbitrary** real bundle `Z : RealBundle B F ι` over a compact Hausdorff base with finite
dimensional fibre, this file sets up the canonical comparison between the cohomology of the
one-point compactification `Z⁺ = OnePoint Z.TotalSpace` (the Thom space of `Z`) and the relative
cohomology of the Thom pair `(Z.TotalSpace, Z∖0)`:

* `Work.ThomBordism.absNZ Z` — the subspace `A = (Z∖0) ∪ {∞} ⊆ Z⁺`;
* `Work.ThomBordism.someHomeoZ Z` — the homeomorphism `Z ≃ₜ {∞}ᶜ ⊆ Z⁺`;
* `Work.ThomBordism.excChainZ`, `homeoChainZ` — the chain-level excision of `{∞}` and the
  homeomorphism of pairs; `compIsoZ` their composite isomorphism on homology and `compPullZ` the
  composite pullback on cohomology;
* `Work.ThomBordism.relCohOfAbsZ Z n` — the inverse of the forgetful map `relToAbs`, available
  because `A` is contractible (`contractibleSpace_absNZ`);
* `Work.ThomBordism.Theta Z n`, `Work.ThomBordism.Phi Z n` — **the canonical comparison**
  `H^n(Z, Z∖0) ≃ₗ H^n(Z⁺)` and its inverse.

**Metric-freeness.**  None of the sets above mentions a norm: only `zeroComplement Z` and `{∞}`.
The single geometric input for contractibility of `A` is a supplied continuous, homogeneous,
norm-like function `NormLike Z` (for the universal bundle `γ` this is the Grassmann chapter's
`fibN`, for a normal bundle `ν` of an embedding it is `Work.Tubular.normalNorm`); the radial scaling
`v ↦ (1-t)⁻¹ v` deforms `A` to `∞`.

This is a copy of the `Work.Tubular` construction of `compIso`/`compPull`/`relCoh_of_abs`,
which is stated there only for the normal bundle `NormalTotal E` of an embedding
(`Submission/Work/Tubular/ThomComparison.lean`, `contractibleSpace_onePointNonzero.lean`,
`onePoint_pairing_transfer.lean`, `OnePointCompl.lean` are the model).
-/

open CategoryTheory Limits
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}

/-! ## A norm-like function on the fibres -/

/-- **A norm-like function** on the total space of a real bundle: a continuous, non-negative,
positively homogeneous function vanishing exactly on the zero section, whose closed unit ball is
compact.  Its only role is to make the radial scaling `v ↦ t⁻¹ v` *proper*, hence a homotopy of the
one-point compactification; it is never used in the definitions of the comparison. -/
structure NormLike (Z : RealBundle B F ι) where
  /-- the function -/
  f : Z.TotalSpace → ℝ
  /-- it is continuous -/
  continuous_f : Continuous f
  /-- it is non-negative -/
  nonneg : ∀ p : Z.TotalSpace, 0 ≤ f p
  /-- it is positively homogeneous on the fibres -/
  smul : ∀ (c : ℝ), 0 ≤ c → ∀ p : Z.TotalSpace, f ⟨p.1, c • p.2⟩ = c * f p
  /-- it vanishes exactly on the zero section -/
  eq_zero : ∀ p : Z.TotalSpace, f p = 0 ↔ p.2 = 0
  /-- its closed unit ball is compact -/
  isCompact_le_one : IsCompact {p : Z.TotalSpace | f p ≤ 1}

/-- Scaling by `c` is continuous. -/
theorem NormLike.continuous_scale {Z : RealBundle B F ι} (c : ℝ) :
    Continuous fun p : Z.TotalSpace => (⟨p.1, c • p.2⟩ : Z.TotalSpace) :=
  Work.Thom.continuous_smul_section Z (ContinuousMap.id _) (ContinuousMap.const _ c)

/-- The zero section is closed: it is the zero set of the continuous norm-like function. -/
theorem NormLike.isClosed_zero {Z : RealBundle B F ι} (N : NormLike Z) :
    IsClosed {p : Z.TotalSpace | p.2 = 0} := by
  have hset : {p : Z.TotalSpace | p.2 = 0} = {p : Z.TotalSpace | N.f p = 0} := by
    ext p
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    exact (N.eq_zero p).symm
  rw [hset]
  exact isClosed_eq N.continuous_f continuous_const

/-- The zero section is compact: it is a closed subset of the compact unit ball. -/
theorem NormLike.isCompact_zero {Z : RealBundle B F ι} (N : NormLike Z) :
    IsCompact {p : Z.TotalSpace | p.2 = 0} := by
  have hset : {p : Z.TotalSpace | p.2 = 0} = {p : Z.TotalSpace | N.f p = 0} := by
    ext p
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    exact (N.eq_zero p).symm
  rw [hset]
  exact (N.isCompact_le_one).of_isClosed_subset
    (isClosed_eq N.continuous_f continuous_const)
    (fun p hp => by rw [Set.mem_ofPred_eq] at hp ⊢; rw [hp]; exact zero_le_one)

/-- The closed ball of radius `c ≥ 0` is compact: it is the image of the unit ball under the
continuous scaling by `c`. -/
theorem NormLike.isCompact_le {Z : RealBundle B F ι} (N : NormLike Z) {c : ℝ} (hc : 0 ≤ c) :
    IsCompact {p : Z.TotalSpace | N.f p ≤ c} := by
  rcases eq_or_lt_of_le hc with h | h
  · have hset : {p : Z.TotalSpace | N.f p ≤ 0} = {p : Z.TotalSpace | p.2 = 0} := by
      ext p
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
      constructor
      · intro hp
        exact (N.eq_zero p).mp (le_antisymm hp (N.nonneg p))
      · intro hp
        exact le_of_eq ((N.eq_zero p).mpr hp)
    rw [← h, hset]
    exact N.isCompact_zero
  · have himg : (fun p : Z.TotalSpace => (⟨p.1, c • p.2⟩ : Z.TotalSpace)) ''
        {p : Z.TotalSpace | N.f p ≤ 1} = {p : Z.TotalSpace | N.f p ≤ c} := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        rw [Set.mem_ofPred_eq] at hq ⊢
        rw [N.smul c hc q]
        exact mul_le_of_le_one_right hc hq
      · intro hp
        rw [Set.mem_ofPred_eq] at hp
        refine ⟨⟨p.1, c⁻¹ • p.2⟩, ?_, ?_⟩
        · rw [Set.mem_ofPred_eq, N.smul c⁻¹ (inv_nonneg.mpr hc) p, inv_mul_le_iff₀ h]
          simpa using hp
        · show (⟨p.1, c • (c⁻¹ • p.2)⟩ : Z.TotalSpace) = p
          rw [smul_inv_smul₀ (ne_of_gt h)]
    rw [← himg]
    exact (N.isCompact_le_one).image (NormLike.continuous_scale c)

/-! ## The complement of the zero section in the one-point compactification -/

/-- **The complement of the zero section in `Z⁺`**: `A = (Z∖0) ∪ {∞}`, the subspace whose
contractibility (`contractibleSpace_absNZ`) makes the forgetful map `relToAbs` invertible. -/
abbrev absNZ (Z : RealBundle B F ι) : Set (OnePoint Z.TotalSpace) :=
  OnePoint.some '' Work.Thom.zeroComplement Z ∪ {OnePoint.infty}

/-- The complement of `∞` in `Z⁺`, as a subset. -/
abbrev infZ (Z : RealBundle B F ι) : Set (OnePoint Z.TotalSpace) := {OnePoint.infty}ᶜ

/-- The intersection `{∞}ᶜ ∩ A`, as a subset of `{∞}ᶜ`. -/
abbrev excSubZ (Z : RealBundle B F ι) : Set ↥(infZ Z) :=
  {y : ↥(infZ Z) | (y : OnePoint Z.TotalSpace) ∈ absNZ Z}

/-- The inclusion `{∞}ᶜ ↪ Z⁺`. -/
def infZIncl (Z : RealBundle B F ι) : C(↥(infZ Z), OnePoint Z.TotalSpace) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The zero section of `Z` inside `Z⁺`. -/
abbrev onePointZeroZ (Z : RealBundle B F ι) : Set (OnePoint Z.TotalSpace) :=
  OnePoint.some '' {p : Z.TotalSpace | p.2 = 0}

/-- **The homeomorphism `Z ≃ₜ {∞}ᶜ ⊆ Z⁺`**, i.e. `OnePoint.some` with its image. -/
noncomputable def someHomeoZ (Z : RealBundle B F ι) : Z.TotalSpace ≃ₜ ↥(infZ Z) :=
  Work.Tubular.onePointRangeHomeo Z.TotalSpace

@[simp] theorem someHomeoZ_apply (Z : RealBundle B F ι) (x : Z.TotalSpace) :
    ((someHomeoZ Z x : ↥(infZ Z)) : OnePoint Z.TotalSpace) = OnePoint.some x :=
  Work.Tubular.onePointRangeHomeo_apply x

@[simp] theorem mem_infZ {Z : RealBundle B F ι} {p : OnePoint Z.TotalSpace} :
    p ∈ infZ Z ↔ p ≠ OnePoint.infty := by
  rw [infZ, Set.mem_compl_iff, Set.mem_singleton_iff]

theorem infty_notMem_infZ (Z : RealBundle B F ι) :
    (OnePoint.infty : OnePoint Z.TotalSpace) ∉ infZ Z := by
  rw [mem_infZ]; exact fun h => h rfl

@[simp] theorem some_mem_absNZ (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    OnePoint.some p ∈ absNZ Z ↔ p ∈ Work.Thom.zeroComplement Z := by
  rw [absNZ, Set.mem_union]
  constructor
  · rintro (⟨q, hq, hqp⟩ | h)
    · rwa [OnePoint.coe_injective hqp] at hq
    · exact absurd h (OnePoint.coe_ne_infty p)
  · intro h; exact Or.inl ⟨p, h, rfl⟩

@[simp] theorem infty_mem_absNZ (Z : RealBundle B F ι) :
    (OnePoint.infty : OnePoint Z.TotalSpace) ∈ absNZ Z := by
  rw [absNZ]; exact Or.inr rfl

theorem some_mem_excSubZ (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    p ∈ Work.Thom.zeroComplement Z ↔ someHomeoZ Z p ∈ excSubZ Z :=
  (some_mem_absNZ Z p).symm.trans (by rw [excSubZ, Set.mem_ofPred_eq, someHomeoZ_apply])

/-! ## The chain-level comparison -/

/-- The compatibility of `{∞}ᶜ ↪ Z⁺` with the inclusions of the punctured parts. -/
theorem excSpecZ (Z : RealBundle B F ι) :
    CategoryTheory.CategoryStruct.comp
        (subtypeIncl (TopCat.of ↥(infZ Z)) (excSubZ Z))
        (TopCat.ofHom (infZIncl Z))
      = CategoryTheory.CategoryStruct.comp
        (inclInterA (TopCat.of (OnePoint Z.TotalSpace)) (infZ Z) (absNZ Z))
        (subtypeIncl (TopCat.of (OnePoint Z.TotalSpace)) (absNZ Z)) := by
  apply TopCat.ext
  intro y
  rfl

/-- The chain map of the excision of `{∞}`: the inclusion of pairs
`({∞}ᶜ, {∞}ᶜ ∩ A) → (Z⁺, A)`. -/
def excChainZ (Z : RealBundle B F ι) :
    relChains (TopCat.of ↥(infZ Z)) (excSubZ Z) ⟶
      relChains (TopCat.of (OnePoint Z.TotalSpace)) (absNZ Z) :=
  relChainsMapOf (TopCat.of ↥(infZ Z)) (TopCat.of (OnePoint Z.TotalSpace))
    (excSubZ Z) (absNZ Z)
    (TopCat.ofHom (infZIncl Z))
    (inclInterA (TopCat.of (OnePoint Z.TotalSpace)) (infZ Z) (absNZ Z))
    (excSpecZ Z)

/-- The map of pairs induced by `someHomeoZ` on the punctured parts. -/
def homeoSubMapZ (Z : RealBundle B F ι) :
    TopCat.of ↥(Work.Thom.zeroComplement Z) ⟶ TopCat.of ↥(excSubZ Z) :=
  TopCat.ofHom ((someHomeoZ Z).subtype (some_mem_excSubZ Z))

/-- The compatibility of `someHomeoZ` with the inclusions of the punctured parts. -/
theorem homeoSubMapZ_spec (Z : RealBundle B F ι) :
    CategoryTheory.CategoryStruct.comp
        (subtypeIncl (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z))
        (TopCat.ofHom (someHomeoZ Z))
      = CategoryTheory.CategoryStruct.comp (homeoSubMapZ Z)
        (subtypeIncl (TopCat.of ↥(infZ Z)) (excSubZ Z)) := by
  apply TopCat.ext
  intro a
  rfl

/-- The chain map of the homeomorphism of pairs
`(Z, Z∖0) ≅ ({∞}ᶜ, {∞}ᶜ ∩ A)`. -/
def homeoChainZ (Z : RealBundle B F ι) :
    relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) ⟶
      relChains (TopCat.of ↥(infZ Z)) (excSubZ Z) :=
  relChainsMapOf (TopCat.of Z.TotalSpace) (TopCat.of ↥(infZ Z))
    (Work.Thom.zeroComplement Z) (excSubZ Z) (TopCat.ofHom (someHomeoZ Z))
    (TopCat.ofHom ((someHomeoZ Z).subtype (some_mem_excSubZ Z))) (homeoSubMapZ_spec Z)

end

end Work.ThomBordism
