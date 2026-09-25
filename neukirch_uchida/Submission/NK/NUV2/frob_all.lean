import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.TameStructureDeep.Tame.Unconditional
import Submission.NK.TameData.Places
import Submission.NK.ResidueFrob.LocalStructureInputs
import Submission.NK.FrobeniusBridge.Main
import Submission.NK.Reconstruct.LevelMap
import Submission.NK.ReconstructField.finrank_eq_of_localCorrespondence

/-! Guidance from the project lead (the requester):

## Context (orchestrator, 2026-09-23)
The old wall `NK.EndgameRepair.ClassicalChaptersRepaired` is UNSATISFIABLE — do not use it or any of its fields'
catalogues as targets: `IndecomposedDeep.DeepInputs.indexOne` fails (quartic K with 2 = 𝔭₁𝔭₂³, K_{𝔭₂} ≅ ℚ₂(∛2):
G_{ℚ₂(∛2)} ≤ D_A is self-normalising, ≅ a local Galois group, of index 3), and `TowerRankCore.finiteIndex_isClosed`
is false without `FiniteDimensional κ M`. Also avoid `LocalStructure.LocalNUExistence` (G_M ≅ G_κ ⇒ M ≅ κ is false,
Yamagata/Jarden–Ritter), `UchidaKummer.IsWeakUchida`, `CyclicPrimeReduction`.
The new wall is `NK.NUV2.ChaptersV2` (`Submission/Work/NUV2/Wall.lean`, do NOT edit): the four inputs of the proved
`NK.EndgameRepair.exists_sigma_of_correctedResiduals`. Library inputs being proved elsewhere in this workspace and
allowed as hypotheses where the statement has them: `NK.GlobalCFTdeep.FundamentalClassElement` (global
fundamental class ⇒ class-formation axioms, reciprocity C_K/N C_L ≅ Gal(L/K)ᵃᵇ via
`artinReciprocity_of_cohomologicalFieldAxiom`, Tate's theorem, Albert–Brauer–Hasse–Noether) and
`NK.LocalArtin.KernelCondition` at every completion (⇒ `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion`).
Design rules: state every local isomorphism as a CONTINUOUS isomorphism (ϕ is a homeomorphism; this removes
Nikolov–Segal entirely); for Brauer arguments use an ODD prime p (Br(ℝ)[p] = 0). Instantiate every new sub-statement
at K = ℚ and at the quartic above as a satisfiability check before relying on it. Delegate; one lemma per step.
## This lemma: the Frobenius correspondence
Route: `TameStructureDeep.localStructureData_all_of_localFieldInputs` (`PlacesUnconditional.lean:181`) gives
`ResidueFrob.LocalStructureData` at every place from `LocalFieldInputs` (a theorem:
`LocalInputs.PowerQuotient.localFieldInputs_of_prime`) and `ArtinReciprocity` at `localClosure A` (from `hKC` via
`artinReciprocity_adicCompletion`, after transporting SeparableClosure(K_𝔭) → `localClosure A` — unchecked, do it
first); then `ResidueFrob.frobeniusCorrespondencePlace_of_localStructureData`. Check that the result holds for an
ARBITRARY place correspondence `a` (it should: a is pinned by `map_decomp`).
-/

/-!
# `NK.NUV2.frob_all`: the Frobenius correspondence, unconditionally

The route suggested in the brief passes through `NK.LocalTame.Zl2ResidueChar` (Shimizu's
`ℤ_ℓ²`-detector of the residue characteristic, i.e. local class field theory at the completion),
which is only available at universe `0` in this workspace
(`NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` is stated for `K : Type`),
whereas `NK.NUV2.FrobAll` is universe-polymorphic.  Fortunately the detector is **not needed**:

* the residue characteristic at every place is *defined* to be
  `NK.TameStructureDeep.residueCharAt A = ringChar (ResidueField (𝒪_{K_𝔭}))`, and the whole local
  structure theorem at that place is unconditional in that parameter
  (`NK.TameStructureDeep.Tame.tameRamificationCore_adicCompletion_residueChar`, hence
  `NK.LocalTame.TameData (residueCharAt A) (residueCard K 𝔭) κ κ'`,
  `TameFrobeniusCore`, `ResidueCardInput`, …);
* the only thing `Zl2ResidueChar` was used for in the existing route is the *equality*
  `p = p₂` of the residue characteristics of corresponding places
  (`NK.LocalTame.residueChar_eq_of_zl2`), i.e. that `p` is a group-theoretic invariant of
  `G_κ`.  For a *place correspondence* `a` this equality is part of the data
  (`a.residueChar`): corresponding primes lie over the same rational prime;
* the residue field cardinalities then agree automatically
  (`NK.LocalTame.residueCard_eq_of_tameData`, from the group isomorphism between the two local
  Galois groups).

So the local Frobenius correspondence at corresponding places
(`NK.LocalTame.isFrobeniusFor_map_iff_of_eq`, the `hZ`-free form of
`frobenius_matching_at_corresponding_places`) and the local–global dictionary
(`NK.ResidueFrob.level_of_local_of_data`, `…inertia_surjective_of_levelInertiaCovered`, …) are
both available with the canonical parameters, and the "lift and descend" argument of
`NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_allLevels` closes the proof.

No hypothesis on `hKC` is used.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.defProp false
set_option maxHeartbeats 1000000

open scoped Classical Pointwise

namespace NK.NUV2

/-! ## Residue characteristics of corresponding places -/

/-- A ring equivalence preserves the characteristic of a ring of prime characteristic. -/
theorem charP_of_ringEquiv {R S : Type*} [Semiring R] [Semiring S] [Nontrivial R] [Nontrivial S]
    (e : R ≃+* S) {p : ℕ} (hp : p.Prime) (h : CharP R p) : CharP S p := by
  rw [CharP.charP_iff_prime_eq_zero hp] at h ⊢
  rw [← map_natCast e p, h, map_zero]

/-- The residue field of the `𝔭`-adic completion is `𝓞K ⧸ 𝔭`, so the characteristic of `𝓞K ⧸ 𝔭`
is the canonical residue characteristic `residueCharAt A` of the place. -/
theorem charP_quotient_primeBelow {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') :
    CharP (NumberField.RingOfIntegers K ⧸ (NK.TameData.primeBelow A).asIdeal)
      (NK.TameStructureDeep.residueCharAt A) := by
  obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
    (K := K) (NK.TameData.primeBelow A)
  exact charP_of_ringEquiv e (NK.TameStructureDeep.prime_residueCharAt A)
    (NK.TameStructureDeep.charP_residueCharAt A)

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **Corresponding places have the same residue characteristic**: the residue characteristic at a
place is the characteristic of the residue field of the prime below it, and the place
correspondence `a` carries the prime below `A` to the prime below `a.placeMap A`. -/
theorem residueCharAt_placeMap {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁') :
    NK.TameStructureDeep.residueCharAt (a.placeMap A) =
      NK.TameStructureDeep.residueCharAt A := by
  have h₂ : CharP (NumberField.RingOfIntegers K₂ ⧸
      (NK.TameData.primeBelow (a.placeMap A)).asIdeal)
      (NK.TameStructureDeep.residueCharAt A) := by
    have h := NK.ReconstructField.charP_primeMap a (NK.TameData.primeBelow A)
      (NK.TameStructureDeep.residueCharAt A) (charP_quotient_primeBelow A)
    rwa [a.primeMap_spec A] at h
  exact CharP.eq _ (charP_quotient_primeBelow (a.placeMap A)) h₂

/-! ## The unconditional local structure data at a place -/

section Place

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The reduced input catalogue at a place, unconditionally**: the local structure theorem for
`G_κ` at `κ = K_𝔭`, with the *canonical* parameters `p = residueCharAt A` (the characteristic of
the residue field of the completion) and `q = residueCard K 𝔭` (its cardinality). -/
noncomputable def canonTameDataInput (A : NK.FrobeniusBridge.FinitePlaceOf K K') :
    NK.TameData.TameDataInput (NK.TameStructureDeep.residueCharAt A)
      (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) :=
  NK.TameStructureDeep.Tame.tameDataInput_adicCompletion_residueChar
    (K := K) (K' := NK.FrobeniusBridge.localClosure A) (NK.TameData.primeBelow A)

/-- The packaged structure theorem `NK.LocalTame.TameData` at a place, with the canonical
parameters and no hypothesis. -/
noncomputable def canonTameData (A : NK.FrobeniusBridge.FinitePlaceOf K K') :
    NK.LocalTame.TameData (NK.TameStructureDeep.residueCharAt A)
      (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) :=
  (canonTameDataInput A).toTameData

/-- The Frobenius element of the local field at the canonical parameters, from the Frobenius
normalisation `NK.LocalStructure.TameFrobeniusCore`. -/
noncomputable def canonResidueCardInput (A : NK.FrobeniusBridge.FinitePlaceOf K K') :
    NK.LocalAnabelian.ResidueCardInput (NK.TameStructureDeep.residueCharAt A)
      (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) :=
  NK.ResidueFrob.residueCardInput_of_tameFrobeniusCore A (canonTameDataInput A).frobenius

/-- **The local Frobenius predicate at a place, with canonical parameters**: `g` lies in the
decomposition group of `A` and its image under `D_A ≃* Gal(κ̄/κ)` acts on the prime-to-`p` roots of
unity by `ζ ↦ ζ^q`, where `p = residueCharAt A` and `q = residueCard K 𝔭` are the canonical
parameters of the local field. -/
def IsLocalFrob (A : NK.FrobeniusBridge.FinitePlaceOf K K') (g : Gal(K'/K)) : Prop :=
  ∃ (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1),
    NK.LocalAnabelian.IsFrobeniusFor (NK.TameStructureDeep.residueCharAt A)
      (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localGaloisEquiv A ⟨g, hg⟩)

/-- **Down**: a local Frobenius lift restricts to a Frobenius element at every finite normal
level — the residue-field normalisation at the canonical parameters. -/
theorem IsLocalFrob.frobAtLevel (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    {g : Gal(K'/K)} (h : IsLocalFrob A g) : NK.FrobeniusBridge.frobAtLevel A L g := by
  obtain ⟨hg, hF⟩ := h
  exact NK.ResidueFrob.level_of_local_of_data A (canonTameData A)
    (NK.ResidueFrob.residueCardMatches_residueCard A) L g hg hF

/-- **Up**: a Frobenius element at a finite normal level agrees there with a local Frobenius lift
(at the canonical parameters).  This is the "up" half of the local–global dictionary; it uses the
existence of one local Frobenius lift and the fact that the local inertia subgroup surjects onto
the level inertia subgroups. -/
theorem exists_isLocalFrob_of_frobAtLevel (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (g : Gal(K'/K)) (hg : NK.FrobeniusBridge.frobAtLevel A L g) :
    ∃ g₀ : Gal(K'/K), AlgEquiv.restrictNormalHom L g₀ = AlgEquiv.restrictNormalHom L g ∧
      IsLocalFrob A g₀ := by
  obtain ⟨u, hu, hFu⟩ :=
    NK.ResidueFrob.exists_frob_of_residueCardInput A (canonResidueCardInput A)
  have hloc_u : IsLocalFrob A u := ⟨hu, hFu⟩
  have huFrob : NK.FrobeniusBridge.frobAtLevel A L u :=
    IsLocalFrob.frobAtLevel A L hloc_u
  have htriv : NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L (g * u⁻¹) :=
    NK.FrobeniusBridge.isTrivialOnResidueAtLevel_mul_inv_of_frobAt A L hg huFrob
  obtain ⟨h, hh, hhI, hhrestrict⟩ :=
    NK.ResidueFrob.inertia_surjective_of_levelInertiaCovered A
      (NK.ResidueFrob.levelInertiaCovered_of_tameData A (canonTameData A)
        (NK.ResidueFrob.residueCardMatches_residueCard A)) L (g * u⁻¹) htriv
  refine ⟨h * u, ?_, ⟨Subgroup.mul_mem _ hh hu, ?_⟩⟩
  · rw [map_mul, hhrestrict, ← map_mul]
    rw [show (g * u⁻¹) * u = g from by group]
  · have hsub : (⟨h * u, Subgroup.mul_mem _ hh hu⟩ :
        Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1) =
        ⟨h, hh⟩ * ⟨u, hu⟩ := Subtype.ext (by simp)
    simpa only [hsub, map_mul] using
      NK.LocalTame.IsFrobeniusFor.mul_mem_inertia (canonTameData A) hFu hhI

end Place

/-! ## The local Frobenius correspondence at corresponding places -/

/-- **The local Frobenius correspondence for a place correspondence `a`**: if `g` is a local
Frobenius lift at `A`, then `ϕ g` is a local Frobenius lift at the corresponding place
`a.placeMap A`.  The two local fields have the same residue characteristic by
`residueCharAt_placeMap`, hence the same residue field cardinality by
`NK.LocalTame.residueCard_eq_of_tameData`, and the (abstract) isomorphism of local Galois groups
induced by `ϕ` then matches the Frobenius cosets
(`NK.LocalTame.isFrobeniusFor_map_iff_of_eq`). -/
theorem isLocalFrob_map {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁')
    (g : Gal(K₁'/K₁))
    (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A.1)
    (hF : NK.LocalAnabelian.IsFrobeniusFor (NK.TameStructureDeep.residueCharAt A)
      (NK.LocalStructure.residueCard K₁ (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localGaloisEquiv A ⟨g, hg⟩)) :
    ∃ (hg' : ϕ g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (a.placeMap A).1),
      NK.LocalAnabelian.IsFrobeniusFor (NK.TameStructureDeep.residueCharAt (a.placeMap A))
        (NK.LocalStructure.residueCard K₂ (NK.TameData.primeBelow (a.placeMap A)))
        (NK.FrobeniusBridge.localGaloisEquiv (a.placeMap A) ⟨ϕ g, hg'⟩) := by
  have hg' : ϕ g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
      (a.placeMap A).1 := by
    rw [← a.map_decomp A]
    exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
  refine ⟨hg', ?_⟩
  let eA := NK.FrobeniusBridge.localGaloisEquiv A
  let eB := NK.FrobeniusBridge.localGaloisEquiv (a.placeMap A)
  let Ψ : ↥(Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A.1) ≃*
      ↥(Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (a.placeMap A).1) :=
    NK.LocalTame.mulEquivSubgroupCongr ϕ (a.map_decomp A)
  let Φ : Gal(NK.FrobeniusBridge.localClosure A / NK.FrobeniusBridge.localField A) ≃*
      Gal(NK.FrobeniusBridge.localClosure (a.placeMap A) /
        NK.FrobeniusBridge.localField (a.placeMap A)) :=
    (eA.symm.trans Ψ).trans eB
  have hp : NK.TameStructureDeep.residueCharAt A =
      NK.TameStructureDeep.residueCharAt (a.placeMap A) :=
    (residueCharAt_placeMap a A).symm
  have hq : NK.LocalStructure.residueCard K₁ (NK.TameData.primeBelow A) =
      NK.LocalStructure.residueCard K₂ (NK.TameData.primeBelow (a.placeMap A)) :=
    NK.LocalTame.residueCard_eq_of_tameData (canonTameData A) (canonTameData (a.placeMap A))
      hp Φ
  have hkey := (NK.LocalTame.isFrobeniusFor_map_iff_of_eq (canonTameData A)
      (canonTameData (a.placeMap A)) hp hq Φ (eA ⟨g, hg⟩)).mp hF
  have hΨ : Ψ (eA.symm (eA ⟨g, hg⟩)) = ⟨ϕ g, hg'⟩ := by
    rw [MulEquiv.symm_apply_apply]
    exact Subtype.ext rfl
  have hEq : Φ (eA ⟨g, hg⟩) = eB ⟨ϕ g, hg'⟩ := by
    show eB (Ψ (eA.symm (eA ⟨g, hg⟩))) = eB ⟨ϕ g, hg'⟩
    rw [hΨ]
  rwa [hEq] at hkey

/-! ## The finite-level Frobenius correspondence -/

/-- **The Frobenius correspondence**, from the local input: `ϕ` carries the Frobenius elements at
a level below a place `A` to the Frobenius elements at the corresponding level below
`a.placeMap A`.  This is the "lift and descend" argument of
`NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_allLevels`, with the local–global dictionary
supplied at the canonical parameters. -/
theorem frobeniusCorrespondencePlace_of_local
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a := by
  intro L _ _ _ _ _ A g hg
  -- a local Frobenius lift at `A` agreeing with `g` on the level `L`
  obtain ⟨g₀, hg₀, hloc⟩ := exists_isLocalFrob_of_frobAtLevel A L g hg
  obtain ⟨hg₀mem, hF₀⟩ := hloc
  -- its image is a local Frobenius lift at the corresponding place
  obtain ⟨hBmem, hBfrob⟩ := isLocalFrob_map a A g₀ hg₀mem hF₀
  -- hence a Frobenius element at the corresponding level
  have hlocB : IsLocalFrob (a.placeMap A) (ϕ g₀) := ⟨hBmem, hBfrob⟩
  have hfrob : NK.FrobeniusBridge.frobAtLevel (a.placeMap A) (NK.Reconstruct.levelMap ϕ L)
      (ϕ g₀) := IsLocalFrob.frobAtLevel (a.placeMap A) (NK.Reconstruct.levelMap ϕ L) hlocB
  -- and `ϕ g` has the same restriction to that level
  have hcongr : AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g₀) =
      AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g) := by
    rw [NK.FrobeniusBridge.restrictNormalHom_eq_iff_mem_fixingSubgroup]
    rw [NK.Reconstruct.fixingSubgroup_levelMap hϕ L]
    exact Subgroup.mem_map.mpr
      ⟨g₀ * g⁻¹, (NK.FrobeniusBridge.restrictNormalHom_eq_iff_mem_fixingSubgroup g₀ g).mp hg₀, by simp⟩
  exact (NK.FrobeniusBridge.frobAtLevel_congr (a.placeMap A) (NK.Reconstruct.levelMap ϕ L)
    hcongr).mp hfrob

theorem frob_all (hKC : NK.NUV2.KCAll) : NK.NUV2.FrobAll := by
  intro K₁ K₂ K₁' K₂' _ _ _ _ _ _ _ _ _ _ ϕ hϕ a
  exact frobeniusCorrespondencePlace_of_local ϕ hϕ a

end NK.NUV2
