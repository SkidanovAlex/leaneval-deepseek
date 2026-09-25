import Mathlib
import Submission.NK.NUV2.LCLeaves
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.NK.Mine.PlaceCorrespondenceArithmetic
import Submission.NK.PTorsionTop.Basic
import Submission.NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg

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
## This lemma: glue G2. Build `NK.Reconstruct.LocalCorrespondence ϕ` from PDG + leaf 6 (+ hKC if needed): placeMap from PDG (uniqueness of B by disjointness), equivariance, map_decomp, and primeMap / primeMap_spec using equal residue characteristic and local degree. Existing: `NK.Mine.localCorrespondence_of_localData`, `NK.LocalInputs.residueChar_and_localDegree_eq_of_decompositionGroup` (do not use its LocalGaloisInputs hypothesis — refuted field). Read those files for the shape.

## Implementation note (this file)

`Submission.NeukirchUchida.localCorrespondenceOf` (in `Submission/NeukirchUchida/Endgame.lean`)
already builds the whole σ-free input (a) of the reconstruction,
`NK.Reconstruct.LocalCorrespondence ϕ`, from

* `h : PreservesDecompositionGroups ϕ` — available from `hpdg : PDGAll0` (glue G1), which supplies
  the place map (`placeMap`), its Galois-equivariance (`map_smul`), the compatibility with `ϕ` on
  decomposition groups (`map_decomp`) and the induced bijection of primes (`primeMap`,
  `primeMap_spec`); and
* the two *arithmetic* fields at every finite place `A` over `𝔭` with image `B = placeMap ϕ h A`
  over `𝔮`: the preservation of the residue characteristic and of the absolute local degree
  `inertiaDeg · ramificationIdx = [K_𝔭 : ℚ_p]`.

The present file supplies those two arithmetic fields from leaf 6
(`h6 : LocalArithInvariants`).  The point that makes this work without any anabelian input is the
workspace lemma `NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map`: the
correspondence of decomposition groups `ϕ(D_A) = D_B` (which is exactly `placeMap_spec`) produces an
isomorphism `ψ` of the two local absolute Galois groups which is a *homeomorphism*
(`isHomeomorph_adjoinLocalEquiv` identifies `D_A` with `Gal(M/κ)` continuously, `eφ` is the
restriction of the homeomorphism `ϕ`, and `Gal(M/κ) ≅ Gal(κ̄/κ)` is continuous by
`isHomeomorph_autCongr`).  Turning `ψ` into a `≃ₜ*`
(`NK.PTorsionTop.continuousMulEquivOfIsHomeomorph`) meets the hypothesis of leaf 6, i.e. of
`h6`, whose conclusions

* `ringChar (ResidueField 𝔭.adicCompletionIntegers) = ringChar (ResidueField 𝔮.….)`
* `localDegree K₁ 𝔭 = localDegree K₂ 𝔮`

are then translated into the prime vocabulary of `LocalCorrespondence` using
`NK.Mine.charP_residueField_iff` (`CharP` of the completion's residue field ↔ `CharP` of
`𝒪 K ⧸ 𝔭`) and
`NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg`
(`localDegree K 𝔭 = ramificationIdx · inertiaDeg`).
-/

set_option linter.unusedVariables false

open scoped Pointwise

namespace NK.NUV2.LC

/-- **The arithmetic fields of the place correspondence at a single place.**

Let `K₁`, `K₂` be number fields with separable closures `K₁'`, `K₂'`,
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` a homeomorphic isomorphism which preserves decomposition groups,
and let `A` be a finite place of `K₁'` over `𝔭`, with image `B = placeMap ϕ h A` over `𝔮`.  Then,
given the local arithmetic invariants `h6` (leaf 6: a continuous isomorphism of local absolute
Galois groups forces equal residue characteristic and equal local degree),

* the residue characteristic below `𝔭` and below `𝔮` coincide
  (as `CharP (𝒪 K ⧸ 𝔭) ℓ → CharP (𝒪 K ⧸ 𝔮) ℓ`); and
* `inertiaDeg · ramificationIdx` — the absolute local degree `[K_𝔭 : ℚ_ℓ]` — is preserved.

These are precisely the two arguments consumed by
`Submission.NeukirchUchida.localCorrespondenceOf`. -/
theorem arith_of_placeMap
    {K₁ K₂ K₁' K₂' : Type} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (h6 : NK.NUV2.LocalArithInvariants)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (A : NK.Reconstruct.FinitePlaceOf K₁ K₁') :
    (∀ ℓ : ℕ, CharP (NumberField.RingOfIntegers K₁ ⧸
        (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
      CharP (NumberField.RingOfIntegers K₂ ⧸
        (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
          (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal) ℓ) ∧
    ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ *
        (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ =
      (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
          (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ *
        (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
          (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ) := by
  -- the image place and the two primes
  set B := Submission.NeukirchUchida.placeMap ϕ h A with hB
  set 𝔭 := Submission.NeukirchUchida.primeOf A.1 A.2 with h𝔭
  set 𝔮 := Submission.NeukirchUchida.primeOf B.1 B.2 with h𝔮
  -- the local Galois groups at corresponding places are continuously isomorphic
  obtain ⟨ψ, hψ⟩ := NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
    𝔭 𝔮 A.1 B.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2)
    (Submission.NeukirchUchida.primeOf_spec B.1 B.2)
    ϕ hϕ (Submission.NeukirchUchida.placeMap_spec ϕ h A)
  -- leaf 6 at the two completions
  obtain ⟨hring, hdeg⟩ := h6 K₁ K₂ 𝔭 𝔮
    ⟨NK.PTorsionTop.continuousMulEquivOfIsHomeomorph ψ hψ⟩
  refine ⟨?_, ?_⟩
  · -- the residue characteristic
    intro ℓ hℓ
    have hℓ' : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) ℓ :=
      (NK.Mine.charP_residueField_iff 𝔭 ℓ).mpr hℓ
    have hℓ'' : ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) = ℓ :=
      ringChar.eq_iff.mpr hℓ'
    have hring' : ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) = ℓ := by
      rw [← hring]; exact hℓ''
    exact (NK.Mine.charP_residueField_iff 𝔮 ℓ).mp (ringChar.of_eq hring')
  · -- the local degree
    rw [mul_comm (𝔭.asIdeal.inertiaDeg ℤ), mul_comm (𝔮.asIdeal.inertiaDeg ℤ)]
    rw [← NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg (K := K₁) (𝔭 := 𝔭),
        ← NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg (K := K₂) (𝔭 := 𝔮)]
    exact hdeg

/-- **Glue G2 of the place correspondence: the σ-free input (a) of the reconstruction.**

From

* `hpdg` — glue G1, `NK.NUV2.PDGAll0`: every homeomorphic isomorphism of absolute Galois
  groups of number fields preserves decomposition groups (CoNF (12.1.9), "if" direction),
* `h6` — leaf 6, `NK.NUV2.LocalArithInvariants`: a continuous isomorphism of local absolute
  Galois groups forces equal residue characteristic and equal local degree,
* `hKC` — the local reciprocity law at every completion (used by leaf 6),

the *local correspondence* `NK.Reconstruct.LocalCorrespondence ϕ` (CoNF (12.1.9)) exists for every
homeomorphic isomorphism `ϕ` of absolute Galois groups: the place map with its equivariance and its
compatibility with decomposition groups, the induced bijection of primes, and the preservation of
the residue characteristic and of the local degree.

The construction is `Submission.NeukirchUchida.localCorrespondenceOf`, whose two arithmetic
arguments are supplied by `arith_of_placeMap`. -/
theorem lc_of_pdg (hpdg : NK.NUV2.PDGAll0) (h6 : NK.NUV2.LocalArithInvariants)
    (hKC : NK.NUV2.KCAll) : NK.NUV2.LCAll0 := by
  intro K₁ K₂ K₁' K₂' _ _ _ _ _ _ _ _ _ _ ϕ hϕ
  have h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ :=
    hpdg K₁ K₂ K₁' K₂' ϕ hϕ
  refine ⟨Submission.NeukirchUchida.localCorrespondenceOf ϕ h ?_ ?_⟩
  · intro A ℓ hℓ
    exact (arith_of_placeMap h6 ϕ hϕ h A).1 ℓ hℓ
  · intro A
    exact (arith_of_placeMap h6 ϕ hϕ h A).2

end NK.NUV2.LC
