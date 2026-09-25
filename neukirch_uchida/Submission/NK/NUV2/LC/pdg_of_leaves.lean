import Mathlib
import Submission.NK.NUV2.LCLeaves
import Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap
import Submission.Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring

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
## This lemma: glue G1. ϕ(D_A) is closed and ≅ₜ a local Galois group (h5 + ϕ homeomorphism), so by h1 it lies in some D_B; ϕ⁻¹(D_B) likewise lies in some D_{A}
-/

namespace NK.NUV2.LC

open IsDedekindDomain

/-! ## Auxiliary topological-group lemmas -/

section Aux

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- The inverse of a homeomorphic group isomorphism is continuous. -/
theorem pdg_continuous_symm (e : G ≃* H) (he : IsHomeomorph (e : G → H)) :
    Continuous (e.symm : H → G) := by
  rw [continuous_def]
  intro U hU
  have hpre : (e.symm : H → G) ⁻¹' U = e '' U := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  rw [hpre]
  exact he.isOpenMap U hU

/-- The restriction of a homeomorphic group isomorphism to a subgroup is a topological
isomorphism onto its image. -/
noncomputable def pdg_subgroupContinuousMulEquiv (e : G ≃* H) (he : IsHomeomorph (e : G → H))
    (S : Subgroup G) : S ≃ₜ* S.map (e : G →* H) := by
  let φ : S ≃* S.map (e : G →* H) := MulEquiv.subgroupMap e S
  refine ContinuousMulEquiv.mk φ ?_ ?_
  · exact Continuous.subtype_mk (he.continuous.comp continuous_subtype_val) (fun x => (φ x).2)
  · exact Continuous.subtype_mk
      ((pdg_continuous_symm e he).comp continuous_subtype_val) (fun y => (φ.symm y).2)

/-- Equal subgroups of a topological group are topologically isomorphic. -/
noncomputable def pdg_subgroupCongrContinuousMulEquiv {S T : Subgroup G} (h : S = T) :
    S ≃ₜ* T := by
  let φ : S ≃* T := MulEquiv.subgroupCongr h
  refine ContinuousMulEquiv.mk φ ?_ ?_
  · exact Continuous.subtype_mk continuous_subtype_val (fun x => (φ x).2)
  · exact Continuous.subtype_mk continuous_subtype_val (fun x => (φ.symm x).2)

/-- A homeomorphic isomorphism carries a closed subgroup onto a closed subgroup. -/
theorem pdg_isClosed_map (e : G ≃* H) (he : IsHomeomorph (e : G → H)) (S : Subgroup G)
    (hS : IsClosed (S : Set G)) : IsClosed ((S.map (e : G →* H) : Subgroup H) : Set H) := by
  rw [Subgroup.coe_map]
  exact (Homeomorph.isClosed_image (IsHomeomorph.homeomorph (e : G → H) he)).mpr hS

end Aux

/-! ## The place correspondence for a single place -/

section Place

variable {K₁ K₂ K₁' K₂' : Type} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- Two places whose decomposition groups have non-trivial intersection agree; this is the
contrapositive of the disjointness of decomposition groups of distinct places
(`Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne`). -/
theorem pdg_eq_of_le_decompositionGroup {A A' : ValuationSubring K₁'}
    (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) (hA' : A'.comap (algebraMap K₁ K₁') ≠ ⊤)
    (hle : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A ≤
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A') :
    A = A' := by
  by_contra hne
  have hbot : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A ⊓
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A' = ⊥ :=
    Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne
      hne hA hA'
  have hSbot : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A = ⊥ := by
    rw [← hbot]
    exact le_antisymm (le_inf le_rfl hle) inf_le_left
  exact Submission.NeukirchUchida.decompositionGroup_ne_bot hA hSbot

/-- **Glue G1, one direction.**  Under the containment input `h1` and the local isomorphism
input `h5`, the image of the decomposition group of a place over a finite prime is again the
decomposition group of a place over a finite prime.

Proof.  Let `S = D_A`.  The image `S.map ϕ` is closed and topologically isomorphic to the
absolute Galois group of the completion (via `h5`), so `h1` produces a place `B` with
`S.map ϕ ≤ D_B`.  Applying the same reasoning to `D_B.comap ϕ` produces a place `A'` with
`D_B.comap ϕ ≤ D_{A'}`; then `D_A ≤ D_{A'}`, and since distinct places have disjoint
decomposition groups (`D_A ≠ ⊥`) we get `A' = A`, whence `D_B.comap ϕ = D_A` and so
`D_B = S.map ϕ`. -/
theorem pdg_exists_place_of_map (h1 : NK.NUV2.DecompContainment)
    (h5 : NK.NUV2.DecompContinuousIso)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph (ϕ : Gal(K₁'/K₁) → Gal(K₂'/K₂)))
    {A : ValuationSubring K₁'} (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) :
    ∃ B : ValuationSubring K₂', B.comap (algebraMap K₂ K₂') ≠ ⊤ ∧
      (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
          (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
        Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B := by
  classical
  obtain ⟨𝔭, h𝔭⟩ := NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := K₁) (K' := K₁') A hA
  let S : Subgroup Gal(K₁'/K₁) :=
    Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A
  have hSclosed : IsClosed (S : Set Gal(K₁'/K₁)) :=
    Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A
  have hSiso : Nonempty
      (S ≃ₜ* Gal(SeparableClosure (𝔭.adicCompletion K₁) / 𝔭.adicCompletion K₁)) :=
    h5 K₁ K₁' 𝔭 A h𝔭
  let H : Subgroup Gal(K₂'/K₂) := S.map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))
  have hHclosed : IsClosed (H : Set Gal(K₂'/K₂)) := pdg_isClosed_map ϕ he S hSclosed
  have hHiso : Nonempty
      (H ≃ₜ* Gal(SeparableClosure (𝔭.adicCompletion K₁) / 𝔭.adicCompletion K₁)) := by
    obtain ⟨e⟩ := hSiso
    exact ⟨(pdg_subgroupContinuousMulEquiv ϕ he S).symm.trans e⟩
  obtain ⟨B, hB, hHle⟩ :=
    h1 K₂ K₂' H hHclosed ⟨K₁, inferInstance, inferInstance, 𝔭, hHiso⟩
  obtain ⟨𝔮, h𝔮⟩ := NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := K₂) (K' := K₂') B hB
  let T : Subgroup Gal(K₂'/K₂) :=
    Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B
  have hTclosed : IsClosed (T : Set Gal(K₂'/K₂)) :=
    Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring B
  have hTiso : Nonempty
      (T ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion K₂) / 𝔮.adicCompletion K₂)) :=
    h5 K₂ K₂' 𝔮 B h𝔮
  let U : Subgroup Gal(K₁'/K₁) := T.comap (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))
  have hUclosed : IsClosed (U : Set Gal(K₁'/K₁)) := by
    have hcoe : (U : Set Gal(K₁'/K₁)) =
        (ϕ : Gal(K₁'/K₁) → Gal(K₂'/K₂)) ⁻¹' (T : Set Gal(K₂'/K₂)) :=
      Subgroup.coe_comap T (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))
    rw [hcoe]
    exact hTclosed.preimage he.continuous
  have hmap : U.map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) = T :=
    Subgroup.map_comap_eq_self_of_surjective ϕ.surjective T
  have hUiso : Nonempty
      (U ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion K₂) / 𝔮.adicCompletion K₂)) := by
    obtain ⟨e⟩ := hTiso
    exact ⟨(pdg_subgroupContinuousMulEquiv ϕ he U).trans
      ((pdg_subgroupCongrContinuousMulEquiv hmap).trans e)⟩
  obtain ⟨A', hA'ne, hUle⟩ :=
    h1 K₁ K₁' U hUclosed ⟨K₂, inferInstance, inferInstance, 𝔮, hUiso⟩
  have hSU : S ≤ U := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact hHle (Subgroup.mem_map_of_mem (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) hx)
  have hle : S ≤ Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A' :=
    hSU.trans hUle
  have hAeq : A' = A := (pdg_eq_of_le_decompositionGroup hA hA'ne hle).symm
  have hUleS : U ≤ S := by
    intro x hx
    have hx' := hUle hx
    rw [hAeq] at hx'
    exact hx'
  have hUeqS : U = S := le_antisymm hUleS hSU
  refine ⟨B, hB, ?_⟩
  have hHT : H = T := by
    have h1' : H = U.map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := by
      show S.map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
        U.map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))
      rw [hUeqS]
    rw [h1', hmap]
  exact hHT

end Place

/-! ## The glue -/

/-- **Glue G1.**  A homeomorphic isomorphism of absolute Galois groups maps decomposition
groups of places over finite primes onto decomposition groups of places over finite primes,
i.e. `PreservesDecompositionGroups ϕ`, given the containment input `h1` (CoNF 12.1.9, hard
half) and the local isomorphism input `h5`. -/
theorem pdg_for (h1 : NK.NUV2.DecompContainment) (h5 : NK.NUV2.DecompContinuousIso)
    {K₁ K₂ K₁' K₂' : Type} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph (ϕ : Gal(K₁'/K₁) → Gal(K₂'/K₂))) :
    Submission.NeukirchUchida.PreservesDecompositionGroups ϕ := by
  constructor
  · intro A hA
    exact pdg_exists_place_of_map h1 h5 ϕ he hA
  · intro B hB
    obtain ⟨A, hA, hAB⟩ := pdg_exists_place_of_map (K₁ := K₂) (K₂ := K₁) (K₁' := K₂')
      (K₂' := K₁') h1 h5 ϕ.symm (Submission.NeukirchUchida.isHomeomorph_symm ϕ he) hB
    refine ⟨A, hA, ?_⟩
    rw [← hAB, Subgroup.map_map]
    have hcomp : ((ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)).comp
        (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁))) = MonoidHom.id Gal(K₂'/K₂) := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
    rfl

theorem pdg_of_leaves (h1 : NK.NUV2.DecompContainment) (h5 : NK.NUV2.DecompContinuousIso) : NK.NUV2.PDGAll0 := by
  intro K₁ K₂ K₁' K₂' hF1 hF2 hF1' hF2' hN1 hN2 hAl1 hAl2 hSC1 hSC2 ϕ he
  exact pdg_for h1 h5 ϕ he

end NK.NUV2.LC
