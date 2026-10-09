import Mathlib
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.levelInertia_defs
import Submission.Work.SSGRoute.exists_levelSub_le_of_isOpen
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
import Submission.Work.SSGRoute.PTWild.WildLevelStructure
import Submission.Work.SSGRoute.SSGIW.Basic
import Submission.Work.SSGRoute.SSGIW.coprime_card_sup
import Submission.Work.SSGRoute.SSGIW.wildLvl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Elementary properties of the level wild kernels `NumIdx` and of the wild kernel `Vsub`

The vocabulary is in `Submission.Work.SSGRoute.SSGIW.Basic`; here we prove that

* the inertia subgroup `I_A` of a finite place is closed (hence compact) in the Krull topology;
* `NumIdx p k Ω A hA i` is normal, closed and open in `↥I_A`, and `Vsub` is normal and closed;
* the index of `NumIdx` at a level `M` equals the index of `wildLvl` inside the level inertia.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open scoped Pointwise NumberField

namespace Work.SSGRoute

/-- The preimage of a subgroup of a discrete group under a continuous map is closed. -/
theorem isClosed_comap_of_discrete {G H : Type*} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] [DiscreteTopology H] (f : G →* H) (S : Subgroup H)
    (hf : Continuous f) : IsClosed ((S.comap f : Subgroup G) : Set G) := by
  rw [Subgroup.coe_comap]
  exact (isClosed_discrete _).preimage hf

/-- The preimage of a subgroup of a discrete group under a continuous map is open. -/
theorem isOpen_comap_of_discrete {G H : Type*} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] [DiscreteTopology H] (f : G →* H) (S : Subgroup H)
    (hf : Continuous f) : IsOpen ((S.comap f : Subgroup G) : Set G) := by
  rw [Subgroup.coe_comap]
  exact (isOpen_discrete _).preimage hf

/-- `levelSub` at a bundled finite normal level, over a base field. -/
noncomputable def levelSubAt (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (i : {M : IntermediateField k Ω // FiniteDimensional k M ∧ Normal k M}) :
    Subgroup (Ω ≃ₐ[k] Ω) :=
  letI := i.2.1
  letI := i.2.2
  levelSub A i.1

/-! ## The inertia subgroup is closed and compact -/

theorem isClosed_inertiaSub_of_levelSub (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω) :
    IsClosed ((inertiaSub k Ω A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
  have hset : ((inertiaSub k Ω A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω))
      = ⋂ (i : {M : IntermediateField k Ω // FiniteDimensional k M ∧ Normal k M}),
          ((levelSubAt k Ω A i : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
    ext δ
    rw [Set.mem_iInter]
    change δ ∈ inertiaSub k Ω A ↔ ∀ i, δ ∈ levelSubAt k Ω A i
    rw [mem_inertiaSub]
    constructor
    · intro h i
      haveI := i.2.1
      haveI := i.2.2
      exact (mem_levelSub_iff A δ).mpr h i.1
    · intro h
      exact (mem_levelSub_iff A δ).mp (fun M hfd hnm => h ⟨M, hfd, hnm⟩)
  rw [hset]
  exact isClosed_iInter fun i => by
    haveI := i.2.1
    haveI := i.2.2
    exact isClosed_levelSub A i.1

theorem compactSpace_inertiaSub (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) : CompactSpace ↥(inertiaSub k Ω A) := by
  haveI : IsGalois k Ω := inferInstance
  exact isCompact_iff_compactSpace.mp ((isClosed_inertiaSub_of_levelSub k Ω A).isCompact)

/-! ## `idxHomOf` is continuous -/

theorem continuous_idxHomOf (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    Continuous (idxHomOf k Ω A hA M) := by
  have h1 : Continuous (((AlgEquiv.restrictNormalHom M).comp (inertiaSub k Ω A).subtype) :
      ↥(inertiaSub k Ω A) → (↥M ≃ₐ[k] ↥M)) :=
    (InfiniteGalois.restrictNormalHom_continuous M).comp continuous_subtype_val
  exact h1.subtype_mk _

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)

/-! ## Normality and closedness of the level wild kernels -/

/-- The level wild kernel, at an explicit level (with the instances as arguments). -/
noncomputable def NumIdxAt (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M]
    [NumberField ↥M] : Subgroup ↥(inertiaSub k Ω A) :=
  (wildLvl p k Ω A hA M).comap (idxHomOf k Ω A hA M)

theorem NumIdx_eq_NumIdxAt (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M]
    [NumberField ↥M] :
    NumIdx p k Ω A hA (idxOf k Ω M) = NumIdxAt p k Ω A hA M := rfl

theorem NumIdx_normal (i : Idx k Ω) : (NumIdx p k Ω A hA i).Normal := by
  letI := i.2.1
  letI := i.2.2.1
  letI := i.2.2.2
  rw [show i = idxOf k Ω i.1 from rfl, NumIdx_eq_NumIdxAt]
  exact (wildLvl_normal p k Ω A hA i.1).comap (idxHomOf k Ω A hA i.1)

theorem NumIdx_isClosed' (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M]
    [NumberField ↥M] :
    IsClosed ((NumIdx p k Ω A hA (idxOf k Ω M) : Subgroup ↥(inertiaSub k Ω A)) :
      Set ↥(inertiaSub k Ω A)) := by
  haveI : DiscreteTopology ↥(levelInertiaOf k Ω A hA M) := inferInstance
  show IsClosed ((NumIdxAt p k Ω A hA M : Subgroup ↥(inertiaSub k Ω A)) : Set ↥(inertiaSub k Ω A))
  exact isClosed_comap_of_discrete (idxHomOf k Ω A hA M) (wildLvl p k Ω A hA M)
    (continuous_idxHomOf k Ω A hA M)

theorem NumIdx_isOpen' (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M]
    [NumberField ↥M] :
    IsOpen ((NumIdx p k Ω A hA (idxOf k Ω M) : Subgroup ↥(inertiaSub k Ω A)) :
      Set ↥(inertiaSub k Ω A)) := by
  haveI : DiscreteTopology ↥(levelInertiaOf k Ω A hA M) := inferInstance
  show IsOpen ((NumIdxAt p k Ω A hA M : Subgroup ↥(inertiaSub k Ω A)) : Set ↥(inertiaSub k Ω A))
  exact isOpen_comap_of_discrete (idxHomOf k Ω A hA M) (wildLvl p k Ω A hA M)
    (continuous_idxHomOf k Ω A hA M)

theorem NumIdx_isClosed (i : Idx k Ω) :
    IsClosed ((NumIdx p k Ω A hA i : Subgroup ↥(inertiaSub k Ω A)) : Set ↥(inertiaSub k Ω A)) := by
  letI := i.2.1
  letI := i.2.2.1
  letI := i.2.2.2
  rw [show i = idxOf k Ω i.1 from rfl]
  exact NumIdx_isClosed' p k Ω A hA i.1

theorem NumIdx_isOpen (i : Idx k Ω) :
    IsOpen ((NumIdx p k Ω A hA i : Subgroup ↥(inertiaSub k Ω A)) : Set ↥(inertiaSub k Ω A)) := by
  letI := i.2.1
  letI := i.2.2.1
  letI := i.2.2.2
  rw [show i = idxOf k Ω i.1 from rfl]
  exact NumIdx_isOpen' p k Ω A hA i.1

theorem Vsub_normal : (Vsub p k Ω A hA).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_Vsub_iff] at hn ⊢
  intro i
  haveI := NumIdx_normal p k Ω A hA i
  exact (inferInstance : (NumIdx p k Ω A hA i).Normal).conj_mem n (hn i) g

theorem Vsub_isClosed :
    IsClosed ((Vsub p k Ω A hA : Subgroup ↥(inertiaSub k Ω A)) : Set ↥(inertiaSub k Ω A)) := by
  rw [show ((Vsub p k Ω A hA : Subgroup ↥(inertiaSub k Ω A)) : Set ↥(inertiaSub k Ω A))
      = ⋂ i : Idx k Ω, ((NumIdx p k Ω A hA i : Subgroup ↥(inertiaSub k Ω A)) :
          Set ↥(inertiaSub k Ω A)) from Subgroup.coe_iInf]
  exact isClosed_iInter fun i => NumIdx_isClosed p k Ω A hA i

/-- The index of the level wild kernel is the index of the wild inertia in the level inertia. -/
theorem NumIdx_index_eq (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M]
    [NumberField ↥M] :
    (NumIdx p k Ω A hA (idxOf k Ω M)).index = (wildLvl p k Ω A hA M).index := by
  have hsurj : Function.Surjective (idxHomOf k Ω A hA M) := by
    intro y
    have hy : (y : ↥M ≃ₐ[k] ↥M) ∈ (inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom M) := by
      rw [inertiaSub_image_eq_levelInertia k Ω A hA M]
      exact y.2
    obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨σ, hσ⟩, Subtype.ext hσeq⟩
  rw [NumIdx_eq_NumIdxAt]
  exact Subgroup.index_comap_of_surjective (f := idxHomOf k Ω A hA M)
    (wildLvl p k Ω A hA M) hsurj

end Work.SSGRoute
