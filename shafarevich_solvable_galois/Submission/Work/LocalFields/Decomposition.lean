import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Submission.Work.LocalFields.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Pointwise Valued WithZero

variable {K : Type*} [Field K] {L : Type*} [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The **decomposition group** of a finite prime `w` of `L` in a finite Galois extension
`L/K`: the stabilizer of the prime ideal `w` under the action of `Gal(L/K)` on the primes of
`L`, i.e. the set of `σ` with `σ(w.asIdeal) = w.asIdeal`. -/
noncomputable abbrev decompositionGroup (K : Type*) [Field K] [NumberField K] {L : Type*}
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : FinitePrime L) : Subgroup Gal(L/K) :=
  MulAction.stabilizer Gal(L/K) w.asIdeal

/-- The **inertia subgroup** `I_w` of a finite prime `w` of `L`, as a subgroup of the
decomposition group `D_w`: the kernel of the action of `D_w` on the residue field `κ_w`. -/
noncomputable abbrev inertiaSubgroup (K : Type*) [Field K] [NumberField K] {L : Type*}
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : FinitePrime L) : Subgroup (decompositionGroup K w) :=
  (Ideal.inertia Gal(L/K) w.asIdeal).subgroupOf (decompositionGroup K w)

/-- A prime `w` of `L` is **unramified** over `K` if its inertia subgroup is trivial. -/
def IsUnramifiedAt (K : Type*) [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : FinitePrime L) : Prop :=
  inertiaSubgroup K w = ⊥

/-- A prime `w` of `L` is **totally ramified** over `K` if its inertia subgroup is everything,
i.e. the whole decomposition group acts trivially on the residue field. -/
def IsTotallyRamifiedAt (K : Type*) [Field K] [NumberField K] {L : Type*} [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : FinitePrime L) : Prop :=
  inertiaSubgroup K w = ⊤

/-- A prime `w` of `L` **splits completely** over `K` if its decomposition group is trivial. -/
def IsSplitAt (K : Type*) [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : FinitePrime L) : Prop :=
  decompositionGroup K w = ⊥

/-- A prime `w` of `L` is **inert** over `K` if its decomposition group is everything, i.e. `w`
is the only prime of `L` above the prime of `K` below it. -/
def IsInertAt (K : Type*) [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : FinitePrime L) : Prop :=
  decompositionGroup K w = ⊤

variable {w : FinitePrime L}

/-- The inertia subgroup is normal in the decomposition group. -/
instance inertiaSubgroup_normal (w : FinitePrime L) : (inertiaSubgroup K w).Normal := by
  rw [show inertiaSubgroup K w = Ideal.inertia (decompositionGroup K w) w.asIdeal from
    AddSubgroup.subgroupOf_inertia (I := w.asIdeal.toAddSubgroup)
      (decompositionGroup K w)]
  infer_instance

theorem mem_decompositionGroup_iff (σ : Gal(L/K)) :
    σ ∈ decompositionGroup K w ↔ σ • w.asIdeal = w.asIdeal := Iff.rfl

theorem mem_decompositionGroup_iff_inv (σ : Gal(L/K)) :
    σ ∈ decompositionGroup K w ↔ σ⁻¹ • w.asIdeal = w.asIdeal := by
  rw [mem_decompositionGroup_iff]
  constructor
  · intro h
    calc σ⁻¹ • w.asIdeal = σ⁻¹ • (σ • w.asIdeal) := by rw [h]
      _ = w.asIdeal := inv_smul_smul σ w.asIdeal
  · intro h
    calc σ • w.asIdeal = σ • (σ⁻¹ • w.asIdeal) := by rw [h]
      _ = w.asIdeal := smul_inv_smul σ w.asIdeal

/-- The inertia subgroup is contained in the decomposition group. -/
theorem inertiaSubgroup_le (w : FinitePrime L) :
    Ideal.inertia Gal(L/K) w.asIdeal ≤ decompositionGroup K w :=
  Ideal.inertia_le_stabilizer w.asIdeal

/-- Membership in the inertia subgroup, in terms of membership in `Gal(L/K)`. -/
theorem mem_inertiaSubgroup_iff (σ : decompositionGroup K w) :
    σ ∈ inertiaSubgroup K w ↔ (σ : Gal(L/K)) ∈ Ideal.inertia Gal(L/K) w.asIdeal :=
  Iff.rfl

/-- The inertia subgroup, computed inside the decomposition group. -/
theorem inertiaSubgroup_eq_inertia_stabilizer :
    inertiaSubgroup K w = Ideal.inertia (decompositionGroup K w) w.asIdeal :=
  AddSubgroup.subgroupOf_inertia (I := w.asIdeal.toAddSubgroup) (decompositionGroup K w)

theorem decompositionGroup_eq_bot_iff :
    decompositionGroup K w = ⊥ ↔ ∀ σ : Gal(L/K), σ • w.asIdeal = w.asIdeal → σ = 1 := by
  rw [Subgroup.eq_bot_iff_forall]
  exact forall_congr' fun σ => by rw [mem_decompositionGroup_iff]

/-- A prime splits completely if and only if every element of the Galois group fixing it is
trivial. -/
theorem isSplitAt_iff : IsSplitAt K w ↔
    ∀ σ : Gal(L/K), σ • w.asIdeal = w.asIdeal → σ = 1 :=
  decompositionGroup_eq_bot_iff

/-- A prime is inert if and only if the Galois group acts trivially on it. -/
theorem isInertAt_iff : IsInertAt K w ↔ ∀ σ : Gal(L/K), σ • w.asIdeal = w.asIdeal :=
  Subgroup.eq_top_iff' _

end Work.LocalFields
