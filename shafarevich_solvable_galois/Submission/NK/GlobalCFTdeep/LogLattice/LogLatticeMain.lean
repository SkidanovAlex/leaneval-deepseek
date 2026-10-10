import Mathlib.RingTheory.TotallySplit
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.StableRep
import Submission.NK.GlobalCFTdeep.LogLattice.finite_ker_logVecLin
import Submission.NK.GlobalCFTdeep.LogLattice.logVec_smul_apply
import Submission.NK.GlobalCFTdeep.LogLattice.sum_logVec_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two `G`-stable lattices of Milne's proof of Proposition 3.1

For `T` a finite `Gal(L/K)`-stable set of places of `L` containing all infinite places, this file
collects the two `ℤ[Gal(L/K)]`-lattices of Milne's proof of the `S`-unit computation:

* `logLattice T`: the image of the log map `U(T) → ∏_{w ∈ T} ℝ`, a full lattice in the sum-zero
  hyperplane;
* `unitLattice T`: `logLattice T + ℤ·e`, a full lattice in `∏_{w ∈ T} ℝ` (Milne's lattice `M`).

Both are `AddSubgroup`s of `↥T → ℝ`, stable under the permutation action of `Gal(L/K)`, hence
`ℤ[Gal(L/K)]`-modules (`repOfStableAddSubgroup`).

## Main definitions

* `NK.GlobalCFTdeep.logLattice`;
* `NK.GlobalCFTdeep.unitLattice`;
* `NK.GlobalCFTdeep.logLatticeRep`, `NK.GlobalCFTdeep.unitLatticeRep`;
* `NK.GlobalCFTdeep.logKernel` (the kernel `μ` of the log map, finite) and its `Rep` structure.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The log lattice** `M' = log U(T) ⊆ ∏_{w ∈ T} ℝ`, the image of the log map on the `T`-units
(Milne, *CFT*, Chapter VII §3). -/
def logLattice (T : Set (Place L)) [Fintype ↥T] : AddSubgroup (↥T → ℝ) :=
  ((logVecLin T).range).toAddSubgroup

@[simp] theorem mem_logLattice {T : Set (Place L)} [Fintype ↥T] {x : ↥T → ℝ} :
    x ∈ logLattice T ↔ ∃ a : Additive (TUnits T), logVecLin T a = x := by
  rw [logLattice, Submodule.mem_toAddSubgroup]
  exact Iff.rfl

/-- **The full log lattice** `M = M' + ℤ·e` (Milne's lattice `M`): the log lattice of the
`T`-units together with the all-ones vector.  It is the union of the cosets `M' + n·e`. -/
def unitLattice (T : Set (Place L)) [Fintype ↥T] : AddSubgroup (↥T → ℝ) where
  carrier := {x | ∃ y ∈ logLattice T, ∃ n : ℤ, x = y + n • oneVec T}
  zero_mem' := ⟨0, zero_mem _, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, m, rfl⟩ ⟨b, hb, n, rfl⟩
    refine ⟨a + b, add_mem ha hb, m + n, ?_⟩
    rw [add_zsmul]
    abel
  neg_mem' := by
    rintro x ⟨a, ha, n, rfl⟩
    refine ⟨-a, neg_mem ha, -n, ?_⟩
    rw [neg_zsmul]
    abel

theorem mem_unitLattice_iff {T : Set (Place L)} [Fintype ↥T] {x : ↥T → ℝ} :
    x ∈ unitLattice T ↔ ∃ y ∈ logLattice T, ∃ n : ℤ, x = y + n • oneVec T := Iff.rfl

theorem logLattice_le_unitLattice (T : Set (Place L)) [Fintype ↥T] :
    logLattice T ≤ unitLattice T := fun x hx => ⟨x, hx, 0, by simp⟩

theorem oneVec_mem_unitLattice (T : Set (Place L)) [Fintype ↥T] :
    oneVec T ∈ unitLattice T := ⟨0, zero_mem _, 1, by simp⟩

theorem unitLattice_eq_sup (T : Set (Place L)) [Fintype ↥T] :
    unitLattice T = logLattice T ⊔ AddSubgroup.closure {oneVec T} := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, n, rfl⟩
    refine add_mem (AddSubgroup.mem_sup_left hy) ?_
    exact AddSubgroup.mem_sup_right
      (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_singleton (oneVec T))) n)
  · refine sup_le (logLattice_le_unitLattice T) ?_
    refine (AddSubgroup.closure_le (unitLattice T)).2 ?_
    rintro x rfl
    exact oneVec_mem_unitLattice T

end NK.GlobalCFTdeep

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Stability

variable (T : Set (Place L)) [Fintype ↥T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)

/-- The log lattice is `Gal(L/K)`-stable: the log vector of `σ a` is the permuted log vector
of `a` (`NK.GlobalCFTdeep.LogLattice.logVec_smul_apply`). -/
theorem smul_mem_logLattice (σ : L ≃ₐ[K] L) {x : ↥T → ℝ} (hx : x ∈ logLattice T) :
    (fun w : ↥T => x ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩) ∈ logLattice T := by
  obtain ⟨a, rfl⟩ := mem_logLattice.mp hx
  letI : MulDistribMulAction (L ≃ₐ[K] L) (TUnits T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TUnits T) (fun σ x hx => smul_mem_TUnits hT hx)
  refine ⟨Additive.ofMul (σ • Additive.toMul a), ?_⟩
  funext w
  show logVec T (((σ • Additive.toMul a : TUnits T)) : Lˣ) w =
    logVec T (((Additive.toMul a : TUnits T)) : Lˣ) ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩
  rw [show (((σ • Additive.toMul a : TUnits T)) : Lˣ) =
    σ • (((Additive.toMul a : TUnits T)) : Lˣ) from rfl]
  exact NK.GlobalCFTdeep.LogLattice.logVec_smul_apply T hT σ
    (((Additive.toMul a : TUnits T)) : Lˣ) w

/-- The all-ones vector is fixed by the permutation action. -/
theorem perm_oneVec_apply (σ : L ≃ₐ[K] L) (w : ↥T) :
    oneVec T ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩ = oneVec T w := by
  simp [oneVec]

/-- The full log lattice `M = M' + ℤ·e` is `Gal(L/K)`-stable. -/
theorem smul_mem_unitLattice (σ : L ≃ₐ[K] L) {x : ↥T → ℝ} (hx : x ∈ unitLattice T) :
    (fun w : ↥T => x ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩) ∈ unitLattice T := by
  obtain ⟨y, hy, n, rfl⟩ := mem_unitLattice_iff.mp hx
  refine ⟨(fun w : ↥T => y ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩),
    smul_mem_logLattice T hT σ hy, n, ?_⟩
  funext w
  simp only [Pi.add_apply, Pi.smul_apply, oneVec]

end Stability

end NK.GlobalCFTdeep

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The divisor lattice** `Hom(T, ℤ) = ∏_{w ∈ T} ℤ` inside `∏_{w ∈ T} ℝ` (Milne's lattice `N`):
the functions with integral values. -/
def divisorLattice (T : Set (Place L)) : AddSubgroup (↥T → ℝ) where
  carrier := {f | ∀ w : ↥T, ∃ n : ℤ, f w = n}
  zero_mem' := fun w => ⟨0, by simp⟩
  add_mem' := by
    intro f g hf hg w
    obtain ⟨m, hm⟩ := hf w
    obtain ⟨n, hn⟩ := hg w
    exact ⟨m + n, by rw [Pi.add_apply, hm, hn]; push_cast; ring⟩
  neg_mem' := by
    intro f hf w
    obtain ⟨m, hm⟩ := hf w
    exact ⟨-m, by rw [Pi.neg_apply, hm]; push_cast; ring⟩

theorem mem_divisorLattice {T : Set (Place L)} {f : ↥T → ℝ} :
    f ∈ divisorLattice T ↔ ∀ w : ↥T, ∃ n : ℤ, f w = n := Iff.rfl

/-- The divisor lattice is `Gal(L/K)`-stable. -/
theorem smul_mem_divisorLattice (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (σ : L ≃ₐ[K] L) {f : ↥T → ℝ} (hf : f ∈ divisorLattice T) :
    (fun w : ↥T => f ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩) ∈ divisorLattice T :=
  fun w => hf _

/-- The divisor lattice spans `∏_{w ∈ T} ℝ`. -/
theorem span_divisorLattice (T : Set (Place L)) [Fintype ↥T] :
    Submodule.span ℝ (divisorLattice T : Set (↥T → ℝ)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  have : f = ∑ w : ↥T, f w • (Pi.single w (1 : ℝ)) := by
    funext v
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
  rw [this]
  refine Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span (show (Pi.single w (1 : ℝ) : ↥T → ℝ) ∈ divisorLattice T from
    fun v => ?_)
  by_cases hv : v = w
  · exact ⟨1, by simp [Pi.single_apply, hv]⟩
  · exact ⟨0, by simp [Pi.single_apply, hv]⟩

end NK.GlobalCFTdeep

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Finiteness

variable (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T)

instance instIsTorsionFreeLogLattice : Module.IsTorsionFree ℤ ↥(logLattice T) :=
  ⟨fun r hr => by
    intro x y hxy
    refine Subtype.ext ?_
    exact (Module.IsTorsionFree.isSMulRegular (M := ↥T → ℝ) hr)
      (by simpa using congrArg (fun z : ↥(logLattice T) => (z : ↥T → ℝ)) hxy)⟩

instance instIsTorsionFreeUnitLattice : Module.IsTorsionFree ℤ ↥(unitLattice T) :=
  ⟨fun r hr => by
    intro x y hxy
    refine Subtype.ext ?_
    exact (Module.IsTorsionFree.isSMulRegular (M := ↥T → ℝ) hr)
      (by simpa using congrArg (fun z : ↥(unitLattice T) => (z : ↥T → ℝ)) hxy)⟩

instance instIsTorsionFreeDivisorLattice : Module.IsTorsionFree ℤ ↥(divisorLattice T) :=
  ⟨fun r hr => by
    intro x y hxy
    refine Subtype.ext ?_
    exact (Module.IsTorsionFree.isSMulRegular (M := ↥T → ℝ) hr)
      (by simpa using congrArg (fun z : ↥(divisorLattice T) => (z : ↥T → ℝ)) hxy)⟩

/-- The log map, viewed as a surjection onto the log lattice. -/
noncomputable def logVecLinToLattice :
    Additive (TUnits T) →ₗ[ℤ] ↥(logLattice T) where
  toFun a := ⟨logVecLin T a, by
    rw [mem_logLattice]
    exact ⟨a, rfl⟩⟩
  map_add' a b := by ext w; simp
  map_smul' n a := by ext w; simp

theorem logVecLinToLattice_surjective : Function.Surjective (logVecLinToLattice T) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, rfl⟩ := mem_logLattice.mp hx
  exact ⟨a, rfl⟩

/-- The log lattice is finitely generated (`finrank_tUnits`). -/
theorem finite_logLattice (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) :
    Module.Finite ℤ ↥(logLattice T) := by
  haveI : Module.Finite ℤ (Additive (TUnits T)) := (Herbrand.finrank_tUnits (L := L) T hTinf).1
  haveI : AddGroup.FG (Additive (TUnits T)) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  exact Module.Finite.iff_addGroup_fg.mpr
    (AddGroup.fg_of_surjective (f := (logVecLinToLattice T).toAddMonoidHom)
      (logVecLinToLattice_surjective T))

theorem free_logLattice (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) :
    Module.Free ℤ ↥(logLattice T) := by
  haveI := finite_logLattice T hTinf
  exact Module.free_of_finite_type_torsion_free'

/-- The surjection `U(T) × ℤ → M = M' + ℤ·e`. -/
noncomputable def unitLatticeSurj :
    Additive (TUnits T) × ℤ →+ ↥(unitLattice T) where
  toFun x := ⟨logVecLin T x.1 + x.2 • oneVec T,
    ⟨logVecLin T x.1, ⟨x.1, rfl⟩, x.2, rfl⟩⟩
  map_zero' := by
    ext w
    simp [Pi.add_apply, oneVec]
  map_add' x y := by
    ext w
    show logVecLin T (x.1 + y.1) w + ((x.2 + y.2) • oneVec T) w =
      (logVecLin T x.1 w + (x.2 • oneVec T) w) +
        (logVecLin T y.1 w + (y.2 • oneVec T) w)
    rw [map_add]
    simp only [Pi.add_apply, Pi.smul_apply, oneVec, add_zsmul]
    ring

theorem unitLatticeSurj_surjective : Function.Surjective (unitLatticeSurj T) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, n, rfl⟩ := mem_unitLattice_iff.mp hx
  obtain ⟨a, rfl⟩ := mem_logLattice.mp hy
  exact ⟨(a, n), rfl⟩

/-- The full log lattice `M = M' + ℤ·e` is finitely generated. -/
theorem finite_unitLattice (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) :
    Module.Finite ℤ ↥(unitLattice T) := by
  haveI : Module.Finite ℤ (Additive (TUnits T)) := (Herbrand.finrank_tUnits (L := L) T hTinf).1
  haveI : Module.Finite ℤ (Additive (TUnits T) × ℤ) := inferInstance
  haveI : AddGroup.FG (Additive (TUnits T) × ℤ) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  exact Module.Finite.iff_addGroup_fg.mpr
    (AddGroup.fg_of_surjective (f := unitLatticeSurj T) (unitLatticeSurj_surjective T))

theorem free_unitLattice (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) :
    Module.Free ℤ ↥(unitLattice T) := by
  haveI := finite_unitLattice T hTinf
  exact Module.free_of_finite_type_torsion_free'

/-- The divisisor lattice is the image of `↥T → ℤ`. -/
noncomputable def divisorHom : (↥T → ℤ) →+ ↥(divisorLattice T) where
  toFun g := ⟨fun w => g w, fun w => ⟨g w, rfl⟩⟩
  map_zero' := by ext w; simp
  map_add' g h := by ext w; simp

theorem divisorHom_bijective : Function.Bijective (divisorHom T) := by
  constructor
  · intro g h hgh
    funext w
    have h2 := congrFun (congrArg (fun z : ↥(divisorLattice T) => (z : ↥T → ℝ)) hgh) w
    change ((g w : ℤ) : ℝ) = ((h w : ℤ) : ℝ) at h2
    exact_mod_cast h2
  · rintro ⟨f, hf⟩
    refine ⟨fun w => Classical.choose (hf w), ?_⟩
    ext w
    exact (Classical.choose_spec (hf w)).symm

/-- The divisor lattice is free. -/
theorem free_divisorLattice : Module.Free ℤ ↥(divisorLattice T) :=
  Module.Free.of_equiv' (R := ℤ) (P := ↥T → ℤ) inferInstance
    (AddEquiv.toIntLinearEquiv (AddEquiv.ofBijective (divisorHom T) (divisorHom_bijective T)))

theorem finite_divisorLattice : Module.Finite ℤ ↥(divisorLattice T) :=
  Module.Finite.iff_addGroup_fg.mpr
    (AddGroup.fg_of_surjective (f := divisorHom T) (divisorHom_bijective T).2)

end Finiteness

end NK.GlobalCFTdeep

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Reps

variable (T : Set (Place L)) [Fintype ↥T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)

/-- The log lattice `M' = log U(T)` as a `ℤ[Gal(L/K)]`-module. -/
noncomputable def logLatticeRep : Rep ℤ (L ≃ₐ[K] L) :=
  letI := permAction T hT ℝ
  letI : DistribMulAction (L ≃ₐ[K] L) ↥(logLattice T) :=
    stableDistribMulActionSubgroup (logLattice T)
      (fun σ x hx => smul_mem_logLattice T hT σ hx)
  Rep.ofDistribMulAction ℤ (L ≃ₐ[K] L) ↥(logLattice T)

/-- The full log lattice `M = M' + ℤ·e` as a `ℤ[Gal(L/K)]`-module. -/
noncomputable def unitLatticeRep : Rep ℤ (L ≃ₐ[K] L) :=
  letI := permAction T hT ℝ
  letI : DistribMulAction (L ≃ₐ[K] L) ↥(unitLattice T) :=
    stableDistribMulActionSubgroup (unitLattice T)
      (fun σ x hx => smul_mem_unitLattice T hT σ hx)
  Rep.ofDistribMulAction ℤ (L ≃ₐ[K] L) ↥(unitLattice T)

/-- The divisor lattice `Hom(T, ℤ) ⊆ ∏_{w ∈ T} ℝ` as a `ℤ[Gal(L/K)]`-module. -/
noncomputable def divisorLatticeRep : Rep ℤ (L ≃ₐ[K] L) :=
  letI := permAction T hT ℝ
  letI : DistribMulAction (L ≃ₐ[K] L) ↥(divisorLattice T) :=
    stableDistribMulActionSubgroup (divisorLattice T)
      (fun σ x hx => smul_mem_divisorLattice T hT σ hx)
  Rep.ofDistribMulAction ℤ (L ≃ₐ[K] L) ↥(divisorLattice T)

end Reps

end NK.GlobalCFTdeep
