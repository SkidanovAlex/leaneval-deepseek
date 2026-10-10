import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `T`-unit lattice: vocabulary

Let `L / K` be a finite Galois extension of number fields, `T` a finite `Gal(L/K)`-stable set of
places of `L`.  Milne's proof of Proposition 3.1 (*Class Field Theory*, Chapter VII §3) computes
the Herbrand quotient of the group `U(T)` of `T`-units by comparing two `Gal(L/K)`-stable full
lattices in the real representation `V = ∏_{w ∈ T} ℝ`:

* the **log lattice** `U(T) → V`, `a ↦ (log |a|_w)_{w ∈ T}` (with the product formula giving that
  its image lies in the sum-zero hyperplane), completed by the all-ones vector `e`;
* the **divisor lattice** `Hom(T, ℤ) = ∏_{w ∈ T} ℤ` (`placeFunRep` below), whose Herbrand quotient
  is `∏_{v ∈ S} |D_v|`.

This file provides the vocabulary: the permutation action on functions on `T`, the module
`placeFunRep`, the log vector `logVec` and its `ℤ`-linear version `logVecLin`.

## Main definitions

* `NK.GlobalCFTdeep.permAction`: the action of `Gal(L/K)` on functions on a stable set of places;
* `NK.GlobalCFTdeep.placeFunRep`: `Hom(T, ℤ)` as a `ℤ[Gal(L/K)]`-module;
* `NK.GlobalCFTdeep.logVec` / `logVecLin`: the logarithm of the normalized local absolute value;
* `NK.GlobalCFTdeep.sumZero`: the sum-zero hyperplane of `↥T → ℝ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The permutation action** of `Gal(L/K)` on functions on a `Gal(L/K)`-stable set of places
`T`: `(σ • f) w = f (σ⁻¹ • w)`.  The action on the values is trivial. -/
noncomputable def permAction (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (A : Type*) [AddCommGroup A] : DistribMulAction (L ≃ₐ[K] L) (↥T → A) where
  smul σ f := fun w => f ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩
  one_smul f := by funext w; exact congrArg f (Subtype.ext (by simp))
  mul_smul σ τ f := by funext w; exact congrArg f (Subtype.ext (by simp [mul_smul]))
  smul_zero σ := by funext w; rfl
  smul_add σ f g := by funext w; rfl

/-- The permutation action, unfolded. -/
theorem permAction_smul_apply {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (A : Type*) [AddCommGroup A] (σ : L ≃ₐ[K] L) (f : ↥T → A) (w : ↥T) :
    letI := permAction T hT A
    (σ • f) w = f ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩ := rfl

/-- **The divisor lattice** `Hom(T, ℤ) = ∏_{w ∈ T} ℤ`, as a `ℤ[Gal(L/K)]`-module: the permutation
module of the `Gal(L/K)`-set `T`. -/
noncomputable def placeFunRep (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) : Rep ℤ (L ≃ₐ[K] L) :=
  letI := permAction T hT ℤ
  Rep.ofDistribMulAction ℤ (L ≃ₐ[K] L) (↥T → ℤ)

/-- **The sum-zero hyperplane** of `↥T → ℝ`, the subspace in which the logarithm of a `T`-unit
lies (the product formula). -/
def sumZero (T : Set (Place L)) [Fintype ↥T] : Submodule ℝ (↥T → ℝ) :=
  { carrier := {f | ∑ w : ↥T, f w = 0}
    zero_mem' := by simp
    add_mem' := by
      intro f g hf hg
      simp only [Set.mem_setOf_eq, Pi.add_apply]
      rw [Finset.sum_add_distrib, hf, hg, add_zero]
    smul_mem' := by
      intro c f hf
      simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, hf, mul_zero] }

@[simp] theorem mem_sumZero {T : Set (Place L)} [Fintype ↥T] {f : ↥T → ℝ} :
    f ∈ sumZero T ↔ ∑ w : ↥T, f w = 0 := Iff.rfl

/-- The all-ones vector `e = (1, …, 1) ∈ ↥T → ℝ` (well defined when `T` is nonempty). -/
def oneVec (T : Set (Place L)) : ↥T → ℝ := fun _ => 1

/-- The all-ones vector is the constant `1`. -/
@[simp] theorem oneVec_apply (T : Set (Place L)) (w : ↥T) : oneVec T w = 1 := rfl

/-- **The logarithm of the normalized local absolute value** of a `T`-unit: the map
`a ↦ (log |a|_w)_{w ∈ T}` from `Lˣ` to `∏_{w ∈ T} ℝ`. -/
noncomputable def logVec (T : Set (Place L)) (a : Lˣ) : ↥T → ℝ :=
  fun w => Real.log ((Idele.localAbs L (w : Place L)
    (Idele.principalIdele L a (w : Place L)) : ℝˣ) : ℝ)

/-- The logarithm of the normalized local absolute value is multiplicative in the argument. -/
theorem logVec_mul (T : Set (Place L)) (a b : Lˣ) :
    logVec T (a * b) = logVec T a + logVec T b := by
  funext w
  simp only [logVec, Pi.add_apply]
  rw [MonoidHom.map_mul (Idele.principalIdele L) a b, Idele.mul_apply, MonoidHom.map_mul,
    Units.val_mul, Real.log_mul (Units.ne_zero _) (Units.ne_zero _)]

@[simp] theorem logVec_one (T : Set (Place L)) : logVec T 1 = 0 := by
  funext w
  simp [logVec]

/-- **The log map on the `T`-units**, as an additive homomorphism. -/
noncomputable def logVecAddHom (T : Set (Place L)) :
    Additive (TUnits T) →+ (↥T → ℝ) where
  toFun a := logVec T ((Additive.toMul a : TUnits T) : Lˣ)
  map_zero' := by simp
  map_add' a b := by
    show logVec T ((Additive.toMul (a + b) : TUnits T) : Lˣ) =
      logVec T ((Additive.toMul a : TUnits T) : Lˣ) + logVec T ((Additive.toMul b : TUnits T) : Lˣ)
    rw [toMul_add, Subgroup.coe_mul, logVec_mul]

/-- **The log map on the `T`-units**, as a `ℤ`-linear map: `a ↦ (log |a|_w)_{w ∈ T}`. -/
noncomputable def logVecLin (T : Set (Place L)) :
    Additive (TUnits T) →ₗ[ℤ] (↥T → ℝ) :=
  (logVecAddHom T).toIntLinearMap

theorem logVecLin_apply (T : Set (Place L)) (a : Additive (TUnits T)) :
    logVecLin T a = logVec T ((Additive.toMul a : TUnits T) : Lˣ) := rfl

end NK.GlobalCFTdeep
