import Mathlib
import Submission.Work.DSG2.Defs

/-!
# DSG2: the dehomogenization isomorphisms for the standard charts of `ℙⁿ`

This file sets up the vocabulary used to prove
`Work.DSG2.nonempty_chartRingEquiv`:

* `Work.DSG2.AtoA0`  : the isomorphism `A ≅ 𝒜 0` given by constants,
  where `𝒜 = MvPolynomial.homogeneousSubmodule (Fin (n+1)) A`.
* `Work.DSG2.AtoAway` : the induced ring map `A →+* Away 𝒜 (X i)`.
* `Work.DSG2.e` : the element `Xⱼ / Xᵢ` of `Away 𝒜 (X i)`, for `j = i.succAbove k`.
* `Work.DSG2.Phi` : the `A`-algebra map `A[Y₀,…,Y_{n-1}] →+* Away 𝒜 (X i)`
  sending `Y_k` to `X_{i.succAbove k} / X_i`.  It is the candidate isomorphism.
* `Work.DSG2.dehomX`, `Work.DSG2.dehom` : dehomogenization at the coordinate `i`
  (`Xᵢ ↦ 1`, `X_j ↦ Y_{j ≠ i}`).
* `Work.DSG2.Psi` : the map `Away 𝒜 (X i) →+* A[Y₀,…,Y_{n-1}]` induced by `dehom`,
  a candidate inverse of `Phi`.
-/

open MvPolynomial HomogeneousLocalization

universe u

namespace Work.DSG2

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1))

/-- The grading used on `A[x₀,…,xₙ]`. -/
abbrev chartGrading : ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- The element `Xᵢ` is homogeneous of degree `1`. -/
theorem chartGrading_X_mem : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A) ∈
    chartGrading A n 1 :=
  MvPolynomial.isHomogeneous_X A i

/-- The ring map `A →+* 𝒜 0` sending `a` to the constant polynomial `a`. -/
noncomputable def AtoA0 : A →+* ↥(chartGrading A n 0) where
  toFun a := ⟨MvPolynomial.C a, by
    rw [MvPolynomial.mem_homogeneousSubmodule]; exact MvPolynomial.isHomogeneous_C _ a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/-- The ring map `A →+* Away 𝒜 (X i)` given by constants. -/
noncomputable def AtoAway :
    A →+* HomogeneousLocalization.Away (chartGrading A n) (MvPolynomial.X i) :=
  (HomogeneousLocalization.fromZeroRingHom (chartGrading A n)
    (Submonoid.powers (MvPolynomial.X i))).comp (AtoA0 A n)

/-- The value of `AtoAway a` in the localization is the constant polynomial `a`. -/
theorem val_AtoAway (a : A) :
    (AtoAway A n i a).val = algebraMap (MvPolynomial (Fin (n + 1)) A)
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
      (MvPolynomial.C a) := by
  rw [AtoAway, RingHom.comp_apply, ← HomogeneousLocalization.algebraMap_eq]
  rw [← HomogeneousLocalization.algebraMap_apply (𝒜 := chartGrading A n)
    (x := Submonoid.powers (MvPolynomial.X i))]
  rw [← IsScalarTower.algebraMap_apply (↥(chartGrading A n 0))
    (HomogeneousLocalization.Away (chartGrading A n) (MvPolynomial.X i))
    (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A)) (AtoA0 A n a)]
  rw [IsScalarTower.algebraMap_apply (↥(chartGrading A n 0)) (MvPolynomial (Fin (n + 1)) A)
    (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A)) (AtoA0 A n a)]
  congr 1

/-- The element `X_{i.succAbove k} / Xᵢ` of the `i`-th chart ring. -/
noncomputable def e (k : Fin n) :
    HomogeneousLocalization.Away (chartGrading A n) (MvPolynomial.X i) :=
  HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) 1
    (MvPolynomial.X (i.succAbove k))
    (by simpa using MvPolynomial.isHomogeneous_X A (i.succAbove k))

/-- The dehomogenization map on coordinates: `Xᵢ ↦ 1` and `X_j ↦ Y_{j ≠ i}`. -/
noncomputable def dehomX : Fin (n + 1) → MvPolynomial (Fin n) A :=
  fun j => if h : j = i then 1 else MvPolynomial.X ((finSuccAboveEquiv i).symm ⟨j, h⟩)

/-- The dehomogenization ring map `A[x₀,…,xₙ] →+* A[Y₀,…,Y_{n-1}]` at the chart `i`. -/
noncomputable def dehom :
    MvPolynomial (Fin (n + 1)) A →+* MvPolynomial (Fin n) A :=
  MvPolynomial.eval₂Hom MvPolynomial.C (dehomX A n i)

@[simp]
theorem dehom_X_self : dehom A n i (MvPolynomial.X i) = 1 := by
  rw [dehom, MvPolynomial.eval₂Hom_X']
  simp [dehomX]

theorem dehomX_succAbove (k : Fin n) : dehomX A n i (i.succAbove k) = MvPolynomial.X k := by
  rw [dehomX, dite_eq_right (Fin.succAbove_ne i k)]
  congr 1
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext (by rw [finSuccAboveEquiv_apply])

theorem dehom_succAbove (k : Fin n) :
    dehom A n i (MvPolynomial.X (i.succAbove k)) = MvPolynomial.X k := by
  rw [dehom, MvPolynomial.eval₂Hom_X', dehomX_succAbove]

/-- The candidate isomorphism `A[Y₀,…,Y_{n-1}] →+* Away 𝒜 (X i)`. -/
noncomputable def Phi :
    MvPolynomial (Fin n) A →+*
      HomogeneousLocalization.Away (chartGrading A n) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom (AtoAway A n i) (e A n i)

theorem dehom_X_self_mul_one : dehom A n i (MvPolynomial.X i) * 1 = 1 := by
  rw [dehom_X_self, mul_one]

/-- The map `A(this) →+* A[Y₀,…,Y_{n-1}]` induced by dehomogenization, where
`A(this)` is the localization of the polynomial ring at `X i`. -/
noncomputable def dehomLift :
    Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A) →+*
      MvPolynomial (Fin n) A :=
  Localization.awayLift (dehom A n i) (MvPolynomial.X i)
    (isUnit_iff_exists_inv.mpr ⟨1, dehom_X_self_mul_one A n i⟩)

@[simp]
theorem dehomLift_algebraMap (a : MvPolynomial (Fin (n + 1)) A) :
    dehomLift A n i (algebraMap _ _ a) = dehom A n i a := by
  unfold dehomLift
  exact IsLocalization.Away.lift_eq (MvPolynomial.X i) _ a

/-- The candidate inverse `Away 𝒜 (X i) →+* A[Y₀,…,Y_{n-1}]`, induced by `dehom`. -/
noncomputable def Psi :
    HomogeneousLocalization.Away (chartGrading A n) (MvPolynomial.X i) →+*
      MvPolynomial (Fin n) A :=
  (dehomLift A n i).comp (algebraMap (HomogeneousLocalization.Away (chartGrading A n)
    (MvPolynomial.X i)) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A)))

end Work.DSG2
