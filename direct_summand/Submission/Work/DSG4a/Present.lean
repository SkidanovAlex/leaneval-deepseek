import Mathlib
import Submission.Work.DSG4a.Split

/-!
# DSG4a: presented modules `A^m ⧸ im D`, their duals and their trace ideals

This file sets up the concrete linear-algebra layer of subproject **DSG4a**.  The
local-to-global argument for the derived direct summand theorem runs on a *finitely
presented* module coming from a finite free model of `RΓ(X, 𝒪)`; concretely such a module
is a quotient `A^m ⧸ im D` of a finite free module by the image of a matrix `D`, and its
element is the class of a vector `e : Fin m → A`.  We record:

* `matMap D`  : the map `A^n → A^m` with matrix `D`;
* `transMap D`: its transpose `A^m → A^n`;
* `solSet D`  : the solution space of the transposed linear system, i.e. `ker (transMap D)`.
  It is the space of vectors `w` such that `x ↦ ⟪w, x⟫` is a well-defined functional on
  `A^m ⧸ im D`;
* `present D` : the module `A^m ⧸ im D`;
* `dot`       : the standard pairing `∑ i, x i * y i`.

The main statements are in the companion files: `mem_splitIdeal_presentMk`
(`Submission.Work.DSG4a.mem_splitIdeal_presentMk`) identifies the splitting ideal of the
class of `e` with the set `{⟪w, e⟫ | w ∈ solSet D}`, and
`solSet_span_eq_baseChange` (`Submission.Work.DSG4a.solSet_span_eq_baseChange`) is the flat
base change theorem for `solSet`.
-/

namespace Work.DSG4a

open TensorProduct

universe u w

section Present

variable {A : Type u} [CommRing A]

/-- The standard pairing on `A^m`: `⟪x, y⟫ = ∑ i, x i * y i`. -/
def dot {m : ℕ} (x y : Fin m → A) : A := ∑ i, x i * y i

@[simp]
lemma dot_apply {m : ℕ} (x y : Fin m → A) : dot x y = ∑ i, x i * y i := rfl

lemma dot_comm {m : ℕ} (x y : Fin m → A) : dot x y = dot y x := by
  simp only [dot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dot_add {m : ℕ} (x y z : Fin m → A) : dot x (y + z) = dot x y + dot x z := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_smul {m : ℕ} (a : A) (x y : Fin m → A) : dot x (a • y) = a * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dot_add_left {m : ℕ} (x y z : Fin m → A) : dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_smul_left {m : ℕ} (a : A) (x y : Fin m → A) : dot (a • x) y = a * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] lemma dot_zero_left {m : ℕ} (y : Fin m → A) : dot (0 : Fin m → A) y = 0 := by
  simp [dot]

@[simp] lemma dot_zero_right {m : ℕ} (x : Fin m → A) : dot x (0 : Fin m → A) = 0 := by
  simp [dot]

/-- The pairing is compatible with the coefficient extension `A → A'`. -/
lemma dot_algebraMap {m : ℕ} {A' : Type*} [CommRing A'] [Algebra A A'] (w x : Fin m → A) :
    dot (fun i => algebraMap A A' (w i)) (fun i => algebraMap A A' (x i)) =
      algebraMap A A' (dot w x) := by
  simp only [dot, map_sum, map_mul]

/-- The linear map `A^n → A^m` with matrix `D`. -/
def matMap {m n : ℕ} (D : Fin m → Fin n → A) : (Fin n → A) →ₗ[A] (Fin m → A) where
  toFun x := fun i => ∑ j, D i j * x j
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun j _ => by ring

@[simp]
lemma matMap_apply {m n : ℕ} (D : Fin m → Fin n → A) (x : Fin n → A) (i : Fin m) :
    matMap D x i = ∑ j, D i j * x j := rfl

/-- The transposed linear map `A^m → A^n`: `w ↦ (j ↦ ∑ i, D i j * w i)`. -/
def transMap {m n : ℕ} (D : Fin m → Fin n → A) : (Fin m → A) →ₗ[A] (Fin n → A) where
  toFun w := fun j => ∑ i, D i j * w i
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp]
lemma transMap_apply {m n : ℕ} (D : Fin m → Fin n → A) (w : Fin m → A) (j : Fin n) :
    transMap D w j = ∑ i, D i j * w i := rfl

/-- The solution space of the transposed linear system: the vectors `w` such that
`x ↦ ⟪w, x⟫` descends to the quotient `A^m ⧸ im D`. -/
def solSet {m n : ℕ} (D : Fin m → Fin n → A) : Submodule A (Fin m → A) :=
  LinearMap.ker (transMap D)

lemma mem_solSet {m n : ℕ} {D : Fin m → Fin n → A} {w : Fin m → A} :
    w ∈ solSet D ↔ ∀ j, ∑ i, D i j * w i = 0 := by
  simp [solSet, LinearMap.mem_ker, funext_iff]

/-- `present D` is the finitely presented module `A^m ⧸ im D`. -/
abbrev present {m n : ℕ} (D : Fin m → Fin n → A) : Type u :=
  (Fin m → A) ⧸ LinearMap.range (matMap D)

/-- The class of a vector in `present D`. -/
abbrev presentMk {m n : ℕ} (D : Fin m → Fin n → A) : (Fin m → A) →ₗ[A] present D :=
  Submodule.mkQ (LinearMap.range (matMap D))

/-- **Adjointness of `matMap` and `transMap`**: the pairing identifies the transpose with
the dual of the matrix map.  This is what makes `⟪w, -⟫` a functional on `present D` for
`w ∈ solSet D`. -/
lemma dot_transMap_matMap {m n : ℕ} (D : Fin m → Fin n → A) (w : Fin m → A) (z : Fin n → A) :
    dot (transMap D w) z = dot w (matMap D z) := by
  simp only [dot, matMap_apply, transMap_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-! ### The dual of a finite free module -/

/-- The vector of coordinates of a linear functional on `A^m` (the dual of `A^m` is `A^m`,
via the standard basis). -/
def coord {m : ℕ} (s : (Fin m → A) →ₗ[A] A) : Fin m → A := fun i => s (Pi.single i 1)

/-- The linear functional attached to a vector of coordinates. -/
def ofCoord {m : ℕ} (w : Fin m → A) : (Fin m → A) →ₗ[A] A :=
  ∑ i, w i • LinearMap.proj i

@[simp]
lemma ofCoord_apply {m : ℕ} (w x : Fin m → A) : ofCoord w x = dot w x := by
  simp only [ofCoord, dot, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]

lemma coord_ofCoord {m : ℕ} (w : Fin m → A) : coord (ofCoord w) = w := by
  funext j
  simp only [coord, ofCoord_apply, dot]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb, Ne.symm hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The basis expansion `x = ∑ i, x i • Pi.single i 1`. -/
lemma sum_single_smul {m : ℕ} (x : Fin m → A) : ∑ i, x i • Pi.single i (1 : A) = x := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb, Ne.symm hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- A linear functional on `A^m` is the pairing with its coordinate vector. -/
lemma apply_eq_dot_coord {m : ℕ} (s : (Fin m → A) →ₗ[A] A) (x : Fin m → A) :
    s x = dot (coord s) x := by
  conv_lhs => rw [← sum_single_smul x]
  rw [map_sum]
  simp only [map_smul, coord, smul_eq_mul, dot]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ofCoord_coord {m : ℕ} (s : (Fin m → A) →ₗ[A] A) : ofCoord (coord s) = s :=
  LinearMap.ext fun x => by rw [ofCoord_apply, ← apply_eq_dot_coord]

end Present

end Work.DSG4a
