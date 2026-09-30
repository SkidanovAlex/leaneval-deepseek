import Mathlib
import Submission.Work.BW.minkowski_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the proof of Minkowski's second theorem (`Work.BW.minkowski_second_l1`)

* `Work.BW.succMinBody L K j` : the `j`-th successive minimum of a lattice `L ⊆ ℝᵈ` with respect
  to a body `K ⊆ ℝᵈ` (the infimum of the positive `λ` such that `λ • K` contains `j` linearly
  independent lattice vectors).
* `Work.BW.stdVec i` : the `i`-th standard basis vector of `Fin d → ℝ`.
* `Work.BW.unitCube d` : the cube `[-1,1]^d`.
* `Work.BW.scaleFirst i t`, `Work.BW.scaleLast i t` : the linear maps multiplying the first `i`
  (resp. the last `d - i`) coordinates by `t`.
* `Work.BW.l1Body c` : the weighted `ℓ¹` body `{x | ∑ᵢ cᵢ |xᵢ| ≤ 1}`.
* `Work.BW.transZ z` : the linear map sending the standard basis vector `e j` to `z j`, and
  `Work.BW.latPull z Λ` the pullback of a lattice under it.
-/

namespace Work.BW

open MeasureTheory Matrix

open scoped Pointwise

/-- The `j`-th successive minimum of the lattice `L` with respect to the body `K`: the infimum
of the positive `λ` such that `λ • K` contains `j` linearly independent lattice vectors. -/
noncomputable def succMinBody {d : ℕ} (L : Submodule ℤ (Fin d → ℝ)) (K : Set (Fin d → ℝ))
    (j : ℕ) : ℝ :=
  sInf {lam : ℝ | 0 < lam ∧
    j ≤ Module.finrank ℝ (Submodule.span ℝ ((L : Set (Fin d → ℝ)) ∩ (lam • K)))}

/-- The `i`-th standard basis vector of `Fin d → ℝ`. -/
def stdVec {d : ℕ} (i : Fin d) : Fin d → ℝ := Pi.single i 1

/-- The cube `[-1,1]^d`. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, |x i| ≤ 1}

/-- The linear map multiplying the first `i` coordinates by `t`. -/
def scaleFirst {d : ℕ} (i : ℕ) (t : ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x := fun j => if (j : ℕ) < i then t * x j else x j
  map_add' x y := by
    ext j
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The linear map multiplying the last `d - i` coordinates by `t`. -/
def scaleLast {d : ℕ} (i : ℕ) (t : ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x := fun j => if (j : ℕ) < i then x j else t * x j
  map_add' x y := by
    ext j
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

@[simp] theorem scaleFirst_apply_lt {d : ℕ} (i : ℕ) (t : ℝ) (x : Fin d → ℝ) {j : Fin d}
    (h : (j : ℕ) < i) : scaleFirst i t x j = t * x j := by simp [scaleFirst, h]

@[simp] theorem scaleFirst_apply_not {d : ℕ} (i : ℕ) (t : ℝ) (x : Fin d → ℝ) {j : Fin d}
    (h : ¬ ((j : ℕ) < i)) : scaleFirst i t x j = x j := by simp [scaleFirst, h]

@[simp] theorem scaleLast_apply_lt {d : ℕ} (i : ℕ) (t : ℝ) (x : Fin d → ℝ) {j : Fin d}
    (h : (j : ℕ) < i) : scaleLast i t x j = x j := by simp [scaleLast, h]

@[simp] theorem scaleLast_apply_not {d : ℕ} (i : ℕ) (t : ℝ) (x : Fin d → ℝ) {j : Fin d}
    (h : ¬ ((j : ℕ) < i)) : scaleLast i t x j = t * x j := by simp [scaleLast, h]

/-- The Minkowski sum `A + B` of two sets (explicit form, no `Pointwise` scope needed). -/
def addSet {E : Type*} [Add E] (A B : Set E) : Set E := {z | ∃ a ∈ A, ∃ b ∈ B, z = a + b}

@[simp] theorem mem_addSet {E : Type*} [Add E] {A B : Set E} {z : E} :
    z ∈ addSet A B ↔ ∃ a ∈ A, ∃ b ∈ B, z = a + b := Iff.rfl

theorem addSet_eq {E : Type*} [Add E] (A B : Set E) : addSet A B = A + B := by
  ext z
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Set.add_mem_add ha hb
  · intro hz
    obtain ⟨a, ha, b, hb, h⟩ := Set.mem_add.mp hz
    exact ⟨a, ha, b, hb, h.symm⟩

/-- The scalar multiple `c • A` of a set (explicit form, no `Pointwise` scope needed). -/
def smulSet {E : Type*} [SMul ℝ E] (c : ℝ) (A : Set E) : Set E := {z | ∃ a ∈ A, z = c • a}

@[simp] theorem mem_smulSet {E : Type*} [SMul ℝ E] {c : ℝ} {A : Set E} {z : E} :
    z ∈ smulSet c A ↔ ∃ a ∈ A, z = c • a := Iff.rfl

theorem smulSet_eq {E : Type*} [SMul ℝ E] (c : ℝ) (A : Set E) : smulSet c A = c • A := by
  ext z
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha, rfl⟩
    exact Set.smul_mem_smul_set ha
  · intro hz
    obtain ⟨a, ha, h⟩ := Set.mem_smul_set.mp hz
    exact ⟨a, ha, h.symm⟩

/-- The weighted `ℓ¹` body `{x | ∑ᵢ cᵢ |xᵢ| ≤ 1}`. -/
def l1Body {n : ℕ} (c : Fin n → ℝ) : Set (Fin n → ℝ) := {x | ∑ i, c i * |x i| ≤ 1}

@[simp] theorem mem_l1Body {n : ℕ} (c : Fin n → ℝ) (x : Fin n → ℝ) :
    x ∈ l1Body c ↔ ∑ i, c i * |x i| ≤ 1 := Iff.rfl

/-- The linear map sending the standard basis vector `e j` to `z j` (namely `x ↦ ∑ⱼ xⱼ • z j`). -/
def transZ {d : ℕ} (z : Fin d → Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  Matrix.mulVecLin (Matrix.of fun i j => z j i)

@[simp] theorem transZ_apply {d : ℕ} (z : Fin d → Fin d → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    transZ z x i = ∑ j, x j * z j i := by
  simp [transZ, Matrix.mulVecLin, Matrix.mulVec, Matrix.of_apply, dotProduct, mul_comm]

theorem transZ_stdVec {d : ℕ} (z : Fin d → Fin d → ℝ) (j : Fin d) :
    transZ z (stdVec j) = z j := by
  ext i
  rw [transZ_apply]
  simp [stdVec, Pi.single_apply]

/-- The pullback of the lattice `Λ` under the change of variables `transZ z`. -/
noncomputable def latPull {d : ℕ} (z : Fin d → Fin d → ℝ) (Λ : Submodule ℤ (Fin d → ℝ)) :
    Submodule ℤ (Fin d → ℝ) :=
  ZLattice.comap ℝ Λ (transZ z)

@[simp] theorem mem_latPull {d : ℕ} (z : Fin d → Fin d → ℝ) (Λ : Submodule ℤ (Fin d → ℝ))
    (x : Fin d → ℝ) : x ∈ latPull z Λ ↔ transZ z x ∈ Λ := by
  simp [latPull, ZLattice.comap]

end Work.BW
