import Mathlib
import Submission.Commons.Analysis.Fourier.gaussian_psf_matrix

namespace Commons.Lattice.PoissonSummation

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open scoped RealInnerProductSpace InnerProductSpace


abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## Integer-valued reals -/

/-- A real number is an integer (seen through the cast). -/
def IntZ (x : ℝ) : Prop := ∃ z : ℤ, (z : ℝ) = x

lemma IntZ_add {x y : ℝ} (hx : IntZ x) (hy : IntZ y) : IntZ (x + y) := by
  rcases hx with ⟨zx, hzx⟩
  rcases hy with ⟨zy, hzy⟩
  refine ⟨zx + zy, ?_⟩
  rw [← hzx, ← hzy, Int.cast_add]

lemma IntZ_mul_int {x : ℝ} (hx : IntZ x) (z : ℤ) : IntZ (((z : ℤ) : ℝ) * x) := by
  rcases hx with ⟨zx, hzx⟩
  refine ⟨z * zx, ?_⟩
  rw [← hzx, Int.cast_mul]

lemma IntZ_zero : IntZ (0 : ℝ) := ⟨0, by norm_num⟩

lemma IntZ_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, IntZ (f i)) : IntZ (∑ i, f i) := by
  classical
  refine ⟨∑ i, (hf i).choose, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (hf i).choose_spec

/-! ## Coordinates of lattice vectors -/

/-- Coordinate of the lattice vector with coefficients `k`. -/
lemma coord_latticeComb {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (k : Fin n → ℤ) (i : Fin n) :
    (((b.equivFun.symm k : ℒ) : Eu n) i) = (A.mulVec (fun j : Fin n => ((k j : ℤ) : ℝ))) i := by
  calc
    (((b.equivFun.symm k : ℒ) : Eu n) i) = ∑ j : Fin n, (((k j : ℤ) : ℝ)) * A i j := by
      simp [hAcoords]
    _ = (A.mulVec (fun j : Fin n => ((k j : ℤ) : ℝ))) i := by
      rw [Matrix.mulVec_apply]
      simp [Matrix.row_apply, dotProduct, mul_comm]

/-- Squared norm of the lattice vector with coefficients `k`. -/
lemma normSq_latticeComb {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (k : Fin n → ℤ) :
    ‖(((b.equivFun.symm k : ℒ) : Eu n))‖ ^ 2 =
      ∑ i : Fin n, ((A.mulVec (fun j : Fin n => ((k j : ℤ) : ℝ))) i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coord_latticeComb ℒ b A hAcoords k i]

/-- Inner product of a vector with a lattice basis vector, in coordinates. -/
lemma inner_basis_coord {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (w : Eu n) (j : Fin n) :
    inner ℝ w ((b j : ℒ) : Eu n) = ∑ i : Fin n, w i * A i j := by
  simp [inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hAcoords i j]
  ring

/-! ## Sum reindexing between the lattice and `ℤⁿ` -/

/-- The canonical bijection between `ℒ` and `Fin n → ℤ` given by the basis. -/
lemma tsum_lattice_reindex {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (f : ℒ → ℝ) :
    (∑' k : Fin n → ℤ, f (b.equivFun.symm k)) = ∑' y : ℒ, f y := by
  exact Equiv.tsum_eq (b.equivFun.symm.toEquiv) f

/-! ## The dual lattice -/

/-- The `j`-th dual vector: its coordinates are the `j`-th row of the inverse matrix. -/
def dualVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : Eu n :=
  WithLp.toLp 2 (fun i : Fin n => M j i)

/-- The dual vectors are biorthogonal to the lattice basis. -/
lemma inner_dualVec_basis {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hMA : M * A = 1)
    (j i : Fin n) :
    inner ℝ (dualVec M j) ((b i : ℒ) : Eu n) = if j = i then 1 else 0 := by
  simp [dualVec, inner, hAcoords]
  calc
    (∑ r : Fin n, A r i * M j r) = (M * A) j i := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = if j = i then 1 else 0 := by
      rw [hMA, Matrix.one_apply]

/-- Basis expansion of a lattice vector, in the ambient space. -/
lemma coerce_basis_expand {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ) (y : ℒ) :
    (y : Eu n) = ∑ j : Fin n, (b.repr y j : ℤ) • ((b j : ℒ) : Eu n) := by
  have hco : ((∑ j : Fin n, (b.repr y j : ℤ) • b j : ℒ) : Eu n) = (y : Eu n) := by
    exact congrArg (fun v : ℒ => (v : Eu n)) (b.sum_repr y)
  rw [← hco]
  change (Submodule.subtype ℒ) (∑ j : Fin n, (b.repr y j : ℤ) • b j)
      = ∑ j : Fin n, (b.repr y j : ℤ) • ((b j : ℒ) : Eu n)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (Submodule.subtype ℒ) ((b.repr y j : ℤ) • b j) = (b.repr y j : ℤ) • ((b j : ℒ) : Eu n)
  rw [map_smul]
  rfl

/-- Inner product against a lattice vector expands along the basis. -/
lemma inner_basis_expand {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (w : Eu n) (y : ℒ) :
    inner ℝ w (y : Eu n)
      = ∑ j : Fin n, (((b.repr y j : ℤ) : ℝ)) * inner ℝ w ((b j : ℒ) : Eu n) := by
  rw [coerce_basis_expand ℒ b y]
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Int.cast_smul_eq_zsmul ℝ (b.repr y j) ((b j : ℒ) : Eu n)]
  rw [inner_smul_right]

/-- Membership in the dual reduces to inner products against basis vectors. -/
lemma IntZ_inner_of_basis_ints {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    {w : Eu n}
    (hw : ∀ j : Fin n, IntZ (inner ℝ w ((b j : ℒ) : Eu n))) :
    ∀ y : ℒ, IntZ (inner ℝ w (y : Eu n)) := by
  intro y
  have hsum := inner_basis_expand ℒ b w y
  rw [hsum]
  apply IntZ_sum
  intro j
  exact IntZ_mul_int (hw j) (b.repr y j)

/-- The dual vectors satisfy the dual membership condition. -/
lemma dualVec_IntZ_inner {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hMA : M * A = 1)
    (j : Fin n) :
    ∀ y : ℒ, IntZ (inner ℝ (dualVec M j) (y : Eu n)) := by
  apply IntZ_inner_of_basis_ints ℒ b
  intro i
  rw [inner_dualVec_basis ℒ b A M hAcoords hMA j i]
  by_cases h : j = i
  · subst h
    exact ⟨1, by norm_num⟩
  · rw [if_neg h]
    exact ⟨0, by norm_num⟩

/-- Every vector is the real combination of dual vectors with coefficients given by inner
products against the lattice basis. -/
lemma vec_eq_dualComb {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hAM : A * M = 1)
    (w : Eu n) :
    w = ∑ j : Fin n, (inner ℝ w ((b j : ℒ) : Eu n)) • dualVec M j := by
  apply PiLp.ext
  intro r
  calc
    w r = ∑ i : Fin n, w i * (if i = r then (1 : ℝ) else 0) := by
      simp
    _ = ∑ i : Fin n, w i * (A * M) i r := by
      simp [hAM, Matrix.one_apply]
    _ = ∑ i : Fin n, w i * (∑ j : Fin n, A i j * M j r) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Matrix.mul_apply]
    _ = ∑ i : Fin n, ∑ j : Fin n, (w i * A i j) * M j r := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        w i * (∑ j : Fin n, A i j * M j r) = ∑ j : Fin n, w i * (A i j * M j r) := by
          exact (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun j => A i j * M j r) (a := w i))
        _ = ∑ j : Fin n, (w i * A i j) * M j r := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ j : Fin n, ∑ i : Fin n, (w i * A i j) * M j r := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin n, (∑ i : Fin n, w i * A i j) * M j r := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (Finset.sum_mul (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => w i * A i j) (a := M j r)).symm
    _ = ∑ j : Fin n, (inner ℝ w ((b j : ℒ) : Eu n)) * (dualVec M j) r := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [inner_basis_coord ℒ b A hAcoords w j]
      simp [dualVec]
    _ = (∑ j : Fin n, (inner ℝ w ((b j : ℒ) : Eu n)) • dualVec M j) r := by
      simp

/-! The key equality `Ld = span ℤ (dualVec M)` as submodules of the ambient space. -/

lemma Ld_eq_span_dualVec {n : ℕ} (ℒ Ld : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hAM : A * M = 1) (hMA : M * A = 1)
    (hLd : ∀ w : Eu n, w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = inner ℝ w (y : Eu n)) :
    Ld = Submodule.span ℤ (Set.range (dualVec (n := n) M)) := by
  apply le_antisymm
  · -- Ld ≤ span
    intro w hw
    have hwd : ∀ y : ℒ, IntZ (inner ℝ w (y : Eu n)) := by
      intro y
      exact (hLd w).mp hw y
    let z : Fin n → ℤ := fun j => (hwd (b j)).choose
    have hz : ∀ j : Fin n, ((z j : ℤ) : ℝ) = inner ℝ w ((b j : ℒ) : Eu n) := by
      intro j
      exact (hwd (b j)).choose_spec
    have hrepr : w = ∑ j : Fin n, (z j : ℤ) • dualVec M j := by
      calc
        w = ∑ j : Fin n, (inner ℝ w ((b j : ℒ) : Eu n)) • dualVec M j :=
          vec_eq_dualComb ℒ b A M hAcoords hAM w
        _ = ∑ j : Fin n, (((z j : ℤ) : ℝ)) • dualVec M j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hz j]
        _ = ∑ j : Fin n, (z j : ℤ) • dualVec M j := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Int.cast_smul_eq_zsmul ℝ (z j) (dualVec M j)
    show w ∈ Submodule.span ℤ (Set.range (dualVec (n := n) M))
    rw [hrepr]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨j, rfl⟩
  · -- span ≤ Ld
    rw [Submodule.span_le]
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact (hLd (dualVec M j)).mpr (dualVec_IntZ_inner ℒ b A M hAcoords hMA j)

/-! ## The dual basis parametrization of `Ld` -/

/-- Inner product with a `ℤ`-scaled vector on the left. -/
lemma inner_zsmul_left {n : ℕ} (v w : Eu n) (z : ℤ) :
    inner ℝ (z • v) w = (((z : ℤ) : ℝ)) * inner ℝ v w := by
  rw [← Int.cast_smul_eq_zsmul ℝ z v]
  rw [inner_smul_left]
  simp

/-- The dual vectors are in `Ld` under the membership hypothesis. -/
lemma dualVec_mem {n : ℕ} (ℒ Ld : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hMA : M * A = 1)
    (hLd : ∀ w : Eu n, w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = inner ℝ w (y : Eu n))
    (j : Fin n) :
    dualVec M j ∈ Ld := by
  exact (hLd (dualVec M j)).mpr (dualVec_IntZ_inner ℒ b A M hAcoords hMA j)

/-- Coefficients of an element of `Ld` (the inner products against basis vectors). -/
noncomputable def LdCoeff {n : ℕ} (ℒ Ld : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (hLd : ∀ w : Eu n, w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = inner ℝ w (y : Eu n))
    (w : Ld) : Fin n → ℤ :=
  fun j => Exists.choose ((hLd (w : Eu n)).mp w.2 (b j))

/-- The coefficients of `w` reproduce `w` via the dual vectors. -/
lemma LdCoeff_spec {n : ℕ} (ℒ Ld : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hAM : A * M = 1)
    (hLd : ∀ w : Eu n, w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = inner ℝ w (y : Eu n))
    (w : Ld) (j : Fin n) :
    (((LdCoeff ℒ Ld b hLd w j : ℤ) : ℝ)) = inner ℝ (w : Eu n) ((b j : ℒ) : Eu n) := by
  exact Exists.choose_spec ((hLd (w : Eu n)).mp w.2 (b j))

/-- The ambient combination over the dual vectors, and its inner products with the basis. -/
lemma inner_dualComb_basis {n : ℕ} (ℒ : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hMA : M * A = 1)
    (m : Fin n → ℤ) (i : Fin n) :
    inner ℝ (∑ j : Fin n, (m j : ℤ) • dualVec M j) ((b i : ℒ) : Eu n) = (((m i : ℤ) : ℝ)) := by
  calc
    inner ℝ (∑ j : Fin n, (m j : ℤ) • dualVec M j) ((b i : ℒ) : Eu n)
        = ∑ j : Fin n, inner ℝ ((m j : ℤ) • dualVec M j) ((b i : ℒ) : Eu n) := by
          simpa using (sum_inner (s := (Finset.univ : Finset (Fin n)))
            (f := fun j => (m j : ℤ) • dualVec M j) (x := ((b i : ℒ) : Eu n)))
    _ = ∑ j : Fin n, (((m j : ℤ) : ℝ)) * inner ℝ (dualVec M j) ((b i : ℒ) : Eu n) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact inner_zsmul_left (dualVec M j) ((b i : ℒ) : Eu n) (m j)
    _ = ∑ j : Fin n, (((m j : ℤ) : ℝ)) * (if j = i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [inner_dualVec_basis ℒ b A M hAcoords hMA j i]
    _ = (((m i : ℤ) : ℝ)) := by
      classical
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        rw [if_neg hji]
        simp
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))

/-- Coordinates of an ambient dual combination. -/
lemma coord_dualCombE {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (m : Fin n → ℤ) (r : Fin n) :
    (∑ j : Fin n, (m j : ℤ) • dualVec M j) r =
      ((M.transpose).mulVec (fun j : Fin n => ((m j : ℤ) : ℝ))) r := by
  calc
    (∑ j : Fin n, (m j : ℤ) • dualVec M j) r = ∑ j : Fin n, (((m j : ℤ) : ℝ)) * M j r := by
      simp [dualVec]
    _ = ((M.transpose).mulVec (fun j : Fin n => ((m j : ℤ) : ℝ))) r := by
      rw [Matrix.mulVec_apply]
      simp [Matrix.row_apply, dotProduct, mul_comm]

/-- Squared norm of an ambient dual combination. -/
lemma normSq_dualCombE {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (m : Fin n → ℤ) :
    ‖(∑ j : Fin n, (m j : ℤ) • dualVec M j)‖ ^ 2 =
      ∑ i : Fin n, (((M.transpose).mulVec (fun j : Fin n => ((m j : ℤ) : ℝ))) i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coord_dualCombE M m i]

/-- The ambient `ℤ`-linear combination over the dual vectors belongs to `Ld`. -/
lemma dualComb_mem {n : ℕ} (ℒ Ld : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hMA : M * A = 1)
    (hLd : ∀ w : Eu n, w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = inner ℝ w (y : Eu n))
    (m : Fin n → ℤ) :
    (∑ j : Fin n, (m j : ℤ) • dualVec M j) ∈ Ld := by
  exact (hLd (∑ j : Fin n, (m j : ℤ) • dualVec M j)).mpr (by
    intro y
    apply IntZ_inner_of_basis_ints ℒ b
    intro i
    rw [inner_dualComb_basis ℒ b A M hAcoords hMA m i]
    exact ⟨m i, rfl⟩)

/-- Any element of `Ld` is an ambient `ℤ`-combination of the dual vectors with its coefficients. -/
lemma LdCoeff_dualComb {n : ℕ} (ℒ Ld : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hAM : A * M = 1)
    (hLd : ∀ w : Eu n, w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = inner ℝ w (y : Eu n))
    (w : Ld) :
    (w : Eu n) = ∑ j : Fin n, (LdCoeff ℒ Ld b hLd w j : ℤ) • dualVec M j := by
  have hrepr0 : (w : Eu n) = ∑ j : Fin n, (inner ℝ (w : Eu n) ((b j : ℒ) : Eu n)) • dualVec M j :=
    vec_eq_dualComb ℒ b A M hAcoords hAM (w : Eu n)
  calc
    (w : Eu n) = ∑ j : Fin n, (inner ℝ (w : Eu n) ((b j : ℒ) : Eu n)) • dualVec M j := hrepr0
    _ = ∑ j : Fin n, (LdCoeff ℒ Ld b hLd w j : ℤ) • dualVec M j := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (inner ℝ (w : Eu n) ((b j : ℒ) : Eu n)) • dualVec M j
            = ((((LdCoeff ℒ Ld b hLd w j : ℤ) : ℝ))) • dualVec M j := by
              rw [LdCoeff_spec ℒ Ld b A M hAcoords hAM hLd w j]
        _ = (LdCoeff ℒ Ld b hLd w j : ℤ) • dualVec M j := by
          exact Int.cast_smul_eq_zsmul ℝ (LdCoeff ℒ Ld b hLd w j) (dualVec M j)

noncomputable def dualFamily {n : ℕ} (ℒ Ld : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hMA : M * A = 1)
    (hLd : ∀ w : Eu n, w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = inner ℝ w (y : Eu n)) :
    Fin n → Ld :=
  fun j => ⟨dualVec M j, dualVec_mem ℒ Ld b A M hAcoords hMA hLd j⟩

/-- The map from `Fin n → ℤ` to `Ld` by the dual family. -/
noncomputable def dualMap {n : ℕ} (ℒ Ld : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hMA : M * A = 1)
    (hLd : ∀ w : Eu n, w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = inner ℝ w (y : Eu n)) :
    (Fin n → ℤ) → Ld :=
  fun m => ∑ j : Fin n, (m j : ℤ) • dualFamily ℒ Ld b A M hAcoords hMA hLd j

/-- The ambient vector underlying `dualMap`. -/
lemma dualMap_val {n : ℕ} (ℒ Ld : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hMA : M * A = 1)
    (hLd : ∀ w : Eu n, w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = inner ℝ w (y : Eu n))
    (m : Fin n → ℤ) :
    (((dualMap ℒ Ld b A M hAcoords hMA hLd m : Ld) : Eu n))
      = ∑ j : Fin n, (m j : ℤ) • dualVec M j := by
  change (Submodule.subtype Ld) (dualMap ℒ Ld b A M hAcoords hMA hLd m)
      = ∑ j : Fin n, (m j : ℤ) • dualVec M j
  unfold dualMap dualFamily
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (Submodule.subtype Ld) ((m j : ℤ) • ⟨dualVec M j, dualVec_mem ℒ Ld b A M hAcoords hMA hLd j⟩)
      = (m j : ℤ) • dualVec M j
  rw [map_smul]
  rfl

/-- The equivalence between `Fin n → ℤ` and the dual lattice `Ld`, with
`toFun` the map through the dual vectors. -/
noncomputable def dualLatticeEquiv {n : ℕ} (ℒ Ld : Submodule ℤ (Eu n)) (b : Basis (Fin n) ℤ ℒ)
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : Eu n) i) = A i j)
    (hAM : A * M = 1) (hMA : M * A = 1)
    (hLd : ∀ w : Eu n, w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = inner ℝ w (y : Eu n)) :
    (Fin n → ℤ) ≃ Ld where
  toFun := dualMap ℒ Ld b A M hAcoords hMA hLd
  invFun := fun w => LdCoeff ℒ Ld b hLd w
  left_inv := by
    intro m
    funext j
    have hc : (((LdCoeff ℒ Ld b hLd (dualMap ℒ Ld b A M hAcoords hMA hLd m) j : ℤ) : ℝ))
        = ((m j : ℤ) : ℝ) := by
      calc
        (((LdCoeff ℒ Ld b hLd (dualMap ℒ Ld b A M hAcoords hMA hLd m) j : ℤ) : ℝ))
            = inner ℝ ((dualMap ℒ Ld b A M hAcoords hMA hLd m : Ld) : Eu n) ((b j : ℒ) : Eu n) := by
              exact LdCoeff_spec ℒ Ld b A M hAcoords hAM hLd
                (dualMap ℒ Ld b A M hAcoords hMA hLd m) j
        _ = inner ℝ (∑ r : Fin n, (m r : ℤ) • dualVec M r) ((b j : ℒ) : Eu n) := by
          congr 1
          exact dualMap_val ℒ Ld b A M hAcoords hMA hLd m
        _ = ((m j : ℤ) : ℝ) := inner_dualComb_basis ℒ b A M hAcoords hMA m j
    exact Int.cast_inj.mp hc
  right_inv := by
    intro w
    apply Subtype.ext
    calc
      (((dualMap ℒ Ld b A M hAcoords hMA hLd (fun j => LdCoeff ℒ Ld b hLd w j) : Ld) : Eu n))
          = ∑ j : Fin n, ((LdCoeff ℒ Ld b hLd w j : ℤ)) • dualVec M j :=
            dualMap_val ℒ Ld b A M hAcoords hMA hLd (fun j => LdCoeff ℒ Ld b hLd w j)
      _ = (w : Eu n) := (LdCoeff_dualComb ℒ Ld b A M hAcoords hAM hLd w).symm
/-- **Poisson summation for a full-rank lattice in `EuclideanSpace ℝ (Fin n)`.**

Let `ℒ ≤ E = EuclideanSpace ℝ (Fin n)` be a full-rank `ℤ`-lattice (`[DiscreteTopology ℒ]`,
`[IsZLattice ℝ ℒ]`), and let `b : Basis (Fin n) ℤ ℒ` be a `ℤ`-basis whose vectors have
canonical coordinate matrix `A` (hypothesis `hAcoords`: the `i`-th coordinate of the `j`-th
basis vector is `A i j`), with `A.det ≠ 0`.  Let `Ld` be the dual lattice: the `ℤ`-submodule
`{w | ∀ y ∈ ℒ, inner w y ∈ ℤ}` (hypothesis `hLd` states exactly this membership).  Then for
every `s > 0`,

    (∑' y : ℒ, exp(-π·‖(y : E)‖²/s²)) · |det A| = sⁿ · (∑' w : Ld, exp(-π·s²·‖(w : E)‖²)).

This is the Gaussian Poisson summation formula for lattices.  Suggested proof route:
(1) via the basis `b`, identify the lattice sum with the ℤⁿ-sum
    `∑' k : Fin n → ℤ, exp(-π·(∑ i, ((A.mulVec (fun j => (k j : ℝ))) i) ^ 2) / s ^ 2)`
    (each `y = ∑ j (k j : ℤ) • (b j)` has canonical coordinates `A.mulVec ...`; the norm on
    `E` satisfies `‖x‖² = ∑ i, (x i)²`, cf. `PiLp.norm_sq_eq_of_L2`);
(2) apply `Commons.Analysis.Fourier.gaussian_psf_matrix n A hA s hs`;
(3) the right-hand sum over `m : Fin n → ℤ` of
    `exp(-π·s²·(∑ i, (((A⁻¹)ᵀ · m) i)²))` equals the sum over the dual lattice `Ld`,
    because the dual basis of the real basis `(b j : E)` has coordinate matrix `(A⁻¹)ᵀ`
    (columns are the vectors `w_j` with `⟪w_j, (b i : E)⟫ = δ_ij`; use that
    `(b.ofZLatticeBasis ℝ)` is the real basis and its `LinearMap.BilinForm.dualBasis` spans
    the dual lattice, or prove directly: for `w = ∑ m_j w_j` with `w_j`-columns `(A⁻¹)ᵀ`,
    `w ∈ Ld` iff `∀ i, inner w (b i) ∈ ℤ` iff each `m_i ∈ ℤ`).
-/
theorem lattice_psf {n : ℕ} (ℒ Ld : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology ℒ] [IsZLattice ℝ ℒ] [DiscreteTopology Ld]
    (hLd : ∀ w : EuclideanSpace ℝ (Fin n), w ∈ Ld ↔
      ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = ⟪w, (y : EuclideanSpace ℝ (Fin n))⟫_ℝ)
    (b : Basis (Fin n) ℤ ℒ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : EuclideanSpace ℝ (Fin n)) i) = A i j)
    (s : ℝ) (hs : 0 < s) :
    (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2)) * |A.det| =
      s ^ n * (∑' w : Ld, Real.exp (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
  let M : Matrix (Fin n) (Fin n) ℝ := A⁻¹
  have hAM : A * M = 1 := by
    dsimp [M]
    exact Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)
  have hMA : M * A = 1 := by
    dsimp [M]
    exact Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)
  let G : ℒ → ℝ := fun y => Real.exp (-Real.pi * ‖(y : Eu n)‖ ^ 2 / s ^ 2)
  let H : (Fin n → ℤ) → ℝ := fun k =>
    Real.exp (-Real.pi * (∑ i : Fin n, ((A.mulVec (fun j : Fin n => ((k j : ℤ) : ℝ))) i) ^ 2) / s ^ 2)
  let P : (Fin n → ℤ) → ℝ := fun m =>
    Real.exp (-Real.pi * s ^ 2 *
      (∑ i : Fin n, ((((A⁻¹).transpose).mulVec (fun j : Fin n => ((m j : ℤ) : ℝ))) i) ^ 2))
  let Q : Ld → ℝ := fun w => Real.exp (-Real.pi * s ^ 2 * ‖(w : Eu n)‖ ^ 2)
  have hstep1 : (∑' y : ℒ, G y) = ∑' k : Fin n → ℤ, H k := by
    calc
      (∑' y : ℒ, G y) = ∑' k : Fin n → ℤ, G (b.equivFun.symm k) := by
        exact (tsum_lattice_reindex ℒ b G).symm
      _ = ∑' k : Fin n → ℤ, H k := by
        apply tsum_congr
        intro k
        dsimp [G, H]
        congr 1
        rw [normSq_latticeComb ℒ b A hAcoords k]
  have hpsf := Commons.Analysis.Fourier.gaussian_psf_matrix n A hA s hs
  have hstep2 : (∑' k : Fin n → ℤ, H k) = (s ^ n / |A.det|) * (∑' m : Fin n → ℤ, P m) := by
    simpa [H, P] using hpsf
  have htermD : ∀ m : Fin n → ℤ, P m = Q ((dualLatticeEquiv ℒ Ld b A M hAcoords hAM hMA hLd) m) := by
    intro m
    dsimp [P, Q]
    congr 1
    have hv : (((dualLatticeEquiv ℒ Ld b A M hAcoords hAM hMA hLd m : Ld) : Eu n))
        = ∑ j : Fin n, (m j : ℤ) • dualVec M j := by
      exact dualMap_val ℒ Ld b A M hAcoords hMA hLd m
    rw [hv]
    rw [normSq_dualCombE M m]
  have hdual : (∑' m : Fin n → ℤ, P m) = ∑' w : Ld, Q w := by
    calc
      (∑' m : Fin n → ℤ, P m) = ∑' m : Fin n → ℤ, Q ((dualLatticeEquiv ℒ Ld b A M hAcoords hAM hMA hLd) m) := by
        apply tsum_congr
        intro m
        exact htermD m
      _ = ∑' w : Ld, Q w := by
        exact Equiv.tsum_eq (dualLatticeEquiv ℒ Ld b A M hAcoords hAM hMA hLd) Q
  have hM1 : (∑' y : ℒ, G y) = (s ^ n / |A.det|) * (∑' w : Ld, Q w) := by
    calc
      (∑' y : ℒ, G y) = ∑' k : Fin n → ℤ, H k := hstep1
      _ = (s ^ n / |A.det|) * (∑' m : Fin n → ℤ, P m) := hstep2
      _ = (s ^ n / |A.det|) * (∑' w : Ld, Q w) := by rw [hdual]
  have hAd : |A.det| ≠ 0 := abs_ne_zero.mpr hA
  calc
    (∑' y : ℒ, G y) * |A.det| = ((s ^ n / |A.det|) * (∑' w : Ld, Q w)) * |A.det| := by
      rw [hM1]
    _ = s ^ n * (∑' w : Ld, Q w) := by
      field_simp [hAd]

end
end Commons.Lattice.PoissonSummation
