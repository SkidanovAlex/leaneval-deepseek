import Mathlib
import Submission.Work.LT.Defs

/-!
# Definitions for `Work.LT.good_base_code`

Supporting notions for the proof of `Work.LT.good_base_code` (Kalachev--Panteleev,
*Two-sided robustly testable codes*, Theorem 1 with `q = 2`, plus their Lemma 1).

All matrices live in `Fin D × Fin D → ZMod 2`.  We use

* `colCode CA`   : matrices all of whose columns lie in `CA` (i.e. `CA ⊗ 𝔽₂^D`),
* `rowCode CB`   : matrices all of whose rows lie in `CB` (i.e. `𝔽₂^D ⊗ CB`),
* `prodSum CA CB`: their sum (`CA ⊞ CB`),
* `ProductExpanding κ CA CB` : every `x ∈ CA ⊞ CB` splits as `a + b` with `a` column-wise in `CA`,
  `b` row-wise in `CB` and `κ * D * (#nonzero columns of a + #nonzero rows of b) ≤ |x|`.
-/

namespace Work.LT

namespace GB

open GoodLTC

/-! ## Matrices, rows, columns, rank, weight -/

/-- The `j`-th column of a matrix, as a vector. -/
def col {D : ℕ} (x : Fin D × Fin D → ZMod 2) (j : Fin D) : Fin D → ZMod 2 := fun i => x (i, j)

/-- The `i`-th row of a matrix, as a vector. -/
def row {D : ℕ} (x : Fin D × Fin D → ZMod 2) (i : Fin D) : Fin D → ZMod 2 := fun j => x (i, j)

/-- The Hamming weight of a matrix (number of non-zero entries). -/
def wt {D : ℕ} (x : Fin D × Fin D → ZMod 2) : ℕ := hammingNorm x

/-- Dimension of a submodule of a `𝔽₂`-vector space, as a plain natural number.

This abbreviation exists because `Module.finrank (ZMod 2) (C ⊓ V)` mis-elaborates
(Lean tries to read `C ⊓ V` as a `Type`); `frk (C ⊓ V)` is unambiguous. -/
noncomputable def frk {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (W : Submodule (ZMod 2) V) : ℕ := Module.finrank (ZMod 2) W

variable {D : ℕ}

/-- The space spanned by the columns of a matrix. -/
noncomputable def colSpan (x : Fin D × Fin D → ZMod 2) : Submodule (ZMod 2) (Fin D → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (col x))

/-- The space spanned by the rows of a matrix. -/
noncomputable def rowSpan (x : Fin D × Fin D → ZMod 2) : Submodule (ZMod 2) (Fin D → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (row x))

/-- The rank of a matrix, as the dimension of its column space. -/
noncomputable def matRank (x : Fin D × Fin D → ZMod 2) : ℕ := frk (colSpan x)

/-- The number of non-zero columns of a matrix. -/
def nzCols (x : Fin D × Fin D → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun j : Fin D => ∃ i, x (i, j) ≠ 0)).card

/-- The number of non-zero rows of a matrix. -/
def nzRows (x : Fin D × Fin D → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i : Fin D => ∃ j, x (i, j) ≠ 0)).card

/-- Every column of `x` lies in `CA`. -/
def IsColwise (CA : Submodule (ZMod 2) (Fin D → ZMod 2)) (x : Fin D × Fin D → ZMod 2) : Prop :=
  ∀ j, col x j ∈ CA

/-- Every row of `x` lies in `CB`. -/
def IsRowwise (CB : Submodule (ZMod 2) (Fin D → ZMod 2)) (x : Fin D × Fin D → ZMod 2) : Prop :=
  ∀ i, row x i ∈ CB

/-! ## The three codes attached to a pair of codes -/

/-- `CA ⊗ 𝔽₂^D`: the matrices whose columns lie in `CA`. -/
noncomputable def colCode (CA : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Submodule (ZMod 2) (Fin D × Fin D → ZMod 2) :=
  ⨅ j : Fin D, CA.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin D => (i, j)))

/-- `𝔽₂^D ⊗ CB`: the matrices whose rows lie in `CB`. -/
noncomputable def rowCode (CB : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Submodule (ZMod 2) (Fin D × Fin D → ZMod 2) :=
  ⨅ i : Fin D, CB.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun j : Fin D => (i, j)))

/-- `CA ⊞ CB = (CA ⊗ 𝔽₂^D) + (𝔽₂^D ⊗ CB)`. -/
noncomputable def prodSum (CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Submodule (ZMod 2) (Fin D × Fin D → ZMod 2) :=
  colCode CA ⊔ rowCode CB

lemma mem_colCode {CA : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (x : Fin D × Fin D → ZMod 2) :
    x ∈ colCode CA ↔ IsColwise CA x := by
  simp only [colCode, Submodule.mem_iInf, Submodule.mem_comap, IsColwise, col]
  rfl

lemma mem_rowCode {CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (x : Fin D × Fin D → ZMod 2) :
    x ∈ rowCode CB ↔ IsRowwise CB x := by
  simp only [rowCode, Submodule.mem_iInf, Submodule.mem_comap, IsRowwise, row]
  rfl

lemma tensorCode_eq (CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    tensorCode CA CB = colCode CA ⊓ rowCode CB := by
  simp only [tensorCode, colCode, rowCode, inf_comm]

lemma mem_tensorCode {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (x : Fin D × Fin D → ZMod 2) :
    x ∈ tensorCode CA CB ↔ IsColwise CA x ∧ IsRowwise CB x := by
  rw [tensorCode_eq, Submodule.mem_inf, mem_colCode, mem_rowCode]

lemma mem_prodSum {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (x : Fin D × Fin D → ZMod 2) :
    x ∈ prodSum CA CB ↔ ∃ a ∈ colCode CA, ∃ b ∈ rowCode CB, x = a + b := by
  simp [prodSum, Submodule.mem_sup, eq_comm]

lemma col_mem_colSpan (x : Fin D × Fin D → ZMod 2) (j : Fin D) : col x j ∈ colSpan x :=
  Submodule.subset_span ⟨j, rfl⟩

lemma row_mem_rowSpan (x : Fin D × Fin D → ZMod 2) (i : Fin D) : row x i ∈ rowSpan x :=
  Submodule.subset_span ⟨i, rfl⟩

lemma colSpan_le_iff {x : Fin D × Fin D → ZMod 2} {V : Submodule (ZMod 2) (Fin D → ZMod 2)} :
    colSpan x ≤ V ↔ ∀ j, col x j ∈ V :=
  Submodule.span_le.trans Set.range_subset_iff

lemma rowSpan_le_iff {x : Fin D × Fin D → ZMod 2} {V : Submodule (ZMod 2) (Fin D → ZMod 2)} :
    rowSpan x ≤ V ↔ ∀ i, row x i ∈ V :=
  Submodule.span_le.trans Set.range_subset_iff

/-! ## Sparseness, property `(*)` and product expansion -/

/-- A subspace is `α`-sparse if it is spanned by vectors of Hamming weight at most `α * D`. -/
def IsSparse (α : ℝ) (V : Submodule (ZMod 2) (Fin D → ZMod 2)) : Prop :=
  ∃ S : Set (Fin D → ZMod 2),
    (∀ v ∈ S, (hammingNorm v : ℝ) ≤ α * D) ∧ Submodule.span (ZMod 2) S = V

/-- Kalachev--Panteleev property `(*)`: no `α`-sparse subspace of dimension `≤ r` meets `C` in
half of its own dimension. -/
def HasStar (α : ℝ) (r : ℕ) (C : Submodule (ZMod 2) (Fin D → ZMod 2)) : Prop :=
  ∀ V : Submodule (ZMod 2) (Fin D → ZMod 2), IsSparse α V → 0 < frk V → frk V ≤ r →
    2 * frk (C ⊓ V) < frk V

/-- `(CA, CB)` is `κ`-product-expanding. -/
def ProductExpanding (κ : ℝ) (CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)) : Prop :=
  ∀ x ∈ prodSum CA CB, ∃ a ∈ colCode CA, ∃ b ∈ rowCode CB,
    x = a + b ∧ κ * D * ((nzCols a : ℝ) + (nzRows b : ℝ)) ≤ (wt x : ℝ)

/-! ## Parity-check codes and the KP pairing condition -/

/-- The dot product `∑ i, u i * v i`. -/
def dot {D : ℕ} (u v : Fin D → ZMod 2) : ZMod 2 := ∑ i, u i * v i

/-- The linear functional `v ↦ ∑ i, u i * v i`. -/
def dotLin {D : ℕ} (u : Fin D → ZMod 2) : (Fin D → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := dot u v
  map_add' v w := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Matrix-vector product `v ↦ x * v`. -/
def matVec (x : Fin D × Fin D → ZMod 2) (v : Fin D → ZMod 2) : Fin D → ZMod 2 :=
  fun i => ∑ j, x (i, j) * v j

/-- The code with parity-check matrix `H` (its rows are the parity checks). -/
noncomputable def kerCode {D r : ℕ} (H : Fin r → Fin D → ZMod 2) :
    Submodule (ZMod 2) (Fin D → ZMod 2) :=
  ⨅ k : Fin r, LinearMap.ker (dotLin (H k))

lemma mem_kerCode {D r : ℕ} {H : Fin r → Fin D → ZMod 2} {v : Fin D → ZMod 2} :
    v ∈ kerCode H ↔ ∀ k, dot (H k) v = 0 := by
  simp only [kerCode, Submodule.mem_iInf, LinearMap.mem_ker, dotLin, dot]
  rfl

/-- The Kalachev--Panteleev condition `H₁ x H₂ᵀ = 0` in coordinates: every row of `H₁` is
orthogonal to `x (row of H₂)`.  It is implied by `x ∈ ker H₁ ⊞ ker H₂`. -/
def pairCond {D r : ℕ} (H1 H2 : Fin r → Fin D → ZMod 2) (x : Fin D × Fin D → ZMod 2) : Prop :=
  ∀ k l, dot (H1 k) (matVec x (H2 l)) = 0

/-! ## Finite sets used in the counting arguments -/

/-- Vectors of weight at most `α * D`. -/
noncomputable def smallVecs (α : ℝ) (D : ℕ) : Finset (Fin D → ZMod 2) := by
  classical exact Finset.univ.filter (fun v => (hammingNorm v : ℝ) ≤ α * D)

/-- Matrices of weight at most `γ * D²`. -/
noncomputable def smallMats (γ : ℝ) (D : ℕ) : Finset (Fin D × Fin D → ZMod 2) := by
  classical exact Finset.univ.filter (fun x => (hammingNorm x : ℝ) ≤ γ * D ^ 2)

lemma mem_smallVecs {α : ℝ} {D : ℕ} {v : Fin D → ZMod 2} :
    v ∈ smallVecs α D ↔ (hammingNorm v : ℝ) ≤ α * D := by
  classical simp [smallVecs]

lemma mem_smallMats {γ : ℝ} {D : ℕ} {x : Fin D × Fin D → ZMod 2} :
    x ∈ smallMats γ D ↔ (hammingNorm x : ℝ) ≤ γ * D ^ 2 := by
  classical simp [smallMats]

end GB

end Work.LT
