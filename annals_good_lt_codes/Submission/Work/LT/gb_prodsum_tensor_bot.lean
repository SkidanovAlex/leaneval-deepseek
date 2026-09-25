import Mathlib
import Submission.Work.LT.good_base_defs

namespace Work.LT

namespace GB

variable {D : ℕ}

/-- Apply a linear map `p : 𝔽₂^D → 𝔽₂^D` to each column of a matrix: the linear map
`(colMap p x) (i, j) = p (col x j) i`. It acts only on the row index. -/
noncomputable def colMap (p : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) :
    (Fin D × Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D × Fin D → ZMod 2) where
  toFun x := fun q => p (fun i => x (i, q.2)) q.1
  map_add' x y := by
    funext q
    have h : (fun i => (x + y) (i, q.2)) =
        (fun i => x (i, q.2)) + (fun i => y (i, q.2)) := by funext i; rfl
    rw [h, map_add]; rfl
  map_smul' c x := by
    funext q
    have h : (fun i => (c • x) (i, q.2)) = c • (fun i => x (i, q.2)) := by funext i; rfl
    rw [h, map_smul]; rfl

/-- Apply a linear map `q : 𝔽₂^D → 𝔽₂^D` to each row of a matrix: the linear map
`(rowMap q x) (i, j) = q (row x i) j`. It acts only on the column index. -/
noncomputable def rowMap (q : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) :
    (Fin D × Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D × Fin D → ZMod 2) where
  toFun x := fun r => q (fun j => x (r.1, j)) r.2
  map_add' x y := by
    funext r
    have h : (fun j => (x + y) (r.1, j)) =
        (fun j => x (r.1, j)) + (fun j => y (r.1, j)) := by funext j; rfl
    rw [h, map_add]; rfl
  map_smul' c x := by
    funext r
    have h : (fun j => (c • x) (r.1, j)) = c • (fun j => x (r.1, j)) := by funext j; rfl
    rw [h, map_smul]; rfl

lemma colMap_apply (p : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) (i j : Fin D) : colMap p x (i, j) = p (col x j) i := rfl

lemma rowMap_apply (q : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) (i j : Fin D) : rowMap q x (i, j) = q (row x i) j := rfl

/-- Coordinate form of `colMap`: `(colMap p x) (i,j) = ∑ k, (toMatrix' p) i k * x (k,j)`. -/
lemma colMap_apply_sum (p : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) (i j : Fin D) :
    colMap p x (i, j) = ∑ k, LinearMap.toMatrix' p i k * x (k, j) := by
  rw [colMap_apply, ← LinearMap.toMatrix'_mulVec, Matrix.mulVec_apply_eq_sum]
  simp only [col]

/-- Coordinate form of `rowMap`: `(rowMap q x) (i,j) = ∑ l, (toMatrix' q) j l * x (i,l)`. -/
lemma rowMap_apply_sum (q : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) (i j : Fin D) :
    rowMap q x (i, j) = ∑ l, LinearMap.toMatrix' q j l * x (i, l) := by
  rw [rowMap_apply, ← LinearMap.toMatrix'_mulVec, Matrix.mulVec_apply_eq_sum]
  simp only [row]

/-- Column-wise and row-wise application of linear maps commute. -/
lemma colMap_rowMap_comm (p q : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) : colMap p (rowMap q x) = rowMap q (colMap p x) := by
  funext r
  obtain ⟨i, j⟩ := r
  simp only [colMap_apply_sum, rowMap_apply_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

lemma colMap_eq_self (p : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
    (C : Submodule (ZMod 2) (Fin D → ZMod 2)) (hp : ∀ v ∈ C, p v = v)
    (x : Fin D × Fin D → ZMod 2) (hx : IsColwise C x) : colMap p x = x := by
  funext r
  obtain ⟨i, j⟩ := r
  rw [colMap_apply]
  exact congrFun (hp (col x j) (hx j)) i

lemma colMap_eq_zero (p : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
    (P : Submodule (ZMod 2) (Fin D → ZMod 2)) (hp : ∀ v ∈ P, p v = 0)
    (x : Fin D × Fin D → ZMod 2) (hx : IsColwise P x) : colMap p x = 0 := by
  funext r
  obtain ⟨i, j⟩ := r
  rw [colMap_apply]
  have h := congrFun (hp (col x j) (hx j)) i
  simpa using h

lemma rowMap_eq_self (q : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
    (C : Submodule (ZMod 2) (Fin D → ZMod 2)) (hp : ∀ v ∈ C, q v = v)
    (x : Fin D × Fin D → ZMod 2) (hx : IsRowwise C x) : rowMap q x = x := by
  funext r
  obtain ⟨i, j⟩ := r
  rw [rowMap_apply]
  exact congrFun (hp (row x i) (hx i)) j

lemma rowMap_eq_zero (q : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
    (P : Submodule (ZMod 2) (Fin D → ZMod 2)) (hp : ∀ v ∈ P, q v = 0)
    (x : Fin D × Fin D → ZMod 2) (hx : IsRowwise P x) : rowMap q x = 0 := by
  funext r
  obtain ⟨i, j⟩ := r
  rw [rowMap_apply]
  have h := congrFun (hp (row x i) (hx i)) j
  simpa using h

end GB

/-- If `x` is a codeword of `C₁ ⊞ C₂` (column-wise `C₁` plus row-wise `C₂`) whose columns all lie in `P₁` and rows all lie in `P₂`, and there are linear maps `p₁`, `p₂` fixing `C₁`, `C₂` pointwise and killing `P₁`, `P₂`, then `x = 0`. (The maps exist as soon as `C₁ ⊓ P₁ = ⊥`, `C₂ ⊓ P₂ = ⊥`.) -/
theorem gb_prodsum_tensor_bot {D : ℕ} (C₁ C₂ P₁ P₂ : Submodule (ZMod 2) (Fin D → ZMod 2))
    (p₁ p₂ : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
    (hp₁C : ∀ v ∈ C₁, p₁ v = v) (hp₁P : ∀ v ∈ P₁, p₁ v = 0)
    (hp₂C : ∀ v ∈ C₂, p₂ v = v) (hp₂P : ∀ v ∈ P₂, p₂ v = 0)
    (x : Fin D × Fin D → ZMod 2) (hx1 : x ∈ GB.prodSum C₁ C₂)
    (hx2 : x ∈ tensorCode P₁ P₂) : x = 0 := by
  obtain ⟨a, ha, b, hb, hab⟩ := (GB.mem_prodSum x).mp hx1
  rw [GB.mem_tensorCode] at hx2
  obtain ⟨hxcol, hxrow⟩ := hx2
  rw [hab] at hxcol hxrow ⊢
  rw [GB.mem_colCode] at ha
  rw [GB.mem_rowCode] at hb
  -- `p₁` fixes the columns of `a`, `p₂` fixes the rows of `b`
  have hca : GB.colMap p₁ a = a := GB.colMap_eq_self p₁ C₁ hp₁C a ha
  have hrb : GB.rowMap p₂ b = b := GB.rowMap_eq_self p₂ C₂ hp₂C b hb
  -- `p₁` (column-wise) dies on `a + b` (columns in `P₁`), likewise `p₂` on rows in `P₂`
  have hcol : GB.colMap p₁ (a + b) = 0 := GB.colMap_eq_zero p₁ P₁ hp₁P (a + b) hxcol
  have hrow : GB.rowMap p₂ (a + b) = 0 := GB.rowMap_eq_zero p₂ P₂ hp₂P (a + b) hxrow
  have h1 : a + GB.colMap p₁ b = 0 := by rw [map_add, hca] at hcol; exact hcol
  have h2 : GB.rowMap p₂ a + b = 0 := by rw [map_add, hrb] at hrow; exact hrow
  -- both mixed terms vanish
  have hcd : GB.colMap p₁ b + GB.rowMap p₂ a = 0 := by
    have h4 : GB.colMap p₁ (GB.rowMap p₂ a) = GB.rowMap p₂ a := by
      rw [GB.colMap_rowMap_comm p₁ p₂ a, hca]
    have h5 : b + GB.rowMap p₂ a = 0 := by rw [add_comm]; exact h2
    calc GB.colMap p₁ b + GB.rowMap p₂ a
        = GB.colMap p₁ b + GB.colMap p₁ (GB.rowMap p₂ a) := by rw [h4]
      _ = GB.colMap p₁ (b + GB.rowMap p₂ a) := (map_add _ _ _).symm
      _ = GB.colMap p₁ 0 := by rw [h5]
      _ = 0 := map_zero _
  have key : a + b = (a + GB.colMap p₁ b) + (GB.rowMap p₂ a + b)
      - (GB.colMap p₁ b + GB.rowMap p₂ a) := by abel
  rw [key, h1, h2, hcd]
  simp

end Work.LT
