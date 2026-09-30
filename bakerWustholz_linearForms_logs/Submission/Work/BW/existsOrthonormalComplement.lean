import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped InnerProductSpace

namespace Work.BW

/-- The inner product of two vectors in `EuclideanSpace ℝ (Fin n)`, expressed as a sum of
products of coordinates. -/
private lemma bw_inner_eq_sum {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ i, x.ofLp i * y.ofLp i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

/-- Given a matrix `B` whose columns are orthonormal, construct a matrix `Bp` whose columns are
orthonormal and orthogonal to the columns of `B`. -/
theorem existsOrthonormalComplement {n k : ℕ} (hk : k ≤ n) (B : Matrix (Fin n) (Fin k) ℝ)
    (hB : B.transpose * B = 1) :
    ∃ Bp : Matrix (Fin n) (Fin (n - k)) ℝ, Bp.transpose * Bp = 1 ∧ B.transpose * Bp = 0 := by
  classical
  -- The columns of `B`, seen as vectors of `EuclideanSpace ℝ (Fin n)`.
  let col : Fin k → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (fun i => B i j)
  -- `hB` says precisely that these columns are orthonormal.
  have hcol : Orthonormal ℝ col := by
    rw [orthonormal_iff_ite]
    intro j1 j2
    have h : inner ℝ (col j1) (col j2) = (B.transpose * B) j1 j2 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, mul_comm, Matrix.mul_apply, Matrix.transpose_apply, col]
    rw [h, hB, Matrix.one_apply]
  -- Extend this orthonormal family to an orthonormal basis of `EuclideanSpace ℝ (Fin n)`.
  let s : Set (Fin n) := {i | (i : ℕ) < k}
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun j => if h : (j : ℕ) < k then col ⟨j, h⟩ else 0
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    have hcomp : s.domRestrict v = col ∘ (fun (j : s) => (⟨j.val, j.property⟩ : Fin k)) := by
      funext j
      simp only [Set.domRestrict, Function.comp_apply, v]
      have hjk : ((↑j : Fin n) : ℕ) < k := j.property
      rw [dite_eq_left hjk]
    rw [hcomp]
    exact hcol.comp _ (fun a b hab => by
      have h2 : ((a : Fin n) : ℕ) = ((b : Fin n) : ℕ) := by
        simpa using congrArg Fin.val hab
      exact Subtype.ext (Fin.ext h2))
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin n)) (ι := Fin n) (by simp) (v := v) (s := s) hv
  -- The `n - k` remaining basis vectors, indexed by `k, k+1, …, n-1`.
  let e : Fin (n - k) → Fin n := fun t => ⟨k + t.val, by have := t.isLt; omega⟩
  have he : Function.Injective e := fun a b hab => by
    simp only [e, Fin.mk.injEq] at hab
    exact Fin.ext (by omega)
  have hne : ∀ (j : Fin k) (t : Fin (n - k)),
      (⟨(j:ℕ), lt_of_lt_of_le j.isLt hk⟩ : Fin n) ≠ e t := by
    intro j t hcontra
    have h1 : (j : ℕ) = k + t.val := by
      have h2 := congrArg Fin.val hcontra
      simpa [e] using h2
    have hj : (j : ℕ) < k := j.isLt
    omega
  have hb_orth : ∀ p q : Fin n, inner ℝ (b p) (b q) = if p = q then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  refine ⟨Matrix.of (fun i t => (b (e t)).ofLp i), ?_, ?_⟩
  · -- The columns of `Bp` are orthonormal.
    ext t1 t2
    have hsum : ∑ x : Fin n, (b (e t1)).ofLp x * (b (e t2)).ofLp x
        = inner ℝ (b (e t1)) (b (e t2)) := by
      rw [bw_inner_eq_sum]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [hsum, hb_orth (e t1) (e t2), Matrix.one_apply]
    exact if_congr he.eq_iff rfl rfl
  · -- The columns of `Bp` are orthogonal to the columns of `B`.
    ext j t
    have hsum : ∑ x : Fin n, B x j * (b (e t)).ofLp x = inner ℝ (col j) (b (e t)) := by
      rw [bw_inner_eq_sum]
    have hcolb : col j = b ⟨(j:ℕ), lt_of_lt_of_le j.isLt hk⟩ := by
      have hjs : (⟨(j:ℕ), lt_of_lt_of_le j.isLt hk⟩ : Fin n) ∈ s := j.isLt
      have h := hb _ hjs
      rw [h]
      simp only [v]
      rw [dite_eq_left j.isLt]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [hsum, hcolb, hb_orth _ (e t), ite_eq_right (hne j t)]

end Work.BW
