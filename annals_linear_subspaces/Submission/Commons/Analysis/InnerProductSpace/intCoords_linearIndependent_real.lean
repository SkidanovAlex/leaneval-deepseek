import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

/-- The values at the coordinates of a finite sum of vectors in `EuclideanSpace ℝ (Fin d)`
are the corresponding coordinate sums. -/
private lemma euclidean_sum_apply (d : ℕ) (f : Fin d → EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    ((∑ i : Fin d, f i) : EuclideanSpace ℝ (Fin d)) j = ∑ i : Fin d, f i j := by
  let proj : EuclideanSpace ℝ (Fin d) →+ ℝ :=
    { toFun := fun v => v j
      map_zero' := by simp
      map_add' := by intro x y; simp }
  exact map_sum proj f Finset.univ

theorem intCoords_linearIndependent_real {d n : ℕ}
    {u : Fin n → EuclideanSpace ℝ (Fin d)}
    (huℤ : ∀ r : Fin n, u r ∈ Submodule.span ℤ
      (Set.range (EuclideanSpace.basisFun (Fin d) ℝ)))
    (hli : LinearIndependent ℤ u) : LinearIndependent ℝ u := by
  classical
  -- `e` is the standard ℝ-basis of the ambient space.
  let e : Fin d → EuclideanSpace ℝ (Fin d) :=
    fun i => (EuclideanSpace.basisFun (Fin d) ℝ i : EuclideanSpace ℝ (Fin d))
  -- coordinates of each basis vector:
  have heval : ∀ i j : Fin d, e i j = if i = j then (1 : ℝ) else 0 := by
    intro i j
    dsimp [e]
    rw [EuclideanSpace.basisFun_apply]
    by_cases h : i = j
    · subst h
      simp
    · have hj : j ≠ i := fun hji => h hji.symm
      simp [h, hj]
  -- each `u r` has integer coordinates: choose them via the membership hypothesis
  have hwmem : ∀ r : Fin n, ∃ c : Fin d → ℤ, (∑ i : Fin d, c i • e i) = u r := fun r =>
    (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (M := EuclideanSpace ℝ (Fin d)) (v := e)
      (x := u r)).mp (huℤ r)
  let w : Fin n → Fin d → ℤ := fun r => Classical.choose (hwmem r)
  have hwsum : ∀ r : Fin n, (∑ i : Fin d, w r i • e i) = u r := fun r =>
    Classical.choose_spec (hwmem r)
  -- coordinate fact
  have hcoord : ∀ r j, (u r) j = (w r j : ℝ) := by
    intro r j
    rw [← hwsum r]
    rw [euclidean_sum_apply]
    simp [heval, zsmul_eq_mul]
  -- the ℤ-linear map from the integer coordinate rows into the ambient space
  let F : (Fin d → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin d) :=
    { toFun := fun x : Fin d → ℤ => WithLp.toLp 2 (fun j : Fin d => (x j : ℝ))
      map_add' := by
        intro x y
        ext j
        simp
      map_smul' := by
        intro a x
        ext j
        simp }
  have hF : ∀ r, F (w r) = u r := by
    intro r
    ext j
    dsimp [F]
    simp [hcoord r j]
  -- integer linear independence of the coordinate rows
  have hwℤ : LinearIndependent ℤ (fun r : Fin n => w r) := by
    apply LinearIndependent.of_comp F
    -- the composed family is exactly `u`
    have huF : (fun r : Fin n => u r) = F ∘ (fun r : Fin n => w r) := by
      funext r
      exact (hF r).symm
    exact huF ▸ hli
  -- base change: ℤ-independence of the rows implies ℝ-independence of their real values
  have hrowsℝ : LinearIndependent ℝ (fun r : Fin n => fun j : Fin d => (w r j : ℝ)) :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (ι := Fin n) (ι' := Fin d)
      (v := w)).mpr hwℤ
  -- finally transfer back to the ambient space via the coordinate projection
  let φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin d → ℝ) :=
    { toFun := fun v => (fun j : Fin d => v j)
      map_add' := by intro x y; ext j; simp
      map_smul' := by intro a x; ext j; simp }
  -- the real rows are exactly the image of `u` under the coordinate projection
  have hrowsφ : (fun r : Fin n => (fun j : Fin d => (w r j : ℝ))) =
      φ ∘ (fun r : Fin n => u r) := by
    funext r
    ext j
    dsimp [φ]
    exact (hcoord r j).symm
  exact LinearIndependent.of_comp φ (by
    exact hrowsφ.symm ▸ hrowsℝ)

end Commons.Analysis.InnerProductSpace