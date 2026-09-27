import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT.Cone

/-- Over `C(X × [0,1], ℂ)`: if `M` is a unit whose slice at `1` is a constant matrix, then the
same holds for any two-sided inverse `M'` of `M`. -/
theorem slice_one_inv_const {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M M' : Matrix ι ι C(X × unitInterval, ℂ)) (h1 : M * M' = 1) (h2 : M' * M = 1)
    (hconst : ∃ k : Matrix ι ι ℂ,
      M.map (sliceAt (1 : unitInterval)) = k.map (algebraMap ℂ C(X, ℂ))) :
    ∃ k' : Matrix ι ι ℂ,
      M'.map (sliceAt (1 : unitInterval)) = k'.map (algebraMap ℂ C(X, ℂ)) := by
  classical
  by_cases hX : Nonempty X
  · -- Nonempty case: the inverse of a constant matrix is constant.
    -- For each `y : X` the algebra hom `sliceAt 1` followed by evaluation at `y` is evaluation
    -- of the function at the point `(y, 1)`.  Sending `M * M' = 1` and `M' * M = 1` through it
    -- exhibits `M'.map (sliceAt 1)` evaluated at `y` as *the* two-sided inverse of the constant
    -- matrix `k`; in particular it does not depend on `y`.
    obtain ⟨x⟩ := hX
    obtain ⟨k, hk⟩ := hconst
    -- The evaluation of the slice at `1` at a point `y`.
    have hM : ∀ y : X,
        M.map (⇑((evalC y).comp (sliceAt (1 : unitInterval)))) = k := by
      intro y
      ext i j
      have hij : (sliceAt (1 : unitInterval) (M i j) : C(X, ℂ)) =
          (algebraMap ℂ C(X, ℂ)) (k i j) := by
        have h := congrArg (fun A => A i j) hk
        rwa [Matrix.map_apply, Matrix.map_apply] at h
      have := congrArg (fun f : C(X, ℂ) => f y) hij
      simpa using this
    have hM' : ∀ y : X, M'.map (⇑((evalC y).comp (sliceAt (1 : unitInterval)))) * k = 1 := by
      intro y
      have hy : (M' * M).map (⇑((evalC y).comp (sliceAt (1 : unitInterval)))) =
          (1 : Matrix ι ι C(X × unitInterval, ℂ)).map
            (⇑((evalC y).comp (sliceAt (1 : unitInterval)))) := by rw [h2]
      have := hy
      rw [Matrix.map_mul, Matrix.map_one] at this
      · rw [hM y] at this
        exact this
      · exact map_zero _
      · exact map_one _
    have hkM' : ∀ y : X, k * M'.map (⇑((evalC y).comp (sliceAt (1 : unitInterval)))) = 1 := by
      intro y
      have hy : (M * M').map (⇑((evalC y).comp (sliceAt (1 : unitInterval)))) =
          (1 : Matrix ι ι C(X × unitInterval, ℂ)).map
            (⇑((evalC y).comp (sliceAt (1 : unitInterval)))) := by rw [h1]
      have := hy
      rw [Matrix.map_mul, Matrix.map_one] at this
      · rw [hM y] at this
        exact this
      · exact map_zero _
      · exact map_one _
    -- uniqueness of the two-sided inverse
    have hsame : ∀ y : X, M'.map (⇑((evalC y).comp (sliceAt (1 : unitInterval)))) =
        M'.map (⇑((evalC x).comp (sliceAt (1 : unitInterval)))) := by
      intro y
      calc M'.map (⇑((evalC y).comp (sliceAt (1 : unitInterval))))
          = M'.map (⇑((evalC y).comp (sliceAt (1 : unitInterval)))) *
              (k * M'.map (⇑((evalC x).comp (sliceAt (1 : unitInterval))))) := by
            rw [hkM' x, mul_one]
        _ = (M'.map (⇑((evalC y).comp (sliceAt (1 : unitInterval)))) * k) *
              M'.map (⇑((evalC x).comp (sliceAt (1 : unitInterval)))) := by
            rw [Matrix.mul_assoc]
        _ = M'.map (⇑((evalC x).comp (sliceAt (1 : unitInterval)))) := by
            rw [hM' y, one_mul]
    refine ⟨M'.map (⇑((evalC x).comp (sliceAt (1 : unitInterval)))), ?_⟩
    ext i j y
    have := congrArg (fun A => A i j) (hsame y)
    rw [Matrix.map_apply, Matrix.map_apply] at this
    simpa using this
  · -- Empty case: `C(X, ℂ)` is the trivial ring, so any two matrices over it agree.
    have := not_nonempty_iff.mp hX
    exact ⟨1, Subsingleton.elim _ _⟩

end Work.KT.Cone
