import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Thom

/-- The polynomial whose value at `z : ℂ` is `det ((1 - z) • A + z • B)`.
It is obtained by lifting the matrix with entries `A i j + (B i j - A i j) * X`
to the polynomial ring and taking its determinant. -/
noncomputable def pathPoly (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) : Polynomial ℂ :=
  (Matrix.of (fun i j : Fin n =>
    Polynomial.C (A i j) + Polynomial.C (B i j - A i j) * Polynomial.X)).det

/-- Evaluating `pathPoly` at `z` gives the determinant of the linear interpolation
`(1 - z) • A + z • B`. -/
lemma pathPoly_eval (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (pathPoly n A B).eval z = ((1 - z) • A + z • B).det := by
  unfold pathPoly
  change (Polynomial.evalRingHom z) (Matrix.of (fun i j : Fin n =>
      Polynomial.C (A i j) + Polynomial.C (B i j - A i j) * Polynomial.X)).det
      = ((1 - z) • A + z • B).det
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, map_add, map_mul]
  simp
  ring

/-- The complex general linear group `GL n ℂ` is path connected: any two invertible
complex matrices can be joined by a continuous path of invertible matrices.

The path is built by first observing that for fixed invertible `A`, `B` the determinant of the
linear interpolation `(1 - z) • A + z • B` is a polynomial in `z` (namely `pathPoly n A B`),
whose zero set is finite, hence countable.  Since `ℂ` has real dimension `2 > 1`, the complement
of this countable set is path connected, so we may choose a continuous `f : [0,1] → ℂ` from `0`
to `1` along which the determinant never vanishes; the required path is `t ↦ (1 - f t) • A + f t • B`. -/
theorem exists_path_GL_complex (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    ∃ γ : C(unitInterval, Matrix (Fin n) (Fin n) ℂ),
      γ 0 = A ∧ γ 1 = B ∧ ∀ t : unitInterval, IsUnit (γ t).det := by
  have hA_ne : A.det ≠ 0 := hA.ne_zero
  have hB_ne : B.det ≠ 0 := hB.ne_zero
  -- `pathPoly n A B` is not the zero polynomial, since its value at `0` is `det A ≠ 0`.
  have hP_ne : pathPoly n A B ≠ 0 := by
    intro h
    have h0 : (pathPoly n A B).eval 0 = A.det := by rw [pathPoly_eval]; simp
    rw [h] at h0
    simp at h0
    exact hA_ne h0.symm
  -- The set of `z` where the interpolation degenerates is the root set of `pathPoly`.
  set S : Set ℂ := {z | (pathPoly n A B).eval z = 0} with hSdef
  have hS_count : S.Countable := by
    have hfin : ({z : ℂ | (pathPoly n A B).IsRoot z}).Finite :=
      Polynomial.finite_setOfPred_isRoot hP_ne
    have heq : S = {z : ℂ | (pathPoly n A B).IsRoot z} := by
      ext z; simp [hSdef, Polynomial.IsRoot.def]
    rw [heq]; exact hfin.countable
  -- The endpoints `0` and `1` do not lie in `S`.
  have h0S : (0 : ℂ) ∈ Sᶜ := by
    rw [hSdef]
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [pathPoly_eval]; simpa using hA_ne
  have h1S : (1 : ℂ) ∈ Sᶜ := by
    rw [hSdef]
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [pathPoly_eval]; simpa using hB_ne
  -- So the complement of `S` is path connected, and joins `0` to `1`.
  have hh : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hconn : IsPathConnected (Sᶜ) :=
    Set.Countable.isPathConnected_compl_of_one_lt_rank hh hS_count
  have hjoin : JoinedIn Sᶜ (0 : ℂ) 1 := hconn.joinedIn 0 h0S 1 h1S
  let f : Path (0 : ℂ) 1 := hjoin.somePath
  have hfmem : ∀ t : unitInterval, f t ∈ Sᶜ := fun t => hjoin.somePath_mem t
  -- The corresponding matrix path, and its continuity.
  have hcont : Continuous (fun t : unitInterval => (1 - (f t : ℂ)) • A + (f t : ℂ) • B) := by
    apply Continuous.add
    · exact (continuous_const.sub f.continuous).smul continuous_const
    · exact f.continuous.smul continuous_const
  let γ : C(unitInterval, Matrix (Fin n) (Fin n) ℂ) :=
    ⟨fun t => (1 - (f t : ℂ)) • A + (f t : ℂ) • B, hcont⟩
  refine ⟨γ, ?_, ?_, ?_⟩
  · show (1 - ((f (0:unitInterval)) : ℂ)) • A + ((f (0:unitInterval)) : ℂ) • B = A
    rw [f.source]; simp
  · show (1 - ((f (1:unitInterval)) : ℂ)) • A + ((f (1:unitInterval)) : ℂ) • B = B
    rw [f.target]; simp
  · intro t
    have hdet : (γ t).det = (pathPoly n A B).eval (f t) := by
      show ((1 - ((f t) : ℂ)) • A + ((f t) : ℂ) • B).det = (pathPoly n A B).eval (f t)
      exact (pathPoly_eval n A B (f t)).symm
    have hne : (γ t).det ≠ 0 := by
      rw [hdet]
      have ht := hfmem t
      rw [hSdef] at ht
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at ht
      exact ht
    exact isUnit_iff_ne_zero.mpr hne

end Work.Thom
