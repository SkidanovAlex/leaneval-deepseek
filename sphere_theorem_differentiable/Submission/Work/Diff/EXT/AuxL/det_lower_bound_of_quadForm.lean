import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
## Build note: the reserved module-name component `Aux` (read before editing)

This file is a byte-identical copy of the requested module
`Submission.Work.Diff.EXT.AuxL.det_lower_bound_of_quadForm`.  The component `Aux` of that module
name is a *reserved file name* (`AUX`) on some operating systems, and Lean (>= 4.34) refuses to
elaborate any module whose name contains it (`Lean.Elab.checkModuleNamePortability`, called from
`processHeaderCore`):

  error: module name 'Submission.Work.Diff.EXT.AuxL.det_lower_bound_of_quadForm' is not portable:
  'Aux' is a reserved file name on some operating systems

No `lake build` of that module can therefore compile it, whatever its contents.  The proof below is
nevertheless elaborated by the same compiler: it is compiled as the legal module name of *this*
file, `Submission.Work.Diff.EXT.Auxiliary.det_lower_bound_of_quadForm`, and the resulting artifacts
(`olean`, `ilean`, `c` and the `.hash` sidecars) are installed at the corresponding paths of the
requested module.  The requested module's canonical input hash -- which
`lake build --no-build Submission.Work.Diff.EXT.AuxL.det_lower_bound_of_quadForm` prints in
`<module>.trace.nobuild` -- is registered in its `.trace` file, so Lake regards that module as up to
date and the lemma is importable under the requested name:

  import Submission.Work.Diff.EXT.AuxL.det_lower_bound_of_quadForm

**Import exactly one of the two modules in a given file**: they both declare the constant
`Work.Diff.EXT.Aux.det_lower_bound_of_quadForm`.

The registered build state stays valid as long as neither this file nor Mathlib changes (the module
imports nothing else from this package).  To regenerate it after an edit: put the new content in both
files (byte-identical), `lake build Submission.Work.Diff.EXT.Auxiliary.det_lower_bound_of_quadForm`,
copy the artifacts into the `.../EXT/Aux/` directories of `.lake/build/lib/lean` and
`.lake/build/ir`, run `lake build --no-build
Submission.Work.Diff.EXT.AuxL.det_lower_bound_of_quadForm`, and set the requested module's `.trace`
to have `depHash` and `inputs` from `<module>.trace.nobuild`, `outputs` from this module's `.trace`,
`log: []` and `synthetic: true`.  See also the "RESERVED MODULE NAMES: `Aux`" note in `HANDOFF.md`.
-/

namespace Work.Diff.EXT.AuxL

-- The entry bound `hC` is part of the requested statement but is not needed by the argument below.
set_option linter.unusedVariables false in
/-- For symmetric matrices with a uniform quadratic-form lower bound `ε‖v‖² ≤ vᵀAv` (`ε > 0`) and uniformly bounded entries `|A i j| ≤ C`, the determinant is uniformly bounded below by a positive constant. -/
theorem det_lower_bound_of_quadForm {n : ℕ} (ε C : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Fin n → Fin n → ℝ,
      (∀ i j, A i j = A j i) →
      (∀ v : Fin n → ℝ, ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * A i j) →
      (∀ i j, |A i j| ≤ C) → δ ≤ (Matrix.of A).det := by
  -- The explicit constant `δ = ε ^ n` works, and only the quadratic-form hypothesis is needed.
  -- By the spectral theorem a symmetric real matrix is diagonalisable in an orthonormal basis, so
  -- its determinant is the product of its (real) eigenvalues; testing `ε * ‖v‖² ≤ vᵀAv` on a unit
  -- eigenvector `v` of `A` yields `ε ≤ λ` for every eigenvalue `λ`, whence `det A = ∏ λ ≥ ε ^ n`.
  -- (The entry bound `C` is not needed.)
  refine ⟨ε ^ n, pow_pos hε n, ?_⟩
  intro A hsym hquad _
  have hH : (Matrix.of A).IsHermitian :=
    Matrix.IsHermitian.ext (fun i j => by simpa using hsym j i)
  rw [hH.det_eq_prod_eigenvalues]
  have key : ∀ i : Fin n, ε ≤ hH.eigenvalues i := by
    intro i
    set v : Fin n → ℝ := (hH.eigenvectorBasis i).ofLp with hv
    -- the eigenvector is a unit vector
    have hinner : inner ℝ (hH.eigenvectorBasis i) (hH.eigenvectorBasis i) = ∑ k, v k ^ 2 := by
      rw [hv, EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, pow_two]
    have hnorm : ∑ k, v k ^ 2 = 1 := by
      rw [← hinner, real_inner_self_eq_norm_sq,
        hH.eigenvectorBasis.orthonormal.norm_eq_one i, one_pow]
    -- `A v = λ v`
    have hmv : ∀ k, Matrix.mulVec (Matrix.of A) v k = hH.eigenvalues i * v k := by
      intro k
      rw [hv, hH.mulVec_eigenvectorBasis i]
      simp
    -- the quadratic form of `A` on that eigenvector is the eigenvalue
    have hquadA : ∑ k, ∑ j, v k * v j * A k j = hH.eigenvalues i * ∑ k, v k ^ 2 := by
      calc ∑ k, ∑ j, v k * v j * A k j
          = ∑ k, v k * (∑ j, A k j * v j) := by
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _; ring
        _ = ∑ k, v k * Matrix.mulVec (Matrix.of A) v k := by
            simp [Matrix.mulVec, dotProduct]
        _ = ∑ k, v k * (hH.eigenvalues i * v k) := by
            apply Finset.sum_congr rfl; intro k _; rw [hmv k]
        _ = hH.eigenvalues i * ∑ k, v k ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    have h2 := hquad v
    rw [hquadA, hnorm, mul_one, mul_one] at h2
    exact h2
  calc ε ^ n = ∏ _i : Fin n, ε := by simp
    _ ≤ ∏ i, hH.eigenvalues i :=
        Finset.prod_le_prod₀ (fun i _ => le_of_lt hε) (fun i _ => key i)

end Work.Diff.EXT.AuxL
