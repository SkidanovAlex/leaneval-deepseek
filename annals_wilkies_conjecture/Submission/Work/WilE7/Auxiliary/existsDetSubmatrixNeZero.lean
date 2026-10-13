/-
  Portable re-homing of the extraction step requested at
  `Submission/Work/WilE7/Aux/existsDetSubmatrixNeZero.lean`
  (module `Submission.Work.WilE7.Aux.existsDetSubmatrixNeZero`).

  That path is unbuildable in this toolchain: `Lean.Elab.checkModuleNamePortability` rejects
  the path component `Aux` in module names (`'Aux' is a reserved file name on some operating
  systems`), so `lake build` can never compile it, whatever the file contains.  This module
  carries the same statement under a portable path, in the `Auxiliary` namespace so that it can
  never clash with the declared name of the original request (which is
  `Work.WilE7.Aux.existsDetSubmatrixNeZero`).

  Statement: **a matrix of full row rank has a nonvanishing maximal minor.**  If
  `R : Matrix (Fin n) (Fin q) ℝ` has `rank = n`, its columns span an `n`-dimensional subspace of
  `ℝⁿ`, so `n` of them are linearly independent and the corresponding `n × n` submatrix is
  nonsingular.

  (The same argument is used, privately, in the proof of
  `Work.WilE7.Aux.critMinorsVanishKer`; see
  `Submission/Work/WilE7/Auxiliary/critMinorsVanishKer.lean`.)

  **Consumers should prefer the copy the prover of the original request shipped at**
  `Submission/Work/WilE7/auxiliary/existsDetSubmatrixNeZero.lean`, which declares the name that was
  actually requested (`Work.WilE7.Aux.existsDetSubmatrixNeZero`).  This module is kept as a second,
  independent buildable copy under a distinct name
  (`Work.WilE7.Auxiliary.existsDetSubmatrixNeZero`), so that the declaration is available even if
  the other copy is moved or renamed; both are `sorry`-free with the permitted axioms.
-/
import Mathlib

set_option autoImplicit false
namespace Work.WilE7.Auxiliary

theorem existsDetSubmatrixNeZero {n q : ℕ} (R : Matrix (Fin n) (Fin q) ℝ) (hrank : R.rank = n) :
    ∃ σ : Fin n → Fin q, (R.submatrix id σ).det ≠ 0 := by
  have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range R.col)) = n := by
    rw [← Matrix.rank_eq_finrank_span_cols (A := R)]
    exact hrank
  obtain ⟨f, hf_mem, -, hf_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range R.col)
  let e := finCongr hfr
  let g : Fin n → (Fin n → ℝ) := fun i => f (e.symm i)
  have hg_mem : ∀ i, g i ∈ Set.range R.col := fun i => hf_mem (e.symm i)
  have hg_li : LinearIndependent ℝ g := by
    have h := hf_li.comp e.symm e.symm.injective
    simpa [g, Function.comp_def] using h
  choose σ hσ using hg_mem
  refine ⟨σ, ?_⟩
  have hcol : (R.submatrix id σ).col = g := by
    funext i a
    simpa [Matrix.col] using congrFun (hσ i) a
  have hli : LinearIndependent ℝ (R.submatrix id σ).col := hcol.symm ▸ hg_li
  have hns : (R.submatrix id σ).Nonsingular := Matrix.Nonsingular.of_linearIndependent_col hli
  exact (Matrix.nonsingular_iff_det_ne_zero (A := R.submatrix id σ)).mp hns

end Work.WilE7.Auxiliary
