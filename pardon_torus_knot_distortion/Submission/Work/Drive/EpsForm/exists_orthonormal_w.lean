import Mathlib
import Submission.Work.Drive.EpsForm.SweepGenericity

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion

/-- Any two orthonormal vectors `n`, `v` of `ℝ³` extend to an orthonormal triple:
the orthogonal complement of `span {n, v}` is one-dimensional, hence contains a
unit vector, which is orthogonal to both `n` and `v`. -/
theorem exists_orthonormal_w {n v : LeanEval.KnotTheory.PardonDistortion.R3} (hn : ‖n‖ = 1) (hv : ‖v‖ = 1) (hnv : inner ℝ n v = 0) :
    ∃ w : LeanEval.KnotTheory.PardonDistortion.R3, ‖w‖ = 1 ∧ inner ℝ n w = 0 ∧ inner ℝ v w = 0 := by
  -- The pair `(n, v)` is an orthonormal family indexed by `Fin 2`.
  let f : Fin 2 → R3 := ![n, v]
  have horth : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f, hn, hv, hnv, real_inner_comm]
  -- Its span `S` has dimension two, so its orthogonal complement has dimension one,
  -- hence is nonzero; any nonzero vector of it, rescaled, is the required `w`.
  let S : Submodule ℝ R3 := Submodule.span ℝ (Set.range f)
  have hdimS : Module.finrank ℝ S = 2 := by
    have h := finrank_span_eq_card horth.linearIndependent
    simpa [S, f] using h
  have hdimE : Module.finrank ℝ R3 = 3 := by
    simpa using finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 3)
  have hdimW : Module.finrank ℝ (Sᗮ) = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal S
    rw [hdimS, hdimE] at h
    omega
  have hWne : Sᗮ ≠ ⊥ := by
    intro hbot
    rw [hbot] at hdimW
    have hz : Module.finrank ℝ (⊥ : Submodule ℝ R3) = 0 := (Submodule.finrank_eq_zero).mpr rfl
    omega
  obtain ⟨w', hw'mem, hw'ne⟩ := (Submodule.ne_bot_iff (Sᗮ)).mp hWne
  have hmemw : (↑‖w'‖)⁻¹ • w' ∈ Sᗮ := Submodule.smul_mem _ _ hw'mem
  have hnS : n ∈ S := Submodule.subset_span ⟨0, rfl⟩
  have hvS : v ∈ S := Submodule.subset_span ⟨1, by simp [f]⟩
  refine ⟨(↑‖w'‖)⁻¹ • w', ?_, ?_, ?_⟩
  · exact norm_smul_inv_norm hw'ne
  · exact (Submodule.mem_orthogonal S _).mp hmemw n hnS
  · exact (Submodule.mem_orthogonal S _).mp hmemw v hvS

end Work.Drive.EpsForm
