import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

open Filter Matrix

/-- **Sequential compactness of the bounded-entry part of `SL₃(ℝ)`.**

If every entry of the sequence `g n ∈ SL₃(ℝ)` is bounded in absolute value by `B`, then
some subsequence converges (in the subspace topology induced from `ℝ^{3×3}`, i.e. entrywise)
to a limit which again lies in `SL₃(ℝ)`.

The bound `B` need not be positive: the hypothesis `|0| ≤ B` forces `B ≥ 0` as soon as the
index type `ℕ` is inhabited (which it is, but no non-vacuity is required for the proof). -/
theorem exists_subseq_tendsto_of_entry_bound {g : ℕ → SL3} {B : ℝ}
    (hB : ∀ n i j, |(g n : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ B) :
    ∃ (gInf : SL3) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (fun n => g (φ n)) Filter.atTop (nhds gInf) := by
  -- Work in the ambient space `ℝ³ ˣ ³`, where first countability is available;
  -- `Matrix (Fin 3) (Fin 3) ℝ` is *definitionally* the iterated function space.
  let f : ℕ → Fin 3 → Fin 3 → ℝ := fun n => (g n : Matrix (Fin 3) (Fin 3) ℝ)
  -- The bounded-entry box is compact (a finite product of compact intervals).
  have hbox : IsCompact (Set.pi Set.univ fun (_ : Fin 3) =>
      Set.pi Set.univ fun (_ : Fin 3) => Set.Icc (-B) B) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, f n ∈ (Set.pi Set.univ fun (_ : Fin 3) =>
      Set.pi Set.univ fun (_ : Fin 3) => Set.Icc (-B) B) := by
    intro n i _ j _
    exact abs_le.mp (hB n i j)
  -- Compactness gives a convergent subsequence.
  obtain ⟨M, _hM, φ, hφ, hlim⟩ := hbox.tendsto_subseq (x := f) hmem
  -- The limit is again special linear: `det` is continuous, and `det (g n) = 1` for all `n`.
  have hconst : (fun n => Matrix.det (f (φ n))) = fun _ => (1 : ℝ) := by
    funext n
    simp [f, Matrix.SpecialLinearGroup.det_coe]
  have hdet_lim : Filter.Tendsto (fun n => Matrix.det (f (φ n))) Filter.atTop
      (nhds (Matrix.det M)) := by
    have h1 : Continuous (fun M : Fin 3 → Fin 3 → ℝ => Matrix.det M) := by fun_prop
    exact (h1.tendsto M).comp hlim
  have hMdet : Matrix.det M = 1 := by
    rw [hconst] at hdet_lim
    exact (tendsto_nhds_unique tendsto_const_nhds hdet_lim).symm
  -- Assemble: convergence in the subtype `SL₃(ℝ)` is convergence of the underlying matrices.
  refine ⟨⟨M, hMdet⟩, φ, hφ, ?_⟩
  exact tendsto_subtype_rng.mpr hlim

end Work.EKLC8Core
