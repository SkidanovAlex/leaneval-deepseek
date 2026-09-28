import Submission.Work.Stems.Hur2c.Defs
import Submission.Work.Stems.Cubical.CubeFace

/-!
# A based cube is a cubical cycle (all degrees)

Generalisation to all degrees of the two lemmas proved for `Fin 2` in
`Submission/Work/Stems/Hur2c/hurewiczMapN_two_injective.lean`
(`faceCube_based_const`, `cubD_single_based`): a face of a *based* cube is the constant cube at the
base point, hence every face-pair in the cubical boundary cancels and a based cube is a cycle.

These are the chain-level inputs of the general-degree Hurewicz argument
(`Work.Stems.Hur2c.hurewiczMapN_injective_of_degen_cycle`): they show that the degenerate chain
produced by the bridge `Work.RatHurewicz.cubicalBridgeDeg` really is a *cycle*, which is what lets
`Ψ` annihilate it.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.Hur2c

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- A face of a *based* cube is the constant cube at the base point. -/
theorem faceCube_based_const {n : ℕ} {x₀ : X} (p : GenLoop (Fin (n + 1)) X x₀)
    (i : Fin (n + 1)) (b : unitInterval) (hb : b = 0 ∨ b = 1) :
    faceCube i b p.1 = ContinuousMap.const (IC n) x₀ := by
  ext t
  refine p.2 (faceCM i b t) ?_
  rw [Cube.boundary]
  rcases hb with rfl | rfl
  · exact ⟨i, Or.inl (faceCM_frozen i 0 t)⟩
  · exact ⟨i, Or.inr (faceCM_frozen i 1 t)⟩

/-- **A based cube is a cubical cycle.** -/
theorem cubD_single_based {n : ℕ} (x₀ : X) (p : GenLoop (Fin (n + 1)) X x₀) :
    cubD n X (Finsupp.single p.1 1) = 0 := by
  rw [cubD_single]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [faceCube_based_const p i 0 (Or.inl rfl), faceCube_based_const p i 1 (Or.inr rfl),
    sub_self, smul_zero]

end

end Work.Stems.Hur2c
