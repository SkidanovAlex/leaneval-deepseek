import Mathlib
import Submission.Work.Diff.GE.onFrameONfield

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Evol

theorem isONFrame_sum_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (y : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hB : Submission.Diff.IsONFrame g y B)
    (Q : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (hQ : ∀ i k, ∑ j, Q i j * Q k j = if i = k then 1 else 0) :
    Submission.Diff.IsONFrame g y (fun i => ∑ j, Q i j • B j) := by
  intro i k
  have key : ∀ a b, g.inner y (B a) (B b) = if a = b then 1 else 0 := hB
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, key, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← hQ i k]
  exact Finset.sum_congr rfl fun x _ => by ring

end Work.Diff.Evol
