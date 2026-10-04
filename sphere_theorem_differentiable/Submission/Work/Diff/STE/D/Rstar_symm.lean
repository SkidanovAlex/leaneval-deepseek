import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.D.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D

theorem Rstar_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hsym : ∀ (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
      u a b z = u b a z)
    (p : M) (X Y : TangentSpace I p) :
    D.Rstar i u p X Y = D.Rstar i u p Y X := by
  -- `Rstar_apply` evaluates both sides as the same scalar coefficient times a double sum over the
  -- frame indices; the two arguments of the bilinear form enter as the two factors of the product,
  -- so the claim is the symmetry of the coefficient family `u` after exchanging the two indices.
  rw [Work.Diff.STE.B3.Rstar_apply D i u p X Y,
      Work.Diff.STE.B3.Rstar_apply D i u p Y X]
  congr 1
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro a _
  rw [hsym a x (Work.Diff.STE.coord (I := I) (D.x₀ i) p)]
  ring

end Work.Diff.STE.D
