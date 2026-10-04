import Mathlib
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

theorem Rstar_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (p : M) (X Y : TangentSpace I p) :
    D.Rstar i u p X Y
      = (D.ζ i p * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)
          * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)))⁻¹)
        * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            u a b (Work.Diff.STE.coord (I := I) (D.x₀ i) p)
              * g₀.inner p X (D.e i a p) * g₀.inner p Y (D.e i b p)) := by
  -- `Rstar` is built from `smulRight`s of the `g₀.inner p (e a p)`-functionals; evaluating the
  -- resulting bilinear form at `(X, Y)` is a pure computation.  The only input beyond
  -- bilinearity is the symmetry of the metric, which swaps the two arguments of `g₀.inner`.
  have hX : ∀ a : Fin (Module.finrank ℝ E),
      ((g₀.inner p) (D.e i a p)) X = ((g₀.inner p) X) (D.e i a p) :=
    fun a => g₀.symm p _ _
  have hY : ∀ b : Fin (Module.finrank ℝ E),
      ((g₀.inner p) (D.e i b p)) Y = ((g₀.inner p) Y) (D.e i b p) :=
    fun b => g₀.symm p _ _
  simp only [Work.Diff.STE.B3Data.Rstar]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, hX, hY]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  ring

end Work.Diff.STE.B3
