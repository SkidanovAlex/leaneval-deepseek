import Mathlib
import Submission.Work.Diff.STE.Man.Sect

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Bundle ContDiff Set
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace Work.Diff.STE.fill

/-- **Expansion of a bilinear form on two finite sums.**  If `e` and `g` are finite families of
tangent vectors and `c`, `d` finite families of scalars, then a continuous bilinear form `f`
evaluated on `∑ i, c i • e i` and `∑ j, d j • g j` is the double sum of `(c i * d j) * f (e i) (g j)`. -/
lemma clm_apply_sum_smul_sum_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {p : M} {n m : ℕ} (f : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)
    (c : Fin n → ℝ) (e : Fin n → TangentSpace I p) (d : Fin m → ℝ)
    (g : Fin m → TangentSpace I p) :
    f (∑ i, c i • e i) (∑ j, d j • g j) = ∑ i, ∑ j, (c i * d j) * f (e i) (g j) := by
  rw [map_sum]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The chart matrix computes a section of `Sym² T*M`.**  If `p` lies in the base set of the
tangent-bundle trivialisation at `x₀`, then the value of a pointwise bilinear form `h` on two
tangent vectors `u`, `v` is the double sum of the chart matrix `bilChart h x₀` evaluated at the
chart image of `p`, contracted with the coordinates of `u` and `v` in the trivialisation at `x₀`
(read in the basis `Module.finBasis ℝ E`). -/
theorem bil_apply_eq_sum_bilChart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ p : M)
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (u v : TangentSpace I p) :
    h p u v = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      Work.Diff.STE.bilChart h x₀ a b ((extChartAt I x₀) p)
        * (((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p u)) a)
        * (((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p v)) b) := by
  classical
  -- `p` lies in the chart at `x₀`, so the chart is a two-sided inverse there
  have hpsrc : p ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]
    rw [TangentBundle.trivializationAt_baseSet (I := I) x₀] at hp
    exact hp
  have hsymm : (extChartAt I x₀).symm ((extChartAt I x₀) p) = p :=
    (extChartAt I x₀).left_inv hpsrc
  -- the chart matrix at the coordinate point is `h` on the frame vectors there
  have hX : ∀ a b : Fin (Module.finrank ℝ E),
      h p (Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E a))
        (Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E b))
      = Work.Diff.STE.bilChart h x₀ a b ((extChartAt I x₀) p) := by
    intro a b
    rw [Work.Diff.STE.bilChart, hsymm]
  -- the expansion of `u` in the frame of the trivialisation at `x₀`
  have hu : u = ∑ a : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p u)) a
        • Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E a) := by
    conv_lhs =>
      rw [← Trivialization.symmₗ_linearMapAt (R := ℝ) (trivializationAt E (TangentSpace I) x₀) hp u,
          ← Module.Basis.sum_repr (Module.finBasis ℝ E)
              ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p u)]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_smul]
    rfl
  -- the expansion of `v`
  have hv : v = ∑ a : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p v)) a
        • Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E a) := by
    conv_lhs =>
      rw [← Trivialization.symmₗ_linearMapAt (R := ℝ) (trivializationAt E (TangentSpace I) x₀) hp v,
          ← Module.Basis.sum_repr (Module.finBasis ℝ E)
              ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p v)]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_smul]
    rfl
  calc h p u v
      = h p (∑ a : Fin (Module.finrank ℝ E),
              ((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p u)) a
                • Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E a))
            (∑ b : Fin (Module.finrank ℝ E),
              ((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p v)) b
                • Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E b)) := by
          conv_lhs => rw [hu, hv]
    _ = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p u)) a
            * ((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p v)) b)
          * h p (Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E a))
                (Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E b)) :=
          clm_apply_sum_smul_sum_smul (h p) _ _ _ _
    _ = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      Work.Diff.STE.bilChart h x₀ a b ((extChartAt I x₀) p)
        * (((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p u)) a)
        * (((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p v)) b) := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
          rw [hX a b]
          ring

end Work.Diff.STE.fill
