import Mathlib
import Submission.Work.Diff.STE.B3.SupBound
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame
import Submission.Work.Diff.STE.fill.bil_apply_eq_sum_bilChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the reconstruction of a section from its chart matrix, and the periodisation identity

Two ingredients of the Layer B3 pointwise control:

* `B3Data.Rper_eq_R`: on the fundamental cube the periodisation of a localised component is the
  localised component itself (its support lies in the open cube);
* `B3Data.apply_eq_sum_mat`: at a point where the frame `e i` is `g₀`-orthonormal and the chart `i`
  is defined, a section `h` is the double sum of its chart matrix against the coefficients of `u`
  and `v` in that orthonormal frame, `h x u v = Σ_{ab} mat i h a b (coord i x) ⟨u, eᵢa⟩ ⟨v, eᵢb⟩`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

namespace B3Data

variable (D : B3Data (I := I) (M := M) ι₀ g₀)

/-- On the fundamental cube the periodisation of a localised component agrees with the component
itself. -/
lemma Rper_eq_R (i : ι₀) (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ∀ j, z j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    D.Rper i h a b z = ((D.R i h a b z : ℝ) : ℂ) := by
  have hsupp : Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i h a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro y hy
    exact D.R_support i h a b (by
      simpa only [Function.mem_support, Complex.ofReal_ne_zero] using hy)
  exact periodization_eq_self hsupp hz

/-- **Reconstruction of a section from its chart matrix.**  At a point `x` of the chart source of
`x₀ i` where the frame `e i` is `g₀`-orthonormal, the value of `h` on `u`, `v` is the double sum of
the chart matrix against the coefficients of `u` and `v` in that orthonormal frame. -/
theorem apply_eq_sum_mat (i : ι₀) (h : Bil (I := I) (M := M))
    {x : M} (hsrc : x ∈ (extChartAt I (D.x₀ i)).source)
    (hON : IsONFrame g₀ x (fun a => D.e i a x)) (u v : TangentSpace I x) :
    h x u v = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      D.mat i h a b (coord (I := I) (D.x₀ i) x)
        * g₀.inner x u (D.e i a x) * g₀.inner x v (D.e i b x) := by
  have hu : u = ∑ a : Fin (Module.finrank ℝ E),
      g₀.inner x u (D.e i a x) • D.e i a x :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g₀ x (fun a => D.e i a x) hON u).symm
  have hv : v = ∑ b : Fin (Module.finrank ℝ E),
      g₀.inner x v (D.e i b x) • D.e i b x :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g₀ x (fun a => D.e i a x) hON v).symm
  conv_lhs => rw [hu, hv]
  rw [Work.Diff.STE.fill.clm_apply_sum_smul_sum_smul (h x) _ _ _ _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hmat : D.mat i h a b (coord (I := I) (D.x₀ i) x)
      = h x (D.e i a x) (D.e i b x) := by
    simp only [mat]
    rw [D.pt_coord i hsrc]
  rw [hmat]
  ring

end B3Data

end Work.Diff.STE
