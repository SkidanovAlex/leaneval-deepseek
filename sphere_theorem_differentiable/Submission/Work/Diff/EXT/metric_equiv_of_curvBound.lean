import Mathlib
import Submission.Work.Diff.EXT.metric_equiv_of_ric_bound
import Submission.Work.Diff.EXT.ric_bound_of_curvBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Metric equivalence along a Ricci flow with a bound on the curvature components

The final metric estimate of the continuation / Shi-estimate step of Brendle–Schoen: if `G` is a
smooth Ricci flow on `[0,T)` all of whose curvature components in `g`-orthonormal frames are bounded
by `C`, then the metrics at different times are uniformly equivalent,
`g(t) ≤ e^{2λt} g(0)` and `g(0) ≤ e^{2λt} g(t)` with `λ = (finrank ℝ E) · C`.

The proof is the composition of the two halves of the classical argument.

* `Work.Diff.EXT.ric_bound_of_curvBound`: a bound `C` on the curvature components in orthonormal
  frames bounds the Ricci tensor by `|Ric(u,v)| ≤ (finrank ℝ E) · C · ‖u‖ · ‖v‖`; on the diagonal
  `u = v` this is `|Ric(w,w)| ≤ (finrank ℝ E) · C · g(w,w)`.
* `Work.Diff.EXT.metric_equiv_of_ric_bound`: if `|Ric(w,w)| ≤ λ g(w,w)` then, since
  `∂ₜ g = -2 Ric`, the Grönwall-type estimate `e^{-λt} g(0) ≤ g(t) ≤ e^{λt} g(0)` holds in the
  sharp form `g(t) ≤ e^{2λt} g(0)`, `g(0) ≤ e^{2λt} g(t)`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

theorem metric_equiv_of_curvBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C) :
    ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u := by
  have hC' : 0 ≤ (Module.finrank ℝ E : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC
  -- It is enough to bound `|Ric(u,u)|` by `λ · g(u,u)` with `λ = (finrank ℝ E) * C`.
  refine metric_equiv_of_ric_bound G T ((Module.finrank ℝ E : ℝ) * C) hT hC' hflow ?_
  intro s hs x u
  have h := ric_bound_of_curvBound (g := G s) hC (hbound s hs) x u u
  have hnn : 0 ≤ (G s).inner x u u := by
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · exact le_of_lt ((G s).pos x u hu)
  have hsq : Real.sqrt ((G s).inner x u u) * Real.sqrt ((G s).inner x u u)
      = (G s).inner x u u :=
    Real.mul_self_sqrt hnn
  calc |Submission.Diff.ricAt (Submission.Diff.lcOf (G s)) x u u|
      ≤ ((Module.finrank ℝ E : ℝ) * C * Real.sqrt ((G s).inner x u u))
          * Real.sqrt ((G s).inner x u u) := h
    _ = (Module.finrank ℝ E : ℝ) * C * (G s).inner x u u := by rw [mul_assoc, hsq]

end Work.Diff.EXT
