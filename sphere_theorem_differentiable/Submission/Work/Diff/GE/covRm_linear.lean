import Mathlib
import Submission.Work.Diff.GE.kato_covRm_multilinear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multilinearity of the frozen `covRm` in its five arguments

The frozen `Submission.Diff.covRm` computes the components `(∇_v Rm)(a,b,c,d)` of the covariant
derivative of the curvature via `Classical.epsilon`-chosen smooth extensions of the five vectors,
so its value on a linear combination of the vectors `e p` is the corresponding five-fold sum of its
values on the `e p`.

The general form (an arbitrary coefficient family `c : Fin 5 → Fin n → ℝ`) is proved in
`Work.Diff.GE.kato_covRm_multilinear`, which assembles the five single-slot linearities
(`Work.Diff.GE.covRm_linear_snd`, `covRm_linear_thd`, `covRm_linear_fth`, `Kato3.covRm_linear_fith`
and the direction-slot additivity of the defining `mvfderiv`/`lcOf`) into the nested finite-sum
expansion.  Here we specialise the coefficient family to the rows `A m, A i, A j, A k, A l` of a
matrix `A`, which is the form in which the frame-independence of `|∇Rm|²` consumes it.
-/

set_option maxHeartbeats 800000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
theorem covRm_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hLC : LCSmooth I M)
    (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (m i j k l : Fin (Module.finrank ℝ E)) :
    covRm g x (∑ p, A m p • e p) (∑ p, A i p • e p) (∑ p, A j p • e p)
        (∑ p, A k p • e p) (∑ p, A l p • e p)
      = ∑ p, ∑ q, ∑ r, ∑ s, ∑ u,
          A m p * A i q * A j r * A k s * A l u *
            covRm g x (e p) (e q) (e r) (e s) (e u) := by
  -- the coefficient family of the general multilinearity statement: the five rows of `A`
  let c : Fin 5 → Fin (Module.finrank ℝ E) → ℝ :=
    Fin.cases (A m) (Fin.cases (A i) (Fin.cases (A j) (Fin.cases (A k)
      (Fin.cases (A l) (fun _ => A l)))))
  have hc0 : c 0 = A m := rfl
  have hc1 : c 1 = A i := rfl
  have hc2 : c 2 = A j := rfl
  have hc3 : c 3 = A k := rfl
  have hc4 : c 4 = A l := rfl
  have h := kato_covRm_multilinear (I := I) (M := M) hLC g x e c
  rw [hc0, hc1, hc2, hc3, hc4] at h
  exact h

end Work.Diff.GE
