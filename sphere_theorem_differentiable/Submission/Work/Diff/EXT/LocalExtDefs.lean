import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.metric_equiv_of_ric_bound
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `EXT` area: the interface vocabulary of the local-extension step

The definitions of the iterated covariant derivatives of the curvature (`covKRmExt`, `covKRmC`,
`curvNormK`) and of the four interfaces of the local-extension argument (`ChartBounds`,
`NormSmoothK`, `EvolK`, `ShiBounds`) live here, in their own module, so that the modules which
*prove* the corresponding facts can import them without creating an import cycle with the module
carrying the target `Work.Diff.EXT.local_ext_of_bounded_curv` (which imports those proofs in turn).
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The geometric vocabulary: iterated covariant derivatives of the curvature -/

/-- The `k`-th covariant derivative of the curvature, as a function on smooth fields. -/
noncomputable def covKRmExt (g : SMet I M) :
    ∀ k : ℕ, (Fin k → (Π y : M, TangentSpace I y)) →
      (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) →
      (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) → M → ℝ
  | 0, _, A, B, C, D => fun y => rmP g y (A y) (B y) (C y) (D y)
  | k + 1, v, A, B, C, D => fun x =>
      mvfderiv I (covKRmExt g k (fun i : Fin k => v i.succ) A B C D) x (v 0 x)
        - (∑ i : Fin k, covKRmExt g k
            (Function.update (fun j : Fin k => v j.succ) i
              (fun y => lcOf g (v i.succ) y (v 0 y))) A B C D x)
        - covKRmExt g k (fun i : Fin k => v i.succ)
            (fun y => lcOf g A y (v 0 y)) B C D x
        - covKRmExt g k (fun i : Fin k => v i.succ) A
            (fun y => lcOf g B y (v 0 y)) C D x
        - covKRmExt g k (fun i : Fin k => v i.succ) A B
            (fun y => lcOf g C y (v 0 y)) D x
        - covKRmExt g k (fun i : Fin k => v i.succ) A B C
            (fun y => lcOf g D y (v 0 y)) x

/-- The components of `∇^k Rm` at `x` in a frame `e`. -/
noncomputable def covKRmC (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (k : ℕ) :
    (Fin k → Fin (Module.finrank ℝ E)) → Curv4 (Module.finrank ℝ E) :=
  fun ι i j l m =>
    covKRmExt g k (fun s : Fin k => smoothExt x (e (ι s)))
      (smoothExt x (e i)) (smoothExt x (e j)) (smoothExt x (e l)) (smoothExt x (e m)) x

/-- `|∇^k Rm|²` at `x`, computed in the chosen orthonormal frame `onFrame g x`. -/
noncomputable def curvNormK (g : SMet I M) (x : M) (k : ℕ) : ℝ :=
  let e := onFrame g x
  ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
    (covKRmC g x e k ι i j l m) ^ 2

/-- **The a priori chart bounds.**  In a neighbourhood of every point of `M` the chart matrix of
`G t` is uniformly bounded in `C^k` for every `k`, uniformly for `t ∈ [σ,T)`. -/
def ChartBounds (G : ℝ → SMet I M) (σ T : ℝ) : Prop :=
  ∀ x₀ : M, ∃ U : Set E, IsOpen U ∧ (extChartAt I x₀) x₀ ∈ U ∧
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Set.Ico σ T, ∀ y ∈ U,
        ‖iteratedFDeriv ℝ k (fun y' : E ↦ chartMat G x₀ t y') y‖ ≤ C

/-! ## Interfaces for the analytic core (Shi's a priori estimates) -/

/-- The `k`-th geometric norm of the curvature is jointly smooth along a Ricci flow. -/
def NormSmoothK : Prop :=
  ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ k : ℕ,
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ curvNormK (G p.1) p.2 k) (Set.Ico 0 T ×ˢ Set.univ)

/-- The evolution inequality for the `k`-th geometric norm of the curvature. -/
def EvolK : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 ≤ c ∧
    ∀ (A : ℕ → ℝ) (_hA : ∀ i, i ≤ k → 0 ≤ A i) (G : ℝ → SMet I M) (σ T : ℝ)
      (hflow : IsRicciFlow G T) (_hσT : σ < T)
      (_hlow : ∀ i, i < k → ∀ t ∈ Set.Ico σ T, ∀ x : M, curvNormK (G t) x i ≤ A i),
      ∀ t ∈ Set.Ico σ T, ∀ x : M,
        ∃ D : ℝ, HasDerivWithinAt (fun s ↦ curvNormK (G s) x k) D (Set.Ico 0 T) t ∧
          D ≤ laplAt (G t) (fun x : M ↦ curvNormK (G t) x k) x
              + c * (1 + Finset.sum (Finset.range k) (fun i => A i)) * curvNormK (G t) x k
              + c * (1 + Finset.sum (Finset.range k) (fun i => A i))

/-- **Shi's a priori estimate** (geometric form). -/
def ShiBounds : Prop :=
  ∀ (G : ℝ → SMet I M) (T C σ : ℝ), 0 < T → IsRicciFlow G T →
    (∀ t ∈ Set.Ico 0 T, CurvBound (G t) C) → 0 < σ → σ < T →
    ∀ k : ℕ, ∃ Ck : ℝ, ∀ t ∈ Set.Ico σ T, ∀ x : M, curvNormK (G t) x k ≤ Ck

end Work.Diff.EXT
