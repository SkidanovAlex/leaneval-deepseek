import Mathlib
import Submission.Work.Diff.GE.bianchi_kato_defs
import Submission.Work.Diff.GE.curvVec_bianchi_nb
import Submission.Work.Diff.GE.curvVec_pair_exchange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.CurvatureVec

/-- The curvature components of the Levi-Civita connection of `g` in an *arbitrary* frame satisfy
the algebraic curvature identities: `rmFrame g x e : Curv4 n` is an `IsAlgCurv` array.
The three components are the seeded symmetries of `curvVec` (transport of `R` through
`rmVec_eq_curvVec`): antisymmetry in the first pair (`curvVec_antisymm`), antisymmetry in the last
pair and pair symmetry (`inner_curvVec_skew`, `inner_curvVec_pair_symm`, both using metric
compatibility) and the first Bianchi identity (`curvVec_bianchi`, using torsion-freeness). -/
theorem isAlgCurv_rmFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (htor : (lcOf g).torsion = 0)
    (hmet : MetricCompat g) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    IsAlgCurv (rmFrame g x e) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- the metric `g.inner` of the interfaces is the instance inner product
  have hbridge : ∀ X Y : TangentSpace I x, g.inner x X Y = inner ℝ X Y := fun X Y => rfl
  -- the frame components of `rmFrame` are the pairings of the tensor `curvVec`
  have hframe : ∀ i j k l, rmFrame g x e i j k l
      = inner ℝ (curvVec (lcOf g) x (e i) (e j) (e l)) (e k) := by
    intro i j k l
    show g.inner x (rmVec (lcOf g) x (e i) (e j) (e l)) (e k) = _
    rw [rmVec_eq_curvVec_lcOf g hcov x (e i) (e j) (e l)]
    exact hbridge _ _
  -- the four algebraic facts about `S a b c d = ⟪R(a,b)c, d⟫`
  have h1 : ∀ a b c d : TangentSpace I x,
      inner ℝ (curvVec (lcOf g) x b a c) d = -inner ℝ (curvVec (lcOf g) x a b c) d := by
    intro a b c d
    rw [curvVec_antisymm (lcOf g) hcov x b a c, inner_neg_left]
  have h2 : ∀ a b c d : TangentSpace I x,
      inner ℝ (curvVec (lcOf g) x a b c) d = -inner ℝ (curvVec (lcOf g) x a b d) c := by
    intro a b c d
    rw [inner_curvVec_skew (lcOf g) hcov hmet x a b c d,
      real_inner_comm c (curvVec (lcOf g) x a b d)]
  have h3 : ∀ a b c d : TangentSpace I x,
      inner ℝ (curvVec (lcOf g) x a b c) d + inner ℝ (curvVec (lcOf g) x b c a) d
        + inner ℝ (curvVec (lcOf g) x c a b) d = 0 := by
    intro a b c d
    have hb := curvVec_bianchi_nb (lcOf g) hcov htor x a b c
    have h := congrArg (fun z : TangentSpace I x => inner ℝ z d) hb
    simp only [inner_add_left, inner_zero_left] at h
    linarith
  have h4 : ∀ a b c d : TangentSpace I x,
      inner ℝ (curvVec (lcOf g) x a b c) d = inner ℝ (curvVec (lcOf g) x c d a) b :=
    fun a b c d => curvVec_pair_exchange (lcOf g) hcov htor hmet x a b c d
  -- assembly: the three components of `IsAlgCurv` in terms of `hframe`
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    rw [hframe j i k l, hframe i j k l]
    exact h1 (e i) (e j) (e l) (e k)
  · intro i j k l
    have A := h4 (e k) (e l) (e j) (e i)
    have B := h1 (e j) (e i) (e k) (e l)
    have C := h2 (e i) (e j) (e k) (e l)
    rw [hframe k l i j, hframe i j k l]
    linarith
  · intro i j k l
    have A := h3 (e i) (e j) (e l) (e k)
    have B := h4 (e j) (e k) (e l) (e i)
    have C := h4 (e k) (e i) (e l) (e j)
    have D := h1 (e l) (e j) (e k) (e i)
    have F := h2 (e j) (e l) (e k) (e i)
    rw [hframe i j k l, hframe j k i l, hframe k i j l]
    linarith

end Work.Diff.GE
