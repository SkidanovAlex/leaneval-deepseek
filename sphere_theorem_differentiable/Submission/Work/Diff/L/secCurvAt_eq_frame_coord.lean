import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.Stmt
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.L.secK_rmFrame_eq_inner

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]

/-! ## Parseval in a `g`-orthonormal frame

The coordinates `i ↦ g.inner x (e i) ·` of a `g`-orthonormal frame preserve the scalar product, so
the coordinates of a `g`-orthonormal pair of vectors form an orthonormal pair of vectors of `ℝⁿ`.
These are the two statements `dot_coord_eq`/`isONPair_coord` of `Work.Diff.L.pinched_of_frame`,
reproved here so that this module does not depend on that (partially `sorry`-ed) file. -/

/-- **Parseval in a `g`-orthonormal frame.**  `∑ i, g.inner x (e i) a * g.inner x (e i) b =
g.inner x a b`. -/
private lemma coord_dot_eq (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (a b : TangentSpace I x) :
    (∑ i, g.inner x (e i) a * g.inner x (e i) b) = g.inner x a b := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    exact he i j
  have hsum : ∀ c : TangentSpace I x, (∑ i, g.inner x (e i) c • e i) = c :=
    fun c => Work.Diff.GE.sum_inner_smul_eq_self g x hn e he c
  have h := Orthonormal.inner_sum hon (fun i => g.inner x (e i) a)
    (fun i => g.inner x (e i) b) Finset.univ
  calc (∑ i, g.inner x (e i) a * g.inner x (e i) b)
      = ∑ i, (starRingEnd ℝ) (g.inner x (e i) a) * g.inner x (e i) b :=
        Finset.sum_congr rfl (fun i _ => by simp)
    _ = inner ℝ (∑ i, g.inner x (e i) a • e i) (∑ i, g.inner x (e i) b • e i) := h.symm
    _ = inner ℝ a b := by rw [hsum a, hsum b]
    _ = g.inner x a b := rfl

/-- **Coordinates of an orthonormal pair.**  The coordinates `u' i = g.inner x (e i) u`,
`v' i = g.inner x (e i) v` of a `g`-orthonormal pair `u, v` form an orthonormal pair of vectors of
`ℝⁿ`. -/
private lemma coord_isONPair (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (a b : TangentSpace I x) (ha : g.inner x a a = 1) (hb : g.inner x b b = 1)
    (hab : g.inner x a b = 0) :
    IsONPair (fun i => g.inner x (e i) a) (fun i => g.inner x (e i) b) :=
  ⟨(coord_dot_eq g x hn e he a a).trans ha, (coord_dot_eq g x hn e he b b).trans hb,
    (coord_dot_eq g x hn e he a b).trans hab⟩

/-- **The sectional curvature of a `g`-orthonormal pair is a frame component of the coordinate
vectors.**  For a `g`-orthonormal frame `e` at `x` and a `g`-orthonormal pair `u, v` at `x`, there is
an *orthonormal pair* `u', v'` of coefficient vectors with
`secCurvAt g x u v = secK (rmFrame g x e) u' v'` — namely the coordinates
`u' i = g.inner x (e i) u`, `v' i = g.inner x (e i) v`.

This transfers bounds on the sectional curvatures of the frame component array
(`Work.Diff.L.rmFrame_pinched_bounds`) to bounds on the intrinsic quantity `secCurvAt`, which is what
`Work.Diff.L.spread_scalar` consumes.

Route.  The coordinates satisfy `IsONPair` by Parseval (`∑ i, g.inner x (e i) a * g.inner x (e i) b =
g.inner x a b`, see `dot_coord_eq`/`isONPair_coord` in `Work.Diff.L.pinched_of_frame`, using
`Work.Diff.GE.sum_inner_smul_eq_self`), and the identity is the multilinearity of `rmVec`
(`Work.Diff.GE.rmVec_sum_left/middle/right`) together with the bilinearity of `g.inner` and the
expansion `u = ∑ i, g.inner x (e i) u • e i`.  If
`Submission.Work.Diff.L.secK_rmFrame_eq_inner` builds, it already provides the needed identity; if not,
prove it inline (do not import a module that fails to build). -/
theorem secCurvAt_eq_frame_coord
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [T2Space M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    {g : Submission.Diff.SMet I M}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g)
      (((⊤ : ℕ∞) : WithTop ℕ∞)))
    (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e)
    (u v : TangentSpace I x) (hu : g.inner x u u = 1) (hv : g.inner x v v = 1)
    (huv : g.inner x u v = 0) :
    ∃ u' v' : Fin (Module.finrank ℝ E) → ℝ, Submission.Diff.Alg.IsONPair u' v' ∧
      Work.Diff.L.secCurvAt g x u v
        = Submission.Diff.Alg.secK (Submission.Diff.rmFrame g x e) u' v' := by
  have hn : 0 < Module.finrank ℝ E := by omega
  refine ⟨fun i => g.inner x (e i) u, fun i => g.inner x (e i) v, ?_, ?_⟩
  · exact coord_isONPair g x hn e he u v hu hv huv
  · -- The frame-component identity expands `secK` in the coordinates, and the expansion of `u`, `v`
    -- in the orthonormal frame turns `secCurvAt` into exactly the same expression.
    have hkey : secK (rmFrame g x e) (fun i => g.inner x (e i) u) (fun i => g.inner x (e i) v)
        = g.inner x (rmVec (lcOf g) x (∑ i, g.inner x (e i) u • e i)
              (∑ i, g.inner x (e i) v • e i) (∑ i, g.inner x (e i) v • e i))
            (∑ i, g.inner x (e i) u • e i) :=
      secK_rmFrame_eq_inner g x e hcov (fun i => g.inner x (e i) u) (fun i => g.inner x (e i) v)
    have huE : (∑ i, g.inner x (e i) u • e i) = u :=
      Work.Diff.GE.sum_inner_smul_eq_self g x hn e he u
    have hvE : (∑ i, g.inner x (e i) v • e i) = v :=
      Work.Diff.GE.sum_inner_smul_eq_self g x hn e he v
    rw [hkey]
    -- Expand `u` and `v` in the *left* side only: rewriting without `conv` would also rewrite
    -- the occurrences of `u`, `v` inside the sums on the right.
    unfold secCurvAt
    conv_lhs => rw [← huE, ← hvE]

end Work.Diff.L
