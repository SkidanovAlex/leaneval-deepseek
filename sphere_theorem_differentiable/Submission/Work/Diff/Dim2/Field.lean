import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.grad_smoothAt
import Submission.Work.Diff.C.rgrad_rdist_eikonal
import Submission.Work.Diff.Dim2.rgrad_rdist_ascent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `d = 2` branch: the global ascent field `V`

This file builds the global `C^∞` vector field `V` on the surface `M` which drives the whole
smooth-Reeb construction of `Work.Diff.Dim2.dim2_exists_local_diffeo`.

Requirements on `V` (with `f = rdist p`, `g = rdist q`, `a`, `γ` small constants):

* `V` is a globally smooth section of the tangent bundle;
* `V = rgrad (rdist p)` on the annulus `{a/4 ≤ f ≤ 3a/2}` (so that the flow lines there are the
  radial geodesics through `p`, which is what makes the map to the sphere smooth at `p`);
* `V = -rgrad (rdist q)` on `{γ/4 ≤ g ≤ 3γ/2}` (the same at `q`);
* `V` is an **ascent field** for `d(p,·)` on the whole slab `{a/4 ≤ f ≤ D - 2γ}`: this is what makes
  `f` strictly increasing along the flow there, and hence gives existence and uniqueness of the
  crossing time of the level `{f = a}`.

The construction is the partition-of-unity gluing of three pieces:

* `vbump χ · rgrad (rdist p)` — the radial field at `p`, cut off by a window `χ` in `f` which is
  `1` on `[a/4, 3a/2]` and `0` outside `(a/8, 2a)`.  The cut-off is what makes the product smooth at
  `p` (`rgrad (rdist p)` is not smooth there) and off `{f < v}`;
* `-χ' (g) · rgrad (rdist q)` — the same at `q`;
* the field produced by `Submission.GSGlobal2.exists_continuous_ascent_field_of_diam` on the compact
  set `{f ≥ 3a/2} ∩ {g ≥ γ}`, multiplied by the remaining weight `1 - χ(f) - χ'(g)`.

The last weight is `0` outside that compact set, so the glued field is smooth, and on the slab
`{a/4 ≤ f ≤ D - 2γ}` the two radial pieces and the middle piece are all ascent fields with
non-negative weights, so the result is an ascent field (`Submission.GSField.isAscentAt_add`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Dim2

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ## The window functions -/

/-- The smooth "window" `win a b c d`: it is `1` on `[b,c]` and `0` outside `(a,d)`. -/
noncomputable def win (a b c d : ℝ) : ℝ → ℝ :=
  fun r => Real.smoothTransition ((r - a) / (b - a)) * Real.smoothTransition ((d - r) / (d - c))

lemma win_smooth {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ContDiff ℝ ∞ (win a b c d) := by
  unfold win
  exact (Real.smoothTransition.contDiff.comp
      (contDiff_id.sub contDiff_const |>.div_const _)).mul
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub contDiff_id |>.div_const _))

lemma win_nonneg {a b c d : ℝ} (r : ℝ) : 0 ≤ win a b c d r := by
  unfold win
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma win_le_one {a b c d : ℝ} (r : ℝ) : win a b c d r ≤ 1 := by
  unfold win
  nlinarith [Real.smoothTransition.nonneg ((r - a) / (b - a)),
    Real.smoothTransition.le_one ((r - a) / (b - a)),
    Real.smoothTransition.nonneg ((d - r) / (d - c)),
    Real.smoothTransition.le_one ((d - r) / (d - c))]

lemma win_eq_one {a b c d r : ℝ} (h1 : a < b) (h2 : b ≤ r) (h3 : r ≤ c) (h4 : c < d) :
    win a b c d r = 1 := by
  have hb : 0 < b - a := sub_pos.mpr h1
  have hd : 0 < d - c := sub_pos.mpr h4
  have hr1 : 1 ≤ (r - a) / (b - a) := by
    rw [le_div_iff₀ hb]; linarith
  have hr2 : 1 ≤ (d - r) / (d - c) := by
    rw [le_div_iff₀ hd]; linarith
  unfold win
  rw [Real.smoothTransition.one_of_one_le hr1, Real.smoothTransition.one_of_one_le hr2, one_mul]

lemma win_eq_zero_of_le {a b c d r : ℝ} (h1 : a < b) (hr : r ≤ a) : win a b c d r = 0 := by
  have hb : 0 < b - a := sub_pos.mpr h1
  have hr' : (r - a) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hb)
  unfold win
  rw [Real.smoothTransition.zero_of_nonpos hr', zero_mul]

lemma win_eq_zero_of_ge {a b c d r : ℝ} (h4 : c < d) (hr : d ≤ r) : win a b c d r = 0 := by
  have hd : 0 < d - c := sub_pos.mpr h4
  have hr' : (d - r) / (d - c) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hd)
  unfold win
  rw [Real.smoothTransition.zero_of_nonpos hr', mul_zero]

end

section Reeb

/-- **The Reeb field data of the `d = 2` branch.**

`V` is the global smooth vector field driving the construction: it is the radial field at `p` on the
annulus `{a/4 ≤ d(p,·) ≤ 3a/2}`, the inward radial field at `q` on `{γ/4 ≤ d(q,·) ≤ 3γ/2}`, and it
is an ascent field for `d(p,·)` on the whole slab `{a/4 ≤ d(p,·) ≤ D - 2γ}`.

The last property is the one used by the level-crossing analysis: on that slab `d(p,·)` is strictly
increasing along the flow (`Submission.GSMono.strictMonoOn_flow`), which gives existence and
uniqueness of the crossing time of the level `{d(p,·) = a}`. -/
def IsReebField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (p q : M) (D a γ : ℝ)
    (V : (y : M) → TangentSpace I y) : Prop :=
  ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))) ∧
    (∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y ≤ 3 * a / 2 →
      V y = Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y) ∧
    (∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 3 * γ / 2 →
      V y = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z) y) ∧
    (∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y ≤ D - 2 * γ →
      Submission.GSField.IsAscentAt hmet p y (V y))

end Reeb

end Work.Diff.Dim2
