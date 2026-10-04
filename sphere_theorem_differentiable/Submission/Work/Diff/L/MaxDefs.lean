import Mathlib
import Submission.Diff.Interfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Maximal existence time of the Ricci flow: shared definitions

This module sets up the vocabulary of the maximal-time argument for the Ricci flow that
`Work.Diff.L.maximal_flow` carries out (and that the delegated lemmas
`Work.Diff.L.flow_package_mono` and `Work.Diff.L.chain_union` speak about).

A *flow package* is a pair `(T, G)` consisting of a time `T > 0` and a family of smooth metrics
`G : ℝ → SMet I M` such that `G` is a Ricci flow on `[0, T)`, starts at `g₀`, and whose curvature
stays in the set `F` on `[0, T)`.

Packages are ordered by *extension*: `q` extends `p` when `q` lives at least as long and restricts
to `p` on `[0, p.1)`.  With this order the maximal elements are exactly the "maximal flows", and
they are produced by Zorn's lemma; the two lemmas above are the ingredients of that application.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.L

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-- `q` extends the flow `p`: `q` exists at least as long as `p` and agrees with it on `[0, p.1)`. -/
def FlowExtends (p q : ℝ × (ℝ → SMet I M)) : Prop :=
  p.1 ≤ q.1 ∧ ∀ t ∈ Set.Ico 0 p.1, q.2 t = p.2 t

/-- A *flow package*: a time `T > 0` and a Ricci flow `G` on `[0, T)` with `G 0 = g₀` whose
curvature lies in `F` throughout. -/
def IsFlowPackage (g₀ : SMet I M) (F : Set (Curv4 (Module.finrank ℝ E)))
    (p : ℝ × (ℝ → SMet I M)) : Prop :=
  0 < p.1 ∧ IsRicciFlow p.2 p.1 ∧ p.2 0 = g₀ ∧ ∀ t ∈ Set.Ico 0 p.1, CurvIn (p.2 t) F

/-- The type of flow packages, ordered by extension. -/
def FlowPackage (g₀ : SMet I M) (F : Set (Curv4 (Module.finrank ℝ E))) :=
  {p : ℝ × (ℝ → SMet I M) // IsFlowPackage g₀ F p}

/-- Extension is a preorder on flow packages. -/
instance instPreorderFlowPackage (g₀ : SMet I M) (F : Set (Curv4 (Module.finrank ℝ E))) :
    Preorder (FlowPackage g₀ F) where
  le p q := FlowExtends p.1 q.1
  le_refl p := ⟨le_refl p.1.1, fun t _ => rfl⟩
  le_trans p q r hpq hqr :=
    ⟨le_trans hpq.1 hqr.1,
      fun t ht => (hqr.2 t ⟨ht.1, lt_of_lt_of_le ht.2 hpq.1⟩).trans (hpq.2 t ht)⟩
  lt p q := FlowExtends p.1 q.1 ∧ ¬ FlowExtends q.1 p.1

@[simp] lemma flowPackage_le_iff {g₀ : SMet I M} {F : Set (Curv4 (Module.finrank ℝ E))}
    (p q : FlowPackage g₀ F) : p ≤ q ↔ FlowExtends p.1 q.1 := Iff.rfl

lemma flowExtends_refl (p : ℝ × (ℝ → SMet I M)) : FlowExtends p p :=
  ⟨le_refl p.1, fun _ _ => rfl⟩

lemma flowExtends_trans {p q r : ℝ × (ℝ → SMet I M)} (hpq : FlowExtends p q)
    (hqr : FlowExtends q r) : FlowExtends p r :=
  ⟨le_trans hpq.1 hqr.1,
    fun t ht => (hqr.2 t ⟨ht.1, lt_of_lt_of_le ht.2 hpq.1⟩).trans (hpq.2 t ht)⟩

end Work.Diff.L
