import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Pair exchange for the frozen curvature form `rmP`

`rmP g x a b c d = g.inner x (rmVec (lcOf g) x a b d) c` is the pairing `⟪R(a,b)d, c⟫` of the
pointwise Levi-Civita curvature of the metric `g` (`Submission/Diff/Grad.lean`).  This file proves
that it is invariant under exchanging the two index pairs,
`rmP g x a b c d = rmP g x c d a b` --- the "pair exchange" (also called the second algebraic
symmetry of the curvature tensor), an ingredient of the algebraic-array (Bianchi) calculus and of
the symmetry of the Ricci tensor.

The mathematical content is the standard derivation from the three elementary inputs, all available
for `rmVec` from the declared imports (with `cov = lcOf g`, `hLC` supplying smoothness,
torsion-freeness and metric compatibility):

* `Work.Diff.GE.rmVec_antisymm`   : `R(u,v)w = -R(v,u)w`                (antisymmetry, pair 1);
* `Work.Diff.GE.inner_rmVec_skew` : `⟪R(u,v)w, z⟫ = -⟪w, R(u,v)z⟫`      (skew-adjointness, pair 2);
* `Work.Diff.GE.rmVec_bianchi`    : `R(u,v)w + R(v,w)u + R(w,u)v = 0`   (first Bianchi identity).

Writing `S(u,v,w,z) := inner ℝ (rmVec (lcOf g) x u v w) z`, pairing Bianchi with `z` and applying
skew-adjointness twice produces the cyclic relation `S(u,v,w,z) = S(v,w,z,u) + S(w,u,z,v)`, and
applying that relation to both summands, then reducing the four resulting terms with the two
symmetries, gives `S(u,v,w,z) = 2 * S(w,z,u,v) - S(u,v,w,z)`, i.e. the pair exchange
`S(u,v,w,z) = S(w,z,u,v)`.  (`_private` since the statement is already available as
`Work.Diff.GE.curvVec_pair_exchange` / `Work.Diff.Evol.rmP_pair_exchange` in the sibling chains.)
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

private theorem rmVec_pair_exchange
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (g : SMet I M) (hcov : ContMDiffCovariantDerivative (lcOf g) ∞)
    (htor : (lcOf g).torsion = 0) (hmet : IsMetricCompatible (lcOf g))
    (x : M) (u v w z : TangentSpace I x) :
    inner ℝ (rmVec (lcOf g) x u v w) z = inner ℝ (rmVec (lcOf g) x w z u) v := by
  -- cyclic relation obtained by pairing the first Bianchi identity with `z`
  have hcyc : ∀ u v w z : TangentSpace I x,
      inner ℝ (rmVec (lcOf g) x u v w) z
        = inner ℝ (rmVec (lcOf g) x v w z) u + inner ℝ (rmVec (lcOf g) x w u z) v := by
    intro u v w z
    have hb := Work.Diff.GE.rmVec_bianchi (lcOf g) hcov htor x u v w
    have h := congrArg (fun t : TangentSpace I x => inner ℝ t z) hb
    simp only [inner_add_left, inner_zero_left] at h
    have h1 : inner ℝ (rmVec (lcOf g) x v w u) z = - inner ℝ (rmVec (lcOf g) x v w z) u := by
      rw [Work.Diff.GE.inner_rmVec_skew (lcOf g) hcov hmet x v w u z,
        real_inner_comm u (rmVec (lcOf g) x v w z)]
    have h2 : inner ℝ (rmVec (lcOf g) x w u v) z = - inner ℝ (rmVec (lcOf g) x w u z) v := by
      rw [Work.Diff.GE.inner_rmVec_skew (lcOf g) hcov hmet x w u v z,
        real_inner_comm v (rmVec (lcOf g) x w u z)]
    linarith
  -- the four instances of the cyclic relation needed below
  have k1 := hcyc u v w z
  have k2 := hcyc v w z u
  have k3 := hcyc w u z v
  have k4 := hcyc z v u w
  -- the two symmetries, in the shapes `linarith` consumes
  have hA2 : inner ℝ (rmVec (lcOf g) x z w v) u = - inner ℝ (rmVec (lcOf g) x w z v) u := by
    rw [Work.Diff.GE.rmVec_antisymm (lcOf g) hcov x z w v, inner_neg_left]
  have hB1 : inner ℝ (rmVec (lcOf g) x w z v) u = - inner ℝ (rmVec (lcOf g) x w z u) v := by
    rw [Work.Diff.GE.inner_rmVec_skew (lcOf g) hcov hmet x w z v u,
      real_inner_comm v (rmVec (lcOf g) x w z u)]
  have hA1 : inner ℝ (rmVec (lcOf g) x v u w) z = - inner ℝ (rmVec (lcOf g) x u v w) z := by
    rw [Work.Diff.GE.rmVec_antisymm (lcOf g) hcov x v u w, inner_neg_left]
  have hB2 : inner ℝ (rmVec (lcOf g) x u z w) v = - inner ℝ (rmVec (lcOf g) x u z v) w := by
    rw [Work.Diff.GE.inner_rmVec_skew (lcOf g) hcov hmet x u z w v,
      real_inner_comm w (rmVec (lcOf g) x u z v)]
  linarith

/-- Exchange of the two index pairs of the frozen curvature form `rmP`:
`rmP g x a b c d = rmP g x c d a b`, i.e. `⟪R(a,b)d, c⟫ = ⟪R(c,d)b, a⟫`. -/
theorem rmP_pair_symm2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (a b c d : TangentSpace I x) :
    Submission.Diff.rmP g x a b c d = Submission.Diff.rmP g x c d a b := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, htor, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  -- pair exchange in the form `⟪R(a,b)d, c⟫ = ⟪R(d,c)a, b⟫`
  have hpair := rmVec_pair_exchange (I := I) (M := M) g hcov htor hmet x a b d c
  -- `⟪R(d,c)a, b⟫ = ⟪R(c,d)b, a⟫` by antisymmetry in the first pair and skew-adjointness
  have hfin : inner ℝ (rmVec (lcOf g) x d c a) b = inner ℝ (rmVec (lcOf g) x c d b) a := by
    rw [Work.Diff.GE.rmVec_antisymm (lcOf g) hcov x d c a, inner_neg_left]
    rw [Work.Diff.GE.inner_rmVec_skew (lcOf g) hcov hmet x c d a b,
      real_inner_comm a (rmVec (lcOf g) x c d b)]
    ring
  simp only [Submission.Diff.rmP]
  change Inner.inner ℝ (rmVec (lcOf g) x a b d) c = Inner.inner ℝ (rmVec (lcOf g) x c d b) a
  rw [hpair, hfin]

end Work.EXT
