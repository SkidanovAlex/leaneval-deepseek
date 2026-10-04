import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exchange of the two index pairs of the frozen curvature form `rmP` (`EXT` area)

`Submission.Diff.rmP g x a b c d = g.inner x (rmVec (lcOf g) x a b d) c = ⟪R(a,b)d, c⟫` is the
pointwise curvature of the Levi-Civita connection of `g`, paired with its last argument.  The lemma
`rmP_pair_symm` below is the exchange of the two index pairs,

`⟪R(a,b)d, c⟫ = ⟪R(c,d)b, a⟫`,

i.e. the classical algebraic curvature symmetry `R_{abcd} = R_{cdab}`.  It is the one non-immediate
ingredient in the statement that the frame components `rmFrame g x e` of a Riemannian metric form an
*algebraic curvature array* (`Submission.Diff.Alg.IsAlgCurv`), the other components being
antisymmetry in the first pair, skew-adjointness in the last pair and the first Bianchi identity.
It is consumed by the `EXT` area (`Work.Diff.EXT.ric_bound_of_curvBound`), which needs the symmetry
`Ric(p,q) = Ric(q,p)` of the Ricci tensor.

## Mathematical content

Write `S(u,v,w,z) := ⟪R(u,v)w, z⟫`.  The three standard inputs, all available here for
`∇ = lcOf g` (`hLC g` supplies smoothness, torsion-freeness and metric compatibility) are

* antisymmetry in the first pair: `S(u,v,w,z) = -S(v,u,w,z)` (`Work.Diff.GE.rmVec_antisymm`);
* skew-adjointness in the last pair: `S(u,v,w,z) = -S(u,v,z,w)` (`Work.Diff.GE.inner_rmVec_skew`);
* the first Bianchi identity `R(u,v)w + R(v,w)u + R(w,u)v = 0` (`Work.Diff.GE.rmVec_bianchi`).

Pairing Bianchi with `z` and using skew-adjointness twice (on the two cyclic terms) gives the
cyclic relation

`(*)  S(u,v,w,z) = S(v,w,z,u) + S(w,u,z,v)`.

Expanding `S(u,v,w,z)` by `(*)`, applying `(*)` once more to each of the two summands, and reducing
the four resulting terms with antisymmetry (h1, h3) and skew-adjointness (h2, h4) yields

`S(u,v,w,z) = 2 * S(w,z,u,v) - S(u,v,w,z)`,

so `2 * S(u,v,w,z) = 2 * S(w,z,u,v)` and hence the pair exchange `S(u,v,w,z) = S(w,z,u,v)`
(characteristic `≠ 2`).  Applied to `(u,v,w,z) = (a,b,d,c)` this gives `S(a,b,d,c) = S(d,c,a,b)`,
and antisymmetry in the first pair followed by skew-adjointness in the last pair turns
`S(d,c,a,b)` into `S(c,d,b,a)`, which is the stated form `rmP g x a b c d = rmP g x c d a b`.

Model check on the unit round sphere, in an orthonormal frame `e₁,e₂`: with
`R(X,Y)Z = ⟪Y,Z⟫X - ⟪X,Z⟫Y` one gets `S(1,2,2,1) = 1 = S(2,1,1,2)` and
`S(1,2,1,2) = -1 = S(2,1,2,1)`, so the statement is neither vacuous nor a restatement of
antisymmetry.

The bridge from `rmVec` to the `g.inner`-form used by `rmP` is the definitional identity
`Inner.inner ℝ = g.inner x` for the instance `⟨g.toRiemannianMetric⟩`.

## Imports

This file is built on the `Submission.Work.Diff.GE.curvbasic` / `Submission.Work.Diff.GE.Frame`
chain, which is the chain used by the other `EXT` modules.  The sibling chain
`Submission.Work.Diff.GE.bianchi_kato_defs` / `...curvVec_pair_exchange` redeclares
`Work.Diff.GE.exists_isONFrame`, `Work.Diff.GE.onFrame_eq_...` and `Work.Diff.GE.rmVec_eq_curvVec`,
so the two chains cannot both be imported.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.EXT

theorem rmP_pair_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (a b c d : TangentSpace I x) :
    Submission.Diff.rmP g x a b c d = Submission.Diff.rmP g x c d a b := by
  -- work with the metric `g` installed as the instance metric
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, htor, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  -- (A) antisymmetry in the first pair
  have hAsym : ∀ u v w z : TangentSpace I x,
      inner ℝ (rmVec (lcOf g) x u v w) z = - inner ℝ (rmVec (lcOf g) x v u w) z := by
    intro u v w z
    rw [Work.Diff.GE.rmVec_antisymm (lcOf g) hcov x u v w, inner_neg_left]
  -- (B) skew-adjointness in the last pair
  have hSkew : ∀ u v w z : TangentSpace I x,
      inner ℝ (rmVec (lcOf g) x u v w) z = - inner ℝ (rmVec (lcOf g) x u v z) w := by
    intro u v w z
    rw [Work.Diff.GE.inner_rmVec_skew (lcOf g) hcov hmet x u v w z,
      real_inner_comm w (rmVec (lcOf g) x u v z)]
  -- (*) the cyclic relation
  have hcyc : ∀ u v w z : TangentSpace I x,
      inner ℝ (rmVec (lcOf g) x u v w) z
        = inner ℝ (rmVec (lcOf g) x v w z) u + inner ℝ (rmVec (lcOf g) x w u z) v := by
    intro u v w z
    have hb := Work.Diff.GE.rmVec_bianchi (lcOf g) hcov htor x u v w
    have h := congrArg (fun t : TangentSpace I x => inner ℝ t z) hb
    simp only [inner_add_left, inner_zero_left] at h
    have hs1 := hSkew v w u z
    have hs2 := hSkew w u v z
    linarith
  -- pair exchange
  have hpair : ∀ u v w z : TangentSpace I x,
      inner ℝ (rmVec (lcOf g) x u v w) z = inner ℝ (rmVec (lcOf g) x w z u) v := by
    intro u v w z
    have k1 := hcyc u v w z
    have k2 := hcyc v w z u
    have k3 := hcyc w u z v
    have k4 := hcyc z v u w
    have h1 := hAsym z w v u
    have h2 := hSkew w z v u
    have h3 := hAsym v u w z
    have h4 := hSkew u z w v
    linarith
  have hconv : ∀ y z : TangentSpace I x, inner ℝ y z = g.inner x y z := fun _ _ => rfl
  have hgoal : inner ℝ (rmVec (lcOf g) x a b d) c = inner ℝ (rmVec (lcOf g) x c d b) a := by
    have hp := hpair a b d c
    have h1 := hAsym d c a b
    have h2 := hSkew c d a b
    linarith
  simp only [Submission.Diff.rmP]
  rw [← hconv (rmVec (lcOf g) x a b d) c, ← hconv (rmVec (lcOf g) x c d b) a]
  exact hgoal

end Work.EXT
