import Mathlib
import Submission.Work.Whitney.PairDet

/-!
# Framing the bigon: the sign comparison along a pair of arcs

The Whitney cancellation needs the *relative sign* of two transverse double points `(p₁,p₂)` and
`(q₁,q₂)` of a smooth immersion `f : M → ℝ^{2n}`, paired by two arcs `γ₁ : p₁ → q₁` and
`γ₂ : p₂ → q₂`.

When `M` is orientable, a *global* oriented atlas `A` makes the comparison canonical
(`Work.Whitney.OppositeSign`, `Work.Whitney.oppositeSign_iff`).  For a **non-orientable** `M` no such
atlas exists, and the comparison has to be made by *framing the bigon*: the orientation is
transported along each arc separately, and the two arcs are only required to be individually
coherent.  Concretely, the comparison is read in four charts `c₁, c₂` (at `p₁, p₂`) and
`c₃, c₄` (at `q₁, q₂`) such that `c₁` and `c₃` are joined by a *chain of charts along `γ₁`* with
positive transitions, and `c₂, c₄` by such a chain along `γ₂`.

The point of the chain formulation is that a chain along a *single arc* is a contractible piece of
data: it always exists (cover the arc by charts and flip them one by one — see
`Work.Whitney.exists_isArcChain`), whereas a globally coherent framing exists only when `M` is
orientable.  Moreover the comparison is *canonical*: replacing a chain by another one flips the two
charts of the double point it is used for *simultaneously*, so the product
`pairDet f c₁ c₂ p₁ p₂ * pairDet f c₃ c₄ q₁ q₂` is unchanged (this is the "transport along a fixed
arc is well-defined up to positive transition" statement,
`Work.Whitney.posTransitionAt_of_isArcChain`).

## Why this is enough for the endgame

The insertion of a double point
(`Work.Whitney.exists_addDoublePoint_both_signs_chart_like`) gives, for one and the same inserted
pair `(p', q')` of preimages, two modified immersions `fp`, `fm` with
`doubleDetC fm c p' q' = - doubleDetC fp c p' q'` in the *insertion chart* `c`, while both agree
with `f` near the pre-existing double point's preimages.  In the comparison above one takes
`c₁ = c₃ = c` (the short arc lies inside `c`, and a chain from `c` to `c` is available) and, for the
long arc, any chain from a chart `c₂` at `p₂` to `c₄ = c`.  The first factor
`pairDet f c c₂ p₁ p₂` only depends on the *germ* of `f` at `p₁, p₂`, hence is the same for `fp`
and `fm`; the second factor is flipped.  So exactly one of the two insertions has a *negative*
comparison, without any need to know which.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **A chart-like map of the smooth structure**: a partial homeomorphism `M ⇀ ℝⁿ` which is smooth
on its source, with smooth inverse on its target.  (The charts of the atlas of `M` are of this
kind; an arbitrary `OpenPartialHomeomorph` need not be.) -/
def IsSmoothChart (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) : Prop :=
  ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c c.source ∧
    ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm c.target

/-- **Two charts are positively related at a point.**  This is the pointwise form of the transition
condition appearing in `Work.Whitney.IsOrientedAtlas`. -/
def PosTransitionAt (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (x : M) : Prop :=
  0 < (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₂ (c₁.symm u)) (c₁ x)).det

/-- **A chain of charts along the arc `γ`, from `c` to `c'`.**

Charts `d 0, …, d N` and junction parameters `0 = t 0 ≤ ⋯ ≤ t N = 1` such that

* the subarc `γ '' [t i, t i+1]` lies in the source of `d i` (so the chain really follows `γ`),
* consecutive charts are positively related at the junction point `γ (t i+1)`,
* the endpoint charts are `c = d 0` and `c' = d N`, with `γ 0 ∈ c.source`, `γ 1 ∈ c'.source`.

This is the datum of a *trivialisation of the tangent bundle along the arc* up to positive
transition, expressed without vector bundles. -/
def IsArcChain (γ : ℝ → M) (c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N)
    (d : Fin (N + 1) → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (t : Fin (N + 1) → ℝ),
    t 0 = 0 ∧ t (Fin.last N) = 1 ∧ Monotone t ∧ d 0 = c ∧ d (Fin.last N) = c' ∧
    γ 0 ∈ c.source ∧ γ 1 ∈ c'.source ∧
    (∀ i : Fin (N + 1), IsSmoothChart (d i)) ∧
    (∀ i : Fin N, γ '' Set.Icc (t i.castSucc) (t i.succ) ⊆ (d i.castSucc).source) ∧
    (∀ i : Fin N, γ (t i.succ) ∈ (d i.succ).source ∧
      PosTransitionAt (d i.castSucc) (d i.succ) (γ (t i.succ)))

/-- **A chart is positively related to itself.** -/
theorem posTransitionAt_self (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {x : M} (hx : x ∈ c.source) : PosTransitionAt c c x := by
  have hx' : c x ∈ c.target := c.map_source hx
  have hmem : ∀ᶠ u in 𝓝 (c x), u ∈ c.target := c.open_target.mem_nhds hx'
  have heq : (fun u : EuclideanSpace ℝ (Fin n) => c (c.symm u)) =ᶠ[𝓝 (c x)] id := by
    refine Filter.eventually_of_mem hmem (fun u hu => ?_)
    simp [c.right_inv hu]
  rw [PosTransitionAt, heq.fderiv_eq, fderiv_id]
  change 0 < LinearMap.det (1 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  rw [show (1 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
      LinearMap.id from rfl, LinearMap.det_id]
  exact zero_lt_one

/-- **The constant chain**: if the whole arc lies in the source of `c`, then `c` and `c` are joined
by an arc chain along `γ`. -/
theorem isArcChain_const {γ : ℝ → M} {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (h0 : γ 0 ∈ c.source) (h1 : γ 1 ∈ c.source) (hc : IsSmoothChart c)
    (hsub : γ '' Set.Icc (0 : ℝ) 1 ⊆ c.source) :
    IsArcChain γ c c := by
  refine ⟨1, Nat.one_pos, fun _ => c, ![0, 1], ?_, ?_, ?_, ?_, ?_, h0, h1, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · simp
  · simp
  · intro i
    exact hc
  · intro i
    fin_cases i
    simpa using hsub
  · intro i
    fin_cases i
    exact ⟨by simpa using h1, by
      simpa using posTransitionAt_self c h1⟩

/-- **The comparison of two double points along a pair of arcs.**  There are four charts, the pairs
`(c₁,c₃)` and `(c₂,c₄)` being joined by arc chains along `γ₁` resp. `γ₂`, and the product of the two
`pairDet`-values is negative.

For an orientable `M` this agrees with the atlas-based `Work.Whitney.OppositeSign` for any oriented
atlas whose charts cover the arcs; for a non-orientable `M` it is the correct replacement. -/
def OppositeType (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (p₁ p₂ q₁ q₂ : M) : Prop :=
  γ₁ 0 = p₁ ∧ γ₁ 1 = q₁ ∧ γ₂ 0 = p₂ ∧ γ₂ 1 = q₂ ∧
  ∃ (c₁ c₂ c₃ c₄ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    p₁ ∈ c₁.source ∧ p₂ ∈ c₂.source ∧ q₁ ∈ c₃.source ∧ q₂ ∈ c₄.source ∧
    IsArcChain γ₁ c₁ c₃ ∧ IsArcChain γ₂ c₂ c₄ ∧
    pairDet f c₁ c₂ p₁ p₂ * pairDet f c₃ c₄ q₁ q₂ < 0

end Work.Whitney
