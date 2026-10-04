import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.CupRing

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linear (affine) simplices of the standard simplex

This file begins the *subdivision* chapter: the geometric input needed for the
small-simplices/Mayer–Vietoris theorem (`Submission/NOTES.md`, "the road from here").

The standard topological `n`-simplex is `Delta n = TopCat.of (stdSimplex ℝ (Fin (n+1)))`, whose
underlying type is the subtype of `Fin (n+1) → ℝ` of nonnegative functions summing to `1`.  The
basic object here is the **linear simplex with a given vertex family**

`affineSimplex v : C(Δᵏ, Δⁿ)`,  `t ↦ ∑ j, t j • v j`   (`v : Fin (k+1) → Δⁿ`),

the affine map determined by the vertices `v`.  Singular simplices of `Δⁿ` which are affine maps
are the pieces into which the barycentric subdivision cuts `Δⁿ`.

## Main definitions

* `Delta n` — the standard topological `n`-simplex as a topological space;
* `affineSimplex v` — the affine map `C(Δᵏ, Δⁿ)` determined by the vertices `v`;
* `linSimplex v` — the same as a singular simplex of `Delta n`.

## Main results

* `affineSimplex_apply` — the coordinates of `affineSimplex v t`;
* `affineSimplex_vertex` — the value at a vertex of `Δᵏ`.

The functoriality of `affineSimplex` (`affineSimplex v (stdSimplex.map f t) = affineSimplex (v ∘ f) t`)
and the resulting boundary formula for `linSimplex` are delegated separately; they are what makes
the subdivision chain maps well defined.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The standard topological `n`-simplex, as a topological space. -/
abbrev Delta (n : ℕ) : TopCat := TopCat.of (stdSimplex ℝ (Fin (n + 1)))

/-- **The linear simplex with vertices `v`**: the continuous map of standard simplices which sends
`t` to the convex combination `∑ⱼ tⱼ • vⱼ`. -/
def affineSimplex {n k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    C(stdSimplex ℝ (Fin (k + 1)), stdSimplex ℝ (Fin (n + 1))) where
  toFun t :=
    ⟨fun i => ∑ j, t j * v j i, by
      constructor
      · intro i
        exact Finset.sum_nonneg fun j _ => mul_nonneg (t.2.1 j) ((v j).2.1 i)
      · have h1 : (∑ i, ∑ j, t j * v j i) = ∑ j, t j * (∑ i, v j i) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
        rw [h1]
        simp⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

/-- The coordinates of the affine simplex: `(affineSimplex v t) i = ∑ j, t j * v j i`. -/
@[simp]
theorem affineSimplex_apply {n k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1)))
    (t : stdSimplex ℝ (Fin (k + 1))) (i : Fin (n + 1)) :
    affineSimplex v t i = ∑ j, t j * v j i := rfl

/-- The value of the affine simplex at a vertex. -/
theorem affineSimplex_vertex {n k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1)))
    (i : Fin (k + 1)) : affineSimplex v (stdSimplex.vertex i) = v i := by
  ext j
  rw [affineSimplex_apply]
  simp [stdSimplex.vertex, Pi.single_apply]

/-- **The affine simplex as a singular simplex of `Δⁿ`.** -/
def linSimplex {n k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    (TopCat.toSSet.obj (Delta n)) _⦋k⦌ :=
  (TopCat.toSSetObjEquivT (Delta n) (Opposite.op ⦋k⦌)).symm (affineSimplex v)

/-- The affine point of `Δⁿ` with vertex family `v : Fin (k+1) → Δⁿ`, evaluated at a point: the
underlying continuous map of `linSimplex v`. -/
theorem toSSetObjEquiv_linSimplex {n k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    TopCat.toSSetObjEquivT (Delta n) (Opposite.op ⦋k⦌) (linSimplex v) = affineSimplex v := by
  rw [linSimplex, Equiv.apply_symm_apply]

/-- The affine simplex with the vertices of the standard simplex is the identity map (this is the
base case of the subdivision recursion). -/
theorem affineSimplex_id {n : ℕ} (t : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplex (fun i : Fin (n + 1) => stdSimplex.vertex i) t = t := by
  apply Subtype.ext
  funext i
  show (∑ j, t j * (stdSimplex.vertex j : Fin (n + 1) → ℝ) i) = t i
  simp [stdSimplex.vertex, Pi.single_apply]

end

end Work.Cohomology
