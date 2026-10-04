import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.koszul
import Submission.Work.Diff.GE.chartcalc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Kit for `Work.Diff.GE.rmChartExpr_eq`

## The target

`Work.Diff.GE.rmChartExpr_eq` identifies the frozen curvature components in the coordinate frame,

`rmC4 G x₀ t y i j k l = (G t).inner y (R(σᵢ,σⱼ)σ_l) σ_k`  (`rmC4` unfolds to this),

with the explicit coordinate expression `rmChartExpr`, i.e. with

`∂_i Γ_{jlk} - Γ_{jlm}Γ_{ikn}(G t)^{mn} - ∂_j Γ_{ilk} + Γ_{ilm}Γ_{jkn}(G t)^{mn}`

where `Γ = koszulPair` is the *lowered* Christoffel pairing `⟨∇_{σ_a}σ_b, σ_c⟩` and
`∂_a = dOp x₀ a` is the derivative in the chart direction `a`.

## Route (and the pieces delegated away from this kit)

1. `rmC4 G x₀ t y i j k l = cGram (G t) x₀ y (cCurv (G t) x₀ y (cBasis i) (cBasis j) (cBasis l)) (cBasis k)`
   (the bridge `Work.Diff.GE.rmC4_eq_cGram_cCurv`, proved in `rmChartExpr_eq.lean`; it is
   `rmP_frameVector_eq_cCurv` at the point `y` instead of `x₀`).
2. `cCurv` unfolds to `dB a d b - dB b d a + chrB (chrB d b) a - chrB (chrB d a) b`, and `cGram` is
   additive in its first vector slot, so the left side is a *difference of two* expressions
   `D(A,B,D,K) := cGram (G t) x₀ y (dB A D B + chrB (chrB D B) A) (cBasis K)`.
3. For each of the two, the **product rule** (`Work.Diff.GE.dOp_fPair_eq`) gives
   `dOp x₀ A (fPair x₀ B D K) t y = D(A,B,D,K) + cGram (G t) x₀ y (chrB D B) (chrB K A)`.
4. `fPair = koszulPair` on the chart (`Work.Diff.GE.fPair_eq_koszul`), and the inner product of two
   coordinate vectors is expanded in the inverse Gram matrix (`Work.Diff.GE.cGram_eq_sum_gramInv`),
   with each `cGram (·) (chrB p q) (cBasis k)` lowered by `Work.Diff.GE.cGram_chrB_eq_koszulPair`.
   The result is `rmChartExpr`.

The three `Work.Diff.GE.*` lemmas of steps 3 and 4 are the delegated pieces; this file collects the
bookkeeping lemmas they and the assembly share.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic Submission.ChartCurv

namespace Work.Diff.GE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

noncomputable section

/-! ## Bilinearity of `cGram` -/

lemma cGram_apply (g : SMet I M) (x₀ p : M) (a b : E) :
    cGram g x₀ p a b = g.inner p (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b) :=
  rfl

lemma cGram_neg_fst (g : SMet I M) (x₀ p : M) (a b : E) :
    cGram g x₀ p (-a) b = - cGram g x₀ p a b := by
  show (g.inner p) (frameVector x₀ p (-a)) (frameVector x₀ p b) = _
  rw [frameVector_neg, show (g.inner p) (-frameVector x₀ p a)
      = - (g.inner p) (frameVector x₀ p a) from map_neg (g.inner p) _]
  rfl

lemma cGram_add_fst (g : SMet I M) (x₀ p : M) (a b c : E) :
    cGram g x₀ p (a + b) c = cGram g x₀ p a c + cGram g x₀ p b c := by
  show (g.inner p) (frameVector x₀ p (a + b)) (frameVector x₀ p c) = _
  rw [frameVector_add, show (g.inner p) (frameVector x₀ p a + frameVector x₀ p b)
      = (g.inner p) (frameVector x₀ p a) + (g.inner p) (frameVector x₀ p b) from
    map_add (g.inner p) _ _]
  rfl

lemma cGram_sub_fst (g : SMet I M) (x₀ p : M) (a b c : E) :
    cGram g x₀ p (a - b) c = cGram g x₀ p a c - cGram g x₀ p b c := by
  rw [sub_eq_add_neg, cGram_add_fst, cGram_neg_fst, sub_eq_add_neg]

/-! ## Expanding a frame vector in the basis of `E` -/

/-- The frame vector of the `E`-vector `V` expands in the coordinate frame with the coordinates
of `V`. -/
lemma frameVector_eq_sum_coord (x₀ p : M) (V : E) :
    frameVector (I := I) x₀ p V
      = ∑ m, ((cBasis (E := E)).coord m V) • frameVector (I := I) x₀ p (cBasis (E := E) m) := by
  conv_lhs => rw [← sum_coord_smul_eq V]
  rw [frameVector_sum Finset.univ]

end

end Work.Diff.GE
