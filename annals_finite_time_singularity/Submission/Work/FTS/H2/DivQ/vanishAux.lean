import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Calculus API for `iteratedDeriv` on a half-open interval `(0, x₁]`

For `f` of class `C^∞` on `(0,x₁]` we collect the elementary facts about the iterated
derivatives needed by `Work.FTS.H2.DivQ.divSinPrimitiveVanish`: continuity and differentiability
on the *open* interval `(0,x₁)`, the `HasDerivAt` relation `(f^{(j)})' = f^{(j+1)}` at interior
points, and the fundamental theorem of calculus on a compact subinterval `[a,b]` with `b < x₁`.
-/

namespace Work.FTS.H2.DivQ

open MeasureTheory Filter Set
open scoped Topology

/-- For `f` of class `C^∞` on the half-open interval `(0,x₁]`, every iterated derivative
`iteratedDeriv j f` is continuous on the open interval `(0,x₁)`.

Route: on the open set `iteratedDerivWithin j f (Ioo 0 x₁)` is continuous
(`ContDiffOn.continuousOn_iteratedDerivWithin`, `IsOpen.uniqueDiffOn`), and
`iteratedDerivWithin_of_isOpen` identifies it with `iteratedDeriv j f` there. -/
lemma continuousOn_iteratedDeriv_Ioo {f : ℝ → ℝ} {x₁ : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)) (j : ℕ) :
    ContinuousOn (iteratedDeriv j f) (Set.Ioo 0 x₁) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have h1 : ContinuousOn (iteratedDerivWithin j f (Set.Ioo 0 x₁)) (Set.Ioo 0 x₁) :=
    (hf.mono Set.Ioo_subset_Ioc_self).continuousOn_iteratedDerivWithin
      (WithTop.coe_le_coe.mpr le_top) hs
  refine h1.congr fun x hx => ?_
  exact (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

/-- For `f` of class `C^∞` on `(0,x₁]`, every iterated derivative `iteratedDeriv j f` is
differentiable on the open interval `(0,x₁)`. -/
lemma differentiableOn_iteratedDeriv_Ioo {f : ℝ → ℝ} {x₁ : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)) (j : ℕ) :
    DifferentiableOn ℝ (iteratedDeriv j f) (Set.Ioo 0 x₁) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have h1 : DifferentiableOn ℝ (iteratedDerivWithin j f (Set.Ioo 0 x₁)) (Set.Ioo 0 x₁) :=
    (hf.mono Set.Ioo_subset_Ioc_self).differentiableOn_iteratedDerivWithin
      (WithTop.coe_lt_coe.mpr (WithTop.natCast_lt_top j)) hs
  refine h1.congr fun x hx => ?_
  exact (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

/-- At an interior point of `(0,x₁]`, the `j`-th iterated derivative of a `C^∞` function on
`(0,x₁]` has derivative the `(j+1)`-st iterated derivative. -/
lemma hasDerivAt_iteratedDeriv_Ioo {f : ℝ → ℝ} {x₁ : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)) (j : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 x₁) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j f) x :=
    (differentiableOn_iteratedDeriv_Ioo hf j).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

/-- Continuity of the iterated derivatives on a compact subinterval `[a,b] ⊆ (0,x₁)`. -/
lemma continuousOn_iteratedDeriv_Icc {f : ℝ → ℝ} {x₁ : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)) (j : ℕ) {a b : ℝ} (ha : 0 < a) (hb : b < x₁) :
    ContinuousOn (iteratedDeriv j f) (Set.Icc a b) :=
  (continuousOn_iteratedDeriv_Ioo hf j).mono
    fun _ hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩


/-- **The fundamental theorem of calculus for the iterated derivatives**, on a compact
subinterval `[a,b]` with `0 < a` and `b < x₁` (so that no endpoint of the half-open interval is
touched):

`∫_a^b f^{(j+1)} = f^{(j)}(b) − f^{(j)}(a)`. -/
theorem intervalIntegral_iteratedDeriv_succ {f : ℝ → ℝ} {x₁ : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)) (j : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < x₁) :
    ∫ s in a..b, iteratedDeriv (j + 1) f s = iteratedDeriv j f b - iteratedDeriv j f a := by
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x :=
    fun x hx =>
      hasDerivAt_iteratedDeriv_Ioo hf j
        ⟨lt_trans ha hx.1, lt_of_lt_of_le hx.2 (le_of_lt hb)⟩
  have hint : IntervalIntegrable (iteratedDeriv (j + 1) f) volume a b :=
    (continuousOn_iteratedDeriv_Icc hf (j + 1) ha hb).intervalIntegrable_of_Icc hab
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuousOn_iteratedDeriv_Icc hf j ha hb) hderiv hint

/-- Pointwise AM-GM with parameter: `2uv ≤ a u² + v²/a` for every real `u`, `v` and `a > 0`. -/
lemma two_mul_le_mul_sq_add_div_sq {a u v : ℝ} (ha : 0 < a) :
    2 * (u * v) ≤ a * u ^ 2 + v ^ 2 / a := by
  have h : 0 ≤ (a * u - v) ^ 2 / a := div_nonneg (sq_nonneg _) ha.le
  have h2 : (a * u - v) ^ 2 / a = a * u ^ 2 - 2 * (u * v) + v ^ 2 / a := by
    field_simp
    ring
  linarith [h, h2 ▸ h]

end Work.FTS.H2.DivQ
