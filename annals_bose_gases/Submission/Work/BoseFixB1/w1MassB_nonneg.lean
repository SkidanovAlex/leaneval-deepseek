import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Nonnegativity of FS's per-box mass `∬ w_{1,B(u)}` (the `Work.BoseFixB1` form)

FS's a-priori remainder `R_Ψ` of `thm:aprioriHLambda` (step 4) carries the
per-box weight `∬ w_{1,B(u)} = ∫_x∫_y wSmall1Pair h M ℓ d u x y`, and `R_Ψ ≥ 0`
needs that weight to be nonnegative.  Here we prove it unconditionally at the
`w1MassB` interface, with *no* hypothesis on the cutoff parameter `M`
(the kernel's sign structure is insensitive to `M`).

* `chiSmallB M ℓ d u x = χ_M(x/ℓ)·χ_M(x/(ℓd) − u) ≥ 0` pointwise
  (`Work.SmallBoxSliding.chiSmallB_nonneg`);
* `convScaleSmall M (ℓd) z = (χ_M ⋆ χ_M)(z/(ℓd)) ≥ 0` pointwise
  (`Work.SmallBoxSliding.convScaleSmall_nonneg`) and
  `convScale ℓ z = (χ ⋆ χ)(z/ℓ) ≥ 0` (`Submission.BoseGases.convScale_nonneg`),
  so both renormalisation denominators are nonnegative;
* the numerator `g₀ v h = v·(1 − w₀)` is `≥ 0` almost everywhere
  (`Submission.BoseGases.g0_nonneg_ae`; FS: `v ≥ 0` and `w₀ ≤ 1` a.e.), and the
  a.e. statement is transported to `g₀ (x − ·)` along the reflection
  `y ↦ x − y` (`Work.SmallBoxSliding.ae_g0_comp_sub`).

Hence the inner integrand is `≥ 0` a.e. and two applications of
`integral_nonneg_of_ae` finish.  This is
`Work.SmallBoxSliding.wSmall1Pair_mass_nonneg` without its (unused) hypothesis
`1 ≤ M`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

theorem w1MassB_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {M : ℕ} {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Work.BoseFixB1.w1MassB h M ℓ d u := by
  rw [w1MassB]
  have hinner : ∀ x : EuclideanSpace ℝ (Fin 3),
      0 ≤ ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
    intro x
    apply integral_nonneg_of_ae
    filter_upwards
      [Work.SmallBoxSliding.ae_g0_comp_sub hv hvrad hv_supp hR h x] with y hy
    simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
      Submission.BoseGases.wSmallScaled]
    exact mul_nonneg
      (mul_nonneg (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u x)
        (div_nonneg
          (div_nonneg hy (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) (x - y)))
          (Submission.BoseGases.convScale_nonneg ℓ (x - y))))
      (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u y)
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall hinner)

end Work.BoseFixB1
