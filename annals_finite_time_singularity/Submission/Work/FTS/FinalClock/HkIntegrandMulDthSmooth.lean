import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.N4Fields.wang_field_smoothInt
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The comparison `HkIntegrand α 4 (3·D_θh/(1+z)) ≤ C·HkIntegrand α 5 h` for `h` locally `C⁵`

`Work.FTS.FinalClock.HkIntegrandMulDthSmooth` is the weighted Leibniz estimate behind the
`τ`-Lipschitz clause of the third `L₁₂`-functional in `Work.FTS.FinalClock.MuHolder`
(the `D_θ` in `3D_θg/(1+z)` costs one order in `ℋ`, so the comparison must use `ℋ⁵`).

The multiplier is `φ(z) = 3/(1+z)`, a `z`-only factor, and the two ingredients are

* `ZopIterLeibniz` — the iterated Leibniz rule for `Zop = z ∂_z` at finite order (the
  `C^∞`-version `Work.Spaces.DerivLike.iterate_mul` needs `C^∞`, and the version
  `Work.Spaces.DzIter_mul` needs analyticity in the `WithTop ℕ∞`-order of this Mathlib);
* the pointwise Cauchy–Schwarz layer `HkIntegrand_zmul_le_pointwise`, which turns the two
  Leibniz expansions into the stated bound, using the bounds `|Zop^b φ| ≤ 100` (`b ≤ 4`)
  of `PhiZopBound`.

The target needs no global smoothness: the hypothesis is only `ContDiffAt ℝ 5` at the point
`(z,θ)`, which is exactly the order needed (`D_θ^i h` with `i ≤ 5` must be differentiated
`j` more times in `z`, `i + j ≤ 5`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.FinalClock

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Plumbing: neighbourhoods and slices -/

/-- The `z`-slice of a function which is `C^k` on a product `V ×ˢ W` is `C^k` on `V`. -/
theorem contDiffOn_zslice {F : ℝ → ℝ → ℝ} {V W : Set ℝ} {θ : ℝ} {k : ℕ}
    (h : ContDiffOn ℝ k (Function.uncurry F) (V ×ˢ W)) (hθ : θ ∈ W) :
    ContDiffOn ℝ k (fun z' => F z' θ) V := by
  have hmap : ContDiffOn ℝ k (fun z' : ℝ => (z', θ)) V := by
    have h1 : ContDiff ℝ k (fun z' : ℝ => (z', θ)) := by fun_prop
    exact h1.contDiffOn
  have := ContDiffOn.comp h hmap (fun z' _ => ⟨by assumption, hθ⟩)
  simpa [Function.comp_def] using this


/-- The multiplier `φ(z) = 3/(1+z)` is `C^k` on `(-1,∞)`. -/
theorem contDiffOn_phiThree (k : ℕ) :
    ContDiffOn ℝ k (fun z : ℝ => 3 / (1 + z)) (Set.Ioi (-1)) := by
  have hden : ContDiffOn ℝ k (fun z : ℝ => 1 + z) (Set.Ioi (-1)) := by fun_prop
  have h3 : ContDiffOn ℝ k (fun _ : ℝ => (3 : ℝ)) (Set.Ioi (-1)) := contDiffOn_const
  exact h3.div hden (fun x hx => by
    have hx' : (-1 : ℝ) < x := hx
    intro hc; linarith)

/-- If both weights of the `H^k`-integrand vanish then the integrand is `0`. -/
theorem HkIntegrand_eq_zero_of_weights (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hH : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0)
    (hW : Work.Spaces.Wt α z θ = 0) : Work.Spaces.HkIntegrand α k F z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have h1 : ∀ i : ℕ,
      (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i; rw [hH, mul_zero]; norm_num
  have h2 : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by
    intro i j; split_ifs with hh
    · rw [hW, mul_zero]; norm_num
    · rfl
  rw [Finset.sum_eq_zero (fun i _ => h1 i),
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => h2 i j)), add_zero]

/-! ## The pointwise Cauchy–Schwarz layer -/



/-! ## The two Leibniz expansions -/

/-- The Leibniz expansion of `D_z^i (m·f)` for a `z`-only multiplier `m`, at finite order,
on an open set `V` on which the `θ`-slice of `f` is `C^i`. -/
theorem DzIter_mul_of_contDiffOn (i : ℕ) (m : ℝ → ℝ) (f : ℝ → ℝ → ℝ) {V : Set ℝ}
    (hV : IsOpen V) {θ : ℝ} (hm : ContDiffOn ℝ i m V)
    (hf : ContDiffOn ℝ i (fun z' => f z' θ) V) :
    ∀ z ∈ V, Work.Spaces.DzIter i (fun z θ => m z * f z θ) z θ
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
          (Work.Spaces.Zop^[b] m z * Work.Spaces.DzIter (i - b) f z θ) := by
  intro z hz
  have hsl : (fun z' => Work.Spaces.DzIter i (fun z θ => m z * f z θ) z' θ)
      = Work.Spaces.Zop^[i] (fun z' => m z' * f z' θ) :=
    Work.FTS.LocData.Zop_iterate_slice i _ θ
  rw [congrFun hsl z]
  change Work.Spaces.Zop^[i] (m * (fun z' => f z' θ)) z = _
  rw [ZopIterLeibniz hV hm hf hz]
  simp only
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← congrFun (Work.FTS.LocData.Zop_iterate_slice (i - b) f θ) z]

/-- The Leibniz expansion of `D_z^jD_θ^i (m·f)` for a `z`-only multiplier `m`, at finite
order, on an open set `V` on which the `θ`-slice of `D_θ^i f` is `C^j`. -/
theorem mixed_mul_of_contDiffOn (j i : ℕ) (m : ℝ → ℝ) (f : ℝ → ℝ → ℝ) {V : Set ℝ}
    (hV : IsOpen V) {θ : ℝ} (hm : ContDiffOn ℝ j m V)
    (hf : ContDiffOn ℝ j (fun z' => Work.Spaces.DthIter i f z' θ) V) :
    ∀ z ∈ V, Work.Spaces.mixed j i (fun z θ => m z * f z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.Zop^[b] m z * Work.Spaces.mixed (j - b) i f z θ) := by
  intro z hz
  have hcomm : Work.Spaces.DthIter i (fun z θ => m z * f z θ)
      = fun z θ => m z * Work.Spaces.DthIter i f z θ :=
    Work.Coercivity.DthIter_mulZm i m f
  have hmain := DzIter_mul_of_contDiffOn j m (Work.Spaces.DthIter i f) hV hm hf z hz
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => m z * f z θ)) z θ = _
  rw [hcomm]
  exact hmain


end Work.FTS.FinalClock
