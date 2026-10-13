/-
# N4 — reusable bookkeeping lemmas for the per-piece rows (design §3.4)

This module collects the *honest*, context-free helpers that the per-piece estimates of the
design's table reuse:

* `N0fix_bound` — **row 1 of §3.4, unconditionally**: `|N₀₁ + N₀₂|_{ℋ⁴} ≤ Kα²` (the pair
  collapses on the open quadrant to `8α²c2m(θ)z²Γ/(c(1+z)⁴)` and `HkSq` only sees the open
  quadrant);
* the scalar-conjugation API `HkIntegrand_const_mul`, `HkSq_const_mul`, `Xn_const_mul` (and
  the underlying `deriv_const_mul'`, `DzIter_const_mul`, `DthIter_const_mul`,
  `mixed_const_mul`);
* `tendsto_of_bdry_z` — the `z = ∞` clause of `BdryTraces` gives the plain decay of
  `mixed b a f · z` used by the radial Hardy inequality;
* `DzIter_radial_apply` — `D_z`-iterates of a `θ`-independent function.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.Construction.Terms
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RowsN0Aux

/-! ## Row 1 of the design table, unconditionally

Row 1 (`|N₀₁ + N₀₂|_{ℋ⁴} ≤ Cα²`) is the only one of the seven rows that mentions *no* interface
clause at all: it is a statement about the concrete functions `N01`, `N02` of `F_*` alone, and
it is therefore **true independently of the defect documented above**.  It is proved here as a
standalone lemma, so that a repaired N4 interface can consume it directly. -/

/-- **Row 1 of design §3.4, unconditionally.**  For `0 < α ≤ 1`,
`|N₀₁ + N₀₂|_{ℋ⁴} ≤ K α²` with a universal `K` (the constant of
`Work.Construction.H4N_GammaTerm_le`).

The pair `N01 + N02` collapses (on the open quadrant, by `N0_first_two_eq'`) to the quadratic
vanishing function `8α²c2m(θ)z²Γ(α,θ)/(c(α)(1+z)⁴)`, whose `ℋ⁴`-norm is `O(α²)`; the identity
holds on `Iz × Iθ` and `HkSq` only sees the open quadrant (`HkSq_congr_open`). -/
theorem N0fix_bound : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N0fix α) ≤ K * α ^ 2 := by
  obtain ⟨C, hC, hle⟩ := Work.Construction.H4N_GammaTerm_le
  refine ⟨C, hC, fun α hα hα1 => ?_⟩
  have hcongr : Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N0fix α)
      = Work.Spaces.HkSq α 4 (fun z θ => 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2
          * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 4)) := by
    refine Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ hθ2 => ?_)
    show Work.FTS.Nonlin.N0fix α z θ = 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2
      * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 4)
    rw [Work.FTS.Nonlin.N0fix]
    simp only [Work.Construction.N01, Work.Construction.N02]
    rw [show (3 / (2 * α)) * Work.Construction.s2 θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ
          + -Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = (3 / (2 * α)) * Work.Construction.s2 θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ
          - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ from by ring]
    exact Work.Construction.N0_first_two_eq' hα hα1 (le_of_lt hz)
      ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hXn : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N0fix α)
      = Work.Construction.H4N α (fun z θ => 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2
          * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 4)) := by
    simp only [Work.FTS.Nonlin.Xn, Work.Construction.H4N, Work.Spaces.HkNorm, hcongr]
  rw [hXn]
  exact hle α hα hα1

/-! ## Two honest fundamentals, and the row 2 derivation

The lemmas below are independent of the defect of §`RowCtx`: they are statements about the
weighted `ℋ⁴`-norm that a *repaired* interface needs as well. -/

/-- Multiplication by a constant commutes with `deriv`, unconditionally: `deriv` is `0` where
the function is not differentiable, and `c • f` is differentiable at `z` iff `f` is (for
`c ≠ 0`), so the two junk values agree. -/
theorem deriv_const_mul' (c : ℝ) (g : ℝ → ℝ) (z : ℝ) :
    deriv (fun z' => c * g z') z = c * deriv g z := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; simp
  · by_cases hg : DifferentiableAt ℝ g z
    · exact deriv_const_mul c hg
    · have hnon : ¬ DifferentiableAt ℝ (fun z' => c * g z') z := by
        intro h
        have h2 : DifferentiableAt ℝ (fun z' => c⁻¹ * (c * g z')) z := h.const_mul c⁻¹
        have heq : (fun z' => c⁻¹ * (c * g z')) = g := by
          funext z'
          rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
        rw [heq] at h2
        exact hg h2
      rw [deriv_zero_of_not_differentiableAt hnon,
        deriv_zero_of_not_differentiableAt hg, mul_zero]

/-- `D_z^i` commutes with multiplication by a constant. -/
theorem DzIter_const_mul (i : ℕ) (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
    funext z θ
    show z * deriv (fun z' => c * Work.Spaces.DzIter i g z' θ) z
      = c * (z * deriv (fun z' => Work.Spaces.DzIter i g z' θ) z)
    rw [deriv_const_mul']
    ring

/-- `D_θ^i` commutes with multiplication by a constant. -/
theorem DthIter_const_mul (i : ℕ) (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
    funext z θ
    show Real.sin (2 * θ) * deriv (fun θ' => c * Work.Spaces.DthIter i g z θ') θ
      = c * (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i g z θ') θ)
    rw [deriv_const_mul']
    ring

/-- The mixed operators `D_z^j D_θ^i` commute with multiplication by a constant. -/
theorem mixed_const_mul (j i : ℕ) (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.mixed j i g z θ := by
  simp only [Work.Spaces.mixed]
  rw [DthIter_const_mul i c g, DzIter_const_mul j c (Work.Spaces.DthIter i g)]

/-- **The `ℋ⁴`-integrand is `2`-homogeneous under scalar multiplication**: `D_z`, `D_θ` commute
with multiplication by a constant, so every slot of the integrand is multiplied by `c²`.  The
identity is pointwise and needs no regularity (`deriv_const_mul'`). -/
theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  have hDza : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.DzIter i f z θ :=
    fun i => congrFun (congrFun (DzIter_const_mul i c f) z) θ
  have hmixa : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed j i f z θ :=
    fun j i => congrFun (congrFun (mixed_const_mul j i c f) z) θ
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  simp only [hDza, hmixa]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc]; ring
    · rw [if_neg hc, if_neg hc]; ring

/-- **`HkSq` scales quadratically** (hence `HkNorm` by `|c|`): the pointwise identity
`HkIntegrand_const_mul` inside the two integrals, using that a constant factors out of the
Bochner integral. -/
theorem HkSq_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => c * f z θ) = c ^ 2 * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
      = c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => HkIntegrand_const_mul α k c f z θ)
  simp only [Work.Spaces.HkSq, Work.Spaces.Iz]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => hinner z),
    MeasureTheory.integral_const_mul]

/-- **The `ℋ⁴`-norm scales by `|c|`.**  (This replaces the interface clause `N4RegQ.smul`,
which asks for `RegQ` of the scaled function; the identity here is unconditional.) -/
theorem Xn_const_mul (α : ℝ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (fun z θ => c * f z θ)
      = |c| * Work.FTS.Nonlin.Xn α f := by
  simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, HkSq_const_mul,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ c ^ 2)]
  rw [Real.sqrt_sq_eq_abs]

/-- **The `z = ∞` boundary condition of `BdryTraces` implies the decay of the function.**
`BdryTraces` gives `z·(A(z)w(z))² → 0`; dividing by `z → ∞` gives `(Aw)² → 0`; since `w ≥ 1`
for `z ≥ 1`, one has `A² = (Aw)²/w² ≤ (Aw)²` there, hence `A² → 0`, `|A| = √(A²) → 0`, i.e.
`A → 0`.  This is the bridge from the boundary conditions of `RegQ` to the decay hypothesis of
the weighted `z`-embedding (`Work.FTS.H2.HQ.HardyZQ`). -/
theorem tendsto_of_bdry_z {A : ℝ → ℝ}
    (h : Filter.Tendsto (fun z : ℝ => z * (A z * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto A Filter.atTop (nhds 0) := by
  have hAw : Filter.Tendsto (fun z : ℝ => (A z * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun z : ℝ => z * (A z * Work.Spaces.w z) ^ 2 / z)
        Filter.atTop (nhds 0) := by
      simpa only [id_eq] using Filter.Tendsto.div_atTop h tendsto_id
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with z hz
    field_simp
  have hA2 : Filter.Tendsto (fun z : ℝ => A z ^ 2) Filter.atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall (fun z => sq_nonneg (A z))) ?_ hAw
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz
    have hw1 : 1 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
      nlinarith
    have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
    have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := by positivity
    calc A z ^ 2 = (A z * Work.Spaces.w z) ^ 2 / (Work.Spaces.w z) ^ 2 := by
          field_simp
      _ ≤ (A z * Work.Spaces.w z) ^ 2 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg (A z * Work.Spaces.w z)]
  have hcomp : Filter.Tendsto ((fun x : ℝ => Real.sqrt x) ∘ fun z : ℝ => A z ^ 2)
      Filter.atTop (nhds (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hA2
  have habs : Filter.Tendsto (fun z : ℝ => |A z|) Filter.atTop (nhds 0) := by
    have h1 := hcomp.congr' (Filter.Eventually.of_forall
      (fun z : ℝ => Real.sqrt_sq_eq_abs (A z)))
    simpa only [Real.sqrt_zero] using h1
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

/-- `D_z^b` of a function of `z` alone does not depend on the angle. -/
theorem DzIter_radial_apply (b : ℕ) (r : ℝ → ℝ) (z : ℝ) :
    ∀ θ : ℝ, Work.Spaces.DzIter b (fun z _ => r z) z θ
      = Work.Spaces.DzIter b (fun z _ => r z) z 0 := by
  induction b generalizing z with
  | zero => intro θ; rfl
  | succ b ih =>
    intro θ
    rw [Work.Spaces.DzIter_succ]
    show z * deriv (fun z' => Work.Spaces.DzIter b (fun z _ => r z) z' θ) z
      = z * deriv (fun z' => Work.Spaces.DzIter b (fun z _ => r z) z' 0) z
    congr 1
    exact congrFun (congrArg deriv (funext (fun z' => ih z' θ))) z


end RowsN0Aux

end Work.FTS.Nonlinear.Pieces
