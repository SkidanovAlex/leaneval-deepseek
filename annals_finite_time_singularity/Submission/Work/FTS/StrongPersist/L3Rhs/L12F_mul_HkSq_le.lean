/-
Copyright: work module for the Elgindi finite-time singularity project.

# Multiplication of the `ℋ³`-norm by the multiplier `L₁₂(F_*(α))`

`Work.FTS.StrongPersist.L3Rhs.L12F_mul_HkSq_le`: there is a universal constant `C > 0`
(independent of `α ∈ (0,1]` and of the datum `g`) such that for every `SmoothOpen` datum
`g` in `ℋ³`,

* `L₁₂(F_*(α)) · g` is in `ℋ³`, and
* `|L₁₂(F_*(α)) · g|_{ℋ³}² ≤ C · |g|_{ℋ³}²`.

## The argument

`L₁₂(F_*(α))` is a function of `z` alone, so this is the multiplier estimate
`Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le` (with `k = 3`) applied to the radial
profile `φ_α := L₁₂(F_*(α))`.  Its two hypotheses are supplied as follows.

* **The profile identity.** `Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one` gives
  `φ_α(z) = 2α/(1+z)` for every `z > -1`; hence `φ_α` is `C^∞` on `(-1,∞)`
  (`ContDiffOn.congr` against the explicit rational function).
* **The `Zop`-bounds.** `Zop u = z·u'` (`Work.Spaces.Zop`).  On `(0,∞)` the profile `φ_α`
  agrees with `z ↦ 2α·(1/(1+z))`, so by locality of `Zop`-iterates
  (`SlotMul.Zop_iterate_eqOn_of_eqOn`; note `(0,∞)` is open) its iterates are those of the
  explicit function, and they split off the constant (`E2pkg.Zop_iter_const_mul`):
  `Zop^b φ_α = 2α · Zop^b (z ↦ 1/(1+z))`.  Under the Möbius chart
  `zchart z = (z-1)/(z+1)` the profile `z ↦ 1/(1+z)` is the polynomial `Pone = ½(1 - X)`
  evaluated at the chart, and `Zop` intertwines the chart evaluation with the polynomial map
  `Tmul P = ½(1-X²)P'` (`SlotMul.Zop_gpoly_iterate`).  Since `z > 0` forces
  `|zchart z| < 1`, each iterate is bounded by the sum `Szop b` of the absolute values of the
  coefficients of `Tmul^b Pone` (`SlotMul.Polynomial_abs_eval_le_sum_abs_coeff`).  Hence
  `|Zop^b φ_α z| ≤ 2α·Szop b ≤ 2·Szop b` for `b ≤ 3` and `α ≤ 1`, and the bound `Kzop`
  obtained by summing over `b ≤ 3` is **independent of `α`** — which is what makes the final
  constant universal.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.FTS.CoercivityFix.E2Bound.zop_phi_bound
import Submission.Work.FTS.CoercivityFix.E2Bound.ZopPhiDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Polynomial_abs_eval_le_sum_abs_coeff
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.CoercivityFix.E2Bound (gpoly Tmul)

/-! ## The chart polynomial for `z ↦ 1/(1+z)` -/

/-- The chart polynomial whose `gpoly`-evaluation is `z ↦ 1/(1+z)`, namely `½(1 - X)`:
`½(1 - (z-1)/(z+1)) = 1/(z+1)`. -/
private def Pone : Polynomial ℝ := Polynomial.C (1 / 2) * (1 - Polynomial.X)

/-- `gpoly Pone z = 1/(1+z)` away from the pole `z = -1`. -/
private lemma gpoly_Pone {z : ℝ} (hz : z ≠ -1) : gpoly Pone z = 1 / (1 + z) := by
  have hz1 : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  rw [Work.FTS.CoercivityFix.E2Bound.gpoly_apply, Pone,
    Work.FTS.CoercivityFix.E2Bound.zchart_apply]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [show (z - 1) / (z + 1) = (1 + z - 2) / (1 + z) by ring]
  rw [show (1 : ℝ) = (1 + z) / (1 + z) by field_simp]
  field_simp
  ring

/-- `Szop b` bounds `|Zop^b (z ↦ 1/(1+z))|` on `(0,∞)`: it is the sum of the absolute values
of the coefficients of the `b`-th `Tmul`-iterate of the chart polynomial `Pone`. -/
private def Szop (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.range ((Tmul^[b] Pone).natDegree + 1), |(Tmul^[b] Pone).coeff k|

private lemma Szop_nonneg (b : ℕ) : 0 ≤ Szop b :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- The **`α`-independent** bound for the `Zop`-iterates of `L₁₂(F_*(α))` of order `≤ 3`. -/
private def Kzop : ℝ := 2 * ∑ b ∈ Finset.range 4, Szop b

private lemma Kzop_nonneg : 0 ≤ Kzop := by
  show (0 : ℝ) ≤ 2 * ∑ b ∈ Finset.range 4, Szop b
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun b _ => Szop_nonneg b))

/-! ## The `Zop`-bound on the profile -/

private lemma zop_L12F_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (b : ℕ) (hb : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    |(Work.Spaces.Zop^[b]
        (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w)) z| ≤ Kzop := by
  have hz' : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  -- the profile identity, in the shape `2α · (1/(1+z))`
  have hEq : Set.EqOn (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w)
      (fun w : ℝ => (2 * α) * (1 / (1 + w))) (Set.Ioi (-1 : ℝ)) := by
    intro w hw
    show Work.Construction.L12 (Work.Construction.Fstar α) w = (2 * α) * (1 / (1 + w))
    rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hw]
    ring
  have h1 : (Work.Spaces.Zop^[b]
        (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w)) z
      = (Work.Spaces.Zop^[b] (fun w : ℝ => (2 * α) * (1 / (1 + w)))) z :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi hEq hz'
  have h2 : (Work.Spaces.Zop^[b] (fun w : ℝ => (2 * α) * (1 / (1 + w)))) z
      = (2 * α) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 / (1 + w))) z :=
    congrFun (Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul b (2 * α)
      (fun w : ℝ => 1 / (1 + w))) z
  -- the explicit function is a chart polynomial
  have h3 : (Work.Spaces.Zop^[b] (fun w : ℝ => 1 / (1 + w))) z
      = gpoly (Tmul^[b] Pone) z := by
    have hb2 : Set.EqOn (fun w : ℝ => 1 / (1 + w)) (gpoly Pone) (Set.Ioi (0 : ℝ)) :=
      fun w hw => (gpoly_Pone (by have hw' : (0 : ℝ) < w := hw; linarith)).symm
    rw [Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi hb2 hz,
      Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate Pone b z hz]
  -- the chart variable lies in `(-1,1)`
  have h4 : |gpoly (Tmul^[b] Pone) z| ≤ Szop b := by
    rw [Work.FTS.CoercivityFix.E2Bound.gpoly_apply]
    exact Work.FTS.CoercivityFix.E2Bound.SlotMul.Polynomial_abs_eval_le_sum_abs_coeff _
      (Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hz)
  have hb4 : b ∈ Finset.range 4 := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hb)
  have hle : Szop b ≤ ∑ b' ∈ Finset.range 4, Szop b' :=
    Finset.single_le_sum (fun i _ => Szop_nonneg i) hb4
  have hα2 : (0 : ℝ) < 2 * α := by linarith
  calc |(Work.Spaces.Zop^[b]
          (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w)) z|
      = |(2 * α) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 / (1 + w))) z| := by rw [h1, h2]
    _ = |2 * α| * |(Work.Spaces.Zop^[b] (fun w : ℝ => 1 / (1 + w))) z| := abs_mul _ _
    _ = (2 * α) * |(Work.Spaces.Zop^[b] (fun w : ℝ => 1 / (1 + w))) z| := by
        rw [abs_of_nonneg hα2.le]
    _ = (2 * α) * |gpoly (Tmul^[b] Pone) z| := by rw [h3]
    _ ≤ (2 * α) * Szop b := mul_le_mul_of_nonneg_left h4 hα2.le
    _ ≤ 2 * Szop b := by
        refine mul_le_mul_of_nonneg_right ?_ (Szop_nonneg b)
        have h2α : 2 * α ≤ 2 * 1 := by linarith
        simpa using h2α
    _ ≤ 2 * ∑ b' ∈ Finset.range 4, Szop b' := mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = Kzop := rfl

/-! ## The profile is `C^∞` on `(-1,∞)` -/

private lemma contDiffOn_L12F (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi (-1)) := by
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi (-1)) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 : ℝ) + z)
        (Set.Ioi (-1)) := contDiffOn_const.add contDiffOn_id
    have h2 := (contDiffOn_const (c := 2 * α) :
        ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ => 2 * α) (Set.Ioi (-1))).div h1
      (fun z hz => ne_of_gt (by have hz' : (-1 : ℝ) < z := hz; linarith))
    exact h2
  refine ContDiffOn.congr hbase ?_
  intro z hz
  exact Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz

/-! ## The theorem -/

theorem L12F_mul_HkSq_le : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      Work.Spaces.HkMem α 3
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * g z θ) ∧
      Work.Spaces.HkSq α 3
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * g z θ)
        ≤ C * Work.Spaces.HkSq α 3 g := by
  obtain ⟨C₀, hC₀, hmain⟩ := Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le 3
  refine ⟨C₀ * (1 + Kzop) ^ 2, mul_pos hC₀ (pow_pos (by linarith [Kzop_nonneg]) 2), ?_⟩
  intro α hα g hg hm
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Set.Ioi (-1)) := contDiffOn_L12F α hα0 hα1
  have hbnd : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |(Work.Spaces.Zop^[b]
        (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w)) z| ≤ Kzop :=
    fun b hb z hz => zop_L12F_le α hα0 hα1 b hb hz
  exact (hmain α (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w) Kzop
    Kzop_nonneg hbnd hsm g hg).2 hm

end Work.FTS.StrongPersist.L3Rhs
