/-
Copyright: work module for the Elgindi finite-time singularity project.

# Boundedness of the `Zop`-iterates of `φ(z) = z/(1+z)²`

`Work.Spaces.Zop u = (z ↦ z·u'(z))`.  The profile `φ(z) = z/(1+z)²` of the fundamental
model satisfies `Zop^[b] φ = P_b((z-1)/(z+1))` for a polynomial `P_b`
(`gpoly (Tmul^[b] Pphi)` with the chart `zchart`), and `z > 0` forces the chart variable
`(z-1)/(z+1)` into `(-1,1)`.  Hence every iterate is bounded on `(0,∞)` by the sum of the
absolute values of the coefficients of `P_b`, which gives `zop_phi_bound`.
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.CoercivityFix.E2Bound.ZopPhiDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS.CoercivityFix.E2Bound

/-- Evaluating a polynomial at a point of `[-1,1]` is bounded by the sum of the absolute
values of its coefficients. -/
lemma poly_eval_abs_le (P : Polynomial ℝ) {y : ℝ} (hy : |y| ≤ 1) :
    |P.eval y| ≤ P.sum (fun _ a => |a|) := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc |∑ e ∈ P.support, P.coeff e * y ^ e|
      ≤ ∑ e ∈ P.support, |P.coeff e * y ^ e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ P.support, |P.coeff e| := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        rw [abs_mul, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg y) hy)

/-- The intertwining identity: in the chart variable, `Zop` acts as `P ↦ ½(1 - X²)·P'`. -/
lemma Zop_gpoly (P : Polynomial ℝ) {z : ℝ} (hz : z ≠ -1) :
    Work.Spaces.Zop (gpoly P) z = gpoly (Tmul P) z := by
  have hz1 : z + 1 ≠ 0 := by intro h; exact hz (by linarith)
  have hzd : HasDerivAt zchart (2 / (z + 1) ^ 2) z := by
    change HasDerivAt (fun w : ℝ => (w - 1) / (w + 1)) (2 / (z + 1) ^ 2) z
    have h1 : HasDerivAt (fun w : ℝ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
    have h2 : HasDerivAt (fun w : ℝ => w + 1) 1 z := (hasDerivAt_id z).add_const 1
    have hdiv := h1.div h2 hz1
    have hval : (1 * (z + 1) - (z - 1) * 1) / (z + 1) ^ 2 = 2 / (z + 1) ^ 2 := by ring
    rw [hval] at hdiv
    exact hdiv
  have hcomp : HasDerivAt (fun w => P.eval (zchart w))
      (P.derivative.eval (zchart z) * (2 / (z + 1) ^ 2)) z :=
    (Polynomial.hasDerivAt P (zchart z)).comp z hzd
  rw [Work.Spaces.Zop]
  change z * deriv (fun w => P.eval (zchart w)) z = (Tmul P).eval (zchart z)
  rw [hcomp.deriv]
  simp only [Tmul, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  have hkey : z * (2 / (z + 1) ^ 2) = (1 - zchart z ^ 2) / 2 := by
    rw [zchart, div_pow]
    field_simp
    ring
  calc z * (P.derivative.eval (zchart z) * (2 / (z + 1) ^ 2))
      = P.derivative.eval (zchart z) * (z * (2 / (z + 1) ^ 2)) := by ring
    _ = P.derivative.eval (zchart z) * ((1 - zchart z ^ 2) / 2) := by rw [hkey]
    _ = 1 / 2 * (1 - zchart z ^ 2) * P.derivative.eval (zchart z) := by ring

/-- The base case: `φ(z) = z/(1+z)²` is the chart-side evaluation of `Pphi = ¼(1 - X²)`. -/
lemma gpoly_Pphi {z : ℝ} (hz : z ≠ -1) : gpoly Pphi z = z / (1 + z) ^ 2 := by
  have hz1 : z + 1 ≠ 0 := by intro h; exact hz (by linarith)
  simp only [gpoly, Pphi, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  rw [show z / (1 + z) ^ 2 = z / (z + 1) ^ 2 by ring]
  rw [zchart, div_pow]
  field_simp
  ring

/-- Every `Zop`-iterate of `φ` is the chart-side evaluation of the corresponding polynomial
iterate. -/
lemma Zop_iter_gpoly : ∀ (b : ℕ) (z : ℝ), 0 < z →
    Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z = gpoly (Tmul^[b] Pphi) z := by
  intro b
  induction b with
  | zero =>
      intro z hz
      simpa using (gpoly_Pphi (z := z) (zchart_ne_neg_one hz)).symm
  | succ b ih =>
      intro z hz
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
      have hev : Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) =ᶠ[𝓝 z]
          gpoly (Tmul^[b] Pphi) := by
        filter_upwards [hmem] with w hw
        exact ih w hw
      have hrec : z * deriv (gpoly (Tmul^[b] Pphi)) z = gpoly (Tmul (Tmul^[b] Pphi)) z := by
        simpa only [Work.Spaces.Zop] using Zop_gpoly (Tmul^[b] Pphi) (zchart_ne_neg_one hz)
      calc Work.Spaces.Zop^[b.succ] (fun z : ℝ => z / (1 + z) ^ 2) z
          = Work.Spaces.Zop (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2)) z :=
              congrFun (Function.iterate_succ_apply' Work.Spaces.Zop b _) z
        _ = z * deriv (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2)) z := rfl
        _ = z * deriv (gpoly (Tmul^[b] Pphi)) z := by rw [hev.deriv_eq]
        _ = gpoly (Tmul (Tmul^[b] Pphi)) z := hrec
        _ = gpoly (Tmul^[b.succ] Pphi) z :=
              congrArg (fun P => gpoly P z) (Function.iterate_succ_apply' Tmul b Pphi).symm

theorem zop_phi_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K := by
  have hbd : ∀ b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z →
      |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ C := by
    intro b
    refine ⟨(Tmul^[b] Pphi).sum (fun _ a => |a|), ?_, ?_⟩
    · rw [Polynomial.sum_def]
      exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    · intro z hz
      rw [Zop_iter_gpoly b z hz]
      exact poly_eval_abs_le _ (abs_zchart_le_one hz)
  choose C hC using hbd
  refine ⟨∑ b ∈ Finset.range (n + 1), C b, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => (hC i).1)
  · intro b hb z hz
    have hbmem : b ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
    have hle : C b ≤ ∑ i ∈ Finset.range (n + 1), C i :=
      Finset.single_le_sum (fun i _ => (hC i).1) hbmem
    exact le_trans ((hC b).2 z hz) hle

end Work.FTS.CoercivityFix.E2Bound
