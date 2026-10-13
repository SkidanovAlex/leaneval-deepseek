/-
# Boundedness of the `Zop`-iterates of `ψ(z) = 1/(1+z)`

`Work.Spaces.Zop u = (z ↦ z·u'(z))` is the one-dimensional operator underlying `D_z`.  This
module proves that every `Zop`-iterate of `ψ(z) = 1/(1+z)` is bounded on `(0,∞)`, uniformly in
`z`, which is the hypothesis of the multiplier estimates
`Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zmul_uniform` (via
`Work.FTS.CoercivityFix.PsiMul.HkMem_psi_mul`) and of the boundary-trace transfer
`Work.FTS.CoercivityFix.PsiMul.BdryTraces_psi_mul`.

The proof is a verbatim adaptation of `E2Bound.zop_phi_bound` (the profile `φ(z) = z/(1+z)²`):
under the Möbius chart `zchart z = (z-1)/(z+1)`, mapping `(0,∞)` onto `(-1,1)`, the operator
`Zop` becomes the polynomial map `Tmul P = ½(1 - X²)·P'` (`E2Bound.Zop_gpoly`), and `ψ` is the
chart-side evaluation of the polynomial `Ppsi = ½(1 - X)`
(`gpoly Ppsi z = Ppsi.eval (zchart z) = (1 - zchart z)/2 = 1/(1+z)`).  Hence
`Zop^[b] ψ = gpoly (Tmul^[b] Ppsi)` on `(0,∞)`, and `|zchart z| < 1` for `z > 0` bounds each
iterate by the sum of the absolute values of the coefficients of `Tmul^[b] Ppsi`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.CoercivityFix.E2Bound.zop_phi_bound
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.CoercivityFix.PsiMul

open Work.FTS.CoercivityFix.E2Bound

set_option autoImplicit false

/-- The polynomial of the chart: `gpoly Ppsi z = 1/(1+z)`, namely `½(1 - X)`. -/
def Ppsi : Polynomial ℝ := Polynomial.C (1 / 2) * (1 - Polynomial.X)

@[simp] lemma Ppsi_eq : Ppsi = Polynomial.C (1 / 2) * (1 - Polynomial.X) := rfl

/-- The chart-side evaluation of `Ppsi` is `ψ(z) = 1/(1+z)`. -/
lemma gpoly_Ppsi {z : ℝ} (hz : z ≠ -1) : gpoly Ppsi z = 1 / (1 + z) := by
  have hz1 : z + 1 ≠ 0 := by intro h; exact hz (by linarith)
  have hkey : (1 : ℝ) - (z - 1) / (z + 1) = 2 / (z + 1) := by
    field_simp
    ring
  simp only [gpoly, Ppsi, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  rw [zchart, hkey]
  have h : (1 : ℝ) / 2 * (2 / (z + 1)) = 1 / (z + 1) := by ring
  rw [h, add_comm (1 : ℝ) z]

/-- Every `Zop`-iterate of `ψ` is the chart-side evaluation of the corresponding polynomial
iterate. -/
lemma Zop_iter_gpoly_psi : ∀ (b : ℕ) (z : ℝ), 0 < z →
    Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z = gpoly (Tmul^[b] Ppsi) z := by
  intro b
  induction b with
  | zero =>
      intro z hz
      simpa using (gpoly_Ppsi (z := z) (zchart_ne_neg_one hz)).symm
  | succ b ih =>
      intro z hz
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
      have hev : Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) =ᶠ[𝓝 z]
          gpoly (Tmul^[b] Ppsi) := by
        filter_upwards [hmem] with w hw
        exact ih w hw
      have hrec : z * deriv (gpoly (Tmul^[b] Ppsi)) z = gpoly (Tmul (Tmul^[b] Ppsi)) z := by
        simpa only [Work.Spaces.Zop] using Zop_gpoly (Tmul^[b] Ppsi) (zchart_ne_neg_one hz)
      calc Work.Spaces.Zop^[b.succ] (fun z : ℝ => 1 / (1 + z)) z
          = Work.Spaces.Zop (Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z))) z :=
              congrFun (Function.iterate_succ_apply' Work.Spaces.Zop b _) z
        _ = z * deriv (Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z))) z := rfl
        _ = z * deriv (gpoly (Tmul^[b] Ppsi)) z := by rw [hev.deriv_eq]
        _ = gpoly (Tmul (Tmul^[b] Ppsi)) z := hrec
        _ = gpoly (Tmul^[b.succ] Ppsi) z :=
              congrArg (fun P => gpoly P z) (Function.iterate_succ_apply' Tmul b Ppsi).symm

/-- **Every `Zop`-iterate of `ψ(z) = 1/(1+z)` is bounded on `(0,∞)`.**  This is the hypothesis
of the multiplier estimates for the radial factor `1/(1+z)`. -/
theorem zop_psi_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z| ≤ K := by
  have hbd : ∀ b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z →
      |Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z| ≤ C := by
    intro b
    refine ⟨(Tmul^[b] Ppsi).sum (fun _ a => |a|), ?_, ?_⟩
    · rw [Polynomial.sum_def]
      exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    · intro z hz
      rw [Zop_iter_gpoly_psi b z hz]
      exact poly_eval_abs_le _ (abs_zchart_le_one hz)
  choose C hC using hbd
  refine ⟨∑ b ∈ Finset.range (n + 1), C b, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => (hC i).1)
  · intro b hb z hz
    have hbmem : b ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
    have hle : C b ≤ ∑ i ∈ Finset.range (n + 1), C i :=
      Finset.single_le_sum (fun i _ => (hC i).1) hbmem
    exact le_trans ((hC b).2 z hz) hle

/-- `ψ(z) = 1/(1+z)` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_psi : ContDiffOn ℝ Work.Stability.smoothOrder
    (fun z : ℝ => 1 / (1 + z)) (Set.Ioi (-1)) := by
  refine ContDiffOn.div (by fun_prop) (by fun_prop) ?_
  intro z hz
  simp only [Set.mem_Ioi] at hz
  intro h
  linarith

end Work.FTS.CoercivityFix.PsiMul
