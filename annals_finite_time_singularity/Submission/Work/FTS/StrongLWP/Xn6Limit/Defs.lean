/-
# `Work.FTS.StrongLWP.Xn6Limit.Defs` — the order-`k` slot vocabulary of the locality limit

The lower-semicontinuity of the `ℋ^k`-norm under locally uniform convergence (the order-`k`
companion of `Work.FTS.OpenPkg.HkNorm_le_of_tendstoLocUnif_open`, which is the case `k = 4`)
is phrased in terms of the weighted *slots*

`slot α ji f = mixed ji.1 ji.2 f · slotWeight α ji`,

of the formal adjoints `adjMixed` and of the cut-off energy.  The order-`4` chapter
(`Submission/Work/FTS/Apriori/Limit/`) fixes `k = 4` in three definitions:

* `activeSlots` (the `Finset` of the slots occurring in `HkIntegrand α 4`),
* `HkIntegrand_eq_sum_slot` (the slot decomposition of the integrand),
* `HksqCut` (the cut-off energy).

This module provides the order-`k` analogues.  Everything else of the chapter
(`slot`, `slotWeight`, `TestQ`, `adjMixed`, `Qμ`, `integral_mixed_mul_adjMixed`,
`TestQ_mul_adjMixed`, `contDiffOn_w_Qd`, `contDiffOn_sin_rpow_Qd`, `exists_test_cutoff`,
`lintegral_le_iSup_integral_mul_of_tendsto_one`, `ofReal_setIntegral_le_lintegral`, …) is
already independent of the order and is reused verbatim.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.FTS.Apriori.Limit.SlotCalc
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.OpenPkg.HkNorm_le_of_tendstoLocUnif_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Xn6Limit

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Work.FTS.Apriori.Limit (Qd Qμ TestQ slot slotWeight adjMixed adjZ adjTh adjDzIter adjDthIter
  HksqCut activeSlots mem_Qd_iff sin_two_pos_of_mem_Qd contDiffOn_w_Qd contDiffOn_sin_rpow_Qd
  integrable_of_continuousOn_of_support TestQ_adjDzIter TestQ_mul_adjMixed)

/-! ## The active slots of the order-`k` norm -/

/-- **The active slots of the `ℋ^k`-norm**: the pure `D_z`-slots `(j,0)` with `j ≤ k` (whose
weight is `w/sin(2θ)^{η/2}`) together with the mixed slots `(j,i)` with `1 ≤ i` and `i + j ≤ k`
(whose weight is `Wt α = w·sin(2θ)^{-γ/2}`). -/
def activeSlotsK (k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
    (fun ji => ji.2 = 0 ∨ (1 ≤ ji.2 ∧ ji.1 + ji.2 ≤ k))

theorem mem_activeSlotsK_iff {k : ℕ} {ji : ℕ × ℕ} :
    ji ∈ activeSlotsK k ↔ (ji.2 = 0 ∧ ji.1 ≤ k) ∨ (1 ≤ ji.2 ∧ ji.1 + ji.2 ≤ k) := by
  rw [activeSlotsK, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h | h⟩
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h.1, h.2⟩
  · rintro (⟨h, h1⟩ | ⟨h1, h2⟩)
    · exact ⟨⟨h1, by omega⟩, Or.inl h⟩
    · exact ⟨⟨by omega, by omega⟩, Or.inr ⟨h1, h2⟩⟩

/-- The order-`4` `activeSlots` of the frozen chapter is the case `k = 4`. -/
theorem activeSlotsK_four : activeSlotsK 4 = activeSlots := rfl

/-! ## The cut-off `ℋ^k`-energy -/

/-- **The cut-off `ℋ^k`-energy**: `∫∫ HkIntegrand α k f · η` over the closed quadrant, i.e. the
`L¹`-norm of the `ℋ^k`-integrand of `f` against the cut-off `η` with respect to the product
measure `Qμ = dz dθ` on `Iz ×ˢ Iθ`. -/
def HksqCutK (α : ℝ) (k : ℕ) (f η : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p, Work.Spaces.HkIntegrand α k f p.1 p.2 * η p.1 p.2 ∂Qμ

/-- The order-`4` `HksqCut` of the frozen chapter is the case `k = 4`. -/
theorem HksqCutK_four (α : ℝ) (f η : ℝ → ℝ → ℝ) : HksqCutK α 4 f η = HksqCut α f η := rfl

/-! ## Continuity of the `ℋ^k`-integrand on the open quadrant

This is the open-quadrant counterpart of `Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`
(which needs genuine `C^∞` through `z = 0`, i.e. `SmoothQuad`).  It is proved directly from the
definition of `HkIntegrand`, so that it does not depend on the slot decomposition: each factor
`D_z^i f`, `mixed j i f`, `w`, `sin(2θ)^{c}` is `C^∞` on the open quadrant. -/

theorem continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd :=
  contDiffOn_w_Qd.continuousOn

theorem continuousOn_sin_rpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  (contDiffOn_sin_rpow_Qd c).continuousOn

theorem continuousOn_DzIter_Qd {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2) Qd :=
  (Work.FTS.LocData.contDiffOn_DzIter Work.FTS.Apriori.Limit.isOpen_Qd hf i).continuousOn

theorem continuousOn_mixed_Qd {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) Qd :=
  (Work.FTS.LocData.contDiffOn_mixed Work.FTS.Apriori.Limit.isOpen_Qd hf j i).continuousOn

theorem continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact continuousOn_w_Qd.mul (continuousOn_sin_rpow_Qd _)

/-- The uncurried `ℋ^k`-integrand is continuous on the open quadrant as soon as the profile is
`C^∞` there. -/
theorem continuousOn_HkIntegrandK_of_contDiffOn {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2) Qd := by
  have hw : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd :=
    continuousOn_w_Qd.div (continuousOn_sin_rpow_Qd _)
      (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Qd hp) _))
  have h1 : ContinuousOn (fun p : ℝ × ℝ =>
      ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) Qd :=
    continuousOn_finsetSum _ (fun i _ =>
      ((continuousOn_DzIter_Qd hf i).mul hw).pow 2)
  have h2 : ContinuousOn (fun p : ℝ × ℝ =>
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 else 0) Qd := by
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    refine continuousOn_finsetSum _ (fun j _ => ?_)
    by_cases hic : 1 ≤ i ∧ i + j ≤ k
    · simp only [hic, ite_true]
      exact ((continuousOn_mixed_Qd hf j i).mul (continuousOn_Wt_Qd α)).pow 2
    · simp only [hic, ite_false]
      exact continuousOn_const
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 else 0 := by
    funext p
    rw [Work.Spaces.HkIntegrand]
  rw [hfun]
  exact h1.add h2

end Work.FTS.StrongLWP.Xn6Limit
