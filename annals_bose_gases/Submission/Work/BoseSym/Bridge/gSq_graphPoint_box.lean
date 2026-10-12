import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — `gSq` of the graph point of a box test function

For a test function `F` supported in the open box, the squared `L²` norm of its
gradient (`gSq (graphPoint N L F)`) is the box integral of the pointwise squared
gradient.  The `3N` gradient components are indexed by `GIdx N = Fin N × Fin 3`;
the right-hand side splits that index into the double sum over the particle
`i : Fin N` and the coordinate `k : Fin 3`.

The two ingredients are:

* `norm_sq_toLp_eq_integral` — the squared `L²` norm of `MemLp.toLp g` is the
  integral of the pointwise square of `g`;
* `integral_eq_intBox_of_support` — a function supported in the box has the same
  integral over the whole configuration space as over the box,

together with the swap of the finite sum outside the integral with the integral
of the pointwise sum (`integral_finsetSum`).

## Main results

* `norm_sq_toLp_eq_integral`
* `integral_eq_intBox_of_support`
* `gSq_graphPoint_box`
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open BoseGases Submission.BoseGases
open scoped Topology Real ContDiff ENNReal

/-- The squared `L²` norm of `MemLp.toLp g` is the integral of the pointwise
square of `g`. -/
lemma norm_sq_toLp_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : α → ℝ) (hg : MemLp g 2 μ) :
    ‖MemLp.toLp g hg‖ ^ 2 = ∫ x, (g x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq (MemLp.toLp g hg), MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hg] with x hx
  rw [hx, Real.inner_apply]
  ring

/-- A function vanishing outside the box has the same integral over the whole
configuration space as over the box. -/
lemma integral_eq_intBox_of_support {N : ℕ} {L : ℝ} {f : Conf N → ℝ}
    (hf : ∀ x, x ∉ box N L → f x = 0) :
    ∫ x, f x ∂(volC N) = ∫ x in box N L, f x :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm

theorem gSq_graphPoint_box {N : ℕ} {L : ℝ} (F : testSub N L) :
    gSq (graphPoint N L F) = intBox N L (fun x => ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ (F : Conf N → ℝ) x (eDir N i k)) ^ 2) := by
  -- `eDir` is `kcDir` and `intBox` is the integral over `box N L`
  simp only [eDir, intBox]
  -- the `j`-th gradient component `x ↦ fderiv F x (kcDir N j.1 j.2)`
  have hgrad : ∀ j : GIdx N, ContDiff ℝ ∞
      (fun x : Conf N => fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) :=
    fun j => firstDir_contDiff F.2.1 (kcDir N j.1 j.2)
  have htsupF : ∀ j : GIdx N,
      tsupport (fun x : Conf N => fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2))
        ⊆ tsupport (F : Conf N → ℝ) :=
    fun j => tsupport_firstDir_subset (kcDir N j.1 j.2)
  have htsup : ∀ j : GIdx N,
      tsupport (fun x : Conf N => fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2))
        ⊆ box N L :=
    fun j => (htsupF j).trans (F.2.2.trans openBox_subset_box)
  have hhcs : ∀ j : GIdx N,
      HasCompactSupport (fun x : Conf N => fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) :=
    fun j => IsCompact.of_isClosed_subset (hasCompactSupport_of_testFun F.2)
      (isClosed_tsupport _) (htsupF j)
  -- the squared gradient components are integrable
  have hint : ∀ j : GIdx N, Integrable
      (fun x : Conf N => (fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) ^ 2) (volC N) := by
    intro j
    refine Continuous.integrable_of_hasCompactSupport ((hgrad j).continuous.pow 2) ?_
    refine IsCompact.of_isClosed_subset (hhcs j) (isClosed_tsupport _) ?_
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro h0
      exact hx (by rw [h0]; norm_num))
  -- squared `L²` norms, as integrals of the pointwise squares
  have hA : gSq (graphPoint N L F) = ∑ j : GIdx N,
      ∫ x, (fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) ^ 2 ∂(volC N) := by
    simp only [gSq, graphPoint]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact norm_sq_toLp_eq_integral _ _
  -- sum of the integrals is the integral of the sum
  have hB : (∑ j : GIdx N, ∫ x, (fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) ^ 2 ∂(volC N))
      = ∫ x, (∑ j : GIdx N, (fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) ^ 2) ∂(volC N) := by
    have h := integral_finsetSum (μ := volC N) (s := Finset.univ)
      (f := fun (j : GIdx N) (x : Conf N) =>
        (fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) ^ 2)
      (fun j _ => hint j)
    simpa using h.symm
  -- the pointwise sum is supported in the box, so the integral over the whole
  -- space is the integral over the box
  have hC : (∫ x, (∑ j : GIdx N, (fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) ^ 2) ∂(volC N))
      = ∫ x in box N L, (∑ j : GIdx N,
          (fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) ^ 2) := by
    refine integral_eq_intBox_of_support ?_
    intro x hx
    refine Finset.sum_eq_zero fun j _ => ?_
    have hxj : x ∉ tsupport
        (fun y : Conf N => fderiv ℝ (F : Conf N → ℝ) y (kcDir N j.1 j.2)) :=
      fun hmem => hx (htsup j hmem)
    rw [image_eq_zero_of_notMem_tsupport hxj]
    norm_num
  -- split the index `GIdx N = Fin N × Fin 3` into particle and coordinate
  have hD : (∫ x in box N L, (∑ j : GIdx N,
        (fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) ^ 2))
      = ∫ x in box N L, (∑ i : Fin N, ∑ k : Fin 3,
          (fderiv ℝ (F : Conf N → ℝ) x (kcDir N i k)) ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact Fintype.sum_prod_type (fun j : Fin N × Fin 3 =>
      (fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2)) ^ 2)
  exact hA.trans (hB.trans (hC.trans hD))

end Work.BoseSym.Bridge
