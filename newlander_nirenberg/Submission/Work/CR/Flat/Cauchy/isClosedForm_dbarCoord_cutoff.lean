import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm
import Submission.Work.CR.Flat.Polydisc.isClosedForm_dbarCoord

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open Set

/-! ### Auxiliary facts about a cut-off vanishing outside a polydisc -/

/-- If `η` vanishes as soon as some coordinate satisfies `ρo i ≤ ‖z i - c i‖` (i.e. `η` is
supported in the open polydisc `P(ρo)`), then `η` vanishes on a whole neighbourhood of every
point outside the closure of `P(ρo)`: such a point has a neighbourhood which misses the polydisc,
and every point outside the polydisc satisfies `ρo i ≤ ‖z i - c i‖` for some `i`. -/
lemma eventuallyEq_zero_of_notMem_closure_polydisc {n : ℕ} {c : Fin n → ℂ} {ρo : Fin n → ℝ}
    {η : (Fin n → ℂ) → ℂ}
    (hηsupp : ∀ z, (∃ i, ρo i ≤ ‖z i - c i‖) → η z = 0)
    {z : Fin n → ℂ} (hz : z ∉ closure (polydisc c ρo)) :
    η =ᶠ[nhds z] 0 := by
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε > 0, ∀ y ∈ polydisc c ρo, ε ≤ dist z y := by
    by_contra h
    push_neg at h
    exact hz (Metric.mem_closure_iff.mpr h)
  filter_upwards [Metric.ball_mem_nhds z hεpos] with y hy
  have hy' : dist z y < ε := by simpa [dist_comm] using Metric.mem_ball.mp hy
  have hyn : y ∉ polydisc c ρo := fun hyP => (not_lt.mpr (hε y hyP)) hy'
  exact hηsupp y (by simpa only [polydisc, Set.mem_ofPred_eq, not_forall, not_lt] using hyn)

/-- A function vanishing on a neighbourhood of a point has `∂̄`-derivative `0` there (the
`fderiv` of a function which is locally `0` is `0`). -/
lemma dbarCoord_eq_zero_of_eventuallyEq_zero {n : ℕ} (j : Fin n) {η : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (h : η =ᶠ[nhds z] 0) : dbarCoord j η z = 0 := by
  have hfd : fderiv ℝ η z = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq h]
    simp
  simp [dbarCoord, hfd]

/-- **The `∂̄` of a cut-off of a solution is closed.**

Let `f` be a closed `(0,1)`-form on the polydisc `P(ρo)` with `∂̄_j u = f_j` there, and let `η` be
`C²` with `η z = 0` as soon as `∃ i, ρo i ≤ ‖z i - c i‖` (so `η` is supported in the open polydisc).
Then the form `j ↦ ∂̄_j (η · u)` is closed.

This is `∂̄² = 0` for the function `η · u`, which is only `C^1` when `k = 0`, so the proof must be
algebraic rather than an appeal to `isClosedForm_dbarCoord`: at every point,
`g_j := ∂̄_j (η u) = η · ∂̄_j u + u · ∂̄_j η`, and hence (Leibniz for `∂̄`, symmetry of the second
derivatives of `η`, and closedness of `f`)
`∂̄_k g_j - ∂̄_j g_k = ∂̄_k η · (f_j - ∂̄_j u) - ∂̄_j η · (f_k - ∂̄_k u)`.
For `z ∈ P(ρo)` both brackets vanish by hypothesis.  For `z ∉ P(ρo`), some `‖z i - c i‖ ≥ ρo i > `
any point of the support of `η` in that coordinate, so `η` — and therefore `∂̄ η`, and `g` itself —
vanishes in a whole neighbourhood of `z`, and both sides are `0`.  (Care is needed when
`k = 0`: then `g` need not be everywhere differentiable, and at points where it is not,
`dbarCoord` is `0` by the junk-value convention of `fderiv`.) -/
theorem isClosedForm_dbarCoord_cutoff {n : ℕ} {c : Fin n → ℂ} {ρo : Fin n → ℝ} {k : ℕ}
    {u : (Fin n → ℂ) → ℂ} {f : Fin n → (Fin n → ℂ) → ℂ} {η : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ (k + 1) u) (hf : ∀ j, ContDiff ℝ (k + 1) (f j))
    (hη : ContDiff ℝ (k + 2) η)
    (hfcl : Work.CR.Flat.IsClosedForm f)
    (heq : ∀ j z, (∀ i, ‖z i - c i‖ < ρo i) → Work.CR.Flat.dbarCoord j u z = f j z)
    (hηsupp : ∀ z, (∃ i, ρo i ≤ ‖z i - c i‖) → η z = 0) :
    Work.CR.Flat.IsClosedForm (fun j => Work.CR.Flat.dbarCoord j (fun z => η z * u z)) := by
  -- ## smoothness bookkeeping
  have hu1 : ContDiff ℝ (1 : WithTop ℕ∞) u := hu.of_le (by simp)
  have hη2 : ContDiff ℝ (2 : WithTop ℕ∞) η := hη.of_le (by simp)
  have hη1 : ContDiff ℝ (1 : WithTop ℕ∞) η := hη2.of_le (by simp)
  have hf1 : ∀ j : Fin n, ContDiff ℝ (1 : WithTop ℕ∞) (f j) :=
    fun j => (hf j).of_le (by simp)
  have hud : Differentiable ℝ u := hu1.differentiable (by simp)
  have hηd : Differentiable ℝ η := hη2.differentiable (by simp)
  have hfd : ∀ j : Fin n, Differentiable ℝ (f j) :=
    fun j => (hf1 j).differentiable (by simp)
  -- the `∂̄` of `η` is `C¹`
  have hdη1 : ∀ j : Fin n, ContDiff ℝ (1 : WithTop ℕ∞) (Work.CR.Flat.dbarCoord j η) := by
    intro j
    rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp j η]
    exact (Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.comp
      (hη2.fderiv_right (m := 1) (by norm_num))
  have hdηd : ∀ j : Fin n, Differentiable ℝ (Work.CR.Flat.dbarCoord j η) :=
    fun j => (hdη1 j).differentiable (by simp)
  -- the `∂̄` of `u` is continuous
  have hducont : ∀ j : Fin n, Continuous (Work.CR.Flat.dbarCoord j u) := by
    intro j
    rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp j u]
    exact (Work.CR.Flat.Polydisc.dbarCoordPhi j).continuous.comp (hu1.continuous_fderiv (by simp))
  -- ## the pointwise identity `∂̄_j (η u) = η · f_j + u · ∂̄_j η`
  -- (`η` vanishes on the complement of the polydisc, so `η · ∂̄_j u = η · f_j` everywhere)
  have hG_eq : ∀ j : Fin n, (fun z => Work.CR.Flat.dbarCoord j (fun w => η w * u w) z)
      = fun z => η z * f j z + u z * Work.CR.Flat.dbarCoord j η z := by
    intro j
    funext z
    rw [Work.CR.Flat.Polydisc.dbarCoord_mul j η u z hηd.differentiableAt hud.differentiableAt]
    by_cases hz : η z = 0
    · rw [hz]; ring
    · have hzP : ∀ i, ‖z i - c i‖ < ρo i := by
        by_contra h
        push_neg at h
        exact hz (hηsupp z h)
      rw [heq j z hzP]; ring
  -- ## `f j - ∂̄_j u` vanishes on the closure of the polydisc
  -- (both `f j` and `∂̄_j u` are continuous, and `η` can only be non-zero inside `P(ρo)`, so the
  -- difference vanishes on the (dense) polydisc and hence at every boundary point as well — this
  -- is what replaces the appeal to `∂̄² = 0`, which is unavailable when `k = 0`)
  have hRzero : ∀ j : Fin n, ∀ z : Fin n → ℂ, z ∈ closure (polydisc c ρo) →
      f j z = Work.CR.Flat.dbarCoord j u z := by
    intro j z hz
    have hcont : Continuous (fun y : Fin n → ℂ => f j y - Work.CR.Flat.dbarCoord j u y) :=
      ((hf j).continuous).sub (hducont j)
    have hclosed : IsClosed {y : Fin n → ℂ | f j y - Work.CR.Flat.dbarCoord j u y = 0} :=
      isClosed_eq hcont continuous_const
    have hsub : polydisc c ρo ⊆ {y : Fin n → ℂ | f j y - Work.CR.Flat.dbarCoord j u y = 0} := by
      intro y hy
      show f j y - Work.CR.Flat.dbarCoord j u y = 0
      rw [heq j y hy, sub_self]
    exact sub_eq_zero.mp (closure_minimal hsub hclosed hz)
  -- ## `∂̄ η` vanishes outside the closure of the polydisc
  have hdηzero : ∀ j : Fin n, ∀ z : Fin n → ℂ, z ∉ closure (polydisc c ρo) →
      Work.CR.Flat.dbarCoord j η z = 0 :=
    fun j z hz => dbarCoord_eq_zero_of_eventuallyEq_zero j
      (eventuallyEq_zero_of_notMem_closure_polydisc hηsupp hz)
  -- ## the second derivatives of `η u`
  have hExp : ∀ (j k : Fin n) (z : Fin n → ℂ),
      Work.CR.Flat.dbarCoord k (fun y => Work.CR.Flat.dbarCoord j (fun w => η w * u w) y) z
        = Work.CR.Flat.dbarCoord k η z * f j z + η z * Work.CR.Flat.dbarCoord k (f j) z
          + Work.CR.Flat.dbarCoord k u z * Work.CR.Flat.dbarCoord j η z
          + u z * Work.CR.Flat.dbarCoord k (Work.CR.Flat.dbarCoord j η) z := by
    intro j k z
    have hsub : (fun y : Fin n → ℂ => Work.CR.Flat.dbarCoord j (fun w => η w * u w) y)
        = fun y => η y * f j y + u y * Work.CR.Flat.dbarCoord j η y := hG_eq j
    rw [hsub, Work.CR.Flat.Polydisc.dbarCoord_add k (fun y => η y * f j y)
      (fun y => u y * Work.CR.Flat.dbarCoord j η y) z
      ((hη1.mul (hf1 j)).differentiable (by simp)).differentiableAt
      ((hud.mul (hdηd j)).differentiableAt)]
    rw [Work.CR.Flat.Polydisc.dbarCoord_mul k η (f j) z hηd.differentiableAt
          (hfd j).differentiableAt,
        Work.CR.Flat.Polydisc.dbarCoord_mul k u (Work.CR.Flat.dbarCoord j η) z
          hud.differentiableAt (hdηd j).differentiableAt]
    ring
  -- ## conclude
  intro j k z
  show Work.CR.Flat.dbarCoord k (fun y => Work.CR.Flat.dbarCoord j (fun w => η w * u w) y) z
      = Work.CR.Flat.dbarCoord j (fun y => Work.CR.Flat.dbarCoord k (fun w => η w * u w) y) z
  rw [hExp j k z, hExp k j z]
  by_cases hz : z ∈ closure (polydisc c ρo)
  · rw [hRzero j z hz, hRzero k z hz, hfcl j k z,
      Work.CR.Flat.Polydisc.dbarCoord_comm j k η z (hη2.contDiffAt (x := z))]
    ring
  · rw [hdηzero k z hz, hdηzero j z hz, hfcl j k z,
      Work.CR.Flat.Polydisc.dbarCoord_comm j k η z (hη2.contDiffAt (x := z))]
    ring

end Work.CR.Flat.Cauchy
