import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Smooth.Slice

/-!
# Differentiability and continuity of iterated slice derivatives

For a `C^∞` function `F : ℝ × ℝ → ℝ` on an open set `V`, the `k`-th iterated derivative of the
slice `u ↦ F (u, t)` at `s` is again differentiable in `s`, with derivative the `(k+1)`-st
iterated derivative; and it is continuous in the parameter `t`.

Both statements are proved by identifying the slice derivatives with the iterates `pderiv1Iter`
of the first partial derivative (`Smooth/Slice.lean`), for which smoothness is automatic.
-/

namespace Work.OddVolterra.Existence

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

noncomputable section

/-- The `k`-th iterated derivative of the slice `u ↦ F (u, t)` is differentiable in `s`, with
derivative the `(k+1)`-st iterated derivative. -/
theorem hasDerivAt_iteratedDeriv_section {V : Set (ℝ × ℝ)} (hV : IsOpen V) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V) (k : ℕ) {s t : ℝ} (hst : (s, t) ∈ V) :
    HasDerivAt (fun s' : ℝ => iteratedDeriv k (fun u : ℝ => F (u, t)) s')
      (iteratedDeriv (k + 1) (fun u : ℝ => F (u, t)) s) s := by
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞) (Work.OddVolterra.Smooth.pderiv1Iter V k F) V :=
    Work.OddVolterra.Smooth.contDiffOn_pderiv1Iter hV hF k
  have h1 : HasDerivAt (fun s' : ℝ => Work.OddVolterra.Smooth.pderiv1Iter V k F (s', t))
      (Work.OddVolterra.Smooth.pderiv1 V (Work.OddVolterra.Smooth.pderiv1Iter V k F) (s, t)) s :=
    Work.OddVolterra.Smooth.hasDerivAt_slice hV hcd hst
  have hmem : ∀ᶠ s' in 𝓝 s, (s', t) ∈ V :=
    (continuous_id.prodMk continuous_const).tendsto s (hV.mem_nhds hst)
  have heq : (fun s' : ℝ => iteratedDeriv k (fun u : ℝ => F (u, t)) s')
      =ᶠ[𝓝 s] (fun s' : ℝ => Work.OddVolterra.Smooth.pderiv1Iter V k F (s', t)) := by
    filter_upwards [hmem] with s' hs'
    exact Work.OddVolterra.Smooth.iteratedDeriv_eq_pderiv1Iter hV hF hs' k
  have hderiv : Work.OddVolterra.Smooth.pderiv1 V (Work.OddVolterra.Smooth.pderiv1Iter V k F) (s, t)
      = iteratedDeriv (k + 1) (fun u : ℝ => F (u, t)) s := by
    rw [← Work.OddVolterra.Smooth.pderiv1Iter_succ]
    exact (Work.OddVolterra.Smooth.iteratedDeriv_eq_pderiv1Iter hV hF hst (k + 1)).symm
  rw [hderiv] at h1
  exact h1.congr_of_eventuallyEq heq

/-- The `k`-th iterated derivative of the slice `u ↦ F (u, t)` is continuous in the parameter
`t`. -/
theorem continuousAt_iteratedDeriv_section {V : Set (ℝ × ℝ)} (hV : IsOpen V) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V) (k : ℕ) {v t : ℝ} (hvt : (v, t) ∈ V) :
    ContinuousAt (fun t' : ℝ => iteratedDeriv k (fun u : ℝ => F (u, t')) v) t := by
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞) (Work.OddVolterra.Smooth.pderiv1Iter V k F) V :=
    Work.OddVolterra.Smooth.contDiffOn_pderiv1Iter hV hF k
  have h2 : ContinuousAt (fun t' : ℝ => (v, t')) t := by fun_prop
  have hcont : ContinuousAt (fun t' : ℝ => Work.OddVolterra.Smooth.pderiv1Iter V k F (v, t')) t :=
    (hcd.continuousOn.continuousAt (hV.mem_nhds hvt)).comp h2
  have hmem : ∀ᶠ t' in 𝓝 t, (v, t') ∈ V :=
    (continuous_const.prodMk continuous_id).tendsto t (hV.mem_nhds hvt)
  have heq : (fun t' : ℝ => Work.OddVolterra.Smooth.pderiv1Iter V k F (v, t'))
      =ᶠ[𝓝 t] (fun t' : ℝ => iteratedDeriv k (fun u : ℝ => F (u, t')) v) := by
    filter_upwards [hmem] with t' ht'
    exact (Work.OddVolterra.Smooth.iteratedDeriv_eq_pderiv1Iter hV hF ht' k).symm
  exact hcont.congr heq

/-- The slice derivative is interval integrable in the parameter, as long as the slices stay in
the domain. -/
theorem intervalIntegrable_iteratedDeriv_section {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V) (k : ℕ) {v a b : ℝ}
    (hv : ∀ t ∈ Set.uIcc a b, (v, t) ∈ V) :
    IntervalIntegrable (fun t : ℝ => iteratedDeriv k (fun u : ℝ => F (u, t)) v) volume a b := by
  have hcontOn : ContinuousOn (fun t : ℝ => iteratedDeriv k (fun u : ℝ => F (u, t)) v)
      (Set.uIcc a b) :=
    fun t ht => (continuousAt_iteratedDeriv_section hV hF k (hv t ht)).continuousWithinAt
  exact hcontOn.intervalIntegrable

end

end Work.OddVolterra.Existence
