import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Commons.Analysis.ODE.sturm_model_lower_bound

namespace Commons.Analysis.ODE

open Set Filter
open scoped Topology

private lemma monotoneOn_Icc_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hder : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hnn : ∀ x ∈ Ioo a b, 0 ≤ f' x) : MonotoneOn f (Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont ?_ ?_
  · rw [interior_Icc]
    exact fun x hx => (hder x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    exact fun x hx => by rw [(hder x hx).deriv]; exact hnn x hx

private lemma le_of_monotoneOn_of_tendsto_nhdsGT {f : ℝ → ℝ} {a b L : ℝ}
    (hmono : MonotoneOn f (Ioo a b))
    (hlim : Tendsto f (nhdsWithin a (Ioi a)) (nhds L)) :
    ∀ t ∈ Ioo a b, L ≤ f t := by
  intro t ht
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
  exact hmono ⟨hs.1, lt_trans hs.2 ht.2⟩ ht hs.2.le

/-- The Wronskian of `h` with the model solution `t ↦ sin (r t) / r`, `r = √K`. -/
private noncomputable def wron (h h' : ℝ → ℝ) (r t : ℝ) : ℝ :=
  h' t * (Real.sin (r * t) / r) - h t * Real.cos (r * t)

private lemma wron_unfold (h h' : ℝ → ℝ) (r : ℝ) :
    wron h h' r = fun t => h' t * (Real.sin (r * t) / r) - h t * Real.cos (r * t) := rfl

private lemma wron_apply (h h' : ℝ → ℝ) (r t : ℝ) :
    wron h h' r t = h' t * (Real.sin (r * t) / r) - h t * Real.cos (r * t) := rfl

theorem sturm_model_lower_bound_general {h h' : ℝ → ℝ} {T K : ℝ} (hK : 0 < K) (hT : 0 < T)
    (hTπ : T ≤ Real.pi / Real.sqrt K)
    (hh : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt h (h' t) t)
    (hh2 : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt h' (deriv h' t) t)
    (hineq : ∀ t ∈ Set.Ioo (0 : ℝ) T, 0 ≤ deriv h' t + K * h t)
    (hlim : Filter.Tendsto
      (fun t : ℝ => h' t * (Real.sin (Real.sqrt K * t) / Real.sqrt K)
        - h t * Real.cos (Real.sqrt K * t)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlim2 : Filter.Tendsto
      (fun t : ℝ => h t / (Real.sin (Real.sqrt K * t) / Real.sqrt K))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, Real.sin (Real.sqrt K * t) / Real.sqrt K ≤ h t := by
  set r : ℝ := Real.sqrt K with hrdef
  have hr : 0 < r := by
    rw [hrdef]; exact Real.sqrt_pos_of_pos hK
  have hr2 : r * r = K := by
    rw [hrdef, ← sq]; exact Real.sq_sqrt (le_of_lt hK)
  have hrnz : r ≠ 0 := ne_of_gt hr
  -- The model solution is positive on `(0,T)`, because `T ≤ π/r`.
  have hpos : ∀ t ∈ Ioo (0 : ℝ) T, 0 < Real.sin (r * t) / r := by
    intro t ht
    have hrt_pos : 0 < r * t := mul_pos hr ht.1
    have hrt_pi : r * t < Real.pi := by
      have hlt : r * t < r * (Real.pi / r) :=
        mul_lt_mul_of_pos_left (lt_of_lt_of_le ht.2 hTπ) hr
      have he : r * (Real.pi / r) = Real.pi := by field_simp
      rwa [he] at hlt
    have hsin : 0 < Real.sin (r * t) := Real.sin_pos_of_pos_of_lt_pi hrt_pos hrt_pi
    exact div_pos hsin hr
  -- Derivative of the model solution.
  have hsin_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.sin (r * s) / r)
      (Real.cos (r * t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => Real.sin (r * s)) (Real.cos (r * t) * r) t :=
      (hasDerivAt_const_mul r (x := t)).sin
    have h2 := h1.div_const r
    have he : Real.cos (r * t) * r / r = Real.cos (r * t) := by field_simp
    rwa [he] at h2
  have hcos_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.cos (r * s))
      ((-Real.sin (r * t)) * r) t := by
    intro t
    exact (hasDerivAt_const_mul r (x := t)).cos
  have hlimW : Tendsto (wron h h' r) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa only [wron_unfold] using hlim
  have hlimR : Tendsto (fun t : ℝ => h t / (Real.sin (r * t) / r))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    simpa only using hlim2
  -- The derivative of the Wronskian is `(h'' + K h) * model`.
  have hWderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (wron h h' r)
      ((deriv h' t + K * h t) * (Real.sin (r * t) / r)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => h' s * (Real.sin (r * s) / r))
        (deriv h' t * (Real.sin (r * t) / r) + h' t * Real.cos (r * t)) t :=
      (hh2 t ht).mul (hsin_deriv t)
    have h2 : HasDerivAt (fun s : ℝ => h s * Real.cos (r * s))
        (h' t * Real.cos (r * t) + h t * ((-Real.sin (r * t)) * r)) t :=
      (hh t ht).mul (hcos_deriv t)
    have h3 : HasDerivAt
        (fun s : ℝ => h' s * (Real.sin (r * s) / r) - h s * Real.cos (r * s))
        ((deriv h' t * (Real.sin (r * t) / r) + h' t * Real.cos (r * t))
          - (h' t * Real.cos (r * t) + h t * ((-Real.sin (r * t)) * r))) t := h1.sub h2
    have h4 : HasDerivAt (wron h h' r)
        ((deriv h' t * (Real.sin (r * t) / r) + h' t * Real.cos (r * t))
          - (h' t * Real.cos (r * t) + h t * ((-Real.sin (r * t)) * r))) t := by
      simpa only [wron_unfold] using h3
    have heq : (deriv h' t + K * h t) * (Real.sin (r * t) / r)
        = (deriv h' t * (Real.sin (r * t) / r) + h' t * Real.cos (r * t))
          - (h' t * Real.cos (r * t) + h t * ((-Real.sin (r * t)) * r)) := by
      rw [← hr2]; field_simp; ring
    rw [heq]
    exact h4
  have hWderiv_nn : ∀ t ∈ Ioo (0 : ℝ) T,
      0 ≤ (deriv h' t + K * h t) * (Real.sin (r * t) / r) := by
    intro t ht
    exact mul_nonneg (hineq t ht) (le_of_lt (hpos t ht))
  have hWcont : ContinuousOn (wron h h' r) (Ioo (0 : ℝ) T) :=
    fun t ht => (hWderiv t ht).continuousAt.continuousWithinAt
  have hWmono : MonotoneOn (wron h h' r) (Ioo (0 : ℝ) T) := by
    intro x hx y hy hxy
    have hsub : Icc x y ⊆ Ioo (0 : ℝ) T :=
      fun z hz => ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
    have hcont : ContinuousOn (wron h h' r) (Icc x y) := hWcont.mono hsub
    have hder : ∀ z ∈ Ioo x y, HasDerivAt (wron h h' r)
        ((deriv h' z + K * h z) * (Real.sin (r * z) / r)) z :=
      fun z hz => hWderiv z ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩
    have hnn : ∀ z ∈ Ioo x y, 0 ≤ (deriv h' z + K * h z) * (Real.sin (r * z) / r) :=
      fun z hz => hWderiv_nn z ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩
    exact (monotoneOn_Icc_of_hasDerivAt_nonneg hcont hder hnn)
      (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy
  have hWnn : ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ wron h h' r t :=
    le_of_monotoneOn_of_tendsto_nhdsGT hWmono hlimW
  -- The derivative of the ratio `h / model` is `wron / model ^ 2`.
  have hRderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s : ℝ => h s / (Real.sin (r * s) / r))
      (wron h h' r t / (Real.sin (r * t) / r) ^ 2) t := by
    intro t ht
    have hpost : 0 < Real.sin (r * t) / r := hpos t ht
    have hdiv := (hh t ht).div (hsin_deriv t) (ne_of_gt hpost)
    exact hdiv
  have hRderiv_nn : ∀ t ∈ Ioo (0 : ℝ) T,
      0 ≤ wron h h' r t / (Real.sin (r * t) / r) ^ 2 := by
    intro t ht
    exact div_nonneg (hWnn t ht) (sq_nonneg _)
  have hRcont : ContinuousOn (fun s : ℝ => h s / (Real.sin (r * s) / r)) (Ioo (0 : ℝ) T) :=
    fun t ht => (hRderiv t ht).continuousAt.continuousWithinAt
  have hRmono : MonotoneOn (fun s : ℝ => h s / (Real.sin (r * s) / r)) (Ioo (0 : ℝ) T) := by
    intro x hx y hy hxy
    have hsub : Icc x y ⊆ Ioo (0 : ℝ) T :=
      fun z hz => ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
    have hcont : ContinuousOn (fun s : ℝ => h s / (Real.sin (r * s) / r)) (Icc x y) :=
      hRcont.mono hsub
    have hder : ∀ z ∈ Ioo x y, HasDerivAt (fun s : ℝ => h s / (Real.sin (r * s) / r))
        (wron h h' r z / (Real.sin (r * z) / r) ^ 2) z :=
      fun z hz => hRderiv z ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩
    have hnn : ∀ z ∈ Ioo x y, 0 ≤ wron h h' r z / (Real.sin (r * z) / r) ^ 2 :=
      fun z hz => hRderiv_nn z ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩
    exact (monotoneOn_Icc_of_hasDerivAt_nonneg hcont hder hnn)
      (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy
  have hRge : ∀ t ∈ Ioo (0 : ℝ) T, 1 ≤ h t / (Real.sin (r * t) / r) :=
    le_of_monotoneOn_of_tendsto_nhdsGT hRmono hlimR
  intro t ht
  have hpost : 0 < Real.sin (r * t) / r := hpos t ht
  have h1 : Real.sin (r * t) / r ≤ h t := by
    have h2 := (le_div_iff₀ hpost).mp (hRge t ht)
    simpa using h2
  exact h1

end Commons.Analysis.ODE