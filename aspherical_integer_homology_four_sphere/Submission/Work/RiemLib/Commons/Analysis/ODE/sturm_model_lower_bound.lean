import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open Set Filter
open scoped Topology

/-- The model solution `t ↦ sin (2 t) / 2` of the equation `h'' + 4 h = 0`. -/
private noncomputable def model (t : ℝ) : ℝ := Real.sin (2 * t) / 2

private lemma model_apply (t : ℝ) : model t = Real.sin (2 * t) / 2 := rfl

private lemma model_hasDerivAt (t : ℝ) : HasDerivAt model (Real.cos (2 * t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.sin (2 * s)) (Real.cos (2 * t) * 2) t :=
    (hasDerivAt_const_mul (2 : ℝ) (x := t)).sin
  have h2 : HasDerivAt (fun s : ℝ => Real.sin (2 * s) / 2) (Real.cos (2 * t)) t := by
    have h3 := h1.div_const 2
    have he : (Real.cos (2 * t) * 2) / 2 = Real.cos (2 * t) := by ring
    rw [he] at h3
    exact h3
  exact h2

private lemma model_cos_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cos (2 * s)) (-Real.sin (2 * t) * 2) t :=
  (hasDerivAt_const_mul (2 : ℝ) (x := t)).cos

private lemma model_pos {t : ℝ} (h0 : 0 < t) (hπ2 : t < Real.pi / 2) : 0 < model t := by
  have h2t : 0 < 2 * t := by linarith
  have h2tπ : 2 * t < Real.pi := by linarith
  have hsin : 0 < Real.sin (2 * t) := Real.sin_pos_of_pos_of_lt_pi h2t h2tπ
  rw [model_apply]
  linarith

/-- The Wronskian of `h` with the model solution `model`. -/
private noncomputable def wron (h h' : ℝ → ℝ) (t : ℝ) : ℝ :=
  h' t * model t - h t * Real.cos (2 * t)

private lemma wron_unfold (h h' : ℝ → ℝ) :
    wron h h' = fun t => h' t * model t - h t * Real.cos (2 * t) := rfl

private lemma wron_apply (h h' : ℝ → ℝ) (t : ℝ) :
    wron h h' t = h' t * model t - h t * Real.cos (2 * t) := rfl

/-- A function with nonnegative derivative on the interior of `Icc a b` is monotone there. -/
private lemma monotoneOn_Icc_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hder : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hnn : ∀ x ∈ Ioo a b, 0 ≤ f' x) : MonotoneOn f (Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont ?_ ?_
  · rw [interior_Icc]
    exact fun x hx => (hder x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    exact fun x hx => by rw [(hder x hx).deriv]; exact hnn x hx

/-- A function monotone on `(a,b)` with a right limit `L` at `a` dominates `L` on `(a,b)`. -/
private lemma le_of_monotoneOn_of_tendsto_nhdsGT {f : ℝ → ℝ} {a b L : ℝ}
    (hmono : MonotoneOn f (Ioo a b))
    (hlim : Tendsto f (nhdsWithin a (Ioi a)) (nhds L)) :
    ∀ t ∈ Ioo a b, L ≤ f t := by
  intro t ht
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
  exact hmono ⟨hs.1, lt_trans hs.2 ht.2⟩ ht hs.2.le

/-- **Sturm comparison with the model solution `sin (2 t) / 2`.**  Let `h` be a positive solution
of the *inequality* `h'' + 4 h ≥ 0` on `(0,T)` with `T ≤ π/2`, whose Wronskian with the model
vanishes at `0⁺` (hypothesis `hlim`) and which behaves like `t` at the origin (hypothesis `hlim2`).
Then `h` dominates the model solution `t ↦ sin (2 t) / 2`.

This is the analytic heart of **Rauch's comparison theorem** in the normalisation `K_max = 4`: the
norm of a Jacobi field along a unit-speed geodesic grows at least as fast as `sin (2 t) / 2`.  The
proof is the classical Wronskian argument: `W := h' * (sin (2t)/2) - h * cos (2t)` satisfies
`W' = (h'' + 4h) * (sin (2t)/2) ≥ 0` and `W → 0` at `0⁺`, so `W ≥ 0`; hence
`(h / (sin (2t)/2))' = W / (sin (2t)/2)^2 ≥ 0`, so `h / (sin (2t)/2)` is nondecreasing on `(0,T)`
and its limit at `0⁺` is `1`; therefore `h ≥ sin (2t)/2`. -/
theorem sturm_model_lower_bound {h h' : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hTπ : T ≤ Real.pi / 2)
    (hh : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt h (h' t) t)
    (hh2 : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt h' (deriv h' t) t)
    (hineq : ∀ t ∈ Set.Ioo (0 : ℝ) T, 0 ≤ deriv h' t + 4 * h t)
    (hlim : Filter.Tendsto (fun t : ℝ => h' t * (Real.sin (2 * t) / 2) - h t * Real.cos (2 * t))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlim2 : Filter.Tendsto (fun t : ℝ => h t / (Real.sin (2 * t) / 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, Real.sin (2 * t) / 2 ≤ h t := by
  have hlimW : Tendsto (wron h h') (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa only [wron_unfold, model_apply] using hlim
  have hlimR : Tendsto (fun t : ℝ => h t / model t) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    simpa only [model_apply] using hlim2
  -- The derivative of the Wronskian is `(h'' + 4 h) * model`.
  have hWderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (wron h h')
      ((deriv h' t + 4 * h t) * model t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => h' s * model s)
        (deriv h' t * model t + h' t * Real.cos (2 * t)) t :=
      (hh2 t ht).mul (model_hasDerivAt t)
    have h2 : HasDerivAt (fun s : ℝ => h s * Real.cos (2 * s))
        (h' t * Real.cos (2 * t) + h t * (-Real.sin (2 * t) * 2)) t :=
      (hh t ht).mul (model_cos_hasDerivAt t)
    have h3 : HasDerivAt (wron h h')
        ((deriv h' t * model t + h' t * Real.cos (2 * t))
          - (h' t * Real.cos (2 * t) + h t * (-Real.sin (2 * t) * 2))) t := by
      have he : (fun s : ℝ => h' s * model s) - (fun s : ℝ => h s * Real.cos (2 * s))
          = wron h h' := by
        funext s
        simp only [Pi.sub_apply, wron_apply]
      rw [← he]
      exact h1.sub h2
    have heq : (deriv h' t + 4 * h t) * model t
        = (deriv h' t * model t + h' t * Real.cos (2 * t))
          - (h' t * Real.cos (2 * t) + h t * (-Real.sin (2 * t) * 2)) := by
      simp only [model_apply]; ring
    rw [heq]
    exact h3
  have hWderiv_nn : ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ (deriv h' t + 4 * h t) * model t := by
    intro t ht
    exact mul_nonneg (hineq t ht) (le_of_lt (model_pos ht.1 (lt_of_lt_of_le ht.2 hTπ)))
  have hWcont : ContinuousOn (wron h h') (Ioo (0 : ℝ) T) :=
    fun t ht => (hWderiv t ht).continuousAt.continuousWithinAt
  have hWmono : MonotoneOn (wron h h') (Ioo (0 : ℝ) T) := by
    intro x hx y hy hxy
    have hsub : Icc x y ⊆ Ioo (0 : ℝ) T :=
      fun z hz => ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
    have hcont : ContinuousOn (wron h h') (Icc x y) := hWcont.mono hsub
    have hder : ∀ z ∈ Ioo x y, HasDerivAt (wron h h') ((deriv h' z + 4 * h z) * model z) z :=
      fun z hz => hWderiv z ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩
    have hnn : ∀ z ∈ Ioo x y, 0 ≤ (deriv h' z + 4 * h z) * model z :=
      fun z hz => hWderiv_nn z ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩
    exact (monotoneOn_Icc_of_hasDerivAt_nonneg hcont hder hnn)
      (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy
  have hWnn : ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ wron h h' t :=
    le_of_monotoneOn_of_tendsto_nhdsGT hWmono hlimW
  -- The derivative of the ratio `h / model` is `wron / model ^ 2`.
  have hRderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s : ℝ => h s / model s)
      (wron h h' t / model t ^ 2) t := by
    intro t ht
    have hpos : 0 < model t := model_pos ht.1 (lt_of_lt_of_le ht.2 hTπ)
    have hdiv := (hh t ht).div (model_hasDerivAt t) (ne_of_gt hpos)
    have he : wron h h' t = h' t * model t - h t * Real.cos (2 * t) := wron_apply h h' t
    rw [he]
    exact hdiv
  have hRderiv_nn : ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ wron h h' t / model t ^ 2 := by
    intro t ht
    exact div_nonneg (hWnn t ht) (sq_nonneg _)
  have hRcont : ContinuousOn (fun s : ℝ => h s / model s) (Ioo (0 : ℝ) T) :=
    fun t ht => (hRderiv t ht).continuousAt.continuousWithinAt
  have hRmono : MonotoneOn (fun s : ℝ => h s / model s) (Ioo (0 : ℝ) T) := by
    intro x hx y hy hxy
    have hsub : Icc x y ⊆ Ioo (0 : ℝ) T :=
      fun z hz => ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
    have hcont : ContinuousOn (fun s : ℝ => h s / model s) (Icc x y) := hRcont.mono hsub
    have hder : ∀ z ∈ Ioo x y,
        HasDerivAt (fun s : ℝ => h s / model s) (wron h h' z / model z ^ 2) z :=
      fun z hz => hRderiv z ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩
    have hnn : ∀ z ∈ Ioo x y, 0 ≤ wron h h' z / model z ^ 2 :=
      fun z hz => hRderiv_nn z ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩
    exact (monotoneOn_Icc_of_hasDerivAt_nonneg hcont hder hnn)
      (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy
  have hRge : ∀ t ∈ Ioo (0 : ℝ) T, 1 ≤ h t / model t :=
    le_of_monotoneOn_of_tendsto_nhdsGT hRmono hlimR
  intro t ht
  have hpos : 0 < model t := model_pos ht.1 (lt_of_lt_of_le ht.2 hTπ)
  have h1 : model t ≤ h t := by
    have h2 := (le_div_iff₀ hpos).mp (hRge t ht)
    simpa using h2
  rw [model_apply] at h1
  exact h1

end Commons.Analysis.ODE