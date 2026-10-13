import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllSol.VthAux.traceAux

/-- **Weighted Hardy inequality with a general primitive.**

For `0 < a < 1`, `0 < δ ≤ θ₀` and `ψ ≥ 0` continuous on `[δ, θ₀]`,

`∫_δ^{θ₀} θ^{a-1} (∫_θ^{θ₀} ψ) dθ ≤ (1/a) ∫_δ^{θ₀} θ^a ψ(θ) dθ`.

*Proof.* Integration by parts with `u(θ) = ∫_θ^{θ₀} ψ` (so `u' = -ψ`) and
`v(θ) = θ^a/a` (so `v' = θ^{a-1}`) on `[δ, θ₀]` gives the exact identity

`∫_δ^{θ₀} θ^{a-1} (∫_θ^{θ₀} ψ) = u θ₀ v θ₀ - u δ v δ + (1/a) ∫_δ^{θ₀} θ^a ψ`

with `u θ₀ = 0` and `u δ ≥ 0`, so the boundary term `-u δ v δ = -(δ^a/a) ∫_δ^{θ₀} ψ` is
nonpositive.  (Equivalently: the triangular region can be swapped, giving
`∫_δ^{θ₀} ψ(s) (s^a - δ^a)/a ds ≤ (1/a) ∫_δ^{θ₀} s^a ψ(s) ds`.) -/
theorem hardyPowPrimIbp {a δ θ₀ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hδ : 0 < δ)
    (hδθ : δ ≤ θ₀) {ψ : ℝ → ℝ} (hψc : ContinuousOn ψ (Set.Icc δ θ₀))
    (hψnn : ∀ s ∈ Set.Icc δ θ₀, 0 ≤ ψ s) :
    ∫ θ in δ..θ₀, θ ^ (a - 1) * (∫ s in θ..θ₀, ψ s) ≤ (1 / a) * ∫ θ in δ..θ₀, θ ^ a * ψ θ := by
  have ha : a ≠ 0 := ne_of_gt ha0
  have _ha1 : a < 1 := ha1
  have hsub : Set.Ioo δ θ₀ ⊆ Set.Icc δ θ₀ := fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hψsm : ∀ x ∈ Set.Ioo δ θ₀, StronglyMeasurableAtFilter ψ (nhds x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hψc.mono hsub)
  have hcont_u : ContinuousOn (fun θ => ∫ s in θ..θ₀, ψ s) (Set.uIcc δ θ₀) := by
    apply intervalIntegral.continuousOn_primitive_interval_left
    rw [Set.uIcc_of_le hδθ]
    exact hψc.integrableOn_Icc
  have hcont_v : ContinuousOn (fun θ => θ ^ a / a) (Set.uIcc δ θ₀) :=
    (ContinuousOn.rpow_const continuousOn_id (fun x _ => Or.inr (le_of_lt ha0))).div_const a
  have hder_u : ∀ θ ∈ Set.Ioo (min δ θ₀) (max δ θ₀),
      HasDerivAt (fun θ => ∫ s in θ..θ₀, ψ s) (-ψ θ) θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo δ θ₀ := by
      rwa [min_eq_left hδθ, max_eq_right hδθ] at hθ
    exact intervalIntegral.integral_hasDerivAt_left
      ((hψc.mono (Set.Icc_subset_Icc (le_of_lt hθ'.1) le_rfl)).intervalIntegrable_of_Icc
        (le_of_lt hθ'.2))
      (hψsm θ hθ') (hψc.continuousAt (Icc_mem_nhds hθ'.1 hθ'.2))
  have hder_v : ∀ θ ∈ Set.Ioo (min δ θ₀) (max δ θ₀),
      HasDerivAt (fun θ => θ ^ a / a) (θ ^ (a - 1)) θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo δ θ₀ := by
      rwa [min_eq_left hδθ, max_eq_right hδθ] at hθ
    have hθne : θ ≠ 0 := ne_of_gt (lt_trans hδ hθ'.1)
    have h1 : HasDerivAt (fun x : ℝ => x ^ a) (a * θ ^ (a - 1)) θ :=
      Real.hasDerivAt_rpow_const (Or.inl hθne)
    have h2 := h1.div_const a
    have h3 : a * θ ^ (a - 1) / a = θ ^ (a - 1) := mul_div_cancel_left₀ _ ha
    rwa [h3] at h2
  have hint_u : IntervalIntegrable (fun θ => -ψ θ) volume δ θ₀ :=
    (hψc.intervalIntegrable_of_Icc hδθ).neg
  have hint_v : IntervalIntegrable (fun θ => θ ^ (a - 1)) volume δ θ₀ := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hδθ] at hx
    exact Or.inl (ne_of_gt (lt_of_lt_of_le hδ hx.1))
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := δ) (b := θ₀)
    (u := fun θ => ∫ s in θ..θ₀, ψ s) (v := fun θ => θ ^ a / a)
    (u' := fun θ => -ψ θ) (v' := fun θ => θ ^ (a - 1))
    hcont_u hcont_v hder_u hder_v hint_u hint_v
  have hL : (∫ θ in δ..θ₀, θ ^ (a - 1) * (∫ s in θ..θ₀, ψ s))
      = ∫ θ in δ..θ₀, (∫ s in θ..θ₀, ψ s) * θ ^ (a - 1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hmid : (∫ x in δ..θ₀, ψ x * (x ^ a / a)) = (1 / a) * ∫ x in δ..θ₀, x ^ a * ψ x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hR : (∫ x in δ..θ₀, (-ψ x) * (x ^ a / a)) = -(1 / a) * ∫ x in δ..θ₀, x ^ a * ψ x := by
    calc ∫ x in δ..θ₀, (-ψ x) * (x ^ a / a)
        = ∫ x in δ..θ₀, -(ψ x * (x ^ a / a)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          ring
      _ = - ∫ x in δ..θ₀, ψ x * (x ^ a / a) := intervalIntegral.integral_neg
      _ = -(1 / a) * ∫ x in δ..θ₀, x ^ a * ψ x := by rw [hmid]; ring
  rw [hL, hIBP, intervalIntegral.integral_same, hR]
  have hIψ : 0 ≤ ∫ s in δ..θ₀, ψ s := intervalIntegral.integral_nonneg hδθ hψnn
  have hδa : 0 ≤ δ ^ a / a :=
    div_nonneg (le_of_lt (Real.rpow_pos_of_pos hδ a)) (le_of_lt ha0)
  have hkey : 0 ≤ (∫ s in δ..θ₀, ψ s) * (δ ^ a / a) := mul_nonneg hIψ hδa
  simp only [zero_mul, zero_sub]
  linarith

end Work.FTS.EllSol.VthAux.traceAux
