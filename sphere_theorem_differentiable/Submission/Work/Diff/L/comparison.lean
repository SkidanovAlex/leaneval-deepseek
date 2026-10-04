import Mathlib
import Submission.Work.Diff.L.Deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

open Set

/-- Pointwise bound for the ODE comparison constant: for `0 < S₀` and `x ≤ S₀` one has
`√(x³ + S₀²) ≤ S₀√S₀ + S₀`.  (Note `S₀√S₀ + S₀ ≥ √(S₀³+S₀²) = S₀√(S₀+1)`, since
`√(S₀+1) ≤ √S₀ + 1`.) -/
theorem sqrt_cube_le {S₀ x : ℝ} (hS₀ : 0 < S₀) (hx : x ≤ S₀) :
    Real.sqrt (x ^ 3 + S₀ ^ 2) ≤ S₀ * Real.sqrt S₀ + S₀ := by
  have hcube : x ^ 3 ≤ S₀ ^ 3 := (show Odd 3 by norm_num).pow_le_pow.mpr hx
  have h1 : Real.sqrt (x ^ 3 + S₀ ^ 2) ≤ Real.sqrt (S₀ ^ 3 + S₀ ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (S₀ ^ 3 + S₀ ^ 2) ≤ S₀ * Real.sqrt S₀ + S₀ := by
    have hsq : S₀ ^ 3 + S₀ ^ 2 ≤ (S₀ * Real.sqrt S₀ + S₀) ^ 2 := by
      nlinarith [Real.sq_sqrt hS₀.le, Real.sqrt_nonneg S₀]
    have hnn : 0 ≤ S₀ * Real.sqrt S₀ + S₀ := by nlinarith [Real.sqrt_nonneg S₀, hS₀]
    calc Real.sqrt (S₀ ^ 3 + S₀ ^ 2)
        ≤ Real.sqrt ((S₀ * Real.sqrt S₀ + S₀) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = S₀ * Real.sqrt S₀ + S₀ := Real.sqrt_sq hnn
  linarith

/-- ODE comparison ("supersolution drop bound"): if `v` is differentiable on `[0,T]` with
`v' ≥ -β √(v³ + S₀²)` and `S₀ ≤ v 0`, then `v t ≥ S₀ - β (S₀ √S₀ + S₀) t` on `[0,T]`.
No positivity of `v` is assumed; the pointwise bound `√(x³+S₀²) ≤ √(S₀³+S₀²)` for `x ≤ S₀` supplies
the constant. -/
theorem comparison {S₀ β T : ℝ} (hβ : 0 < β) (hS₀ : 0 < S₀) {v : ℝ → ℝ}
    (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (deriv v t) t)
    (hineq : ∀ t ∈ Icc 0 T,
      -(β * Real.sqrt ((v t) ^ 3 + S₀ ^ 2)) ≤ deriv v t)
    (h0 : S₀ ≤ v 0) :
    ∀ t ∈ Icc 0 T, S₀ - β * (S₀ * Real.sqrt S₀ + S₀) * t ≤ v t := by
  intro t₁ ht₁
  by_contra hcon
  simp only [not_le] at hcon
  -- Compare `v` with the affine supersolution `u t = S₀ - c t`, `c = β (S₀√S₀ + S₀)`.
  set c : ℝ := β * (S₀ * Real.sqrt S₀ + S₀) with hc_def
  set w : ℝ → ℝ := fun t => v t - (S₀ - c * t) with hw_def
  have hc_pos : 0 < c := by
    rw [hc_def]
    exact mul_pos hβ (by nlinarith [Real.sqrt_nonneg S₀, hS₀])
  have hwt₁ : w t₁ < 0 := by
    simp only [hw_def, hc_def] at hcon ⊢
    linarith
  have hw0 : 0 ≤ w 0 := by
    simp only [hw_def, hc_def]
    linarith [h0]
  -- `w` has derivative `v' + c` on `[0,T]`.
  have hw_deriv : ∀ t ∈ Icc 0 T, HasDerivAt w (deriv v t + c) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => S₀ - c * s) (-c) t := by
      have h2 := ((hasDerivAt_id t).const_mul c).const_sub S₀
      convert h2 using 1
      · funext s; rfl
      · ring
    have h3 := (hv t ht).sub h1
    have h4 : HasDerivAt (fun s : ℝ => v s - (S₀ - c * s)) (deriv v t + c) t := by
      convert h3 using 1
      ring
    rw [hw_def]
    exact h4
  -- `K` is the (closed) set of times up to `t₁` where `v` is still above the barrier.
  set K : Set ℝ := {t | t ∈ Icc 0 t₁ ∧ 0 ≤ w t} with hK_def
  have hKne : K.Nonempty := ⟨0, ⟨⟨le_rfl, ht₁.1⟩, hw0⟩⟩
  have hKbdd : BddAbove K := ⟨t₁, fun x hx => hx.1.2⟩
  -- `t₀` is the last time at which `v` meets the barrier.
  set t₀ : ℝ := sSup K with ht₀_def
  have ht₀_cl : t₀ ∈ closure K := by
    rw [ht₀_def]; exact csSup_mem_closure hKne hKbdd
  have hKsub : K ⊆ Icc 0 t₁ := fun x hx => hx.1
  have ht₀_Icc : t₀ ∈ Icc 0 t₁ := by
    have hcl : closure K ⊆ Icc 0 t₁ := by
      rw [← isClosed_Icc.closure_eq]
      exact closure_mono hKsub
    exact hcl ht₀_cl
  have ht₀_memT : t₀ ∈ Icc 0 T := ⟨ht₀_Icc.1, ht₀_Icc.2.trans ht₁.2⟩
  -- at `t₀` we are still above the barrier (by continuity).
  have hw_t₀ : 0 ≤ w t₀ := by
    by_contra h
    simp only [not_le] at h
    have hcont : ContinuousAt w t₀ := (hw_deriv t₀ ht₀_memT).continuousAt
    have hmem : {y | w y < 0} ∈ nhds t₀ := hcont.preimage_mem_nhds (Iio_mem_nhds h)
    obtain ⟨y, hy, hyK⟩ := (mem_closure_iff_nhds.mp ht₀_cl) _ hmem
    exact absurd hyK.2 (not_le.mpr hy)
  have ht₀_lt : t₀ < t₁ := by
    rcases lt_or_eq_of_le ht₀_Icc.2 with h | h
    · exact h
    · exfalso
      rw [h] at hw_t₀
      linarith
  -- just after `t₀` the barrier is crossed: `w < 0` on `(t₀, t₁)`.
  have hout : ∀ t ∈ Ioo t₀ t₁, w t < 0 := by
    intro t ht
    by_contra h
    simp only [not_lt] at h
    have htK : t ∈ K := ⟨⟨ht₀_Icc.1.trans ht.1.le, ht.2.le⟩, h⟩
    have hle : t ≤ sSup K := le_csSup hKbdd htK
    linarith [hle, ht₀_def, ht.1]
  -- mean value theorem on `[t₀, t₁]`.
  have hcont_w : ContinuousOn w (Icc t₀ t₁) := by
    intro t ht
    exact ((hw_deriv t ⟨ht₀_Icc.1.trans ht.1, ht.2.trans ht₁.2⟩).continuousAt).continuousWithinAt
  have hdiff_w : DifferentiableOn ℝ w (Ioo t₀ t₁) := by
    intro t ht
    exact ((hw_deriv t ⟨ht₀_Icc.1.trans ht.1.le, ht.2.le.trans ht₁.2⟩).differentiableAt).differentiableWithinAt
  obtain ⟨ξ, hξ, hξderiv⟩ := exists_deriv_eq_slope w ht₀_lt hcont_w hdiff_w
  have hξ_in : ξ ∈ Icc 0 T := ⟨ht₀_Icc.1.trans hξ.1.le, hξ.2.le.trans ht₁.2⟩
  -- the slope is negative because `w t₁ < 0 ≤ w t₀`.
  have hderiv_neg : deriv w ξ < 0 := by
    rw [hξderiv]
    exact div_neg_of_neg_of_pos (by linarith [hwt₁, hw_t₀]) (by linarith [ht₀_lt])
  -- but `v ξ < S₀`, so the differential inequality forces `deriv w ξ ≥ 0`.
  have hξlow : w ξ < 0 := hout ξ hξ
  have hvξ : v ξ < S₀ := by
    have h1 : w ξ < 0 := hξlow
    simp only [hw_def] at h1
    have h2 : 0 ≤ c * ξ := mul_nonneg hc_pos.le (ht₀_Icc.1.trans hξ.1.le)
    linarith
  have hderiv_ge : 0 ≤ deriv w ξ := by
    have hb := hineq ξ hξ_in
    have hs := sqrt_cube_le hS₀ hvξ.le
    have hcβ : β * Real.sqrt ((v ξ) ^ 3 + S₀ ^ 2) ≤ c := by
      rw [hc_def]
      exact mul_le_mul_of_nonneg_left hs hβ.le
    have hdw : deriv w ξ = deriv v ξ + c := (hw_deriv ξ hξ_in).deriv
    linarith
  linarith [hderiv_neg, hderiv_ge]

end Work.Diff.L
