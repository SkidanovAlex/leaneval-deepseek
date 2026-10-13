import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open scoped Real Topology
open MeasureTheory Set intervalIntegral

set_option autoImplicit false

/-- The integral form of Grönwall's inequality, backwards in time.

Let `φ : ℝ → ℝ` be continuous on `[a,b]` with continuous derivative there, nonnegative on
`[a,b]`, and suppose that on the open interval `(a,b)`

  `deriv φ x ≥ -(C * φ x + ψ x)`

with `C ≥ 0` and `ψ ≥ 0` on `(a,b)`.  Then, for every `x ∈ [a,b]`,

  `φ x ≤ exp (C * (b - a)) * (φ b + ∫ s in a..b, ψ s)`.

The proof is the standard one: the function `t ↦ exp (C * (t - b)) * φ t` has derivative
`exp (C * (t - b)) * (C * φ t + deriv φ t) ≥ -exp (C * (t - b)) * ψ t`, so by the fundamental
theorem of calculus its increment `φ b - exp (C * (x - b)) * φ x` is bounded below by
`-∫ s in x..b, exp (C * (s - b)) * ψ s`.  Multiplying by the nonnegative factor
`exp (C * (b - x))`, using `exp (C * (b - x)) ≤ exp (C * (b - a))`, `φ b ≥ 0` and
`0 ≤ ∫ s in x..b, exp (C * (s - b)) * ψ s ≤ ∫ s in a..b, ψ s` (from `ψ ≥ 0`) gives the claim. -/
theorem gronwallIntegralOn {φ ψ : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hφnn : ∀ x ∈ Set.Icc a b, 0 ≤ φ x)
    (hψi : IntervalIntegrable ψ volume a b)
    (hψnn : ∀ x ∈ Set.Ioo a b, 0 ≤ ψ x)
    (hφc : ContinuousOn φ (Set.Icc a b))
    (hφd : ∀ x ∈ Set.Icc a b, HasDerivAt φ (deriv φ x) x)
    (hφdc : ContinuousOn (deriv φ) (Set.Icc a b))
    (hineq : ∀ x ∈ Set.Ioo a b, -(C * φ x + ψ x) ≤ deriv φ x) :
    ∀ x ∈ Set.Icc a b,
      φ x ≤ Real.exp (C * (b - a)) * (φ b + ∫ s in a..b, ψ s) := by
  intro x hx
  obtain ⟨hax, hxb⟩ := hx
  -- the interval `[x,b]` sits inside `[a,b]`
  have hsub : Set.uIcc x b ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hxb]
    exact Set.Icc_subset_Icc hax le_rfl
  have hsub' : Set.uIcc x b ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact hsub
  -- the auxiliary function `t ↦ exp (C * (t - b)) * φ t` and its derivative
  have hderiv : ∀ t ∈ Set.uIcc x b,
      HasDerivAt (fun s : ℝ => Real.exp (C * (s - b)) * φ s)
        (Real.exp (C * (t - b)) * (C * φ t + deriv φ t)) t := by
    intro t ht
    have ht_ab : t ∈ Set.Icc a b := hsub ht
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (C * (s - b)))
        (Real.exp (C * (t - b)) * C) t := by
      have h1 : HasDerivAt (fun s : ℝ => C * (s - b)) C t := by
        simpa using ((hasDerivAt_id t).sub_const b).const_mul C
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (C * (t - b))).comp t h1
    have hmul : HasDerivAt ((fun s : ℝ => Real.exp (C * (s - b))) * φ)
        (Real.exp (C * (t - b)) * C * φ t + Real.exp (C * (t - b)) * deriv φ t) t :=
      hexp.mul (hφd t ht_ab)
    have hv : Real.exp (C * (t - b)) * C * φ t + Real.exp (C * (t - b)) * deriv φ t
        = Real.exp (C * (t - b)) * (C * φ t + deriv φ t) := by ring
    exact hmul.congr_deriv hv
  -- continuity of the derivative, and the fundamental theorem of calculus on `[x,b]`
  have hcont' : ContinuousOn (fun t : ℝ => Real.exp (C * (t - b)) * (C * φ t + deriv φ t))
      (Set.uIcc x b) := by
    have h1 : ContinuousOn (fun t : ℝ => Real.exp (C * (t - b))) (Set.uIcc x b) := by
      simpa [Function.comp_def] using
        ((Real.continuous_exp.comp (continuous_const.mul
          (continuous_id.sub continuous_const))).continuousOn (s := Set.uIcc x b))
    have h2 : ContinuousOn (fun t : ℝ => C * φ t + deriv φ t) (Set.uIcc x b) :=
      ((hφc.mono hsub).const_mul C).add (hφdc.mono hsub)
    exact h1.mul h2
  have hFTC : ∫ t in x..b, Real.exp (C * (t - b)) * (C * φ t + deriv φ t)
      = φ b - Real.exp (C * (x - b)) * φ x := by
    have h0 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont'.intervalIntegrable
    simpa [show C * (b - b) = 0 by ring] using h0
  -- integrability of the source term on `[x,b]`
  have hGint : IntervalIntegrable (fun t : ℝ => Real.exp (C * (t - b)) * ψ t) volume x b :=
    (hψi.mono_set hsub').continuousOn_mul (by
      simpa [Function.comp_def] using
        ((Real.continuous_exp.comp (continuous_const.mul
          (continuous_id.sub continuous_const))).continuousOn (s := Set.uIcc x b)))
  have hsumint : IntervalIntegrable
      (fun t : ℝ => Real.exp (C * (t - b)) * (C * φ t + deriv φ t)
        + Real.exp (C * (t - b)) * ψ t) volume x b :=
    hcont'.intervalIntegrable.add hGint
  -- the integrand is nonnegative on `(x,b)`
  have hpt : ∀ t ∈ Set.Ioo x b,
      (0 : ℝ) ≤ Real.exp (C * (t - b)) * (C * φ t + deriv φ t)
        + Real.exp (C * (t - b)) * ψ t := by
    intro t ht
    have ht_ab : t ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hax ht.1, ht.2⟩
    have h1 : 0 ≤ C * φ t + ψ t + deriv φ t := by
      have := hineq t ht_ab
      linarith
    have h2 : 0 ≤ Real.exp (C * (t - b)) := Real.exp_nonneg _
    have heq : Real.exp (C * (t - b)) * (C * φ t + ψ t + deriv φ t)
        = Real.exp (C * (t - b)) * (C * φ t + deriv φ t)
          + Real.exp (C * (t - b)) * ψ t := by ring
    rw [← heq]
    exact mul_nonneg h2 h1
  have hnonneg : 0 ≤ ∫ t in x..b,
      (Real.exp (C * (t - b)) * (C * φ t + deriv φ t) + Real.exp (C * (t - b)) * ψ t) := by
    have h0 := intervalIntegral.integral_mono_on_of_le_Ioo (f := fun _ : ℝ => (0 : ℝ))
      (g := fun t : ℝ => Real.exp (C * (t - b)) * (C * φ t + deriv φ t)
        + Real.exp (C * (t - b)) * ψ t) hxb intervalIntegrable_const hsumint hpt
    simpa using h0
  -- split the integral and apply the fundamental theorem of calculus
  have hkey : Real.exp (C * (x - b)) * φ x
      ≤ φ b + ∫ t in x..b, Real.exp (C * (t - b)) * ψ t := by
    have hsplit : ∫ t in x..b,
        (Real.exp (C * (t - b)) * (C * φ t + deriv φ t) + Real.exp (C * (t - b)) * ψ t)
        = (φ b - Real.exp (C * (x - b)) * φ x)
          + ∫ t in x..b, Real.exp (C * (t - b)) * ψ t := by
      rw [intervalIntegral.integral_add hcont'.intervalIntegrable hGint, hFTC]
    rw [hsplit] at hnonneg
    linarith
  -- the tail integral is nonnegative
  have htailnn : 0 ≤ ∫ t in x..b, Real.exp (C * (t - b)) * ψ t := by
    have h0 := intervalIntegral.integral_mono_on_of_le_Ioo (f := fun _ : ℝ => (0 : ℝ))
      (g := fun t : ℝ => Real.exp (C * (t - b)) * ψ t) hxb intervalIntegrable_const hGint
      (fun t ht => mul_nonneg (Real.exp_nonneg _)
        (hψnn t ⟨lt_of_le_of_lt hax ht.1, ht.2⟩))
    simpa using h0
  -- and is dominated by `∫ s in a..b, ψ s`
  have hψint_xb : IntervalIntegrable ψ volume x b := hψi.mono_set hsub'
  have htail_le : ∫ t in x..b, Real.exp (C * (t - b)) * ψ t ≤ ∫ t in x..b, ψ t := by
    have h0 := intervalIntegral.integral_mono_on_of_le_Ioo
      (f := fun t : ℝ => Real.exp (C * (t - b)) * ψ t) (g := ψ) hxb hGint hψint_xb
      (fun t ht => by
        have ht_ab : t ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hax ht.1, ht.2⟩
        have hexp : Real.exp (C * (t - b)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonneg_of_nonpos hC (by linarith [ht.2])
        exact mul_le_of_le_one_left (hψnn t ht_ab) hexp)
    simpa using h0
  have hψint_ax : IntervalIntegrable ψ volume a x :=
    hψi.mono_set (by
      rw [Set.uIcc_of_le hax, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc le_rfl hxb)
  have htail_le2 : ∫ t in x..b, ψ t ≤ ∫ t in a..b, ψ t := by
    have hnn : 0 ≤ ∫ t in a..x, ψ t := by
      have h0 := intervalIntegral.integral_mono_on_of_le_Ioo (f := fun _ : ℝ => (0 : ℝ))
        (g := ψ) hax intervalIntegrable_const hψint_ax
        (fun t ht => hψnn t ⟨ht.1, lt_of_lt_of_le ht.2 hxb⟩)
      simpa using h0
    have hadj := intervalIntegral.integral_add_adjacent_intervals hψint_ax hψint_xb
    linarith
  -- multiply by the nonnegative factor `exp (C * (b - x))`
  have hmult : Real.exp (C * (b - x)) * (Real.exp (C * (x - b)) * φ x) = φ x := by
    have h1 : Real.exp (C * (b - x)) * Real.exp (C * (x - b)) = 1 := by
      rw [← Real.exp_add, show C * (b - x) + C * (x - b) = 0 by ring, Real.exp_zero]
    rw [← mul_assoc, h1, one_mul]
  have hexpbx : Real.exp (C * (b - x)) ≤ Real.exp (C * (b - a)) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (by linarith) hC
  have hPhinn : 0 ≤ Real.exp (C * (x - b)) * φ x :=
    mul_nonneg (Real.exp_nonneg _) (hφnn x ⟨hax, hxb⟩)
  calc φ x = Real.exp (C * (b - x)) * (Real.exp (C * (x - b)) * φ x) := hmult.symm
    _ ≤ Real.exp (C * (b - x)) * (φ b + ∫ t in x..b, Real.exp (C * (t - b)) * ψ t) :=
        mul_le_mul_of_nonneg_left hkey (Real.exp_nonneg _)
    _ ≤ Real.exp (C * (b - a)) * (φ b + ∫ t in x..b, Real.exp (C * (t - b)) * ψ t) :=
        mul_le_mul_of_nonneg_right hexpbx
          (by linarith [hφnn b ⟨hab, le_rfl⟩, htailnn])
    _ ≤ Real.exp (C * (b - a)) * (φ b + ∫ s in a..b, ψ s) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)

end Work.FTS.EllipticEst.AngAWeak
