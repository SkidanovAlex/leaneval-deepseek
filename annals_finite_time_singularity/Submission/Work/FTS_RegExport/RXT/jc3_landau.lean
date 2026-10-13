/-
# `Work.FTS_RegExport.RXT.jc3_landau` — the abstract Landau step

If `V` is Lipschitz in the time variable `τ` and `∂_x V = W` with `W` controlled by a
Lipschitz bound in `x` at the base point `x₀`, then `W x₀ ·` is `1/2`-Hölder in `τ`.  This is
the tool that upgrades the time-Lipschitz bound for the order-≤2 slots of the strong solution
to the time-continuity of the order-3 slots (see `RXT.jc3_tau`).

The proof: for `h = √|τ-τ'|` the fundamental theorem of calculus gives
`V(x₀+h,τ) - V(x₀,τ) = ∫_{x₀}^{x₀+h} W(x,τ) dx` and the same for `τ'`, so

  `h·(W x₀ τ - W x₀ τ') = ∫_{x₀}^{x₀+h} (W x τ - W x τ') dx
      - ∫_{x₀}^{x₀+h} ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ')) dx`,

where the first integral is bounded by `2L|τ-τ'|` (the τ-Lipschitz bound on `V` at the two
endpoints) and the second by `∫_{x₀}^{x₀+h} 2K(x-x₀) dx = K h²` (the `x`-Lipschitz bound).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-- `|a - b| ≤ |a| + |b|`. -/
lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_sub_le a 0 b
  rwa [sub_zero, zero_sub, abs_neg] at h

/-- **The abstract Landau step.**  If `V` is Lipschitz in `τ` and has `x`-derivative `W`, and
`W` is Lipschitz in `x` at the base point `x₀`, then `W x₀ ·` is `1/2`-Hölder in `τ` on the
side `τ ≥ 0`, up to the size `δ²` of the space interval used in the argument. -/
theorem tau_lip_sqrt_of_primitive_self {V W : ℝ → ℝ → ℝ} {x₀ δ L K : ℝ}
    (hδ : 0 < δ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hV : ∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → ∀ x ∈ Set.Icc x₀ (x₀ + δ),
      |V x τ - V x τ'| ≤ L * |τ - τ'|)
    (hcont : ∀ τ : ℝ, 0 ≤ τ → ContinuousOn (fun x => W x τ) (Set.Icc x₀ (x₀ + δ)))
    (hW : ∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δ),
      |W x τ - W x₀ τ| ≤ K * |x - x₀|)
    (hderiv : ∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δ),
      HasDerivAt (fun x' => V x' τ) (W x τ) x) :
    ∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → |τ - τ'| ≤ δ ^ 2 →
      |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * Real.sqrt |τ - τ'| := by
  intro τ τ' hτ hτ' hdiff
  rcases eq_or_lt_of_le (abs_nonneg (τ - τ')) with hz | hpos
  · have hττ : τ = τ' := by
      have h1 : τ - τ' = 0 := abs_eq_zero.mp hz.symm
      exact sub_eq_zero.mp h1
    subst hττ
    simp [Real.sqrt_zero]
  · set h : ℝ := Real.sqrt |τ - τ'| with hh
    have hhpos : 0 < h := Real.sqrt_pos.mpr hpos
    have hh2 : h ^ 2 = |τ - τ'| := Real.sq_sqrt (abs_nonneg _)
    have hhle : h ≤ δ := by
      rw [hh, ← Real.sqrt_sq hδ.le]
      exact Real.sqrt_le_sqrt hdiff
    have hab : x₀ ≤ x₀ + h := by linarith
    have hx0 : x₀ ∈ Set.Icc x₀ (x₀ + δ) := ⟨le_rfl, by linarith⟩
    have hxh : x₀ + h ∈ Set.Icc x₀ (x₀ + δ) := ⟨by linarith, by linarith⟩
    have hderiv' : ∀ σ : ℝ, 0 ≤ σ → ∀ x ∈ Set.uIcc x₀ (x₀ + h),
        HasDerivAt (fun x' => V x' σ) (W x σ) x := by
      intro σ hσ x hx
      rw [Set.uIcc_of_le hab] at hx
      exact hderiv σ hσ x ⟨hx.1, by linarith [hx.2]⟩
    have hint : ∀ σ : ℝ, 0 ≤ σ → IntervalIntegrable (fun x => W x σ) volume x₀ (x₀ + h) := by
      intro σ hσ
      refine (ContinuousOn.intervalIntegrable ?_)
      rw [Set.uIcc_of_le hab]
      exact (hcont σ hσ).mono (Set.Icc_subset_Icc le_rfl (by linarith))
    have hFTC : ∀ σ : ℝ, 0 ≤ σ →
        ∫ x in x₀..(x₀ + h), W x σ = V (x₀ + h) σ - V x₀ σ := fun σ hσ =>
      intervalIntegral.integral_eq_sub_of_hasDerivAt (hderiv' σ hσ) (hint σ hσ)
    -- the first integral
    have hA : ∫ x in x₀..(x₀ + h), (W x τ - W x τ')
        = (V (x₀ + h) τ - V x₀ τ) - (V (x₀ + h) τ' - V x₀ τ') := by
      rw [intervalIntegral.integral_sub (hint τ hτ) (hint τ' hτ'), hFTC τ hτ, hFTC τ' hτ']
    have hb1 : |∫ x in x₀..(x₀ + h), (W x τ - W x τ')| ≤ 2 * L * |τ - τ'| := by
      rw [hA]
      have h1 := hV τ τ' hτ hτ' (x₀ + h) hxh
      have h2 := hV τ τ' hτ hτ' x₀ hx0
      have h3 : (V (x₀ + h) τ - V x₀ τ) - (V (x₀ + h) τ' - V x₀ τ')
          = (V (x₀ + h) τ - V (x₀ + h) τ') - (V x₀ τ - V x₀ τ') := by ring
      rw [h3]
      have h4 : |(V (x₀ + h) τ - V (x₀ + h) τ') - (V x₀ τ - V x₀ τ')|
          ≤ |V (x₀ + h) τ - V (x₀ + h) τ'| + |V x₀ τ - V x₀ τ'| := by
        exact abs_sub_le_abs_add _ _
      calc |(V (x₀ + h) τ - V (x₀ + h) τ') - (V x₀ τ - V x₀ τ')|
          ≤ |V (x₀ + h) τ - V (x₀ + h) τ'| + |V x₀ τ - V x₀ τ'| := h4
        _ ≤ L * |τ - τ'| + L * |τ - τ'| := add_le_add h1 h2
        _ = 2 * L * |τ - τ'| := by ring
    -- the second integral
    have hsub1 : IntervalIntegrable (fun x => W x τ - W x₀ τ) volume x₀ (x₀ + h) :=
      (hint τ hτ).sub intervalIntegrable_const
    have hsub2 : IntervalIntegrable (fun x => W x τ' - W x₀ τ') volume x₀ (x₀ + h) :=
      (hint τ' hτ').sub intervalIntegrable_const
    have hint2 : IntervalIntegrable
        (fun x => (W x τ - W x₀ τ) - (W x τ' - W x₀ τ')) volume x₀ (x₀ + h) :=
      hsub1.sub hsub2
    have hInt : ∫ x in x₀..(x₀ + h), (2 * K * (x - x₀)) = K * h ^ 2 := by
      have hsub : ∫ x in x₀..(x₀ + h), (x - x₀) = h ^ 2 / 2 := by
        have h1 : (fun x : ℝ => x - x₀) = fun x => (fun y : ℝ => y) (x - x₀) := by
          funext x; rfl
        rw [h1, intervalIntegral.integral_comp_sub_right (f := fun y : ℝ => y) x₀]
        simp only [sub_self, add_sub_cancel_left]
        simp
      rw [intervalIntegral.integral_const_mul, hsub]
      ring
    have hb2 : |∫ x in x₀..(x₀ + h), ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ'))| ≤ K * h ^ 2 := by
      rw [← hInt, ← Real.norm_eq_abs]
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
      refine intervalIntegral.integral_mono_on hab hint2.norm
        ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _) ?_
      intro x hx
      rw [Real.norm_eq_abs]
      have hxIcc : x ∈ Set.Icc x₀ (x₀ + δ) := ⟨hx.1, by linarith [hx.2]⟩
      have h1 := hW τ hτ x hxIcc
      have h2 := hW τ' hτ' x hxIcc
      have hxnn : 0 ≤ x - x₀ := by linarith [hx.1]
      calc |(W x τ - W x₀ τ) - (W x τ' - W x₀ τ')|
          ≤ |W x τ - W x₀ τ| + |W x τ' - W x₀ τ'| := abs_sub_le_abs_add _ _
        _ ≤ K * |x - x₀| + K * |x - x₀| := add_le_add h1 h2
        _ = 2 * K * (x - x₀) := by rw [abs_of_nonneg hxnn]; ring
    -- combine
    have hsplit : ∫ x in x₀..(x₀ + h), (W x τ - W x τ')
        = h * (W x₀ τ - W x₀ τ')
          + ∫ x in x₀..(x₀ + h), ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ')) := by
      have hfun : (fun x => W x τ - W x τ')
          = fun x => (W x₀ τ - W x₀ τ') + ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ')) := by
        funext x; ring
      rw [hfun, intervalIntegral.integral_add intervalIntegrable_const hint2,
        intervalIntegral.integral_const]
      ring
    have hkey : h * |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * h ^ 2 := by
      have h1 : h * (W x₀ τ - W x₀ τ')
          = (∫ x in x₀..(x₀ + h), (W x τ - W x τ'))
            - ∫ x in x₀..(x₀ + h), ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ')) := by
        rw [hsplit]; ring
      calc h * |W x₀ τ - W x₀ τ'| = |h * (W x₀ τ - W x₀ τ')| := by
            rw [abs_mul, abs_of_pos hhpos]
        _ = |(∫ x in x₀..(x₀ + h), (W x τ - W x τ'))
                - (∫ x in x₀..(x₀ + h), ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ')))| := by
            rw [h1]
        _ ≤ |∫ x in x₀..(x₀ + h), (W x τ - W x τ')|
              + |∫ x in x₀..(x₀ + h), ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ'))| := by
            exact abs_sub_le_abs_add _ _
        _ ≤ 2 * L * |τ - τ'| + K * h ^ 2 := add_le_add hb1 hb2
        _ = (2 * L + K) * h ^ 2 := by rw [← hh2]; ring
    have hfin : |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * h := by
      have h2 : h * |W x₀ τ - W x₀ τ'| ≤ h * ((2 * L + K) * h) := by
        rw [show h * ((2 * L + K) * h) = (2 * L + K) * h ^ 2 by ring]
        exact hkey
      exact le_of_mul_le_mul_left h2 hhpos
    exact hfin

end Work.FTS_RegExport.RXT
