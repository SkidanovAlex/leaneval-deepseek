import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise bound in the "middle" angular window `[π/8, 3π/8]`

This file proves `Work.FTS.EllipticEst.remov.mid_pointwise_bound`: for `u` of class `C^{k+2}`
on `(0, π/2)` and `g = Lzero1 u`, the top derivative `u^{(k+2)}` at a point `θ` of the closed
window `[π/8, 3π/8]` is controlled by the lower derivatives of `u` at `θ` together with
`g^{(k)}(θ)`.

The mechanism is the exact expansion of `Lzero1 u = g` after differentiating `k` times
(`Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq`),

`u^{(k+2)} = ∑_{i ≤ k+1} C(k+1,i) (tan)^{(i)} u^{(k+1-i)} - 6 u^{(k)} - g^{(k)}`,

read as a pointwise relation on `Ioo 0 (π/2)`.  Since `tan` is smooth on a neighbourhood of the
window, all its derivatives up to `k+1` are bounded there, so the right hand side is a fixed
(finite) real linear combination of `u^{(0)}, …, u^{(k+1)}` and `g^{(k)}`.  Squaring and using
`(∑ a_j)^2 ≤ (card)·∑ a_j^2`-free reasoning — here simply `|x| ≤ √S` for every summand and
`√S · √S = S` — yields the stated quadratic bound.
-/

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

/-- Continuity of the `i`-th derivative of `tan` on the closed angular window
`[π/8, 3π/8]`, which lies strictly inside `(-π/2, π/2)`. -/
private theorem continuousOn_iteratedDeriv_tan (i : ℕ) :
    ContinuousOn (iteratedDeriv i Real.tan) (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := by
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  -- `tan = sin / cos` is smooth on the open interval
  have htanU : ContDiffOn ℝ (⊤ : WithTop ℕ∞) Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun x : ℝ => Real.sin x / Real.cos x)
        (Set.Ioo 0 (Real.pi / 2)) := by
      refine ContDiffOn.div Real.contDiff_sin.contDiffOn Real.contDiff_cos.contDiffOn ?_
      intro x hx
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    exact h.congr (fun x _ => Real.tan_eq_sin_div_cos x)
  have hcontW : ContinuousOn (iteratedDerivWithin i Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    htanU.continuousOn_iteratedDerivWithin le_top hU.uniqueDiffOn
  -- on an open set the derivative within the set is the ordinary derivative
  have hcont' : ContinuousOn (iteratedDeriv i Real.tan) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcontW.congr
      (fun x hx => (iteratedDerivWithin_of_isOpen (n := i) (f := Real.tan) hU hx).symm)
  refine hcont'.mono ?_
  intro x hx
  exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩

/-- Every derivative of `tan` of a fixed order is bounded on the closed window. -/
private theorem tan_deriv_le (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8), |iteratedDeriv i Real.tan θ| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_iteratedDeriv_tan i)
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have := hC θ hθ
  rw [Real.norm_eq_abs] at this
  exact le_trans this (le_max_left C 0)

/-- A single constant bounds all derivatives of `tan` up to order `k` on the closed window. -/
private theorem tan_deriv_bound (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ i ≤ k, ∀ θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
      |iteratedDeriv i Real.tan θ| ≤ C := by
  choose c hc0 hc using tan_deriv_le
  refine ⟨∑ j ∈ Finset.range (k + 1), c j, Finset.sum_nonneg (fun j _ => hc0 j), ?_⟩
  intro i hi θ hθ
  refine le_trans (hc i θ hθ) (Finset.single_le_sum (fun j _ => hc0 j) ?_)
  exact Finset.mem_range.mpr (by omega)

theorem mid_pointwise_bound (k : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (u g : ℝ → ℝ),
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      ∀ θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
        (iteratedDeriv (k + 2) u θ) ^ 2
          ≤ K * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
              + (iteratedDeriv k g θ) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := tan_deriv_bound (k + 1)
  let D : ℝ := (∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * C) + 6 + 1
  refine ⟨D ^ 2 + 1, by linarith [sq_nonneg D], ?_⟩
  intro u g hu hg θ hθ
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hid := Lzero1_iteratedDeriv_eq k hu hg θ hθ'
  set S : ℝ := (∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
      + (iteratedDeriv k g θ) ^ 2 with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact add_nonneg (Finset.sum_nonneg (fun m _ => sq_nonneg _)) (sq_nonneg _)
  -- every summand is bounded by `√S`
  have hX : ∀ m ∈ Finset.range (k + 2), |iteratedDeriv m u θ| ≤ Real.sqrt S := by
    intro m hm
    refine (Real.le_sqrt (abs_nonneg _) hSnn).mpr ?_
    rw [sq_abs]
    rw [hSdef]
    refine le_trans (Finset.single_le_sum (s := Finset.range (k + 2))
      (f := fun j => (iteratedDeriv j u θ) ^ 2) (fun j _ => sq_nonneg _) hm) ?_
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hY : |iteratedDeriv k g θ| ≤ Real.sqrt S := by
    refine (Real.le_sqrt (abs_nonneg _) hSnn).mpr ?_
    rw [sq_abs]
    rw [hSdef]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun m _ => sq_nonneg _))
  -- the coefficient terms
  have hterm : ∀ i ∈ Finset.range (k + 2),
      |((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ|
        ≤ ((k + 1).choose i : ℝ) * C * Real.sqrt S := by
    intro i hi
    have hi1 : i ≤ k + 1 := by
      have := Finset.mem_range.mp hi; omega
    have hi2 : k + 1 - i ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
    have htan := hC i hi1 θ hθ
    have hXu := hX (k + 1 - i) hi2
    have hch : (0 : ℝ) ≤ ((k + 1).choose i : ℝ) := Nat.cast_nonneg _
    rw [abs_mul, abs_mul, abs_of_nonneg hch]
    exact mul_le_mul (mul_le_mul_of_nonneg_left htan hch) hXu (abs_nonneg _) (mul_nonneg hch hC0)
  have hT1 : |∑ i ∈ Finset.range (k + 2),
        ((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ|
      ≤ (∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * C) * Real.sqrt S := by
    rw [Finset.sum_mul]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hXk : |iteratedDeriv k u θ| ≤ Real.sqrt S :=
    hX k (Finset.mem_range.mpr (by omega))
  have h6 : |6 * iteratedDeriv k u θ| ≤ 6 * Real.sqrt S := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    exact mul_le_mul_of_nonneg_left hXk (by norm_num)
  -- assemble
  have hmain : |iteratedDeriv (k + 2) u θ| ≤ D * Real.sqrt S := by
    rw [hid]
    have h1 : |(∑ i ∈ Finset.range (k + 2),
          ((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ)
          - 6 * iteratedDeriv k u θ - iteratedDeriv k g θ|
        ≤ |∑ i ∈ Finset.range (k + 2),
            ((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ|
          + |6 * iteratedDeriv k u θ| + |iteratedDeriv k g θ| := by
      have a := abs_sub ((∑ i ∈ Finset.range (k + 2),
          ((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ)
          - 6 * iteratedDeriv k u θ) (iteratedDeriv k g θ)
      have b := abs_sub (∑ i ∈ Finset.range (k + 2),
          ((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ)
        (6 * iteratedDeriv k u θ)
      linarith
    calc |(∑ i ∈ Finset.range (k + 2),
          ((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ)
          - 6 * iteratedDeriv k u θ - iteratedDeriv k g θ|
        ≤ |∑ i ∈ Finset.range (k + 2),
            ((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ|
          + |6 * iteratedDeriv k u θ| + |iteratedDeriv k g θ| := h1
      _ ≤ (∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * C) * Real.sqrt S
          + 6 * Real.sqrt S + Real.sqrt S := by linarith [hT1, h6, hY]
      _ = D * Real.sqrt S := by rw [show D = (∑ i ∈ Finset.range (k + 2),
            ((k + 1).choose i : ℝ) * C) + 6 + 1 from rfl]; ring
  calc (iteratedDeriv (k + 2) u θ) ^ 2
      = |iteratedDeriv (k + 2) u θ| ^ 2 := (sq_abs _).symm
    _ ≤ (D * Real.sqrt S) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmain 2
    _ = D ^ 2 * S := by rw [mul_pow, Real.sq_sqrt hSnn]
    _ ≤ (D ^ 2 + 1) * S := mul_le_mul_of_nonneg_right (by linarith [sq_nonneg D]) hSnn

end Work.FTS.EllipticEst.remov
