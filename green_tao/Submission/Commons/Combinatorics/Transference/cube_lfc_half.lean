import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.BooleanRing

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Green–Tao Lemma 3.1, linear forms part (cube form).**  The `(d, d·2^d)`-cube linear forms
condition passes from `ν` to `ν' = (ν+1)/2` with the same error `ε`.  This is the device which
allows one to replace the hypothesis `|F| ≤ ν + 1` by `|F| ≤ ν` in the polynomial lemma
(Green–Tao Lemma 6.6). -/
theorem cube_lfc_half {p : ℕ} [Fact p.Prime] {d : ℕ} (ν : ZMod p → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hLFC : ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ ε) :
    ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A,
            ((ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) + 1) / 2) - 1|
        ≤ ε := by
  classical
  intro A hA _hAne b
  set N : ℝ := (Fintype.card (Fin d → ZMod p) : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩)
  have hNne : N ≠ 0 := ne_of_gt hNpos
  set u : (Fin d → Bool) → (Fin d → ZMod p) → ZMod p :=
    fun ω h => b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j with hu
  -- Step 1: pull the factor `(1/2)^{|A|}` out of the product and expand `∏ (x+1)`.
  have hfac : ∀ h : Fin d → ZMod p,
      (∏ ω ∈ A, ((ν (u ω h)) + 1) / 2)
        = ((2 : ℝ) ^ A.card)⁻¹ * ∏ ω ∈ A, (ν (u ω h) + 1) := by
    intro h
    rw [Finset.prod_div_distrib, Finset.prod_const]
    rw [div_eq_inv_mul]
  have hexp : ∀ h : Fin d → ZMod p,
      (∏ ω ∈ A, (ν (u ω h) + 1)) = ∑ A' ∈ A.powerset, ∏ ω ∈ A', ν (u ω h) := by
    intro h
    have hswap : (∏ ω ∈ A, (ν (u ω h) + 1)) = ∏ ω ∈ A, (1 + ν (u ω h)) := by
      apply Finset.prod_congr rfl
      intro ω _
      ring
    rw [hswap, Finset.prod_one_add]
  -- The averaged `ν`-products attached to each sub-cube.
  set g : Finset (Fin d → Bool) → ℝ :=
    fun A' => N⁻¹ * ∑ h : Fin d → ZMod p, ∏ ω ∈ A', ν (u ω h) with hg
  have hg_empty : g ∅ = 1 := by
    show N⁻¹ * (∑ h : Fin d → ZMod p, ∏ ω ∈ (∅ : Finset (Fin d → Bool)), ν (u ω h)) = 1
    simp only [Finset.prod_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hN]
    rw [inv_mul_cancel₀ hNne]
  have hg_bound : ∀ A' ∈ A.powerset, |g A' - 1| ≤ ε := by
    intro A' hA'
    rw [Finset.mem_powerset] at hA'
    by_cases hAne' : A'.Nonempty
    · exact hLFC A' (hA'.trans hA) hAne' b
    · rw [Finset.not_nonempty_iff_eq_empty] at hAne'
      rw [hAne', hg_empty]
      simpa using hε
  -- Step 2: express the average over `ν' = (ν+1)/2` as a `powerset` average of the `g A'`.
  have hmain : N⁻¹ * (∑ h : Fin d → ZMod p, ∏ ω ∈ A, ((ν (u ω h)) + 1) / 2)
      = ((2 : ℝ) ^ A.card)⁻¹ * ∑ A' ∈ A.powerset, g A' := by
    have e1 : ∀ h : Fin d → ZMod p,
        (∏ ω ∈ A, ((ν (u ω h)) + 1) / 2)
          = ((2 : ℝ) ^ A.card)⁻¹ * (∑ A' ∈ A.powerset, ∏ ω ∈ A', ν (u ω h)) := by
      intro h; rw [hfac h, hexp h]
    have e2 : ∑ A' ∈ A.powerset, g A'
        = N⁻¹ * ∑ A' ∈ A.powerset, ∑ h : Fin d → ZMod p, ∏ ω ∈ A', ν (u ω h) := by
      simp only [hg, Finset.mul_sum]
    rw [e2]
    simp only [e1]
    rw [← Finset.mul_sum, Finset.sum_comm]
    ring
  -- Step 3: the numerical bound.
  have hcard2 : (0 : ℝ) < (2 : ℝ) ^ A.card := by positivity
  have hsum1 : ∑ A' ∈ A.powerset, (1 : ℝ) = (2 : ℝ) ^ A.card := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
    push_cast
    ring
  have hstep : N⁻¹ * (∑ h : Fin d → ZMod p, ∏ ω ∈ A, ((ν (u ω h)) + 1) / 2) - 1
      = ((2 : ℝ) ^ A.card)⁻¹ * ∑ A' ∈ A.powerset, (g A' - 1) := by
    have hc : ((2 : ℝ) ^ A.card) ≠ 0 := ne_of_gt hcard2
    rw [hmain, Finset.sum_sub_distrib, hsum1, mul_sub, inv_mul_cancel₀ hc]
  rw [hstep, abs_mul, abs_of_pos (inv_pos.mpr hcard2)]
  calc ((2 : ℝ) ^ A.card)⁻¹ * |∑ A' ∈ A.powerset, (g A' - 1)|
      ≤ ((2 : ℝ) ^ A.card)⁻¹ * ∑ A' ∈ A.powerset, |g A' - 1| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ ((2 : ℝ) ^ A.card)⁻¹ * ∑ A' ∈ A.powerset, ε :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hg_bound) (by positivity)
    _ = ((2 : ℝ) ^ A.card)⁻¹ * ((2 : ℝ) ^ A.card * ε) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
        push_cast
        ring
    _ = ε := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard2), one_mul]

end Commons.Combinatorics.Transference