import Mathlib
import Submission.Work.A7.ModelApproxCore_aux.kernComp_eq_tsum

namespace Work.KMTPlan.A6

open scoped BigOperators

/-- The indicator-weighted `ℤ⁴`-sum of the fourfold kernel equals the iterated composition kernel
`kernComp K κ κ' p₁ p₂`: the two indicator factors force `w.1 = (p₁ - w.2.1, p₂ - w.2.2)`, so the
`w.1`-sum collapses by `tsum_eq_single` onto the single surviving term, and the remaining `w.2`-sum
is exactly the sum of `kernComp_eq_tsum`. -/
theorem tsum_kernelTerm_eq_kernComp (K : ℤ → ℤ → ℂ) (κ κ' : ℤ → ℂ)
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hκ : Summable κ) (hκ' : Summable κ')
    (p₁ p₂ : ℤ) :
    (∑' w : (ℤ × ℤ) × (ℤ × ℤ), K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2
        * (if w.1.1 + w.2.1 = p₁ then 1 else 0) * (if w.1.2 + w.2.2 = p₂ then 1 else 0))
      = Work.KMTAreas.A7.kernComp K κ κ' p₁ p₂ := by
  classical
  have hκn : Summable fun j : ℤ => ‖κ j‖ := hκ.norm
  have hκ'n : Summable fun j : ℤ => ‖κ' j‖ := hκ'.norm
  -- The `ℓ¹`-mass of the product family `(a, b) ↦ κ a · κ' b`.
  have hκκ' : Summable fun q : ℤ × ℤ => ‖κ q.1‖ * ‖κ' q.2‖ :=
    Summable.mul_of_nonneg hκn hκ'n (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  -- The joint nonnegative majorant `‖K‖ ⊗ (‖κ‖ ⊗ ‖κ'‖)`.
  have hM : Summable fun w : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K w.1.1 w.1.2‖ * (‖κ w.2.1‖ * ‖κ' w.2.2‖) :=
    Summable.mul_of_nonneg (f := fun p : ℤ × ℤ => ‖K p.1 p.2‖)
      (g := fun q : ℤ × ℤ => ‖κ q.1‖ * ‖κ' q.2‖) hK hκκ'
      (fun _ => norm_nonneg _) (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  let F : (ℤ × ℤ) × (ℤ × ℤ) → ℂ := fun w =>
      K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2
        * (if w.1.1 + w.2.1 = p₁ then 1 else 0) * (if w.1.2 + w.2.2 = p₂ then 1 else 0)
  have hF : ∀ w, F w = K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2
        * (if w.1.1 + w.2.1 = p₁ then 1 else 0) * (if w.1.2 + w.2.2 = p₂ then 1 else 0) :=
    fun w => rfl
  -- The summand is absolutely summable: the indicator factors have norm `≤ 1`.
  have hFsum : Summable F := by
    change Summable fun w : (ℤ × ℤ) × (ℤ × ℤ) =>
      K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2
        * (if w.1.1 + w.2.1 = p₁ then 1 else 0) * (if w.1.2 + w.2.2 = p₂ then 1 else 0)
    refine Summable.of_norm_bounded hM (fun w => ?_)
    have h1 : ‖(if w.1.1 + w.2.1 = p₁ then (1:ℂ) else 0)‖ ≤ 1 := by split <;> simp
    have h2 : ‖(if w.1.2 + w.2.2 = p₂ then (1:ℂ) else 0)‖ ≤ 1 := by split <;> simp
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have hde : ‖(if w.1.1 + w.2.1 = p₁ then (1:ℂ) else 0)‖ *
        ‖(if w.1.2 + w.2.2 = p₂ then (1:ℂ) else 0)‖ ≤ 1 := by
      nlinarith [h1, h2, norm_nonneg (if w.1.1 + w.2.1 = p₁ then (1:ℂ) else 0),
        norm_nonneg (if w.1.2 + w.2.2 = p₂ then (1:ℂ) else 0)]
    calc ‖K w.1.1 w.1.2‖ * ‖κ w.2.1‖ * ‖κ' w.2.2‖
            * ‖(if w.1.1 + w.2.1 = p₁ then (1:ℂ) else 0)‖
            * ‖(if w.1.2 + w.2.2 = p₂ then (1:ℂ) else 0)‖
        = (‖K w.1.1 w.1.2‖ * ‖κ w.2.1‖ * ‖κ' w.2.2‖)
          * (‖(if w.1.1 + w.2.1 = p₁ then (1:ℂ) else 0)‖
            * ‖(if w.1.2 + w.2.2 = p₂ then (1:ℂ) else 0)‖) := by ring
      _ ≤ (‖K w.1.1 w.1.2‖ * ‖κ w.2.1‖ * ‖κ' w.2.2‖) * 1 :=
          mul_le_mul_of_nonneg_left hde (by positivity)
      _ = ‖K w.1.1 w.1.2‖ * (‖κ w.2.1‖ * ‖κ' w.2.2‖) := by ring
  -- For fixed `y` the `x`-sum collapses: only `x = (p₁ - y.1, p₂ - y.2)` survives.
  have hinner : ∀ y : ℤ × ℤ, (∑' x : ℤ × ℤ, F (x, y))
      = K (p₁ - y.1) (p₂ - y.2) * κ y.1 * κ' y.2 := by
    intro y
    rw [tsum_eq_single (p₁ - y.1, p₂ - y.2)]
    · rw [hF]
      dsimp only
      rw [if_pos (sub_add_cancel p₁ y.1), if_pos (sub_add_cancel p₂ y.2)]
      ring
    · intro x hx
      rw [hF]
      have hx1 : x.1 ≠ p₁ - y.1 ∨ x.2 ≠ p₂ - y.2 := by
        by_contra h
        rw [not_or] at h
        exact hx (Prod.ext (by simpa using h.1) (by simpa using h.2))
      rcases hx1 with h | h
      · simp only [if_neg (fun hc => h ((eq_sub_iff_add_eq).mpr hc)), mul_zero, zero_mul]
      · simp only [if_neg (fun hc => h ((eq_sub_iff_add_eq).mpr hc)), mul_zero]
  -- Rewrite the target sum as `∑' w, F w`, then Fubini and swap the order of summation.
  rw [show (∑' w : (ℤ × ℤ) × (ℤ × ℤ), K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2
        * (if w.1.1 + w.2.1 = p₁ then 1 else 0) * (if w.1.2 + w.2.2 = p₂ then 1 else 0))
      = ∑' w, F w from tsum_congr (fun w => (hF w).symm)]
  rw [hFsum.tsum_prod]
  rw [← Summable.tsum_comm (f := fun x y => F (x, y)) hFsum]
  rw [tsum_congr hinner]
  rw [Work.A7.ModelApproxCore_aux.kernComp_eq_tsum hK hκn hκ'n p₁ p₂]

end Work.KMTPlan.A6
