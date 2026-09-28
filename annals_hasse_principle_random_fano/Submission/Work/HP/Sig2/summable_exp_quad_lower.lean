import Mathlib
import Submission.Work.HP.Sig2.Poisson1D
import Submission.Work.HP.Sig2.summable_pi_prod

namespace Work.HP.Sig2

/-- A quadratic form that dominates `ε ∑ xᵢ²` (with `ε > 0`) makes the Gaussian weight
`n ↦ exp(-c · nᵀGn)` summable on `ℤ^κ`, for any `c > 0`.

Indeed `nᵀGn ≥ ε ∑ nᵢ²`, so `exp(-c·nᵀGn) ≤ exp(-cε·∑ nᵢ²) = ∏ᵢ exp(-cε·nᵢ²)`, and the latter is
summable as the product over a finite index set of the 1-D Gaussian sums. -/
lemma summable_exp_quad_lower {κ : Type*} [Fintype κ] (G : Matrix κ κ ℝ) (c ε : ℝ)
    (hε : 0 < ε) (hc : 0 < c)
    (hbound : ∀ x : κ → ℝ, ε * (∑ i, (x i) ^ 2) ≤ ∑ i, ∑ j, x i * G i j * x j) :
    Summable (fun n : κ → ℤ =>
      Real.exp (-c * (∑ i, ∑ j, (n i : ℝ) * G i j * (n j : ℝ)))) := by
  have hd : 0 < c * ε := mul_pos hc hε
  -- Pointwise rewriting of the majorant as a product of 1-D Gaussians.
  have hpt : ∀ n : κ → ℤ,
      Real.exp (-(c * ε) * ∑ i, (n i : ℝ) ^ 2)
        = ∏ i, Real.exp (-(c * ε) * (n i : ℝ) ^ 2) := fun n => by
    rw [Finset.mul_sum, Real.exp_sum]
  -- The majorant is summable: product over the finite type of summable 1-D Gaussians.
  have hmaj : Summable (fun n : κ → ℤ => Real.exp (-(c * ε) * ∑ i, (n i : ℝ) ^ 2)) := by
    have hprod : Summable
        (fun n : κ → ℤ => ∏ i, Real.exp (-(c * ε) * (n i : ℝ) ^ 2)) :=
      summable_pi_prod
        (f := fun _ : κ => fun m : ℤ => Real.exp (-(c * ε) * (m : ℝ) ^ 2))
        (fun _ => summable_gauss_int (c * ε) hd)
        (fun _ _ => Real.exp_nonneg _)
    exact hprod.congr (fun n => (hpt n).symm)
  -- Domination: the target is nonnegative and bounded by the majorant.
  refine Summable.of_nonneg_of_le
    (f := fun n : κ → ℤ => Real.exp (-(c * ε) * ∑ i, (n i : ℝ) ^ 2))
    (fun n => Real.exp_nonneg _) (fun n => ?_) hmaj
  rw [Real.exp_le_exp]
  have hq : ε * (∑ i, (n i : ℝ) ^ 2)
      ≤ ∑ i, ∑ j, (n i : ℝ) * G i j * (n j : ℝ) := hbound (fun i => (n i : ℝ))
  calc -c * (∑ i, ∑ j, (n i : ℝ) * G i j * (n j : ℝ))
      ≤ -c * (ε * ∑ i, (n i : ℝ) ^ 2) := mul_le_mul_of_nonpos_left hq (by linarith)
    _ = -(c * ε) * ∑ i, (n i : ℝ) ^ 2 := by ring

end Work.HP.Sig2
