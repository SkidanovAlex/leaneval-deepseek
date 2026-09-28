import Mathlib
import Submission.Work.HP.Sig2.GaussPoissonDefs
import Submission.Work.HP.Sig2.summable_gauss_quad
import Submission.Work.HP.Sig2.summable_pi_prod

/-!
# Summability of a shifted Gaussian weight attached to a positive definite quadratic form

For a positive definite `G : Matrix ι ι ℝ`, a positive `β` and an arbitrary real shift
`u : ι → ℝ`, the function
`n ↦ exp (-β * qForm G (fun i => n i + u i))` on `ℤ^ι` is summable.

This is the analytic input behind the Poisson summation formula for a Gaussian carrying a real
shift: unlike the unshifted case, the shift is not integral, so no reindexing is available and
one has to dominate the shifted Gaussian directly.

The proof combines the coercivity bound `posdef_lower_bound`
(`ε ∑ xᵢ² ≤ qForm G x` with `ε > 0`, obtained from the positive definiteness of `G`) with the
elementary estimate `(a + b)² ≥ a²/2 - b²`: the shift is then absorbed into the multiplicative
constant `exp (β ε ∑ uᵢ²)`, leaving the unshifted product of one-dimensional Gaussian weights,
which is summable because a product over a finite index type of summable nonnegative functions of
the coordinates is summable (`summable_pi_prod`).
-/

noncomputable section

open Matrix

namespace Work.HP.Sig2

/-- Elementary pointwise estimate `(a i + b i) ^ 2 ≥ (1/2) * (a i) ^ 2 - (b i) ^ 2`, summed over a
finite index type: a shift perturbs the Gaussian weight only by a bounded factor. -/
lemma half_mul_sum_sq_sub_sum_sq_le_sum_sq_add {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (1 / 2) * (∑ i, (a i) ^ 2) - ∑ i, (b i) ^ 2 ≤ ∑ i, (a i + b i) ^ 2 := by
  have hper : ∀ i : ι, (1 / 2) * (a i) ^ 2 - (b i) ^ 2 ≤ (a i + b i) ^ 2 := by
    intro i
    nlinarith [sq_nonneg (a i + 2 * b i)]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hper i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  exact h

/-- The scalar core of the domination estimate: if `ε * (A/2 - B) ≤ F` and `β > 0`, then
`exp (-β F) ≤ exp (β ε B) * exp (-(β ε / 2) A)`. -/
lemma exp_shifted_arith {A B F ε β : ℝ} (hβ : 0 < β)
    (h1 : ε * ((1 / 2) * A - B) ≤ F) :
    -β * F ≤ β * ε * B + -(β * ε / 2) * A := by
  have step2 : -F ≤ -(ε * ((1 / 2) * A - B)) := by linarith
  have step3 : β * (-F) ≤ β * (-(ε * ((1 / 2) * A - B))) :=
    mul_le_mul_of_nonneg_left step2 hβ.le
  have e1 : β * (-F) = -β * F := by ring
  have e2 : β * (-(ε * ((1 / 2) * A - B))) = β * ε * B + -(β * ε / 2) * A := by ring
  linarith [step3, e1, e2]

/-- For `c > 0`, the unshifted Gaussian weight `n ↦ exp (-c ∑ nᵢ²)` is summable on `ℤ^ι`: it is
the product over the finite index type of the summable one-dimensional Gaussian weights. -/
lemma summable_gauss_pi {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ι → ℤ => Real.exp (-c * ∑ i, (n i : ℝ) ^ 2)) := by
  have hprod : Summable (fun n : ι → ℤ => ∏ i, Real.exp (-c * (n i : ℝ) ^ 2)) :=
    summable_pi_prod (f := fun _ : ι => fun m : ℤ => Real.exp (-c * (m : ℝ) ^ 2))
      (fun _ => summable_gauss_int c hc) (fun _ _ => Real.exp_nonneg _)
  refine hprod.congr (fun n => ?_)
  rw [Finset.mul_sum, Real.exp_sum]

/-- Pointwise domination of the shifted Gaussian weight by a constant multiple of the unshifted
one, using the coercivity bound `hbound` for `G`. -/
lemma exp_shifted_qForm_le {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (β ε : ℝ) (hβ : 0 < β)
    (hε : 0 < ε) (hbound : ∀ x : ι → ℝ, ε * (∑ i, (x i) ^ 2) ≤ qForm G x)
    (u : ι → ℝ) (n : ι → ℤ) :
    Real.exp (-β * qForm G (fun i => (n i : ℝ) + u i))
      ≤ Real.exp (β * ε * ∑ i, (u i) ^ 2)
        * Real.exp (-(β * ε / 2) * ∑ i, (n i : ℝ) ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : ε * ((1 / 2) * ∑ i, (n i : ℝ) ^ 2 - ∑ i, (u i) ^ 2)
      ≤ qForm G (fun i => (n i : ℝ) + u i) :=
    (mul_le_mul_of_nonneg_left
        (half_mul_sum_sq_sub_sum_sq_le_sum_sq_add (fun i => (n i : ℝ)) u) hε.le).trans
      (hbound (fun i => (n i : ℝ) + u i))
  exact exp_shifted_arith hβ h1

theorem summable_shifted_gauss {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (β : ℝ) (hβ : 0 < β) (u : ι → ℝ) :
    Summable (fun n : ι → ℤ => Real.exp (-β * qForm G (fun i => (n i : ℝ) + u i))) := by
  classical
  obtain ⟨ε, hε, hbound⟩ := posdef_lower_bound G hG
  have hc : 0 < β * ε / 2 := div_pos (mul_pos hβ hε) (by norm_num)
  have hmaj : Summable (fun n : ι → ℤ => Real.exp (-(β * ε / 2) * ∑ i, (n i : ℝ) ^ 2)) :=
    summable_gauss_pi (β * ε / 2) hc
  have hmul : Summable (fun n : ι → ℤ => Real.exp (β * ε * ∑ i, (u i) ^ 2)
      * Real.exp (-(β * ε / 2) * ∑ i, (n i : ℝ) ^ 2)) :=
    Summable.mul_left (Real.exp (β * ε * ∑ i, (u i) ^ 2)) hmaj
  refine Summable.of_nonneg_of_le
    (f := fun n : ι → ℤ => Real.exp (β * ε * ∑ i, (u i) ^ 2)
      * Real.exp (-(β * ε / 2) * ∑ i, (n i : ℝ) ^ 2))
    (fun n => Real.exp_nonneg _)
    (fun n => exp_shifted_qForm_le G β ε hβ hε hbound u n) hmul

end Work.HP.Sig2
