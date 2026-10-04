import Mathlib
import Submission.Work.Diff.Evol.Vocab

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Evol

/-- The diagonal second derivative of `NormedSpace.exp` at `0` is the multiplication:
`(d(d exp)₀ u) u = u * u`, in an ARBITRARY (possibly noncommutative) real Banach algebra.
Proof route: `exp` has `expSeries` as power series with infinite radius
(`exp_hasFPowerSeriesOnBall`), and `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace`
gives `iteratedFDeriv ℝ 2 exp 0 v = ∑ σ : Perm (Fin 2), expSeries ℝ 𝔸 2 (fun i => v (σ i))`;
with `expSeries_apply_eq` (`expSeries ℝ 𝔸 2 w = (2! : ℝ)⁻¹ • (w 0 * w 1)`) and
`iteratedFDeriv_two_apply` (`iteratedFDeriv ℝ 2 f z m = fderiv (fderiv f) z (m 0) (m 1)`)
this gives the claim for `v = ![u,u]`. -/
theorem exp_second_deriv_zero
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (u : 𝔸) :
    fderiv ℝ (fun Y : 𝔸 => fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) Y) 0 u u = u * u := by
  -- Step 1: identify the second Fréchet derivative with the second iterated derivative
  -- evaluated at `![u, u]`.
  have h1 : fderiv ℝ (fun Y : 𝔸 => fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) Y) 0 u u
      = (iteratedFDeriv ℝ 2 (NormedSpace.exp : 𝔸 → 𝔸) 0) ![u, u] := by
    rw [iteratedFDeriv_two_apply]
    simp
  rw [h1]
  -- Step 2: `exp` is the sum of its power series `expSeries`, with infinite radius, so the
  -- second iterated derivative at `0` is given by the permutation sum over `Perm (Fin 2)`.
  have hsum := (NormedSpace.exp_hasFPowerSeriesOnBall (𝕂 := ℝ) (𝔸 := 𝔸))
    |>.iteratedFDeriv_eq_sum_of_completeSpace (v := ![u, u])
  rw [hsum]
  -- Step 3: every summand is the same: `expSeries ℝ 𝔸 2 w = (2!)⁻¹ • (w 0 * w 1)`, and here
  -- both entries are `u`.
  have hconst : ∀ σ : Equiv.Perm (Fin 2),
      NormedSpace.expSeries ℝ 𝔸 2 (fun i => ![u, u] (σ i)) = ((Nat.factorial 2 : ℝ))⁻¹ • (u * u) := by
    intro σ
    have h2 : ∀ j : Fin 2, ![u, u] j = u := by intro j; fin_cases j <;> rfl
    have hfun : (fun i : Fin 2 => ![u, u] (σ i)) = fun _ => u := by
      funext i; exact h2 (σ i)
    rw [hfun, NormedSpace.expSeries_apply_eq, pow_two]
  -- Step 4: there are `2! = 2` permutations, and `2 * (2!)⁻¹ = 1`.
  simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Nat.factorial_two]
  rw [two_nsmul, ← add_smul]
  norm_num

end Work.Diff.Evol
