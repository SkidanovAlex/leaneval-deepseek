import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.polyrel_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared elementary helpers for the scaling-down step

`Work.BMF.corr_shift` records that re-anchoring the linear perturbation of a completed sum to the
left endpoint of the interval only multiplies it by a unit complex number, hence does not change
its magnitude.  This is the trick that makes the phase produced by `completion_of_sums`
`PolyRel`-compatible: with the plain `θ·X` the perturbation would be `θ·t`, unbounded in `t` over
the incidence intervals, whereas `θ·(X - x')` is bounded by `|θ| · 4H/a` on every incidence
interval of a cell of radius `3H/a`.

`Work.BMF.PolyRel.change_second'` is the variant of `PolyRel.change_second` that simultaneously
changes the second interval and perturbs the second phase by a polynomial that is small on the
*first* interval.
-/

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

namespace Work.BMF

/-- The additive character is multiplicative: `eC (s+t) = eC s * eC t`. -/
lemma eC_add_loc (s t : ℝ) : eC (s + t) = eC s * eC t := by
  rw [eC, eC, eC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Shift of a completed sum: replacing the linear perturbation `θ·X` by `θ·(X - y)`
(the perturbation vanishing at the left endpoint of `[y, y+H]`) only multiplies the sum by a
constant of modulus one, so the magnitudes agree. -/
lemma corr_shift (a : ℕ → ℂ) (P : ℝ[X]) (y H θ : ℝ) :
    (∑ n ∈ natIcc y (y + H),
        a n * eC (-((P + Polynomial.C θ * (Polynomial.X - Polynomial.C y)).eval (n : ℝ))))
      = eC (θ * y) *
        (∑ n ∈ natIcc y (y + H),
          a n * eC (-((P + Polynomial.C θ * Polynomial.X).eval (n : ℝ)))) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have harg : -Polynomial.eval (n : ℝ) (P + Polynomial.C θ * (Polynomial.X - Polynomial.C y))
      = (-Polynomial.eval (n : ℝ) (P + Polynomial.C θ * Polynomial.X)) + θ * y := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X]
    ring
  rw [harg, eC_add_loc]
  ring

/-- `corr_shift` restated for `corr`: the two correlations have the same magnitude. -/
lemma corr_shift' (f : ℕ → ℂ) (P : ℝ[X]) (y L θ : ℝ) :
    corr f (P + Polynomial.C θ * (Polynomial.X - Polynomial.C y)) y L
      = eC (θ * y) * corr f (P + Polynomial.C θ * Polynomial.X) y L := by
  simpa only [corr] using corr_shift f P y L θ

/-- Changing the *second* interval of a `PolyRel` relation to a comparable one and simultaneously
perturbing the second phase by `η`: the `ε`-bound lives on the first interval, so we may absorb
`-η` (estimated on the first interval) and only the comparability bookkeeping changes. -/
lemma PolyRel.change_second' {k : ℕ} {C δ Cη : ℝ} {x₁ L₁ : ℝ} {P₁ : ℝ[X]} {x₂ L₂ x₂' L₂' : ℝ}
    {P₂ η : ℝ[X]} (h : PolyRel k C δ x₁ L₁ P₁ x₂ L₂ P₂) (hC : 0 < C) (hCη : 0 ≤ Cη)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₂' : 0 < L₂')
    (h1 : L₂ ≤ C * L₂') (h2 : L₂' ≤ C * L₂) (h3 : |x₂ - x₂'| ≤ C * L₂)
    (hη : η ∈ degreeLE ℝ (k : WithBot ℕ))
    (hb : ∀ t ∈ Set.Icc x₁ (x₁ + L₁), |η.eval t| ≤ Cη) :
    PolyRel k (C * C + C + 1 + Cη) δ x₁ L₁ P₁ x₂' L₂' (P₂ + η) := by
  obtain ⟨h11, h12, h13, ε, γ, hε, hγ, heq, hbdd, hint⟩ := h
  refine ⟨?_, ?_, ?_, ε - η, γ, Submodule.sub_mem _ hε hη, hγ, ?_, ?_, hint⟩
  · nlinarith [h11, h1, hC, hL₂', hL₂]
  · nlinarith [h12, h2, hC, hL₂', hL₂]
  · have h4 : |x₁ - x₂'| ≤ |x₁ - x₂| + |x₂ - x₂'| := abs_sub_le _ _ _
    have h6 : C * L₁ + C * L₂ ≤ (C * C + C + 1 + Cη) * L₁ := by
      nlinarith [h12, hC, hL₁, mul_nonneg hC.le hC.le, hCη]
    linarith [h4, h13, h3, h6]
  · show P₁ = ε - η + (P₂ + η) + γ
    rw [heq]; ring
  · intro t ht
    rw [eval_sub]
    have hsq : 0 ≤ C * C := mul_nonneg hC.le hC.le
    have habs : |ε.eval t - η.eval t| ≤ |ε.eval t| + |η.eval t| := by
      rw [sub_eq_add_neg, ← abs_neg (η.eval t)]
      exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    have hsum : |ε.eval t - η.eval t| ≤ C + Cη := by linarith [habs, hbdd t ht, hb t ht]
    linarith [hsum, hsq]

end Work.BMF
