import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.eC_integral_oneDim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integral of a linear character over the unit box

`eC t = e(t) = exp(2π i t)` is the additive character.  This file evaluates the integral of the
character of a linear form with integer coefficients over the unit box `unitBox k = [0,1]^k`:

`∫_{[0,1]^k} e(Σ_j α_j v_j) dα = 1` if the integer vector `v` vanishes, and `0` otherwise.

The proof splits the linear character into a product of one-dimensional characters
(`prod_eC_univ_loc`), rewrites the restriction of Lebesgue measure to the box as the product of
the restricted one-dimensional Lebesgue measures (`MeasureTheory.volume_pi` and
`Measure.restrict_pi_pi`), applies Fubini in the coordinates
(`MeasureTheory.integral_fintype_prod_eq_prod`, which is unconditional and stated over any
`RCLike` field, here `ℂ`), evaluates each one-dimensional integral by `eC_integral_oneDim`, and
finally identifies the product of the resulting `if`s with the single `if` on `v = 0`.
-/

namespace Work.BMF

open MeasureTheory
open scoped BigOperators

/-- `eC` is additive: `eC (a + b) = eC a * eC b`. -/
private lemma eC_add_loc (a b : ℝ) : eC (a + b) = eC a * eC b := by
  simp only [eC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The product of additive characters is the character of the sum. -/
private lemma prod_eC_loc {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ∏ i ∈ s, eC (a i) = eC (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [eC, Complex.exp_zero]
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, eC_add_loc]

/-- The product of additive characters over a finite type is the character of the sum. -/
private lemma prod_eC_univ_loc {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∏ i, eC (a i) = eC (∑ i, a i) := prod_eC_loc Finset.univ a

/-- **The character integral over the unit box.**  For every integer vector `v : Fin k → ℤ`,
`∫_{unitBox k} e(Σ_j α_j v_j) dα` equals `1` when `v = 0` and `0` otherwise. -/
theorem eC_integral_unitBox (k : ℕ) (v : Fin k → ℤ) :
    (∫ α in Work.BMF.unitBox k, Work.BMF.eC (∑ j : Fin k, α j * (v j : ℝ)))
      = if v = 0 then (1:ℂ) else 0 := by
  classical
  -- The character of the linear form is the product of the coordinate characters.
  have h1 : (∫ α in Work.BMF.unitBox k, Work.BMF.eC (∑ j : Fin k, α j * (v j : ℝ)))
      = ∫ α in Work.BMF.unitBox k, ∏ j : Fin k, Work.BMF.eC (α j * (v j : ℝ)) := by
    refine MeasureTheory.setIntegral_congr_fun ?_ ?_
    · rw [Work.BMF.unitBox]
      exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
    · intro α _
      exact (prod_eC_univ_loc (fun j : Fin k => α j * (v j : ℝ))).symm
  rw [h1]
  -- The restriction of Lebesgue measure to the box is the product of the restricted
  -- one-dimensional Lebesgue measures.
  have hmass : (volume : Measure (Fin k → ℝ)).restrict (Work.BMF.unitBox k)
      = Measure.pi (fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)) := by
    rw [Work.BMF.unitBox, MeasureTheory.volume_pi (α := fun _ : Fin k => ℝ)]
    exact Measure.restrict_pi_pi _ _
  rw [hmass]
  -- Fubini in the coordinates.
  rw [MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (μ := fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1))
    (f := fun j : Fin k => fun t : ℝ => Work.BMF.eC (t * (v j : ℝ)))]
  -- Evaluate each one-dimensional integral.
  rw [Finset.prod_congr rfl (fun j (_ : j ∈ Finset.univ) => eC_integral_oneDim (v j))]
  -- The product of the resulting `if`s is the `if` on `v = 0`.
  by_cases hv : v = 0
  · subst hv
    simp
  · have hne : ∃ j : Fin k, v j ≠ 0 := by
      by_contra h
      have hall : ∀ j : Fin k, v j = 0 := by
        intro j
        by_contra hj
        exact h ⟨j, hj⟩
      exact hv (funext hall)
    obtain ⟨j, hj⟩ := hne
    rw [ite_eq_right hv]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

end Work.BMF
