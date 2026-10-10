import Mathlib
import Submission.Work.MotV5.WtDefs
import Submission.Work.MotV5.Wt_kleinQPoly_le

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- The coefficients of `polyOf y` are the `y j`. -/
lemma coeff_polyOf {F : Type*} [CommRing F] (y : Fin 5 → F) (l : ℕ) (hl : l < 5) :
    (polyOf y).coeff l = y ⟨l, hl⟩ := by
  classical
  rw [polyOf, ← Polynomial.lcoeff_apply, map_sum]
  rw [Finset.sum_eq_single ⟨l, hl⟩]
  · rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
      mul_one]
  · intro j _ hj
    rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hj (Fin.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Wt_polyOf {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {g : F} {y : Fin 5 → F} {l₀ : Fin 5}
    (hmax : ∀ l : Fin 5, Work.MotV5.wt v g (y l) l ≤ Work.MotV5.wt v g (y l₀) l₀)
    (huniq : ∀ l : Fin 5, Work.MotV5.wt v g (y l) l = Work.MotV5.wt v g (y l₀) l₀ → l = l₀) :
    Work.MotV5.Wt v g (Work.MotV5.polyOf y) = Work.MotV5.wt v g (y l₀) l₀ := by
  have hbig : ∀ l : ℕ, 5 ≤ l → (polyOf y).coeff l = 0 := by
    intro l hl
    rw [polyOf, ← Polynomial.lcoeff_apply, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg,
      mul_zero]
    intro h
    exact absurd (h ▸ j.isLt) (by omega)
  apply le_antisymm
  · rw [WtKL_Wt_le_iff]
    intro l
    by_cases hl : l < 5
    · rw [coeff_polyOf y l hl]; exact hmax ⟨l, hl⟩
    · rw [hbig l (by omega)]
      simp only [wt, map_zero, zero_pow (by norm_num : (5 : ℕ) ≠ 0), mul_zero]
      exact zero_le
  · have hcoeff : (polyOf y).coeff (l₀ : ℕ) = y l₀ := coeff_polyOf y (l₀ : ℕ) l₀.isLt
    have := WtKL_wt_coeff_le_Wt v g (polyOf y) (l₀ : ℕ)
    rwa [hcoeff] at this

end Work.MotV5
