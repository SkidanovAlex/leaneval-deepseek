import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

/-- For `0 ≤ c`, the supremum of `c ^ m` over `m = 0, …, D` is `max 1 (c ^ D)`. -/
lemma iSup_pow_fin {c : ℝ} (hc : 0 ≤ c) (D : ℕ) :
    (⨆ m : Fin (D+1), c ^ (m:ℕ)) = max 1 (c^D) := by
  apply le_antisymm
  · apply ciSup_le
    intro m
    rcases le_total 1 c with h | h
    · calc c ^ (m:ℕ) ≤ c ^ D := pow_le_pow_right₀ h (Nat.le_of_lt_succ m.isLt)
        _ ≤ max 1 (c^D) := le_max_right _ _
    · calc c ^ (m:ℕ) ≤ 1 := pow_le_one₀ hc h
        _ ≤ max 1 (c^D) := le_max_left _ _
  · apply max_le
    · exact le_trans (le_of_eq (pow_zero c).symm)
        (le_ciSup (f := fun m : Fin (D+1) => c ^ (m:ℕ)) (Finite.bddAbove_range _) 0)
    · exact le_ciSup (f := fun m : Fin (D+1) => c ^ (m:ℕ)) (Finite.bddAbove_range _)
        ⟨D, Nat.lt_succ_self D⟩

section aux

variable {F : Type*} [Field F]

/-- The supremum of the absolute value `v` over the geometric progression `b ^ m`,
`m = 0, …, D`, equals `max (v (b ^ D)) 1`. -/
lemma iSup_abv_pow (v : AbsoluteValue F ℝ) (b : F) (D : ℕ) :
    (⨆ m : Fin (D+1), v (b ^ ((m:ℕ):ℤ))) = max (v (b^D)) 1 := by
  have h : (fun m : Fin (D+1) => v (b ^ ((m:ℕ):ℤ))) =
      (fun m : Fin (D+1) => (v b)^(m:ℕ)) := by
    funext m; rw [zpow_natCast, map_pow]
  rw [h]
  have hc : (0:ℝ) ≤ v b := v.nonneg b
  rw [iSup_pow_fin hc D, map_pow, max_comm]

/-- The multiplicative height of the tuple `(b ^ m)_{m=0}^D` equals `mulHeight₁ (b ^ D)`. -/
lemma mulHeight_fin_pow [Height.AdmissibleAbsValues F] (b : F) (D : ℕ) :
    Height.mulHeight (fun m : Fin (D+1) => b ^ ((m:ℕ):ℤ)) = Height.mulHeight₁ (b^D) := by
  have hy : (fun m : Fin (D + 1) => b ^ ((m:ℕ):ℤ)) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hfun : (fun v : AbsoluteValue F ℝ => ⨆ m : Fin (D+1), v (b^((m:ℕ):ℤ)))
            = (fun v => max (v (b^D)) 1) := by
    funext v; exact iSup_abv_pow v b D
  rw [Height.mulHeight_eq hy, Height.mulHeight₁_eq, hfun]
  congr 1
  apply finprod_congr
  intro v
  exact iSup_abv_pow v.val b D

/-- The logarithmic height of the tuple `(b ^ m)_{m=0}^D` equals `D · h(b)`. -/
lemma logHeight_fin_pow [Height.AdmissibleAbsValues F] (b : F) (D : ℕ) :
    Height.logHeight (fun m : Fin (D+1) => b ^ ((m:ℕ):ℤ))
      = (D:ℝ) * Height.logHeight₁ b := by
  rw [Height.logHeight_eq_log_mulHeight, mulHeight_fin_pow,
    ← Height.logHeight₁_eq_log_mulHeight₁, Height.logHeight₁_pow]

end aux

theorem logHeight_monomial_le {F : Type*} [Field F] [NumberField F] {r : ℕ} (a : Fin r → F)
    (s : ℤ) (D : Fin r → ℕ) :
    Height.logHeight (fun lm : (j : Fin r) → Fin (D j + 1) =>
        ∏ j, a j ^ (s * ((lm j : ℕ) : ℤ)))
      ≤ ∑ j, (|(s : ℝ)| * (D j : ℝ)) * Height.logHeight₁ (a j) := by
  have hy : ∀ j : Fin r, (fun m : Fin (D j + 1) => (a j ^ s) ^ ((m:ℕ):ℤ)) ≠ 0 := by
    intro j h
    have := congrFun h 0
    simp at this
  have hprod : Height.logHeight (fun lm : (j : Fin r) → Fin (D j + 1) =>
        ∏ j, a j ^ (s * ((lm j : ℕ) : ℤ)))
      = Height.logHeight (fun lm : (j : Fin r) → Fin (D j + 1) =>
        ∏ j, (a j ^ s) ^ ((lm j : ℕ) : ℤ)) := by
    congr 1
    funext lm
    apply Finset.prod_congr rfl
    intro j _
    rw [zpow_mul]
  rw [hprod, Height.logHeight_fun_prod_eq hy]
  apply Finset.sum_le_sum
  intro j _
  refine le_of_eq ?_
  rw [logHeight_fin_pow, Height.logHeight₁_zpow]
  have hs : ((s.natAbs : ℝ)) = |(s : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; norm_num
  rw [hs]; ring

end Work.BW
