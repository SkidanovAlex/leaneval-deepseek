import Submission.ZagierHoffmanProof.EndgameLast8

/-!
# SESSION 364 — `hNsupp`: the `{0,q}`-support of the inhomogeneity `N`

`PLAN.md` §«SESSION 363» §3.  `Nm = P·(A₁·H_w) - A₂·Λ = A₁P² + M·Λ` with `P = X^q - X`,
`Λ = X^q - C(θ^q)`: the first summand is `θ`-free and `Λ` has `θ`-support `{0,q}`, so every
`θ^j`-coefficient of `Nm` with `q ∤ j` vanishes — the `hN` hypothesis of `tp_num_eq_zero`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The coefficients of `Λ = X^q - C(θ^q)` lie in `A_0`. -/
lemma coeff_mem_ambA_zero_Lam (b : ℕ) :
    ((Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F) :
      Polynomial (Ambient F)).coeff b) ∈ ambA F 0 := by
  rw [Polynomial.coeff_sub]
  refine (ambASub F 0).sub_mem ?_ ?_
  · rw [Polynomial.coeff_X_pow]
    split_ifs with h
    · exact ambA_one_mem F 0
    · exact ambA_zero_mem 0
  · exact coeff_C_mem_ambA F (ambA_pow_mem F 0 (ambTheta_mem_ambA F 0) (Nat.card F)) b

/-- ★★★★ **The `θ`-coefficients of the coefficients of `Λ` vanish off `{0,q}`.** -/
lemma coeffNu_Lam_coeff_eq_zero (hq : 0 < Nat.card F) {b j : ℕ} (hj0 : j ≠ 0)
    (hjq : j ≠ Nat.card F) :
    coeffNu F 0 j ((Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F) :
      Polynomial (Ambient F)).coeff b) = 0 := by
  have hone : (1 : Ambient F) ∈ ambF F := (ambF F).one_mem
  have hneg : (-1 : Ambient F) ∈ ambF F := (ambF F).neg_mem hone
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  by_cases hb : b = Nat.card F
  · rw [if_pos hb]
    have hb0 : ¬ b = 0 := by omega
    rw [if_neg hb0, sub_zero]
    exact coeffNu_eq_zero_of_mem_ambF F hone hj0
  · rw [if_neg hb]
    by_cases hb0 : b = 0
    · rw [hb0, if_pos rfl, zero_sub]
      rw [show (-((ambTheta F) ^ Nat.card F)) = (ambTheta F) ^ Nat.card F * (-1) from by ring,
        coeffNu_theta_pow_mul F (x := (-1 : Ambient F)) (ambF_subset_ambA_zero (F := F) hneg)]
      by_cases h : Nat.card F ≤ j
      · rw [if_pos h]
        exact coeffNu_eq_zero_of_mem_ambF F hneg
          (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne h (Ne.symm hjq)))
      · rw [if_neg h]
    · rw [if_neg hb0, sub_self, coeffNu_zero]

/-- ★★★★ **`M·Λ` has `θ`-support in `{0,q}`** for `M` with `ambF`-coefficients. -/
lemma coeffNu_mul_Lam_eq_zero (hq0 : 0 < Nat.card F) {M : Polynomial (Ambient F)}
    (hM : ∀ n, M.coeff n ∈ ambF F) {n j : ℕ} (hj0 : j ≠ 0) (hjq : j ≠ Nat.card F) :
    coeffNu F 0 j ((M * (Polynomial.X ^ Nat.card F
      - Polynomial.C ((ambTheta F) ^ Nat.card F)) : Polynomial (Ambient F)).coeff n) = 0 := by
  rw [Polynomial.coeff_mul,
    coeffNu_sum F _ (fun b _ => ambA_mul_mem F (ambF_subset_ambA_zero (F := F) (hM b.1))
      (coeff_mem_ambA_zero_Lam F b.2)) j]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [coeffNu_mul_of_constant F (ambF_subset_ambA_zero (F := F) (hM b.1))
      (coeff_mem_ambA_zero_Lam F b.2)
      (fun i hi => coeffNu_eq_zero_of_mem_ambF F (hM b.1) hi) j,
    coeffNu_zero_of_mem_ambF F (hM b.1),
    coeffNu_Lam_coeff_eq_zero F hq0 hj0 hjq, mul_zero]

/-- ★★★★★ **`hNsupp`** (`PLAN.md` §«SESSION 363» §3): every `θ`-coefficient of `Nm` of degree
outside `qℤ` vanishes. -/
theorem coeffNu_Nm_eq_zero {w : ℕ} {A₁ A₂ : Polynomial (Ambient F)}
    (hq : 3 ≤ Nat.card F) (hwq : Nat.card F < w)
    (hA₁m : ∀ n, A₁.coeff n ∈ ambF F) (hA₂m : ∀ n, A₂.coeff n ∈ ambF F)
    {n j : ℕ} (hj : ¬ Nat.card F ∣ j) :
    coeffNu F 0 j (((Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
      - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) :
        Polynomial (Ambient F)).coeff n) = 0 := by
  set P : Polynomial (Ambient F) := Polynomial.X ^ Nat.card F - Polynomial.X with hPs
  set Lam : Polynomial (Ambient F) :=
    Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F) with hLs
  set Mm : Polynomial (Ambient F) :=
    A₁ * P * Polynomial.C ((w - Nat.card F : ℕ) : Ambient F) - A₂ with hMs
  have hq0 : 0 < Nat.card F := by omega
  have hj0 : j ≠ 0 := fun h0 => hj (h0 ▸ dvd_zero _)
  have hjq : j ≠ Nat.card F := fun h0 => hj (h0 ▸ dvd_refl _)
  have hPambF : ∀ m, P.coeff m ∈ ambF F := by rw [hPs]; exact coeff_X_pow_sub_X_mem_ambF
  have hMambF : ∀ m, Mm.coeff m ∈ ambF F := by
    rw [hMs]
    intro m
    rw [Polynomial.coeff_sub]
    refine (ambF F).sub_mem ?_ (hA₂m m)
    exact coeff_mul_mem_ambF F (coeff_mul_mem_ambF F hA₁m hPambF)
      (fun k => natCast_poly_coeff_mem_ambF F _ k) m
  have hdecomp : P * (A₁ * ambH F w) - A₂ * Lam = A₁ * P ^ 2 + Mm * Lam := by
    rw [ambH_factor_of_lt (F := F) hwq, X_sub_C_pow_card F (ambTheta F), ← hLs, hMs]
    ring
  rw [hdecomp, Polynomial.coeff_add,
    coeffNu_add F
      (coeff_mul_mem_ambA (fun k => ambF_subset_ambA_zero (F := F) (hA₁m k))
        (fun k => ambF_subset_ambA_zero (F := F) (coeff_pow_two_mem_ambF F hPambF k)) n)
      (coeff_mul_mem_ambA (fun k => ambF_subset_ambA_zero (F := F) (hMambF k))
        (fun k => coeff_mem_ambA_zero_Lam F k) n),
    coeffNu_eq_zero_of_mem_ambF F
      (coeff_mul_mem_ambF F hA₁m (coeff_pow_two_mem_ambF F hPambF) n) hj0,
    coeffNu_mul_Lam_eq_zero F hq0 hMambF hj0 hjq, add_zero]

end ZagierHoffmanPositiveChar
