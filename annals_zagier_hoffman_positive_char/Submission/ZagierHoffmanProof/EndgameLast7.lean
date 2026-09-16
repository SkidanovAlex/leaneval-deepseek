import Submission.ZagierHoffmanProof.EndgameLast6

/-!
# SESSION 363 — the last case `w = 2q-2`: item (ii), the final contradiction

`PLAN.md` §«SESSION 362» §7.2.  From `N·D = D₂·P·(P - 2Λ)` and `N = A₁P² + M·Λ`
(`M = A₁P·C(q-2) - A₂`) one gets `P²(DA₁ - D₂) + (DM + 2D₂P)·Λ = 0`.  Expanding
`Λ = X^q - C(θ^q)` and reading the `θ^q`-coefficient (`tp · q`) gives `DM + 2D₂P = 0`; then
`P²(DA₁ - D₂) = 0` gives `DA₁ = D₂`; finally
`D·A₂ = D₂P(C(q-2) + 2) = D₂P·C(q) = 0`, so `A₂ = 0` — contradiction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §8. The `tp`-atoms of the final read -/

lemma tp_zero_of_coeff_mem_ambF {p : Polynomial (Ambient F)} (hp : ∀ n, p.coeff n ∈ ambF F)
    {j : ℕ} (hj : j ≠ 0) : tp F p j = 0 := by
  ext n
  rw [tp_coeff, Polynomial.coeff_zero]
  exact coeffNu_eq_zero_of_mem_ambF F (hp n) hj

lemma tp_X_pow_card_eq_zero (hq : 0 < Nat.card F) :
    tp F (Polynomial.X ^ Nat.card F : Polynomial (Ambient F)) (Nat.card F) = 0 := by
  ext n
  rw [tp_coeff, Polynomial.coeff_zero, Polynomial.coeff_X_pow]
  by_cases hn : n = Nat.card F
  · rw [if_pos hn]
    exact coeffNu_eq_zero_of_mem_ambF F (ambF F).one_mem (by omega : Nat.card F ≠ 0)
  · rw [if_neg hn, coeffNu_zero]

lemma tp_C_theta_pow_card_eq_one (hq : 0 < Nat.card F) :
    tp F (Polynomial.C ((ambTheta F) ^ Nat.card F)) (Nat.card F) = 1 := by
  ext n
  rw [tp_coeff, Polynomial.coeff_one, Polynomial.coeff_C]
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl, if_pos rfl,
      show (ambTheta F) ^ Nat.card F = (ambTheta F) ^ Nat.card F * 1 from (mul_one _).symm,
      coeffNu_theta_pow_mul F (x := (1 : Ambient F)) (ambA_one_mem F 0),
      if_pos (le_refl _), Nat.sub_self, coeffNu_zero_of_mem_ambF F (ambF F).one_mem]
  · rw [if_neg hn, if_neg hn, coeffNu_zero]

lemma tp_mul_C_theta_pow_card {y : Polynomial (Ambient F)} (hy : ∀ n, y.coeff n ∈ ambF F)
    (hq : 0 < Nat.card F) :
    tp F (y * Polynomial.C ((ambTheta F) ^ Nat.card F)) (Nat.card F) = y := by
  rw [tp_mul_const F hy
      (coeff_C_mem_ambA F (ambA_pow_mem F 0 (ambTheta_mem_ambA F 0) (Nat.card F))) (Nat.card F),
    tp_C_theta_pow_card_eq_one F hq, mul_one]

/-- `(m : Polynomial (Ambient F))` has coefficients in the coefficient field. -/
lemma natCast_poly_coeff_mem_ambF (m n : ℕ) :
    ((m : Polynomial (Ambient F))).coeff n ∈ ambF F := by
  rw [show (m : Polynomial (Ambient F)) = Polynomial.C ((m : ℕ) : Ambient F) from rfl,
    Polynomial.coeff_C]
  split_ifs with h
  · exact natCast_mem_ambF (F := F) m
  · exact (ambF F).zero_mem

/-! ## §9. The final contradiction -/

/-- ★★★★★ **Item (ii)**: the weight-`2q-2` datum is impossible. -/
theorem contradiction_of_ND {w : ℕ} {A₁ A₂ D D2 : Polynomial (Ambient F)}
    (hq : 3 ≤ Nat.card F) (hwq : Nat.card F < w) (hw2 : w = 2 * Nat.card F - 2)
    (hA₁m : ∀ n, A₁.coeff n ∈ ambF F) (hA₂m : ∀ n, A₂.coeff n ∈ ambF F)
    (hDm : ∀ n, D.coeff n ∈ ambF F) (hD2m : ∀ n, D2.coeff n ∈ ambF F)
    (hA₂ne : A₂ ≠ 0) (hD0 : D ≠ 0)
    (hND : ((Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
          - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))) * D
        = D2 * ((Polynomial.X ^ Nat.card F - Polynomial.X)
          * ((Polynomial.X ^ Nat.card F - Polynomial.X)
            - 2 * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))))) :
    False := by
  set P : Polynomial (Ambient F) := Polynomial.X ^ Nat.card F - Polynomial.X with hPs
  set Lam : Polynomial (Ambient F) :=
    Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F) with hLs
  set M : Polynomial (Ambient F) :=
    A₁ * P * Polynomial.C ((w - Nat.card F : ℕ) : Ambient F) - A₂ with hMs
  have hq0 : 0 < Nat.card F := by omega
  have hqne : Nat.card F ≠ 0 := by omega
  have hP0 : P ≠ 0 := by
    intro h0
    refine eval_X_pow_sub_X_theta_ne_zero F hq ?_
    rw [hPs] at h0
    rw [h0, Polynomial.eval_zero]
  have hPambF : ∀ n, P.coeff n ∈ ambF F := by
    rw [hPs]; exact coeff_X_pow_sub_X_mem_ambF
  have hMambF : ∀ n, M.coeff n ∈ ambF F := by
    rw [hMs]
    intro n
    rw [Polynomial.coeff_sub]
    refine (ambF F).sub_mem ?_ (hA₂m n)
    exact coeff_mul_mem_ambF F (coeff_mul_mem_ambF F hA₁m hPambF)
      (fun m => natCast_poly_coeff_mem_ambF F _ m) n
  have hXq : ∀ n, (Polynomial.X ^ Nat.card F : Polynomial (Ambient F)).coeff n ∈ ambA F 0 := by
    intro n
    rw [Polynomial.coeff_X_pow]
    split_ifs with h
    · exact ambA_one_mem F 0
    · exact ambA_zero_mem 0
  have hNLam : P * (A₁ * ambH F w) - A₂ * Lam = A₁ * P ^ 2 + M * Lam := by
    rw [ambH_factor_of_lt (F := F) hwq, X_sub_C_pow_card F (ambTheta F), ← hLs, hMs]
    ring
  have h1 : (A₁ * P ^ 2 + M * Lam) * D = D2 * (P * (P - 2 * Lam)) := by
    rw [hNLam] at hND
    exact hND
  have h2 : P ^ 2 * (D * A₁ - D2) + (D * M + 2 * D2 * P) * Lam = 0 := by
    have h1' : (A₁ * P ^ 2 + M * Lam) * D - D2 * (P * (P - 2 * Lam)) = 0 := by
      rw [h1]; ring
    rw [show P ^ 2 * (D * A₁ - D2) + (D * M + 2 * D2 * P) * Lam
        = (A₁ * P ^ 2 + M * Lam) * D - D2 * (P * (P - 2 * Lam)) from by ring]
    exact h1'
  have hxambF : ∀ n, (P ^ 2 * (D * A₁ - D2)).coeff n ∈ ambF F := fun n =>
    coeff_mul_mem_ambF F (coeff_pow_two_mem_ambF F hPambF)
      (fun m => by
        rw [Polynomial.coeff_sub]
        exact (ambF F).sub_mem (coeff_mul_mem_ambF F hDm hA₁m m) (hD2m m)) n
  have hYambF : ∀ n, (D * M + 2 * D2 * P).coeff n ∈ ambF F := fun n => by
    rw [Polynomial.coeff_add]
    refine (ambF F).add_mem (coeff_mul_mem_ambF F hDm hMambF n) ?_
    exact coeff_mul_mem_ambF F
      (coeff_mul_mem_ambF F (fun m => natCast_poly_coeff_mem_ambF F 2 m) hD2m) hPambF n
  have h3 : P ^ 2 * (D * A₁ - D2) + (D * M + 2 * D2 * P) * Polynomial.X ^ Nat.card F
      = (D * M + 2 * D2 * P) * Polynomial.C ((ambTheta F) ^ Nat.card F) := by
    have h := h2
    rw [hLs, mul_sub] at h
    linear_combination h
  have h4 : D * M + 2 * D2 * P = 0 := by
    have hr := congrArg (fun p : Polynomial (Ambient F) => tp F p (Nat.card F)) h3
    rw [tp_add F (fun n => ambF_subset_ambA_zero (F := F) (hxambF n))
        (fun n => coeff_mul_mem_ambA (fun m => ambF_subset_ambA_zero (F := F) (hYambF m)) hXq n)
        (Nat.card F),
      tp_zero_of_coeff_mem_ambF F hxambF hqne,
      tp_mul_const F hYambF hXq (Nat.card F), tp_X_pow_card_eq_zero F hq0, mul_zero, zero_add,
      tp_mul_C_theta_pow_card F hYambF hq0] at hr
    exact hr.symm
  have h5 : P ^ 2 * (D * A₁ - D2) = 0 := by
    have h := h3
    rw [h4, zero_mul, add_zero] at h
    exact h
  have h6 : D * A₁ - D2 = 0 := (mul_eq_zero.mp h5).resolve_left (pow_ne_zero 2 hP0)
  have hD2eq : D * A₁ = D2 := by linear_combination h6
  have hDM : D * M = -(2 * D2 * P) := by linear_combination h4
  have hexp : D * A₂ = D * (A₁ * P * Polynomial.C ((w - Nat.card F : ℕ) : Ambient F)) - D * M := by
    rw [hMs]; ring
  have hexp2 : D * (A₁ * P * Polynomial.C ((w - Nat.card F : ℕ) : Ambient F))
      = D2 * P * Polynomial.C ((w - Nat.card F : ℕ) : Ambient F) := by
    rw [← hD2eq]; ring
  have hfin : D * A₂ = 0 := by
    have hwq2 : w - Nat.card F + 2 = Nat.card F := by omega
    have hcast : ((w - Nat.card F : ℕ) : Ambient F) + 2 = ((w - Nat.card F + 2 : ℕ) : Ambient F) := by
      push_cast; ring
    have hCq : (Polynomial.C ((w - Nat.card F : ℕ) : Ambient F) : Polynomial (Ambient F)) + 2 = 0 := by
      rw [show (2 : Polynomial (Ambient F)) = Polynomial.C (2 : Ambient F) from rfl,
        ← Polynomial.C_add, hcast, hwq2, natCast_card_eq_zero_ambient, Polynomial.C_0]
    rw [hexp, hexp2, hDM]
    have : D2 * P * Polynomial.C ((w - Nat.card F : ℕ) : Ambient F) - -(2 * D2 * P)
        = D2 * P * (Polynomial.C ((w - Nat.card F : ℕ) : Ambient F) + 2) := by ring
    rw [this, hCq, mul_zero]
  exact hA₂ne ((mul_eq_zero.mp hfin).resolve_left hD0)

end ZagierHoffmanPositiveChar
