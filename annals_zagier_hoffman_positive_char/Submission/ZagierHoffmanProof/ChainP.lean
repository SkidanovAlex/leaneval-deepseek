import Submission.ZagierHoffmanProof.NestP
import Submission.ZagierHoffmanProof.BridgeP

/-!
# The `ζ_A`-value as a chain sum of the power sums `P_d`

Generalisation of `ATBridge2.ambInfHom_zeta_A_eq_chain` (which used the purity `P_d(n) = ℓ_d^{-n}`
for `n ≤ q`) to arbitrary entries `𝔰` with `q ∤` entries (in particular `1 ≤ s ≤ 2q-2`):

  `ambInfHom (ζ_A 𝔰) = ∑'_u (if StrictAnti u then ∏_j ambInfHom (P_{u_j}(𝔰_j)) else 0)`.

This is the `ζ_A`-side of the bridge (4.2) for the Anderson–Thakur datum.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open Polynomial Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The nested power sum `nestLvlP` as an iterated `tsum` with the factor family
`fun j i => ambInfHom F (P F i (𝔰 j))`. -/
lemma nestLvlP_eq_nestT (r : ℕ) : ∀ (𝔰 : Fin r → ℕ+) (d : ℕ),
    nestLvlP F r 𝔰 d = nestT r (fun j i => ambInfHom F (P F i (𝔰 j))) d := by
  induction r with
  | zero => intro 𝔰 d; simp
  | succ r ih =>
    intro 𝔰 d
    rw [nestLvlP_succ, nestT_succ, sum_range_eq_tsum_ite]
    refine tsum_congr fun i => ?_
    have hcong : (fun j i => ambInfHom F (P F i (ftail r 𝔰 j)))
        = (fun j i => ambInfHom F (P F i (𝔰 j.succ))) := by
      funext j i
      rw [ftail_apply]
    have hthis : nestLvlP F r (ftail r 𝔰) i
        = nestT r (fun j i => ambInfHom F (P F i (𝔰 j.succ))) i := by
      rw [ih (ftail r 𝔰) i, hcong]
    show (if i < d then ambInfHom F (P F i (𝔰 0)) * nestLvlP F r (ftail r 𝔰) i else 0)
      = (if i < d then ambInfHom F (P F i (𝔰 0)) else 0)
        * nestT r (fun j i => ambInfHom F (P F i (𝔰 j.succ))) i
    rw [hthis]
    by_cases h : i < d
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]

/-- ★★★ **The `ζ_A`-value as a chain sum of the power sums `P_d`** (arbitrary entries
`1 ≤ s ≤ 2q-2`). -/
theorem ambInfHom_zeta_A_eq_chainP (r : ℕ) (𝔰 : Fin (r + 1) → ℕ+)
    (h𝔰 : ∀ j, (𝔰 j : ℕ) ≤ 2 * Nat.card F - 2) :
    ambInfHom F (ζ_A F 𝔰)
      = ∑' u : Fin (r + 1) → ℕ,
          (if StrictAnti u then ∏ j, ambInfHom F (P F (u j) (𝔰 j)) else 0) := by
  have harch : ∀ a : ℚᵐ⁰, a < 1 → ∀ ε : ℚᵐ⁰, ε ≠ 0 → ∃ m : ℕ, a ^ m < ε :=
    gammaArchimedean_rat
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hCpos : (0 : ℚᵐ⁰) < WithZero.exp ((Nat.card F : ℚ) * (2 * Nat.card F - 2 : ℕ)) :=
    WithZero.exp_pos
  set C : ℚᵐ⁰ := WithZero.exp ((Nat.card F : ℚ) * (2 * Nat.card F - 2 : ℕ)) with hC
  have hZ : ∀ (j : Fin (r + 1)) (i : ℕ),
      Valued.v (ambInfHom F (P F i (𝔰 j))) ≤ C * (ambRho F) ^ i := by
    intro j i
    refine le_trans (v_ambInfHom_P_le F (𝔰 j) (h𝔰 j) i) ?_
    rw [hC, ambRho, ← WithZero.exp_nsmul, nsmul_eq_mul,
      show (↑i * -↑(Nat.card F) : ℚ) = -↑(Nat.card F) * ↑i by ring]
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt WithZero.exp_pos)
    refine WithZero.exp_le_exp.mpr ?_
    have h1 : ((𝔰 j : ℕ) : ℚ) ≤ ((2 * Nat.card F - 2 : ℕ) : ℚ) := by
      exact_mod_cast h𝔰 j
    have h2 : (0 : ℚ) < Nat.card F := by
      have : (1 : ℚ) ≤ Nat.card F := by exact_mod_cast (le_trans (by norm_num) hq2)
      linarith
    nlinarith [h1, h2]
  rcases r with _ | r'
  · rw [ambInfHom_zeta_A_eq_nestLvlP F 0 𝔰]
    simp only [nestLvlP_zero, mul_one]
    rw [← Equiv.tsum_eq (Equiv.funUnique (Fin 1) ℕ).symm
      (fun u : Fin 1 → ℕ => if StrictAnti u then ∏ j, ambInfHom F (P F (u j) (𝔰 j)) else 0)]
    refine tsum_congr fun d => ?_
    rw [Fin.prod_univ_one, if_pos (strictAnti_fin_one _)]
    simp
  · rw [ambInfHom_zeta_A_eq_nestLvlP F (r' + 1) 𝔰]
    have hstep : (∑' d : ℕ, ambInfHom F (P F d (𝔰 0))
          * nestLvlP F (r' + 1) (ftail (r' + 1) 𝔰) d)
        = ∑' d : ℕ, ambInfHom F (P F d (𝔰 0))
          * nestT (r' + 1) (fun j : Fin (r' + 1) => fun i => ambInfHom F (P F i (𝔰 j.succ))) d := by
      refine tsum_congr fun d => ?_
      have hfam : (fun j i => ambInfHom F (P F i (ftail (r' + 1) 𝔰 j)))
          = (fun j i => ambInfHom F (P F i (𝔰 j.succ))) := by
        funext j i
        rw [ftail_apply]
      rw [nestLvlP_eq_nestT F (r' + 1) (ftail (r' + 1) 𝔰) d, hfam]
    rw [hstep]
    have hY : ∀ (j : Fin (r' + 1)) (i : ℕ),
        Valued.v (ambInfHom F (P F i (𝔰 j.succ))) ≤ C * (ambRho F) ^ i := fun j i => hZ j.succ i
    have hstep2 : (∑' d : ℕ, ambInfHom F (P F d (𝔰 0))
          * nestT (r' + 1) (fun j : Fin (r' + 1) => fun i => ambInfHom F (P F i (𝔰 j.succ))) d)
        = ∑' d : ℕ, ambInfHom F (P F d (𝔰 0))
          * (∑' v : Fin (r' + 1) → ℕ,
              (if StrictAnti v ∧ ∀ j, v j < d
                then ∏ j, ambInfHom F (P F (v j) (𝔰 j.succ)) else 0)) := by
      refine tsum_congr fun d => ?_
      rw [nestT_succ_eq_tsum
        (Y := fun j : Fin (r' + 1) => fun i => ambInfHom F (P F i (𝔰 j.succ)))
        d (ambRho_pos F) (ambRho_lt_one F) (ne_of_gt WithZero.exp_pos) harch hY]
    rw [hstep2]
    exact tsum_cons_chain (fun j : Fin (r' + 1 + 1) => fun i => ambInfHom F (P F i (𝔰 j)))
      (ambRho_pos F) (ambRho_lt_one F) (ne_of_gt WithZero.exp_pos) harch (fun j i => hZ j i)

end ZagierHoffmanPositiveChar
