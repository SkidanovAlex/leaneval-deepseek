import Mathlib
import Submission.Work.Peluse.SwapC.Basic

/-!
# Support and sup-norm of the iterated `Δ'`-composite

The composite `Work.Peluse.SwapC.iterDeltaP k sh F` is the product, over the `2^k` sign patterns
`ω : Fin k → Bool`, of `F` at the points `x + ∑_j T_j (ω j)`, where `T_j true = (sh j).1` and
`T_j false = (sh j).2` (with a `star` on the factors, which is immaterial here).  Two elementary
consequences, both by induction on `k`:

* **support**: if `F` is supported in `[-N,N]` then `iterDeltaP k sh F x = 0` as soon as
  `|x + ∑_j (sh j).2| > N` — just look at the leaf of the pattern `ω ≡ false`, whose argument is
  `x + ∑_j (sh j).2`;
* **sup-norm**: if `‖F‖ ≤ 1` then `‖iterDeltaP k sh F‖ ≤ 1`, being a product of `2^k` factors of
  modulus `≤ 1`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-- **Support of the iterated `Δ'`-composite.**  If `F` vanishes off `[-N,N]`, then
`iterDeltaP k sh F` vanishes at every `x` with `N < |x + ∑ j, (sh j).2|`: the `ω ≡ false` leaf of
the expansion is `F (x + ∑ j, (sh j).2)`. -/
theorem iterDeltaP_supp_aux (N : ℕ) (F : ℤ → ℂ) (hF : SupportIn F N) :
    ∀ k (sh : Fin k → ℤ × ℤ) (x : ℤ),
      N < (x + ∑ j : Fin k, (sh j).2).natAbs → iterDeltaP k sh F x = 0 := by
  intro k
  induction k with
  | zero =>
    intro sh x hx
    rw [iterDeltaP_zero]
    exact hF x (by simpa using hx)
  | succ k ih =>
    intro sh x hx
    rw [iterDeltaP_succ]
    have hx' : N < ((x + (sh 0).2) + ∑ j : Fin k, (sh j.succ).2).natAbs := by
      rw [Fin.sum_univ_succ] at hx
      rwa [← add_assoc] at hx
    have h := ih (fun i : Fin k => sh i.succ) (x + (sh 0).2) hx'
    simp [h]

/-- **Sup-norm of the iterated `Δ'`-composite.**  If `‖F‖ ≤ 1` pointwise then
`‖iterDeltaP k sh F‖ ≤ 1` pointwise: each value of the composite is a product of `2^k` factors
of modulus `≤ 1`. -/
theorem iterDeltaP_norm_le_one (F : ℤ → ℂ) (hb : ∀ x : ℤ, ‖F x‖ ≤ 1) :
    ∀ k (sh : Fin k → ℤ × ℤ) (x : ℤ), ‖iterDeltaP k sh F x‖ ≤ 1 := by
  intro k
  induction k with
  | zero => intro sh x; rw [iterDeltaP_zero]; exact hb x
  | succ k ih =>
    intro sh x
    rw [iterDeltaP_succ, norm_mul, norm_star]
    calc ‖iterDeltaP k (fun i => sh i.succ) F (x + (sh 0).1)‖
          * ‖iterDeltaP k (fun i => sh i.succ) F (x + (sh 0).2)‖
        ≤ 1 * 1 := mul_le_mul (ih _ _) (ih _ _) (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

theorem iterDeltaPSupp {k : ℕ} (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ) {N : ℕ}
    (hF : Work.Peluse.SupportIn F N) (hb : ∀ x : ℤ, ‖F x‖ ≤ 1) :
    (∀ x : ℤ, (N : ℤ) < |x - (-(∑ j : Fin k, (sh j).2))| → Work.Peluse.SwapC.iterDeltaP k sh F x = 0)
      ∧ (∀ x : ℤ, ‖Work.Peluse.SwapC.iterDeltaP k sh F x‖ ≤ 1) := by
  constructor
  · intro x hx
    refine iterDeltaP_supp_aux N F hF k sh x ?_
    rw [Int.abs_eq_natAbs] at hx
    rw [sub_neg_eq_add] at hx
    exact_mod_cast hx
  · exact iterDeltaP_norm_le_one F hb k sh

end

end Work.Peluse.SwapC
