/-
  WilG4c / `CritFixAux.critIdxFixCard` — cardinality bookkeeping for the *corrected* criterion
  index set `critIdxFix` (`CritFixDefs`), the analogue of `Work.WilkG4c.CritIdxCardLe` for the
  frozen `critIdx`.

  `critIdxFix n k = Σ_{m < k} (Fin (n+1) → Fin (m+2))`, so

    `#(critIdxFix n k) = Σ_{m<k} (m+2)^{n+1} ≤ (k+2)^{n+2}`,

  the bound being the evaluation at `k` of the fixed polynomial `(X+2)^{n+2}` (with `n` fixed).
  Consequently, `Ω`-intersections over `critIdxFix n k` of sets with a uniform degree bound
  `M` have degree at most `(k+2)^{n+2} · M` — i.e. `M * eval ![D,k] ((X₁+2)^{n+2})`-shaped,
  which is what the `MvPolynomial (Fin 2) ℕ` bookkeeping of `UVFix`-definability needs.

  Also included: monotonicity of `b.eval ![D,k]` in the two slots `D`, `k` (all coefficients of
  `b` are natural), used to replace the per-index bound `eval ![D,m+1] b` by `eval ![D,k] b`
  when `m < k`.
-/
import Mathlib
import Submission.Work.WilG4c.CritFixDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c.CritFixAux

/-- The cardinality of the corrected index set: each order `m < k` contributes `(m+2)^{n+1}`
counts vectors. -/
theorem card_critIdxFix (n k : ℕ) :
    (Work.WilkG4c.critIdxFix n k).card = ∑ m : Fin k, (m.val + 2) ^ (n + 1) := by
  rw [Work.WilkG4c.critIdxFix, Finset.card_sigma]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  simp

/-- **Cardinality bound.**  `#(critIdxFix n k) ≤ (k+2)^{n+2}`, a polynomial bound in `k` whose
coefficients do not depend on `k`. -/
theorem card_critIdxFix_le (n k : ℕ) :
    (Work.WilkG4c.critIdxFix n k).card ≤ (k + 2) ^ (n + 2) := by
  rw [card_critIdxFix]
  have hterm : ∀ m : Fin k, (m.val + 2) ^ (n + 1) ≤ (k + 2) ^ (n + 1) :=
    fun m => Nat.pow_le_pow_left (by have := m.isLt; omega) _
  calc ∑ m : Fin k, (m.val + 2) ^ (n + 1)
      ≤ ∑ _m : Fin k, (k + 2) ^ (n + 1) := Finset.sum_le_sum fun m _ => hterm m
    _ = k * (k + 2) ^ (n + 1) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ (k + 2) * (k + 2) ^ (n + 1) := Nat.mul_le_mul_right _ (by omega)
    _ = (k + 2) ^ (n + 2) := by ring

/-- The bound multiplied by an arbitrary degree `M`: the number of terms times the uniform
degree bound is bounded by the evaluation of `(X₁+2)^{n+2}` at `k` times `M`. -/
theorem card_critIdxFix_mul_le (n k M : ℕ) :
    (Work.WilkG4c.critIdxFix n k).card * M ≤ (k + 2) ^ (n + 2) * M :=
  Nat.mul_le_mul_right M (card_critIdxFix_le n k)

/-- **Monotonicity of the evaluation of a two-variable natural polynomial.**  If all coefficients
of `b` are natural numbers then `D ↦ k ↦ b.eval ![D,k]` is monotone in both slots. -/
theorem eval_pair_mono (b : MvPolynomial (Fin 2) ℕ) {D D' k k' : ℕ} (hD : D ≤ D')
    (hk : k ≤ k') : MvPolynomial.eval ![D, k] b ≤ MvPolynomial.eval ![D', k'] b := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq']
  refine Finset.sum_le_sum fun d _ => Nat.mul_le_mul_left _ ?_
  exact Finset.prod_le_prod fun i _ =>
    Nat.pow_le_pow_left (by fin_cases i <;> simp [hD, hk]) _

/-- Specialised form used in the `UVFix` bookkeeping: the per-index bound at order `m < k` may be
replaced by the bound at `k`. -/
theorem eval_pair_mono_right (b : MvPolynomial (Fin 2) ℕ) {D k k' : ℕ} (hk : k ≤ k') :
    MvPolynomial.eval ![D, k] b ≤ MvPolynomial.eval ![D, k'] b :=
  eval_pair_mono b le_rfl hk

end Work.WilkG4c.CritFixAux
