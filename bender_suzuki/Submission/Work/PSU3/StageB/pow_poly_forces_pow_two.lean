import Mathlib
import Submission.Work.PSU3.StageB.pow_eq_forces_pow_two
import Submission.Work.PSU3.StageB.natDegree_X_add_C_pow_sub_X_pow_sub_C_lt

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

open Polynomial

theorem pow_poly_forces_pow_two {F : Type} [Field F] [CharP F 2]
    {c α : F} (hc : c ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (S : Finset F) (hcard : m ≤ S.card)
    (h : ∀ A ∈ S, (c + A) ^ m = α + A ^ m) :
    ∃ s : ℕ, m = 2 ^ s ∧ α = c ^ m := by
  classical
  -- The polynomial `p = (X + c)^m - X^m - α` vanishes on `S`, which has at least `m` elements,
  -- but has degree `< m`; hence it is the zero polynomial.
  let p : F[X] := (Polynomial.X + Polynomial.C c) ^ m - Polynomial.X ^ m - Polynomial.C α
  have heval : ∀ A ∈ S, Polynomial.eval A p = 0 := by
    intro A hA
    have hA' := h A hA
    dsimp only [p]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
    rw [add_comm A c, hA']
    ring
  have hdeg : p.natDegree < S.card := by
    have hex := natDegree_X_add_C_pow_sub_X_pow_sub_C_lt (R := F) c α hm
    have h2 : p.natDegree < m := by dsimp only [p]; exact hex
    omega
  have hp0 : p = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p S heval hdeg
  have hp0' : (Polynomial.X + Polynomial.C c : F[X]) ^ m - Polynomial.X ^ m - Polynomial.C α = 0 := hp0
  -- The constant coefficient is `c ^ m`, so `α = c ^ m`.
  have hα : α = c ^ m := by
    have h1 := congrArg (Polynomial.eval (0 : F)) hp0
    dsimp only [p] at h1
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_zero, zero_add] at h1
    rw [zero_pow (by omega : m ≠ 0), sub_zero] at h1
    exact (sub_eq_zero.mp h1).symm
  -- Reduce to `(X + c)^m = X^m + c^m`, which forces `m` to be a power of two in characteristic 2.
  have hp' : (Polynomial.X + Polynomial.C c : F[X]) ^ m = Polynomial.X ^ m + Polynomial.C (c ^ m) := by
    have h1 := hp0'
    rw [hα] at h1
    rw [← sub_eq_zero]
    rw [show (Polynomial.X + Polynomial.C c : F[X]) ^ m - (Polynomial.X ^ m + Polynomial.C (c ^ m))
        = (Polynomial.X + Polynomial.C c : F[X]) ^ m - Polynomial.X ^ m - Polynomial.C (c ^ m) by ring]
    exact h1
  obtain ⟨s, hs⟩ := pow_eq_forces_pow_two c hc hm hp'
  exact ⟨s, hs, hα⟩

end Work.PSU3.StageB
