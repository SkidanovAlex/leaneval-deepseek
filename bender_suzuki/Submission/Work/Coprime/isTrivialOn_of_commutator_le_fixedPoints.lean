import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.commutator_commutator_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Coprime action with `[G, A] ≤ C_G(A)` is trivial

If a finite group `A` acts by automorphisms on a finite group `G` with
`(|A|, |G|) = 1` and every commutator `x⁻¹ * (a • x)` lies in the fixed-point
subgroup `C_G(A)`, then the action of `A` on `G` is trivial.

The proof is the classical power argument: for fixed `a : A` and `g : G`, put
`y = g⁻¹ * (a • g) ∈ C_G(A)`.  Since `a` fixes `y`, induction gives
`a ^ n • g = g * y ^ n`; evaluating at `n = orderOf a` gives `y ^ (orderOf a) = 1`,
so `orderOf y ∣ orderOf a ∣ |A|` while `orderOf y ∣ |G|`.  Coprimality forces
`orderOf y = 1`, i.e. `y = 1`, i.e. `a • g = g`.
-/

set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.Coprime

theorem isTrivialOn_of_commutator_le_fixedPoints (A : Type*) {G : Type*} [Group A] [Group G]
    [Finite A] [Finite G] [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (h : FT.commutator A (⊤ : Subgroup G) ≤ FT.fixedPoints A G) : FT.IsTrivialOn A G := by
  intro a g
  -- `y = g⁻¹ * (a • g)` is fixed by `A`.
  set y := g⁻¹ * (a • g) with hydef
  have hy : y ∈ FT.fixedPoints A G := by
    rw [hydef]; exact h (FT.le_commutator a (Subgroup.mem_top g))
  have hag : a • g = g * y := by
    rw [hydef]; exact (mul_inv_cancel_left g (a • g)).symm
  -- Iteration: `a ^ n • g = g * y ^ n`.
  have hiter : ∀ n : ℕ, a ^ n • g = g * y ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a ^ (n + 1) • g = a • (a ^ n • g) := by rw [pow_succ', mul_smul]
        _ = a • (g * y ^ n) := by rw [ih]
        _ = (a • g) * (a • y ^ n) := by rw [smul_mul']
        _ = (a • g) * (y ^ n) := by rw [smul_pow', hy a]
        _ = g * y ^ (n + 1) := by rw [hag, mul_assoc, pow_succ']
  have h1 : g = g * y ^ (orderOf a) := by
    have := hiter (orderOf a)
    rwa [pow_orderOf_eq_one, one_smul] at this
  have hyord : y ^ (orderOf a) = 1 := by
    have := congrArg (fun z => g⁻¹ * z) h1
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
    exact this.symm
  -- The order of `y` divides both `|A|` and `|G|`, hence is `1`.
  have hdvdA : orderOf y ∣ Nat.card A :=
    dvd_trans (orderOf_dvd_iff_pow_eq_one.mpr hyord) (orderOf_dvd_natCard a)
  have hdvdG : orderOf y ∣ Nat.card G := orderOf_dvd_natCard y
  have hy1 : orderOf y = 1 := by
    have hg : orderOf y ∣ (Nat.card A).gcd (Nat.card G) := Nat.dvd_gcd hdvdA hdvdG
    rw [hcop.gcd_eq_one] at hg
    exact Nat.dvd_one.mp hg
  have hyy : y = 1 := orderOf_eq_one_iff.mp hy1
  have hfin : g⁻¹ * (a • g) = 1 := by
    have := hyy
    rwa [hydef] at this
  rw [inv_mul_eq_one] at hfin
  exact hfin.symm

end Work.Coprime
