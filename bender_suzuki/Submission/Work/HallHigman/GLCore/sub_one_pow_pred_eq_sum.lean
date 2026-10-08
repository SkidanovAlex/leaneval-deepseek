import Mathlib
import Submission.Work.HallHigman.GLCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- In the domain `(ZMod p)[X]`, `(X - 1) ^ (p - 1) = Σ_{i < p} X ^ i`: multiply both
sides by the nonzerodivisor `X - 1` and use that `(X - 1) ^ p = X ^ p - 1` in characteristic `p`. -/
private lemma X_sub_one_pow_pred_eq_sum (p : ℕ) [Fact p.Prime] :
    (Polynomial.X - Polynomial.C 1 : Polynomial (ZMod p)) ^ (p - 1)
      = ∑ i ∈ Finset.range p, (Polynomial.X : Polynomial (ZMod p)) ^ i := by
  have hp : p.Prime := Fact.out
  have hf : (Polynomial.X - Polynomial.C 1 : Polynomial (ZMod p)) ≠ 0 :=
    (Polynomial.monic_X_sub_C 1).ne_zero
  have h1 : (Polynomial.X - Polynomial.C 1 : Polynomial (ZMod p)) ^ p
      = Polynomial.X ^ p - 1 := by
    rw [sub_pow_char]
    simp
  have h2 : (Polynomial.X - Polynomial.C 1 : Polynomial (ZMod p))
      * ((Polynomial.X - Polynomial.C 1 : Polynomial (ZMod p)) ^ (p - 1))
      = Polynomial.X ^ p - 1 := by
    rw [← pow_succ' (Polynomial.X - Polynomial.C 1 : Polynomial (ZMod p)) (p - 1),
      Nat.sub_add_cancel hp.one_le, h1]
  have h3 : (Polynomial.X - Polynomial.C 1 : Polynomial (ZMod p))
      * (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial (ZMod p)) ^ i)
      = Polynomial.X ^ p - 1 := by
    simpa using mul_geom_sum (Polynomial.X : Polynomial (ZMod p)) p
  exact mul_left_cancel₀ hf (h2.trans h3.symm)

set_option linter.style.haveILetI false in
/-- **L0 of the GL-core design**: in a ring of characteristic `p`, `(T - 1) ^ (p - 1) = Σ_{i < p} T ^ i`;
this is the identity `(X - 1) ^ (p - 1) = Σ X^i` used throughout the GL-core proof of Hall--Higman B
(`NOTES_LEAD_ft_hallhigman.md` (N)). -/
lemma sub_one_pow_pred_eq_sum {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p] (T : R) :
    (T - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, T ^ i := by
  haveI : Algebra (ZMod p) R := ZMod.algebra R p
  have h := congrArg (Polynomial.aeval (R := ZMod p) (A := R) T) (X_sub_one_pow_pred_eq_sum p)
  simpa using h

end Work.HallHigman.GLCore
