import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes.UEPR

theorem map_maximalIdeal_eq_of_ramificationIdx_eq_one {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] (h : q.ramificationIdx A = 1) : Ideal.map (algebraMap A (Localization.AtPrime q)) p = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  -- `q.ramificationIdx A` is the length of `Sq ⧸ p·Sq` where `Sq = Localization.AtPrime q`
  -- (Mathlib's definition), with `p = q.under A`.
  rw [Ideal.ramificationIdx_eq p q] at h
  -- Length one means the quotient is a simple module, i.e. the ideal is maximal; in a
  -- local ring the only maximal ideal is the maximal ideal.
  rw [ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def] at h
  exact (IsLocalRing.isMaximal_iff _).mp h

end Work.MotV5.Nodes.UEPR
