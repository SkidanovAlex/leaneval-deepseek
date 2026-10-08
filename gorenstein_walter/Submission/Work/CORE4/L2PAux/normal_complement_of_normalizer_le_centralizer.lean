import Mathlib

namespace Work.CORE4.L2PAux

theorem normal_complement_of_normalizer_le_centralizer {N : Type} [Group N] [Finite N]
    {p : ℕ} [Fact p.Prime] (P : Sylow p N)
    (h : Subgroup.normalizer ((P : Subgroup N) : Set N) ≤
      Subgroup.centralizer ((P : Subgroup N) : Set N)) :
    ∃ Q : Subgroup N, Q.Normal ∧ Q.IsComplement' (P : Subgroup N) ∧ ¬ p ∣ Nat.card Q := by
  -- This is Burnside's normal `p`-complement theorem. The hypothesis
  -- `N(P) ≤ C(P)` is exactly the hypothesis of `MonoidHom.transferSylow`, and
  -- `MonoidHom.ker_transferSylow_isComplement'` supplies the complement
  -- `(transferSylow P h).ker`, with `MonoidHom.not_dvd_card_ker_transferSylow`
  -- giving that its order is prime to `p`.
  refine ⟨(MonoidHom.transferSylow P h).ker, MonoidHom.normal_ker _, ?_, ?_⟩
  · exact MonoidHom.ker_transferSylow_isComplement' P h
  · exact MonoidHom.not_dvd_card_ker_transferSylow P h

end Work.CORE4.L2PAux
