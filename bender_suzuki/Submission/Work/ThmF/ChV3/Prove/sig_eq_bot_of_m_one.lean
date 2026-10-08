import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

theorem sig_eq_bot_of_m_one {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (hpf : Nat.card P = orderOf (s * t))
    (h6 : Work.ThmF.oddPart Q = ⊥ → IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) →
      Work.ThmF.ChV3.Sig H t P = ⊥)
    (h8 : Work.ThmF.oddPart Q ≠ ⊥ → Work.ThmF.Prove.Step8Out H Q t P)
    (hm1 : h15.m = 1) : Work.ThmF.ChV3.Sig H t P = ⊥ := by
  -- `m = 1` turns step (2)'s link `|C_Q(P)| + 1 = f^m` into `|C_Q(P)| + 1 = |P|`.
  have hpc : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = Nat.card P := by
    have h := h15.hcq
    rw [hm1, pow_one, ← hpf] at h
    exact h
  -- `C_Q(P)` is abelian: otherwise step (5) gives `|C_Q(P)| = 8`, hence `|P| = 9`, not prime.
  have hcomm : IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) := by
    by_contra hn
    have h8c : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 := (h15.h5 hn).1
    have hp9 : Nat.card P = 9 := by omega
    exact absurd (hp9 ▸ c.P_prime) (by norm_num)
  by_cases hQ1 : Work.ThmF.oddPart Q = ⊥
  · -- `Q` is a 2-group: step (6) applies.
    exact h6 hQ1 hcomm
  · -- `Q₁ ≠ 1`: if `Σ ≠ 1`, step (8) makes `|P| = |C_Q(P)| + 1` a prime power with
    -- exponent `|Σ| ≥ 2`, which is not prime.
    by_contra hsig
    obtain ⟨hSigPrime, hcase⟩ := h8 hQ1 hsig
    have h2 : 2 ≤ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) := hSigPrime.two_le
    rcases hcase with h | h | h
    · exact (Nat.Prime.not_prime_pow h2) ((hpc.symm.trans h) ▸ c.P_prime)
    · exact (Nat.Prime.not_prime_pow h2) ((hpc.symm.trans h) ▸ c.P_prime)
    · exact (Nat.Prime.not_prime_pow h2) ((hpc.symm.trans h) ▸ c.P_prime)

end Work.ThmF.ChV3.Prove
