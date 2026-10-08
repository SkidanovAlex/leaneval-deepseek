import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

theorem hpf_of_dvd_sig {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h9 : Work.ThmF.oddPart Q ≠ ⊥ → ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P))
    (h6n : Work.ThmF.oddPart Q = ⊥ → ¬ IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) →
      Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 1 ∨
        Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 3)
    (h6a : Work.ThmF.oddPart Q = ⊥ → IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) →
      Work.ThmF.ChV3.Sig H t P = ⊥)
    (hsig : Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P)) :
    Nat.card P = orderOf (s * t) := by
  -- `O_{2'}(Q) = 1`, else `h9` contradicts `hsig`.
  have hQ1 : Work.ThmF.oddPart Q = ⊥ := by
    by_contra h
    exact h9 h hsig
  by_cases hcomm : IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P)
  · -- `C_Q(P)` abelian: `h6a` gives `Σ = 1`, whence `|P| = 1`, contradicting primality.
    have hbot := h6a hQ1 hcomm
    rw [hbot] at hsig
    simp at hsig
    exact absurd (by rw [hsig]; simp : Nat.card ↥P = 1) c.P_prime.ne_one
  · -- `C_Q(P)` non-abelian: `|Σ| ∈ {1,3}`, and `1` is excluded, so `|Σ| = 3`.
    have hc8 : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 := (h15.h5 hcomm).1
    have hs : Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 3 := by
      rcases h6n hQ1 hcomm with h | h
      · rw [h] at hsig
        simp at hsig
        exact absurd (by rw [hsig]; simp : Nat.card ↥P = 1) c.P_prime.ne_one
      · exact h
    -- `|P| ∣ 3` and `|P|` prime, so `|P| = 3`.
    have hp3 : Nat.card P = 3 := by
      rw [hs] at hsig
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hsig with h | h
      · exact absurd h c.P_prime.ne_one
      · exact h
    -- `orderOf (s * t)^m = 9`, so `orderOf (s * t) ∣ 9 = 3^2`, and primality gives `3`.
    have h9eq : orderOf (s * t) ^ h15.m = 9 := by
      rw [← h15.hcq, hc8]
    have hdvd9 : orderOf (s * t) ∣ 9 := by
      have h := dvd_pow_self (orderOf (s * t)) (Nat.one_le_iff_ne_zero.mp h15.hm)
      rw [h9eq] at h
      exact h
    have hf3 : orderOf (s * t) = 3 := by
      have h32 : orderOf (s * t) ∣ 3 ^ 2 := by
        rw [show (3:ℕ)^2 = 9 from by norm_num]
        exact hdvd9
      have h3 : orderOf (s * t) ∣ 3 := h15.hf.dvd_of_dvd_pow h32
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h | h
      · exact absurd h h15.hf.ne_one
      · exact h
    rw [hp3, hf3]

end Work.ThmF.ChV3.Prove
