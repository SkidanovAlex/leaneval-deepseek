import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV3.step9
import Submission.Work.ThmF.Prove.step9X
import Submission.Work.ThmF.Prove.step9N2
import Submission.Work.ThmF.Tools.burnsideCorollary
import Submission.Work.S3.P_card_ne_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Classical

/-- `|G|` even: `s` is an involution (`c.s_inv`), so `2 ∣ |G|`. -/
theorem even_card_G_of_ctx {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) : Even (Nat.card G) := by
  have hdvd : 2 ∣ Nat.card G := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers s)
    rw [Nat.card_zpowers, c.s_inv] at h
    exact h
  rwa [even_iff_two_dvd]

theorem hpf_of_not_dvd_sig {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (hG : Nat.card G = (Nat.card Q + 1) * Nat.card ↥H)
    (hH : Nat.card ↥H = Nat.card Q * Nat.card ↥(Submission.Blueprint.twoPoint H t))
    (hD : Nat.card ↥(Submission.Blueprint.twoPoint H t) =
      (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) * Nat.card P)
    (hQ : ¬ Nat.card P ∣ Nat.card Q)
    (hSigW : ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) →
      ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.W H t))
    (hsig : ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P)) :
    Nat.card P = orderOf (s * t) := by
  -- ## the two chain outputs that pin `p = f` to a divisibility
  have hF : (orderOf (s * t)).Prime ∧ ∃ m : ℕ, 1 ≤ m ∧
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m :=
    ⟨h15.hf, h15.m, h15.hm, h15.hcq⟩
  refine (Work.ThmF.ChV3.card_eq_orderOf_iff_dvd_omega hC4 c hF).mpr ?_
  -- ## suppose `p ∤ |G : H|` and derive `HasNormalIndexP p G` from Burnside
  by_contra hX
  have hp : (Nat.card P).Prime := c.P_prime
  have hp2 : Nat.card P ≠ 2 := Work.S3.P_card_ne_two c
  haveI : Fact (Nat.card P).Prime := ⟨hp⟩
  have hpW : ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.W H t) := hSigW hsig
  have hQ1 : ¬ Nat.card P ∣ Nat.card Q + 1 := by
    intro h
    exact hX (by rwa [Work.ThmF.ChV3.card_omega_eq c.split])
  -- ## the `p`-adic exponent of `|G|` is `1`
  have hfacG : (Nat.card G).factorization (Nat.card P) = 1 := by
    have hFermat : ¬ Nat.card P ∣ 2 ^ Nat.card P - 1 :=
      Work.ThmF.Prove.prime_not_dvd_two_pow_sub_one hp
    have h2p : 2 ^ Nat.card P - 1 ≠ 0 := by
      have h2 : 2 ≤ 2 ^ Nat.card P := by
        simpa using Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by norm_num) hp.one_lt.le
      omega
    have hK : ¬ Nat.card P ∣ (Nat.card Q + 1) *
        (Nat.card Q * ((2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t))) := by
      intro h
      rcases hp.dvd_mul.mp h with h' | h'
      · exact hQ1 h'
      · rcases hp.dvd_mul.mp h' with h'' | h''
        · exact hQ h''
        · rcases hp.dvd_mul.mp h'' with h''' | h'''
          · exact hFermat h'''
          · exact hpW h'''
    have hKnz : (Nat.card Q + 1) *
        (Nat.card Q * ((2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t))) ≠ 0 :=
      fun h => hK (h ▸ dvd_zero (Nat.card P))
    have hG' : Nat.card G =
        ((Nat.card Q + 1) * (Nat.card Q * ((2 ^ Nat.card P - 1) *
          Nat.card ↥(Work.ThmF.W H t)))) * Nat.card P := by
      rw [hG, hH, hD]
      ring
    rw [hG', Nat.factorization_mul hKnz hp.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hK, hp.factorization_self, zero_add]
  -- ## `P` is a Sylow `p`-subgroup of `G`
  have hsyl : Nat.card ↥P = (Nat.card P) ^ (Nat.card G).factorization (Nat.card P) := by
    rw [hfacG, pow_one]
  let S : Sylow (Nat.card P) G := Sylow.ofCard P hsyl
  have hScoe : (S : Subgroup G) = P := Sylow.coe_ofCard P hsyl
  have hpc : Nat.card P ∣ Nat.card G := Subgroup.card_subgroup_dvd_card P
  have hno : ¬ Work.ThmF.HasNormalIndexP (Nat.card P) G :=
    Work.ThmF.Prove.simple_not_hasNormalIndexP hp hp2 c.simple (even_card_G_of_ctx c)
  -- ## `N_G(P) = C_G(P)` makes the Sylow subgroup central in its normalizer, so Burnside
  --    provides a normal subgroup of index `p`, contradicting simplicity
  refine Work.ThmF.Tools.burnsideCorollary hpc hno S ?_
  have hSset : (S : Set G) = (P : Set G) := by
    rw [← Sylow.coe_coe S, hScoe]
  rw [hSset, h15.hNG]

end Work.ThmF.ChV3.Prove
