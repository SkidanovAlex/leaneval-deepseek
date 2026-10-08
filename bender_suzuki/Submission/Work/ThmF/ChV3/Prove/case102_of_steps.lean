import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV12.lemma6
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV3.Prove.isSuzukiTwoGroup_of_isPGroup_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.case102_of_steps` — Ch. V §3, case (10-2)

Peterfalvi II Ch. V §3, case (10-2) of step (10) (p. 252): under the standing context, the chain
(1)–(5), step (7) (`Ker H Q P t = P`), the outputs of step (9) (`h9`), step (6) (`h6a`, `h6n`)
and the divisibility `|P| ∣ |Σ|` (`hsig`), one is in the case

* `|P| = 3`, `|Σ| = 3`, `|C_Q(P)| = 8` (steps (6), (10));
* `|W| ∈ {3, 9}` and `W` **cyclic** — this is Ch. V §2 Lemma 6
  (`Work.ThmF.ChV12.lemma6`): `W = C_V(K)` is cyclic with `|W| ∣ |Q₀sub H| + 1`, and
  `|Q₀sub H| = 2 ^ |P| = 8` (`h15.hQ0`), while `Σ ≤ W` forces `3 ∣ |W|`.  Lemma 6 needs `Q`
  to be a Suzuki 2-group; in case (10-2) `|Q| = |C_Q(P)| ^ |P| = 8³ = 2⁹`, so `Q` is a 2-group
  (`h15.h4`), and `C_Q(P)` is non-abelian, so `Q` is non-abelian: Ch. V §1, Corollary of
  Proposition 2 (`Work.ThmF.ChV3.Prove.isSuzukiTwoGroup_of_isPGroup_two`) applies.
* `st = s * t` has order `3` (`hpf : |P| = orderOf (s * t)`).

The first four conjuncts are the `Case102` data of `Work.ThmF.ChV3.Case102` other than its
arithmetic field `G3`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

theorem case102_of_steps {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    (h9 : Work.ThmF.oddPart Q ≠ ⊥ → ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P))
    (h6a : Work.ThmF.oddPart Q = ⊥ → IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) →
      Work.ThmF.ChV3.Sig H t P = ⊥)
    (h6n : Work.ThmF.oddPart Q = ⊥ → ¬ IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) →
      Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 1 ∨
        Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 3)
    (hsig : Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P)) :
    Nat.card P = 3 ∧ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 3 ∧
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 ∧
      (Nat.card ↥(Work.ThmF.W H t) = 3 ∨ Nat.card ↥(Work.ThmF.W H t) = 9) ∧
      orderOf (s * t) = 3 ∧ IsCyclic ↥(Work.ThmF.W H t) := by
  -- ## step (9)'s dichotomy: `O_{2'}(Q) = 1`, otherwise `h9` contradicts `hsig`
  have hQ1 : Work.ThmF.oddPart Q = ⊥ := by
    by_contra h
    exact h9 h hsig
  -- ## step (6): `C_Q(P)` cannot be abelian (`h6a` gives `Σ = 1`, so `|P| = 1`)
  have hcomm_ne : ¬ IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) := by
    intro hcomm
    have hbot := h6a hQ1 hcomm
    rw [hbot] at hsig
    rw [Subgroup.card_bot] at hsig
    exact c.P_prime.ne_one (Nat.dvd_one.mp hsig)
  -- ## step (6): `|Σ| ∈ {1, 3}`, and `1` is excluded by `hsig`
  have hSig3 : Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 3 := by
    rcases h6n hQ1 hcomm_ne with h1 | h3
    · rw [h1] at hsig
      exact absurd (Nat.dvd_one.mp hsig) c.P_prime.ne_one
    · exact h3
  -- ## step (10): `|P| ∣ 3` and `|P|` is prime, so `|P| = 3`
  have hP3 : Nat.card P = 3 := by
    rw [hSig3] at hsig
    rcases (Nat.dvd_prime Nat.prime_three).mp hsig with h | h
    · exact absurd h c.P_prime.ne_one
    · exact h
  -- ## step (5): `C_Q(P)` is not abelian, hence `|C_Q(P)| = 8`
  have hCQ8 : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 := (h15.h5 hcomm_ne).1
  -- ## `st` has order `3` (= `|P|`, `hpf`)
  have hf3 : orderOf (s * t) = 3 := by rw [← hpf, hP3]
  -- ## `Q` is a `2`-group: `|Q| = |C_Q(P)| ^ |P| = 8 ^ 3 = 2 ^ 9` (step (4))
  have hQcard : Nat.card ↥Q = 2 ^ 9 := by rw [h15.h4, hP3, hCQ8]; norm_num
  have hSp : IsPGroup 2 ↥Q := IsPGroup.of_card hQcard
  -- ## `Q` is non-abelian because its subgroup `C_Q(P)` is
  have hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q := by
    intro habel
    exact hcomm_ne (by
      rw [isMulCommutative_iff]
      intro a b
      exact Subtype.ext (habel (a : G) (a.2.1) (b : G) (b.2.1)))
  -- ## `|Q₀sub H| = 2 ^ |P| = 8` (step (1)) and `|Q| = |Q₀sub H|³`
  have hQ0card : Nat.card ↥(Work.ThmF.Q0sub H) = 8 := by rw [h15.hQ0, hP3]; norm_num
  have hQcard3 : Nat.card ↥Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3 := by
    rw [hQcard, hQ0card]; norm_num
  -- ## Ch. V §1, Corollary of Prop. 2: `Q` is a Suzuki 2-group
  have hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    isSuzukiTwoGroup_of_isPGroup_two hFT hC4 c.sit c.split hSp hnab
  -- ## Ch. V §2, Lemma 6: `W` is cyclic and `|W| ∣ |Q₀sub H| + 1 = 9`
  have h5 : Work.ThmF.Lemma5.Hyp5 H Q t s := ⟨c.sit, c.split, c.s_mem, c.s_inv, hf3⟩
  obtain ⟨hWcyc, hWdvd0⟩ := Work.ThmF.ChV12.lemma6 hC4 hHig h5 hSuz hQcard3
  have hWdvd : Nat.card ↥(Work.ThmF.W H t) ∣ 9 := by
    rw [hQ0card] at hWdvd0
    norm_num at hWdvd0
    exact hWdvd0
  -- ## `Σ ≤ W` with `|Σ| = 3` forces `3 ∣ |W|`
  have h3dvd : 3 ∣ Nat.card ↥(Work.ThmF.W H t) := by
    rw [← hSig3]
    exact Subgroup.card_dvd_of_le (show Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t from inf_le_left)
  -- ## `3 ∣ |W| ∣ 9` gives `|W| ∈ {3, 9}`
  have hW39 : Nat.card ↥(Work.ThmF.W H t) = 3 ∨ Nat.card ↥(Work.ThmF.W H t) = 9 := by
    have hpow : Nat.card ↥(Work.ThmF.W H t) ∣ 3 ^ 2 := by
      rw [show (3:ℕ)^2 = 9 from by norm_num]; exact hWdvd
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hpow
    have hge : 3 ≤ Nat.card ↥(Work.ThmF.W H t) := Nat.le_of_dvd Nat.card_pos h3dvd
    interval_cases k
    · exfalso; rw [pow_zero] at hkeq; omega
    · left; exact hkeq
    · right; exact hkeq
  exact ⟨hP3, hSig3, hCQ8, hW39, hf3, hWcyc⟩

end Work.ThmF.ChV3.Prove
