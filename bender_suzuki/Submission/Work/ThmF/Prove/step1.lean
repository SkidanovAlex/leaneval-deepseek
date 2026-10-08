import Mathlib
import Submission.Work.ThmF.ChV3.step1
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.lemma2a
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.ThmF.ChV3.A_reduction
import Submission.Work.ThmF.ChV3.A_aux.W_sup_P_eq_centD_of_FT
import Submission.Work.NormalComplement.sec4_c_normalizer_eq
import Submission.Work.ThmF.Prove.Q0sub_card_eq_two_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step1`

Peterfalvi II, Ch. V §3, step (1) — the statement as requested by the requester.

In the standing context `CtxF H Q t s r P` (G in situation (B0)–(B2), simple, split rank-one data
`H = Q ⋊ D` with `D = twoPoint H t`, `t` an involution outside `H`, the structure identity
`t s t = r⁻¹ t r`, and (F1): `P ≤ V = centD H t` of prime order with `C_G(P)` of 2-rank 1), and
with `FeitThompsonProp` (Appendix X) available:

* `W ∩ P = 1` — `ChV3.W_inf_eq_bot_of_prime`;
* `W ⊔ P = V` — `ChV3.A_aux.W_sup_P_eq_centD_of_FT` (Ch. V §1 Prop. 2 = `Ksub_cyclic_normal` +
  Prop. 3 + Artin);
* `|Q₀| = 2 ^ |P|` — `Prove.Q0sub_card_eq_two_pow` (Artin: `|Q₀| = |C_{Q₀}(P)|^|P| = 2^|P|`);
* `N_G(P) = C_G(P)` — Ch. V §2 Lemma 2 (a), (b) (`ChV12.lemma2a`, `ChV12.lemma2b`) together with
  `N_V(P) = C_W(P)·P` (the `A ⊓ N(P) = A ⊓ C(P)` argument, `NormalComplement.sec4_c_normalizer_eq`)
  and `P` commutative (`P` of prime order);
* `C_D(P) = C_W(P) · P` — the assembly `ChV3.eq_of_W_sup_P_eq_centD` applied to `W ⊔ P = V`.

The whole point of step (1) in the source is the coincidence `V = W · P` (`V/W ≅ Aut(F)` has order
`|P|`), which is what makes the fourth and fifth clauses accessible.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.Prove

theorem step1 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P) : Work.ThmF.W H t ⊓ P = ⊥ ∧ Work.ThmF.W H t ⊔ P = Submission.Blueprint.centD H t ∧ Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ Nat.card P ∧ Subgroup.normalizer (P : Set G) = Subgroup.centralizer (P : Set G) ∧ Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (P : Set G) = Work.ThmF.ChV3.Sig H t P ⊔ P := by
  classical
  -- **(1a)** `W ∩ P = 1`
  have hWbot : Work.ThmF.W H t ⊓ P = ⊥ :=
    Work.ThmF.ChV3.W_inf_eq_bot_of_prime c.sit hC4 c.split c.P_prime c.F1
  -- **(1b)** `V = W · P` (Ch. V §1 Prop. 2 + Prop. 3 + Artin)
  have hVsup : Work.ThmF.W H t ⊔ P = Submission.Blueprint.centD H t :=
    Work.ThmF.ChV3.A_aux.W_sup_P_eq_centD_of_FT hFT hC4 c
  -- **(1c)** `|Q₀| = 2 ^ |P|` (Artin, via the field structure of Ch. V §1 Prop. 3)
  have hQ0 : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ Nat.card P :=
    Work.ThmF.Prove.Q0sub_card_eq_two_pow hFT hC4 c
  -- `P` has prime order, hence is commutative and centralises itself
  have hPleC : P ≤ Subgroup.centralizer (P : Set G) := by
    haveI : Fact (Nat.card P).Prime := ⟨c.P_prime⟩
    haveI : IsCyclic ↥P := isCyclic_of_prime_card rfl
    haveI : IsMulCommutative ↥P := IsCyclic.isMulCommutative
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative ↥P) ⟨q, hq⟩ ⟨p, hp⟩)
  -- `V = centD H t` normalises `W = C_V(K)`: `W` does, and `V = W ⊔ P`
  have hNW : Submission.Blueprint.centD H t ≤
      Subgroup.normalizer (Work.ThmF.W H t : Set G) := by
    rw [← hVsup]
    exact sup_le Subgroup.le_normalizer (Work.ThmF.ChV3.le_normalizer_W hC4 c)
  -- `N_V(P) = C_W(P) · P` (`A ⊓ N(P) = A ⊓ C(P)` for `A = W`, `A ⊓ P = 1`)
  have hVN : Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (P : Set G) =
      (Work.ThmF.W H t ⊓ Subgroup.centralizer (P : Set G)) ⊔ P :=
    Work.NormalComplement.sec4_c_normalizer_eq (D := Submission.Blueprint.centD H t)
      (V := Submission.Blueprint.centD H t) (A := Work.ThmF.W H t) (P := P)
      le_rfl (Work.ThmF.W_le_centD H t) hNW hWbot hVsup c.P_le inf_le_left
  have hVPN : Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer (P : Set G) := by
    rw [hVN]
    exact sup_le inf_le_right hPleC
  -- Ch. V §2 Lemma 2 (a) and (b)
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P = 1 := by rw [hbot]; exact Subgroup.card_bot
    exact c.P_prime.ne_one h1
  have hfam := Work.ThmF.ChV12.lemma2a c.sit hC4 H Q t c.split P c.P_le hPne
  have h2b := Work.ThmF.ChV12.lemma2b c.sit hC4 H Q t c.split P c.P_le hPne hfam
  -- **(1d)** `N_G(P) = C_G(P)`
  have hNC : Subgroup.normalizer (P : Set G) = Subgroup.centralizer (P : Set G) := by
    refine le_antisymm ?_ (Subgroup.centralizer_le_normalizer (P : Set G))
    rw [h2b]
    exact sup_le le_rfl hVPN
  -- **(1e)** `C_D(P) = C_W(P) · P` (the assembly of `ChV3.A_reduction`)
  have hCD : Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (P : Set G) =
      Work.ThmF.ChV3.Sig H t P ⊔ P :=
    Work.ThmF.ChV3.eq_of_W_sup_P_eq_centD hC4 c hVsup
  exact ⟨hWbot, hVsup, hQ0, hNC, hCD⟩

end Work.ThmF.Prove
