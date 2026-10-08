import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV3.step1
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.ThmF.ChV12.L5Base

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Ch. V §3, step (1): `|Q₀| = 2^{|P|}`

Peterfalvi II Ch. V §1 Prop. 3 identifies `Q₀ = ⟨Inv H⟩ = Q0sub H` with the additive group of a
finite field `F`, and `V = centD H t` with a group of *field* automorphisms of `F`, the kernel of
that action being `W = C_V(K)`.

With `FeitThompsonProp` the kernel `K = J(D,t)` is cyclic (`ChV12.Ksub_cyclic_normal`), which is
exactly the hypothesis of Prop. 3, so `ρ : V →* (F ≃+* F)` with `ker ρ = W` is available.  Two
counting facts then give the result:

* `P ∩ W = 1` (`ChV3.W_inf_eq_bot_of_prime`), so `P` acts faithfully, i.e. `ρ` is injective on
  `P`;
* `|C_{Q₀}(P)| = 2` (`ChV3.Q0sub_inf_centralizer_card`), while by Artin's theorem for the fixed
  field of a finite group of automorphisms of a finite field (`ChV12.prop3_card_fixed_pow`),
  `|C_{Q₀}(P)|^{|P|} = |Q₀|`.

Hence `|Q₀sub H| = 2^{|P|}`.  (This is the second conjunct of `Prove/step1.lean`.)
-/

namespace Work.ThmF.Prove

theorem Q0sub_card_eq_two_pow {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ Nat.card P := by
  classical
  have hS : Submission.Blueprint.Situation G := c.sit
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := c.split
  -- Ch. V §1 Prop. 2 (`FeitThompsonProp`): `K = J(D,t)` is cyclic and normal in `D`
  obtain ⟨hKcyc, hKsub, hKn⟩ := Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hS hsplit
  have hcomm := Work.ThmF.L5.involutions_commute hS hC4 hsplit
  have hreg := Work.ThmF.L5.Kset_regular hsplit
  -- Ch. II §4 Prop. 2 (a): `V = C_D(u)` for some involution `u ∈ H`
  obtain ⟨u, hu, huV⟩ :=
    (hC4 G hS H hsplit.stronglyEmbedded t hsplit.invol hsplit.not_mem).2.1
  -- Ch. V §1 Prop. 3: the field structure on `Q₀` and the action `ρ` of `V` with kernel `W`
  obtain ⟨F, hFld, hFint, e, κ, ρ, hcardF, hactK, hactV, hker⟩ :=
    Work.ThmF.ChV12.prop3 H Q t hsplit hcomm hKsub hKcyc hKn hreg u hu huV
  letI : Field F := hFld
  letI : Fintype F := hFint
  -- step (1), first clause: `P ∩ W = 1`
  have hPW : P ⊓ Work.ThmF.W H t = ⊥ := by
    rw [inf_comm]
    exact Work.ThmF.ChV3.W_inf_eq_bot_of_prime hS hC4 hsplit c.P_prime c.F1
  -- step (1): `|C_{Q₀}(P)| = 2`
  have hQ0inf : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) = 2 :=
    Work.ThmF.ChV3.Q0sub_inf_centralizer_card hS hC4 hsplit c.P_le c.F1
  -- the Prop. 3 data, in the shape consumed by `prop3_card_fixed_pow`
  have hstr : ∃ (F' : Type) (_ : Field F') (_ : Fintype F')
      (e' : ↥(Work.ThmF.Q0sub H) ≃* Multiplicative F')
      (ρ' : ↥(Submission.Blueprint.centD H t) →* (F' ≃+* F')),
      ρ'.ker = (Work.ThmF.W H t).subgroupOf (Submission.Blueprint.centD H t) ∧
        ∀ (v : ↥(Submission.Blueprint.centD H t)) (x : ↥(Work.ThmF.Q0sub H))
          (hx : (v : G) * x * (v : G)⁻¹ ∈ Work.ThmF.Q0sub H),
          Multiplicative.toAdd (e' ⟨(v : G) * x * (v : G)⁻¹, hx⟩)
            = ρ' v (Multiplicative.toAdd (e' x)) :=
    ⟨F, hFld, hFint, e, ρ, hker, hactV⟩
  -- Artin: `|C_{Q₀}(P)|^{|P|} = |Q₀|`, hence `|Q₀| = 2^{|P|}`
  have h1 := Work.ThmF.ChV12.prop3_card_fixed_pow H Q t c.P_le hPW c.P_prime hstr
  rw [hQ0inf] at h1
  exact h1.symm

end Work.ThmF.Prove
