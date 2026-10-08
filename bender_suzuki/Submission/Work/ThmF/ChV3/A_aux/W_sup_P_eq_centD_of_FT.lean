import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV3.step1
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_quot_cyclic
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.ThmF.ChV12.lemma3a
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.structureIdentity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.A_aux.W_sup_P_eq_centD_of_FT`

Peterfalvi II Ch. V §3, step (1), last clause: `V = W · P`.

In the standing context `CtxF H Q t s r P` (split rank-one data `H = Q ⋊ D`, `t ∉ H` an
involution, structure identity `t s t = r⁻¹ t r`, and `(F1)`: `P ≤ V = centD H t` of prime order
with `C_G(P)` of 2-rank `1`), and with `FeitThompsonProp` available,

  `W H t ⊔ P = centD H t`,

i.e. `V = C_V(K) · P`, where `K = Kset H t = J(D,t)`.

## Proof

`FeitThompsonProp` is exactly the missing ingredient of the sibling file
`Work/ThmF/ChV3/A_reduction.lean`: it supplies Ch. V §1 **Proposition 2**
(`ChV12.Ksub_cyclic_normal`): `K̄ = ⟨K⟩ = K` is a *cyclic normal* subgroup of `D`.  With Prop. 2 in
hand, Ch. V §1 **Proposition 3** (`ChV12.prop3`) gives the field structure:

* a finite field `F` with `|F| = |Q₀sub H|` and a group isomorphism `Q₀ = ⟨Inv H⟩ ≅ (F, +)`,
* a homomorphism `ρ : V →* (F ≃+* F)` (the action of `V` on `Q₀` by field automorphisms) whose
  **kernel is `W`**.

The two counting facts then determine `V/W` completely.

* `P ∩ W = 1` (`ChV3.step1.W_inf_eq_bot_of_prime`), so `|ρ(P)| = |P|`
  (`ChV12.card_map_subgroupOf_eq`).
* `|C_{Q₀}(P)| = 2` (`ChV3.step1.Q0sub_inf_centralizer_card`), so Artin's theorem for the fixed
  field of `ρ(P) ≤ Aut F` (`ChV12.prop3_card_fixed_pow`) gives `|Q₀| = 2^{|P|}`.
* The automorphism group of a finite field of order `2^n` has order `n`
  (`ChV12.natCard_ringEquiv_finiteField`), hence `|F ≃+* F| = |P|`.

Therefore the image `ρ(P) ≤ F ≃+* F` has the cardinality of the whole automorphism group, so
`ρ(P) = F ≃+* F`; in particular `ρ : V → F ≃+* F` is onto `ρ(P)`, and for every `v ∈ V` there is
`p ∈ P` with `ρ p = ρ v`, i.e. `p⁻¹ v ∈ ker ρ = W`.  Hence `V ≤ P · W`, and `P · W ≤ V` is
immediate.  ∎
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ThmF.ChV3.A_aux

theorem W_sup_P_eq_centD_of_FT (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp) {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) : Work.ThmF.W H t ⊔ P = Submission.Blueprint.centD H t := by
  classical
  have hS : Submission.Blueprint.Situation G := c.sit
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := c.split
  -- Ch. V §1 Prop. 2: `K = J(D,t)` is a cyclic normal subgroup of `D`
  obtain ⟨hKcyc, hKsub, hKn⟩ := Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hS hsplit
  -- Ch. V §1 Prop. 1 (c): the involutions of `H` commute; `K` acts regularly on `Inv H`
  have hcomm := Work.ThmF.L5.involutions_commute hS hC4 hsplit
  have hreg := Work.ThmF.L5.Kset_regular hsplit
  -- Ch. II §4 Prop. 2 (a): `V = C_D(u)` for some involution `u ∈ H`
  obtain ⟨u, hu, huV⟩ :=
    (hC4 G hS H hsplit.stronglyEmbedded t hsplit.invol hsplit.not_mem).2.1
  -- Ch. V §1 Prop. 3: the field structure of `Q₀` and the action `ρ` of `V` with kernel `W`
  obtain ⟨F, hFld, hFint, e, κ, ρ, hcardF, hactK, hactV, hker⟩ :=
    Work.ThmF.ChV12.prop3 H Q t hsplit hcomm hKsub hKcyc hKn hreg u hu huV
  letI : Field F := hFld
  letI : Fintype F := hFint
  -- `P ∩ W = 1` (step (1), first clause)
  have hPW : P ⊓ Work.ThmF.W H t = ⊥ := by
    rw [inf_comm]
    exact Work.ThmF.ChV3.W_inf_eq_bot_of_prime hS hC4 hsplit c.P_prime c.F1
  -- `|C_{Q₀}(P)| = 2` (step (1))
  have hQ0inf : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) = 2 :=
    Work.ThmF.ChV3.Q0sub_inf_centralizer_card hS hC4 hsplit c.P_le c.F1
  -- the Prop. 3 structure, in the shape consumed by `prop3_card_fixed_pow`
  have hstr : ∃ (F' : Type) (_ : Field F') (_ : Fintype F')
      (e' : ↥(Work.ThmF.Q0sub H) ≃* Multiplicative F')
      (ρ' : ↥(Submission.Blueprint.centD H t) →* (F' ≃+* F')),
      ρ'.ker = (Work.ThmF.W H t).subgroupOf (Submission.Blueprint.centD H t) ∧
        ∀ (v : ↥(Submission.Blueprint.centD H t)) (x : ↥(Work.ThmF.Q0sub H))
          (hx : (v : G) * x * (v : G)⁻¹ ∈ Work.ThmF.Q0sub H),
          Multiplicative.toAdd (e' ⟨(v : G) * x * (v : G)⁻¹, hx⟩)
            = ρ' v (Multiplicative.toAdd (e' x)) :=
    ⟨F, hFld, hFint, e, ρ, hker, hactV⟩
  -- Artin: `|C_{Q₀}(P)| ^ |P| = |Q₀|`, so `|Q₀| = 2 ^ |P|`
  have hQ0pow : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ Nat.card P := by
    have h1 := Work.ThmF.ChV12.prop3_card_fixed_pow H Q t c.P_le hPW c.P_prime hstr
    rw [hQ0inf] at h1
    exact h1.symm
  have hcardF2 : Nat.card F = 2 ^ Nat.card P := hcardF.trans hQ0pow
  -- the characteristic of `F` is `2` (it divides `|F| = 2 ^ |P|`)
  obtain ⟨pp, hcharp⟩ := CharP.exists F
  haveI : CharP F pp := hcharp
  obtain ⟨k, hkprime, hkcard⟩ := FiniteField.card F pp
  have hpk : pp ^ (k : ℕ) = 2 ^ Nat.card P := by
    rw [← hkcard, Fintype.card_eq_nat_card, hcardF2]
  have hp_dvd : pp ∣ 2 := by
    have h1 : pp ∣ pp ^ (k : ℕ) := dvd_pow_self pp k.pos.ne'
    rw [hpk] at h1
    exact Nat.Prime.dvd_of_dvd_pow hkprime h1
  have hp2 : pp = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hp_dvd with h | h
    · exact absurd h hkprime.ne_one
    · exact h
  haveI : CharP F 2 := hp2 ▸ hcharp
  -- the automorphism group of `F` has order `|P|`
  have hcardAut : Nat.card (F ≃+* F) = Nat.card P :=
    Work.ThmF.ChV12.natCard_ringEquiv_finiteField (Nat.card P) hcardF2
  haveI : Finite (F ≃+* F) := Finite.of_injective (fun f : F ≃+* F => (f : F → F))
    (fun f g h => RingEquiv.ext (congrFun h))
  -- `ρ(P)` is injective, hence `|ρ(P)| = |P| = |Aut F|`, hence `ρ(P) = Aut F`
  have hAcard : Nat.card ↥(Subgroup.map ρ (P.subgroupOf (Submission.Blueprint.centD H t)))
      = Nat.card ↥P :=
    Work.ThmF.ChV12.card_map_subgroupOf_eq H t P c.P_le hPW ρ hker
  have hAtop : Subgroup.map ρ (P.subgroupOf (Submission.Blueprint.centD H t)) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (hAcard.trans hcardAut.symm)
  refine le_antisymm ?_ ?_
  · -- `W · P ≤ V`
    exact sup_le (Work.ThmF.W_le_centD H t) c.P_le
  · -- `V ≤ W · P`
    intro x hx
    have hmem : ρ ⟨x, hx⟩ ∈ Subgroup.map ρ (P.subgroupOf (Submission.Blueprint.centD H t)) := by
      rw [hAtop]; exact Subgroup.mem_top _
    obtain ⟨p, hp, hρp⟩ := Subgroup.mem_map.mp hmem
    have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    -- `p⁻¹ x ∈ ker ρ = W`
    have hwmem : ((p⁻¹ * ⟨x, hx⟩ : ↥(Submission.Blueprint.centD H t)) : G) ∈ Work.ThmF.W H t := by
      have h1 : (p⁻¹ * ⟨x, hx⟩ : ↥(Submission.Blueprint.centD H t)) ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hρp, inv_mul_cancel]
      rwa [hker, Subgroup.mem_subgroupOf] at h1
    have hxeq : x = (p : G) * (((p⁻¹ * ⟨x, hx⟩ : ↥(Submission.Blueprint.centD H t)) : G)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hxeq, sup_comm]
    exact Subgroup.mul_mem_sup hpP hwmem

end Work.ThmF.ChV3.A_aux
