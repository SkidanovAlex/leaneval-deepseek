import Mathlib
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.Prove.S3.frobenius_element_action
import Submission.Work.ThmF.Prove.Q0sub_card_eq_two_pow
import Submission.Work.ThmF.ChV3.step3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.S3

/-- **Peterfalvi II, Ch. V §3 (Prop. 3 in the "strong" / structural form), from the standing
context `CtxF`.**

In the standing context of §3, the group `K = J(D,t) = Ksub H t` carries a finite field structure
of characteristic `2` on which it acts as `Fˣ`, and `V = centD H t` acts on `K` through ring
automorphisms `ρ v ∈ F ≃+* F`, compatibly with the conjugation action
`κ (v k v⁻¹) = ρ v (κ k)`.

The proof assembles the ingredients already available in the workspace:

* `hcomm` (`Work.ThmF.L5.involutions_commute`), `hreg` (`Work.ThmF.L5.Kset_regular`) — Ch. I/II;
* `hKcyc`, `hKsub`, `hKn` (`Work.ThmF.ChV12.Ksub_cyclic_normal`, using `FeitThompsonProp`) — Ch. V
  §1 Prop. 2;
* `hV` — Ch. II §4 Prop. 2 (a), the clause `(hC4 G …).2.1`;

then applies Ch. V §1 Prop. 3 (`Work.ThmF.ChV12.prop3`) to obtain the field `F`, the isomorphism
`κ : Ksub ≃* Fˣ` and the action `ρ : centD →* F ≃+* F`.  The characteristic is `2` because
`|F| = |Q₀sub H| = 2 ^ |P|` (`Work.ThmF.Prove.Q0sub_card_eq_two_pow`); the compatiblity is
`Work.ThmF.Prove.S3.ksub_conj_action_eq`. -/
theorem ctxF_prop3_hstr {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2)
      (κ : ↥(Work.ThmF.Ksub H t) ≃* Fˣ)
      (ρ : ↥(Submission.Blueprint.centD H t) →* (F ≃+* F)),
      ∀ (v : ↥(Submission.Blueprint.centD H t)) (k : ↥(Work.ThmF.Ksub H t))
        (hk : (v : G) * (k : G) * (v : G)⁻¹ ∈ Work.ThmF.Ksub H t),
        (κ ⟨(v : G) * (k : G) * (v : G)⁻¹, hk⟩ : F) = ρ v (κ k) := by
  classical
  have hS : Submission.Blueprint.Situation G := c.sit
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := c.split
  -- Ch. V §1 Prop. 2: `K = J(D,t)` is cyclic, equals `Kset H t`, and is normal in `D`
  obtain ⟨hKcyc, hKsub, hKn⟩ := Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hS hsplit
  -- Ch. II §4: the involutions of `H` commute, and `Kset H t` acts regularly on them
  have hcomm := Work.ThmF.L5.involutions_commute hS hC4 hsplit
  have hreg := Work.ThmF.L5.Kset_regular hsplit
  -- Ch. II §4 Prop. 2 (a): `V = C_D(u)` for an involution `u ∈ H`
  obtain ⟨u, hu, huV⟩ :=
    (hC4 G hS H hsplit.stronglyEmbedded t hsplit.invol hsplit.not_mem).2.1
  -- Ch. V §1 Prop. 3: the field, `κ` and the action `ρ` of `V`
  obtain ⟨F, hFld, hFint, e, κ, ρ, hcardF, hactK, hactV, _hker⟩ :=
    Work.ThmF.ChV12.prop3 H Q t hsplit hcomm hKsub hKcyc hKn hreg u hu huV
  letI : Field F := hFld
  letI : Fintype F := hFint
  -- `|Q₀sub H| = 2 ^ |P|`, so `F` has characteristic `2`
  have hQ0 : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ Nat.card P :=
    Work.ThmF.Prove.Q0sub_card_eq_two_pow hFT hC4 c
  have hFcard : Nat.card F = 2 ^ Nat.card P := by rw [hcardF, hQ0]
  haveI : CharP F 2 := Work.ThmF.Prove.S3.charP_two_of_card_eq_two_pow hFcard
  refine ⟨F, hFld, hFint, ?_, κ, ρ, ?_⟩
  · infer_instance
  · exact Work.ThmF.Prove.S3.ksub_conj_action_eq (H := H) (t := t) e κ ρ hactK hactV

end Work.S3
