import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.ChV3.Prove.A_LV_aux
import Submission.Work.ThmF.ChV3.Prove.card_sup_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.hD_of_chain15` — `|D| = (2^p − 1)·|W|·p` (Ch. V §3, step (1)+(10))

`D = twoPoint H t = H ∩ H^t`, `V = centD H t = C_D(t)`, `K = J(D,t) = Kset H t`,
`W = C_V(K)`, and `P ≤ V` has prime order `p = |P|` (the standing context `CtxF` plus the chain
through step (5)).  The claim is the cardinality formula used by step (10):

`|D| = (2^|P| − 1) · |W| · |P|`.

The three ingredients are all already in the tree:

* `|D| = |V| · |K|` — Peterfalvi I App. I (1)(b) at `d = 2`
  (`Work.ThmF.card_centD_mul_card_Kset`);
* `|K| = |Inv H| = |Q₀| − 1 = 2^|P| − 1` — Ch. I §2 (`Bender.cardKsetEqInv`) together with
  `|Q₀| = 2^|P|` (step (1), `Chain15.hQ0`) and the commutativity of `Inv H`
  (`L5.involutions_commute` + `L5.card_Q0sub_eq`);
* `|V| = |W| · |P|` — step (1) gives `V = W ⊔ P`, `W ⊓ P = ⊥`, and `P` normalises `W`
  (`P_le_normalizer_W`), so the multiplication map `W × P → V` is a bijection
  (`card_sup_of_le_normalizer`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.ThmF.ChV3.Prove

theorem hD_of_chain15 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) (hpf : Nat.card P = orderOf (s * t)) :
    Nat.card ↥(Submission.Blueprint.twoPoint H t) =
      (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) * Nat.card P := by
  classical
  -- Ch. V §1 Prop. 1 (c): the involutions of `H` commute pairwise.
  have hcomm : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G), a * b = b * a :=
    Work.ThmF.L5.involutions_commute c.sit hC4 c.split
  -- `|Inv H| = |Q₀| - 1 = 2 ^ |P| - 1`.
  have hInv : (involutions (H : Set G)).ncard = 2 ^ Nat.card P - 1 := by
    have h := Work.ThmF.L5.card_Q0sub_eq (H := H) hcomm
    rw [h15.hQ0] at h
    have hpos : 1 ≤ 2 ^ Nat.card P := Nat.one_le_two_pow
    omega
  -- Ch. I §2: `|K| = |Inv H|`.
  have hKinv : (Work.ThmF.Kset H t).ncard = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv c.split.stronglyEmbedded c.split.invol c.split.not_mem
  -- Peterfalvi I App. I (1)(b): `|D| = |V| · |K|`.
  have hDcard : Nat.card ↥(Submission.Blueprint.twoPoint H t) =
      Nat.card ↥(Submission.Blueprint.centD H t) * (Work.ThmF.Kset H t).ncard :=
    (Work.ThmF.card_centD_mul_card_Kset (H := H) (Q := Q) (t := t)
      (Work.ThmF.IsSplitRankOne.toData c.split)).symm
  -- Step (1): `V = W ⊔ P`, `W ⊓ P = ⊥`, `P` normalises `W`, so `|V| = |W| · |P|`.
  have hVcard : Nat.card ↥(Submission.Blueprint.centD H t) =
      Nat.card ↥(Work.ThmF.W H t) * Nat.card P := by
    have h := Work.ThmF.ChV3.Prove.card_sup_of_le_normalizer
      (A := Work.ThmF.W H t) (B := P)
      (Work.ThmF.ChV3.Prove.P_le_normalizer_W (H := H) (t := t) c) h15.hWP
    rwa [h15.hV] at h
  rw [hDcard, hKinv, hInv, hVcard]
  ring

end Work.ThmF.ChV3.Prove
