import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.step1
import Submission.Work.ThmF.ChV12.lemma2a_cent_split
import Submission.Work.PGroup.card_sup_mul_card_inf
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
import Submission.Work.ThmF.ChV3.Prove.Sig_sup_P_le_normalizer_CQ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.CH_card_chainfree`

Step (1) of Peterfalvi II, Ch. V §3 in its **chain-free** form:

  `|C_H(P)| = |C_Q(P)| · |C_W(P)| · |P|`,

where `C_H(P) = H ⊓ C_G(P)`, `C_Q(P) = Q ⊓ C_G(P)` and `Σ = C_W(P) = W H t ⊓ C_G(P)`.

Unlike `Prove/S1_CH_card` this needs no `Chain15` data, and unlike the route through
`Prove/S1_centralizerP_eq` it needs no `R`, no `m` and no near-field input.  The whole content is

* `ChV12.lemma2a_cent_split`: for `X ≤ D = H ⊓ H^t`, `H ⊓ C_G(X) = (Q ⊓ C_G(X)) ⊔ (D ⊓ C_G(X))`
  -- valid because `Q ⊴ H`, `Q ⊓ D = ⊥`, `Q ⊔ D = H` in a split rank-one datum -- applied to
  `X = P ≤ V = C_D(t)`;
* step (1) of the source in the form in which `Prove.step1` states it: `D ⊓ C_G(P) = Σ ⊔ P`
  and `W ⊓ P = ⊥`;

after which the counting is pure algebra.  `Σ ⊔ P ≤ D` is disjoint from `C_Q(P) ≤ Q` (because
`Q ⊓ D = ⊥`) and `Σ ⊓ P ≤ W ⊓ P = ⊥`, so `Work.PGroup.card_sup_mul_card_inf_of_le_normalizer`
applied to `(C_Q(P), Σ ⊔ P)` -- the normaliser containment is the delegated lemma
`Sig_sup_P_le_normalizer_CQ` -- and the elementwise-commuting form
`Work.PGroup.card_sup_mul_card_inf` applied to `(Σ, P)` give the product formula.

`hFT` and `hC4` enter through `Prove.step1` (which uses `FeitThompsonProp` for `V = W · P` and
`ChIIFourProp` for `W = C_D(Inv H)`); nothing else from the §3 chain is used.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

theorem CH_card_chainfree {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Nat.card ↥(H ⊓ Work.ThmF.ChV3.CG P) =
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) * Nat.card ↥(Work.ThmF.ChV3.Sig H t P) * Nat.card P := by
  classical
  -- step (1) of §3, chain-free: `W ⊓ P = ⊥` and `D ⊓ C_G(P) = Σ ⊔ P`
  obtain ⟨hWbot, _hVsup, _hQ0, _hNC, hCD⟩ := Work.ThmF.Prove.step1 hFT hC4 c
  have hPleD : P ≤ Submission.Blueprint.twoPoint H t :=
    c.P_le.trans (Work.ThmF.centD_le_twoPoint t)
  -- `C_H(P) = C_Q(P) ⊔ (Σ ⊔ P)`, the centralizer split `H ⊓ C_G(P) = C_Q(P) ⊔ C_D(P)`
  have hsplit : H ⊓ Work.ThmF.ChV3.CG P =
      Work.ThmF.ChV3.CQ Q P ⊔ (Work.ThmF.ChV3.Sig H t P ⊔ P) := by
    have h := Work.ThmF.ChV12.lemma2a_cent_split (H := H) (Q := Q)
      (D := Submission.Blueprint.twoPoint H t) (X := P)
      c.split.normal c.split.inf_eq c.split.sup_eq hPleD
    rw [hCD] at h
    exact h
  -- `Σ ⊔ P ≤ D`
  have hSigP_le_D : Work.ThmF.ChV3.Sig H t P ⊔ P ≤ Submission.Blueprint.twoPoint H t :=
    sup_le (((inf_le_left : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t).trans
      (Work.ThmF.W_le_centD H t)).trans (Work.ThmF.centD_le_twoPoint t)) hPleD
  -- `C_Q(P) ⊓ (Σ ⊔ P) = ⊥`, since the second factor lies in `D = twoPoint H t` and `Q ⊓ D = ⊥`
  have hCQ_bot : Work.ThmF.ChV3.CQ Q P ⊓ (Work.ThmF.ChV3.Sig H t P ⊔ P) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc Work.ThmF.ChV3.CQ Q P ⊓ (Work.ThmF.ChV3.Sig H t P ⊔ P)
        ≤ Q ⊓ Submission.Blueprint.twoPoint H t :=
          le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hSigP_le_D)
      _ = ⊥ := c.split.inf_eq
  -- `Σ ⊓ P = ⊥`, since `Σ ≤ W` and `W ⊓ P = ⊥`
  have hSigP_bot : Work.ThmF.ChV3.Sig H t P ⊓ P = ⊥ := by
    refine le_bot_iff.mp ?_
    calc Work.ThmF.ChV3.Sig H t P ⊓ P
        ≤ Work.ThmF.W H t ⊓ P :=
          le_inf (inf_le_left.trans inf_le_left) inf_le_right
      _ = ⊥ := hWbot
  -- the two product formulas
  have hcard1 : Nat.card ↥(Work.ThmF.ChV3.CQ Q P ⊔ (Work.ThmF.ChV3.Sig H t P ⊔ P)) =
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) *
        Nat.card ↥(Work.ThmF.ChV3.Sig H t P ⊔ P) := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
      (H := Work.ThmF.ChV3.CQ Q P) (K := Work.ThmF.ChV3.Sig H t P ⊔ P)
      (Sig_sup_P_le_normalizer_CQ c)
    rw [hCQ_bot, Subgroup.card_bot, mul_one] at h
    exact h
  have hcard2 : Nat.card ↥(Work.ThmF.ChV3.Sig H t P ⊔ P) =
      Nat.card ↥(Work.ThmF.ChV3.Sig H t P) * Nat.card P := by
    have h := Work.PGroup.card_sup_mul_card_inf (Work.ThmF.ChV3.Sig H t P) P
      (fun σ hσ p hp =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hσ).2 p hp).symm)
    rw [hSigP_bot, Subgroup.card_bot, mul_one] at h
    exact h
  rw [hsplit, hcard1, hcard2]
  ring

end Work.ThmF.ChV3.Prove
