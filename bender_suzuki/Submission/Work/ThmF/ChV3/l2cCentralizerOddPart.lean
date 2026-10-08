import Mathlib
import Submission.Work.ThmF.ChV12.fpf_oddPart
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.l2cCentralizerOddPart` — Peterfalvi II, Ch. V §2 Lemma 2 (c), at `X ≤ V`

For `X ≤ V = C_D(t)` of `D = H ⊓ H^t`, non-trivial, normalised by a non-trivial element of
`K = J(D,t)`, and with `C_G(X)` of 2-rank `≥ 2`, the odd part `Q₁ = O_{2'}(Q)` centralises no
non-trivial element of `X`:

  `O_{2'}(Q) ⊓ C_G(X) = ⊥`.

This is the `S`-clause of Ch. II §4 Prop. 3 (`ChIIFourProp`) fed into
`Work.ThmF.ChV12.oddPart_inf_centralizer_eq_bot`: Prop. 3 produces a 2-subgroup `S ≤ H` with
`S ⊔ (D ⊓ N_G(X)) = H ⊓ N_G(X)`, `S ⊓ D = ⊥`, normalised by `H ⊓ N_G(X)`; the counting argument
of `oddPart_inf_centralizer_eq_bot` then forces `Q₁ ⊓ C_G(X) = ⊥`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3

theorem l2cCentralizerOddPart {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {X : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hS : Submission.Blueprint.Situation G) (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hnil : Group.IsNilpotent ↥Q)
    (hXV : X ≤ Submission.Blueprint.centD H t) (hXne : X ≠ ⊥)
    (hK : ∃ k ∈ Work.ThmF.Kset H t, k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G))
    (hfour : Submission.Blueprint.HasFourGroup ↥(Subgroup.centralizer (X : Set G))) :
    Work.ThmF.oddPart Q ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  -- Ch. II §4 Prop. 3 (the P3 clause of `ChIIFourProp`) applied to `X` and the element `k ∈ K#`
  have hP3 := (hC4 G hS H hsplit.stronglyEmbedded t hsplit.invol hsplit.not_mem).2.2.2.1
  obtain ⟨S, hSp, hSFH, _hIdx, hSnorm, hSD, hSsup⟩ := (hP3 X hXne hXV hK).2.1
  -- `S` lies in `F = O^{2'}(C_G(X))`, hence centralises `X`, hence normalises `X`
  have hSC : S ≤ Subgroup.centralizer (X : Set G) := by
    intro s hs
    have hmem : s ∈ (oddResidual (Subgroup.centralizer (X : Set G))).map
        (Subgroup.centralizer (X : Set G)).subtype := (Subgroup.mem_inf.mp (hSFH hs)).1
    obtain ⟨c, _hc, hcs⟩ := Subgroup.mem_map.mp hmem
    rw [← hcs]
    exact c.2
  have hSH : S ≤ H := fun s hs => (Subgroup.mem_inf.mp (hSFH hs)).2
  have hSN : S ≤ Subgroup.normalizer (X : Set G) :=
    hSC.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  -- finally, the `S`-data clause of the counting lemma
  exact Work.ThmF.ChV12.oddPart_inf_centralizer_eq_bot hsplit.le hsplit.normal hsplit.inf_eq hnil
    ⟨S, hSp, hSN, hSH, hSD, hSsup, hSnorm⟩

end Work.ThmF.ChV3
