import Mathlib
import Submission.Work.NormalComplement._design.Vocab
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- **Peterfalvi I Ch. III §4 Lemma 1 (d)** (p.179), in the design vocabulary: with
`Setup45A G H t W p P A`, `P` is a Sylow `p`-subgroup of `D = twoPoint H t` and
`E = W ⊓ D = E' ⋊ P` (`E' = ⁅E,E⁆`).

Route (the paper): suppose `P` is not a `p`-Sylow of `D`.  By (c), a `p`-Sylow of `D` is not cyclic
(it is `P × (C_A(P))_p`); `Section2Prop` with `W = H` (whose hypotheses hold: `H ≤ N(H)`,
`H ⊔ D = H`, `p ∣ |H ⊓ D| = |D|`, `D ≠ 1`) then gives `D` `p`-control in `H`, the second alternative
being impossible since it demands a cyclic Sylow.  `TransferProp` with `hpE = Setup45.dvd` and a
`p`-element `y ∈ E ∖ E'` (`Work.NormalComplement.exists_ppow_notMem_of_dvd_index`) gives
`P ⊄ O^p(H)`, hence `P ⊄ O^p(W)`, and `StrategyProp` (with `E = W ⊓ D = W ⊓ twoPoint H t`)
contradicts the minimality of `W` (`Setup45A.minW`).  For the second part, (c) gives `E = M ⋊ P` for
the preimage `M` of `E'` in `E`; if `E' ≠ M`, some prime `q ≠ p` divides `|E:E'|`, (D1) gives
`1 ≠ Q ≤ E ⊓ V` a `q`-subgroup fixed-point-free on `K`, but `Q ≤ A ≤ V` and `Q ≠ 1` centralises
`C_K(A) ≠ 1` (`Setup45A.A_CK`), contradicting App. I (1)(b). -/
theorem sec4_one_d (hTrans : Work.NormalComplement.TransferProp)
    (hStrat : Work.NormalComplement.StrategyProp)
    (hS2 : Work.NormalComplement.Section2Prop)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G} (h : Work.NormalComplement.Design.Setup45A G H t W p P A) :
    Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t) ∧
      Work.NormalComplement.Design.Ecomm H t W ⊓ P = ⊥ ∧
      Work.NormalComplement.Design.Ecomm H t W ⊔ P = Work.NormalComplement.Design.Egrp H t W := by sorry

end Work.NormalComplement
