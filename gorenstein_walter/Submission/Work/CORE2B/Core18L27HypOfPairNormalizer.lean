import Mathlib
import Submission.Work.CORE2B.L27Hyp_of_L28MHyp
import Submission.Work.CORE2B.C18L27HypOfPairNormalizer_proved

/-!
# GW design 18, item A′, leaf H3: Lemma 2.7's hypotheses for `M ⊇ N_S(⟨t,s⟩)`

Replaces `L27Hyp_of_L28MHyp` (which needs `S ≤ M`) in the per-prime step: Bender applies
Lemma 2.7 to `M ⊇ N_G(X) ⊇ N_S(⟨t,s⟩)`, *not* to an `M ⊇ S`.

Sketch (0.15–0.3k).  `V = ⟨t,s⟩` is a four-group (`t ∈ Z(S)`, `s ∉ S₀` an involution `≠ t`).
* `t ∈ M`: `t ∈ S` normalizes `V`.
* `sylow_nc`: `V ≤ M`; any `P ∈ Syl₂(M)` contains an `M`-conjugate of `V`, a four-group, and a
  cyclic group has a unique involution.
* `size`: if `|S| = 4` take the middle disjunct.  Otherwise `|S| ≥ 8` (S dihedral, not cyclic,
  contains `V`), `V < S`, and in the 2-group `S` normalizers grow (`normalizerCondition` of
  nilpotent groups), so `|N_S(V)| ≥ 8` and `N_S(V) = S ⊓ N(V) ≤ S ⊓ M`.
GAP: `gw18_A.g` (A2) — `|N_S(⟨t,s⟩)| = 8` for dihedral `S` of order 8..128.
-/


namespace Work.GW18

open Subgroup

theorem Core18L27HypOfPairNormalizer {G : Type} [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (s : G)
    (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (M : Subgroup G) (hMne : M ≠ ⊤)
    (hrel : Work.GW2.BRel B.Hhat M) (hnle : ¬ M ≤ B.Hhat) (htl : B.t ∉ Work.GW2.layerIn M)
    (hN : (B.S : Subgroup G) ⊓
      Subgroup.normalizer ((Subgroup.closure ({B.t, s} : Set G) : Subgroup G) : Set G) ≤ M) :
    Work.CORE2B.L27Hyp B M := Work.CORE2B.C18L27HypOfPairNormalizer_proved hCtx B s hs hs0 M hMne hrel hnle htl hN

end Work.GW18
