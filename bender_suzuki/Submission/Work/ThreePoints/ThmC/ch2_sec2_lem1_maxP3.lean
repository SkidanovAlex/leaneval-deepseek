import Mathlib
import Submission.Work.ThreePoints.ThmC.Prop2h2t
import Submission.Work.ThreePoints.ThmC.ch1_sec6_cor1
import Submission.Work.ThreePoints.ThmC.maxP3_proof

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

/-- **Peterfalvi I Ch. II §2 Lemma 1 (a) (p. 164).**  `P` is maximal among the `p`-subgroups of
`G` fixing at least three points of `Ω = G ⧸ H`.

Proof sketch (the source's, p. 165).  `P ≤ D ⊓ D^u = H ⊓ H^g ⊓ H^{ug}` fixes the three distinct
points `1, g, ug`.  Let `Q ≥ P` be maximal among the `p`-subgroups of `H` with `≥ 3` fixed points;
by App. II (6) (`Work.ThreePoints.app2_6_uniform`) `Q` is maximal among the `p`-subgroups of `G`
with `≥ 3` fixed points and `N_G(Q)` acts `2`-transitively on `Ω_Q`.  By Ch. I §4 Prop. 2
(`Work.ThreePoints.ThmC.even_card_normalizer_h2t`, in module
`Submission.Work.ThreePoints.ThmC.Prop2h2t`) `|N_H(Q)|` is even, so there is an involution
`v ∈ N_G(Q) ⊓ H`.  Pick `H₂ = conj h₂ H ∈ Ω_Q`, `H₂ ≠ H`; then `Q` is a `p`-Sylow of
`E = H ⊓ H₂ ⊓ H₂^v`, and Ch. I §6 Cor. 1 (`Work.ThreePoints.ThmC.ch1_sec6_cor1`) applied to the
triples `(H, H^g, u)` and `(H, H₂, v)` exhibits `x` with `conj x (D ⊓ D^u) = E`.  Hence `conj x P`
and `Q` are `p`-Sylows of `E`, so `P` is conjugate to `Q`, and `P` is maximal among the
`p`-subgroups of `G` with `≥ 3` fixed points.

Note `conj u (twoPoint H g) = H ⊓ conj (u*g) H`, so `D ⊓ D^u = H ⊓ conj g H ⊓ conj (u*g) H`; the
uniqueness of the fixed point of the involution `u`
(`Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two`) shows that the three conjugates
`H`, `conj g H`, `conj (u*g) H` are pairwise distinct, whence `3 ≤ (fixedPts H P).ncard`. -/
theorem ch2_sec2_lem1_maxP3 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (h2t : Submission.Blueprint.IsTwoTransitiveOn H)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {g : G} (hg : g ∉ H) {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsSylowOf p P
      (Submission.Blueprint.twoPoint H g ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)))
    (huP : u ∈ Subgroup.normalizer (P : Set G)) :
    Work.ThreePoints.ThmC.IsMaxP3 H p P :=
  maxP3_proof hH h2t hBrSz hg hu hp hpodd hP huP

end Work.ThreePoints.ThmC
