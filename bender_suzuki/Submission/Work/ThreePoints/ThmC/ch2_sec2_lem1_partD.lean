import Mathlib
import Submission.Work.ThreePoints.ThmC.Prop2h2t
import Submission.Work.ThreePoints.ThmC.partD_proof

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

/-- **Peterfalvi I Ch. II §2 Lemma 1 (d) (p. 164).**  Given parts (a) and (b), if `P` is not a
`p`-Sylow of `P·C_G(P) ∩ D = P ⊔ (C_G(P) ⊓ D)` (where `D = twoPoint H g`) then `u` centralises
`P`.

Proof sketch (the source's).  Put `X = P ⊔ C_G(P)`.  The hypothesis says `P` is not a `p`-Sylow of
`X ⊓ D = P ⊔ (C_G(P) ⊓ D)` (Dedekind, `P ≤ D`), so a `p`-Sylow `Q` of `X ⊓ D` strictly contains
`P`; since `P ≤ Q ≤ D` and `P` is maximal among the `p`-subgroups of `G` with `≥ 3` fixed points
(part (a)), `Q` has exactly the two fixed points `H, conj g H`.  Using the `2`-transitivity of
`M = N_G(P)` on `Ω_P` (part (b)) and the fact that `M` normalises `X` (it normalises `P` and
`C_G(P)`), every two-element subset of `Ω_P` is the fixed set of a `p`-subgroup of `X`; Appendix
II (4) (`Work.DoubleTransitivity.App2.app2_4`) then makes `X` `2`-transitive on `Ω_P`.  Since
`|Ω_P| ≥ 3`, `|X| = |Ω_P|·(|Ω_P|-1)·|X_{ab}|`, so `|X|` is even; with `X = P·C_G(P)` and `|P|`
odd, `|C_G(P)|` is even, giving an involution `v ∈ C_G(P)`.  Finally, by part (b)
(`M ⊓ H` strongly embedded in `M`) all involutions of `M` are conjugate in `M`
(Ch. I §2 Prop. 1(b)), so `u = m v m⁻¹` for some `m ∈ M`; since `M = N_G(P)` and
`v ∈ C_G(P)`, also `u ∈ C_G(P)`, i.e. `u` centralises `P`. -/
theorem ch2_sec2_lem1_partD {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (h2t : Submission.Blueprint.IsTwoTransitiveOn H)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {g : G} (hg : g ∉ H) {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsSylowOf p P
      (Submission.Blueprint.twoPoint H g ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)))
    (huP : u ∈ Subgroup.normalizer (P : Set G))
    (hA : Work.ThreePoints.ThmC.IsMaxP3 H p P)
    (hB : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
        (Submission.Blueprint.fixedPts H P) ∧
      ∀ g₁ : G, P ≤ Submission.Blueprint.conj g₁ H →
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded
          ((Subgroup.normalizer (P : Set G) ⊓ Submission.Blueprint.conj g₁ H).subgroupOf
            (Subgroup.normalizer (P : Set G)))) :
    ¬ Work.ThreePoints.ThmC.IsSylowOf p P
        (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H g)) →
      ∀ x ∈ P, u * x = x * u :=
  partD_proof hH h2t hBrSz hg hu hp hpodd hP huP hA hB

end Work.ThreePoints.ThmC
