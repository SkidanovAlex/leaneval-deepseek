import Mathlib
import Submission.Work.PSU3.StageA.lemma2cHig
import Submission.Work.PSU3.StageB.Wiring
import Submission.Work.PSU3.StageA.coarseFrame_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

/-
# Item 3, cycle-free placement: `|C_Q(P)| = ℓ³`

Same content as `Work.PSU3.StageB.card_centralizer_eq_cube`, but placed in a module that imports
only `Work.PSU3.StageA.lemma2cHig`, `Work.PSU3.StageA.coarseFrame_defs` (for the *proved* brick
`Work.PSU3.StageA.Q0sub_le_Q`, which the dispatch needs) and `Work.PSU3.StageB.Wiring`, so that
`Work.PSU3.StageB.centralizer_oddResidual_isPSU3_v2` can import it.  (The sibling file imports *that*
module — for the brick `Work.PSU3.StageB.inf_center_centralizerOddResidual_eq_bot`, now in
`Wiring` — which makes importing it back a build cycle.)

Dispatch of `lemma2cHig`'s trichotomy exactly as in the sibling file: `h3` kills branch (b), and
branch (a) gives `|C| = ℓ` with `C_{Q₀}(P) ≤ C` (via `Q0sub_le_Q`), forcing `C = C_{Q₀}(P)` by
`Subgroup.eq_of_le_of_card_ge`; then `y ∈ C` (`hyQ`+`hyc`) contradicts `hy0`; branch (c) is the
goal. -/
theorem card_centralizer_eq_cube_acyclic {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hST : Work.PSU3.BenderSTProp) {s r : G}
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h3 : orderOf (s * t) = 3)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    {y : G} (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H)
    (hyc : ∀ p ∈ P, p⁻¹ * y * p = y) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G))
      = (Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))) ^ 3 := by
  classical
  -- The local trichotomy of `lemma2cHig` (Ch. V §2 Lemma 2 c, transferred through `BenderSTProp`).
  have htri := Work.PSU3.StageA.lemma2cHig hS hC4 hST hs hs2 hr hsr hPV hPp
  dsimp only at htri
  rcases htri with ⟨h1, _hab, hcard⟩ | ⟨h1, _hnab, _hcard, _⟩ | ⟨_h1, hcard, _⟩
  · -- Case (a): `C` is abelian and `|C| = ℓ`.  Since `C_{Q₀}(P) ≤ C` (because `Q₀sub H ≤ Q`)
    -- and `|C| = ℓ = |C_{Q₀}(P)|`, equality of the subgroups follows.  But then `y ∈ C ⊆ Q₀sub H`
    -- (using `y ∈ Q` and `y ∈ C_G(P)`), contradicting `hy0`.
    exfalso
    have hle : Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)
        ≤ Q ⊓ Subgroup.centralizer (P : Set G) :=
      inf_le_inf_right _ (Work.PSU3.StageA.Q0sub_le_Q hS.split)
    have heq : Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)
        = Q ⊓ Subgroup.centralizer (P : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
    have hyC : y ∈ Q ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨hyQ, Subgroup.mem_centralizer_iff.mpr (fun p hp => by
        calc p * y = p * (p⁻¹ * y * p) := by rw [hyc p hp]
          _ = y * p := by group)⟩
    have hyQ0 : y ∈ Work.ThmF.Q0sub H := by
      have : y ∈ Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) := by
        rw [heq]; exact hyC
      exact this.1
    exact hy0 hyQ0
  · -- Case (b): `orderOf (s * t) = 5` contradicts the given `orderOf (s * t) = 3`.
    exfalso
    rw [h3] at h1
    exact absurd h1 (by decide)
  · -- Case (c): exactly the goal.
    exact hcard

end Work.PSU3.StageB
