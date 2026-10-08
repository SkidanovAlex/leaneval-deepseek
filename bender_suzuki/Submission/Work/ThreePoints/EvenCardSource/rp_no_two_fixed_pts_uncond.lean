import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.ThreePoints.EvenCardSource.lemma2_propagation_uncond
import Submission.Work.DoubleTransitivity.App2.app2_1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.EvenCardSource.rp_no_two_fixed_pts_uncond`

Peterfalvi I, Ch. I §4 Prop. 1 (b) (p. 156), with the Brauer–Suzuki hypothesis removed, in the
direction used by Prop. 2's Case 2: `𝓡_p ≠ ∅` implies that no `p`-subgroup of `G` fixes exactly two
points of `Ω = G ⧸ H`.

This is a transcription of `Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts` with `hBrSz` deleted;
that argument uses `hBrSz` only through `Work.DoubleTransitivity.Sec4.sec4_lemma2_of_part1`, which is
replaced here by the Brauer–Suzuki-free `sec4_lemma2_of_part1_uncond`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.DoubleTransitivity
open Work.DoubleTransitivity.Sec4
open scoped Pointwise

namespace Work.ThreePoints.EvenCardSource

variable {G : Type} [Group G] [Finite G]

/-- **Peterfalvi I, Ch. I §4 Prop. 1 (b)** (p. 156), without the Brauer–Suzuki hypothesis:
`𝓡_p ≠ ∅` implies that no `p`-subgroup fixes exactly two points of `Ω = G ⧸ H`.

The witness `P` of `Rp p H` fixes at least three points (`three_le_fixedPts_of_even_normalizer`),
so it lies in a maximal `Q` with at least three fixed points (`exists_maxFixesThree_le`); Ch. I §4
Lemma 2 (`Sec4Lemma2 p H`, obtained from `h1` via `sec4_lemma2_of_part1_uncond`) makes `Q` a
`p`-Sylow of `Stab ω ⊓ Stab ω'` for every pair of distinct fixed points of `Q`.  If a `p`-subgroup
`T` fixed exactly `{σ₁,σ₂}`, Appendix II (1) (`App2.app2_1`) gives a `p`-Sylow `S` of `G` with
`fixedBySub S = {σ₁,σ₂}`; conjugating `S` so that `Q ≤ S'` and applying Lemma 2 to `Q` and the two
(distinct) points of `S'` — which are fixed by `Q` — shows that `Q` is a `p`-Sylow of that
two-point stabiliser, and since `Q ≤ S'` lies in it, `S' = Q`; but `|Ω_{S'}| = 2` while
`|Ω_Q| ≥ 3`. -/
theorem rp_no_two_fixed_pts_uncond
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : Sec4Lemma2Part1 p H) :
    Rp p H → ∀ T : Subgroup G, IsPGroup p T → (fixedPts H T).ncard ≠ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Omega H) := Fintype.ofFinite _
  intro hRp T hTp hT2
  have hL2 : Sec4Lemma2 p H := sec4_lemma2_of_part1_uncond hH hp hp2 h1
  have hBender : IsBender H := (isStronglyEmbedded_iff H).mp hH |>.2
  have hp2' : 2 < p := by
    have h2 := hp.two_le
    omega
  -- the two fixed points of `T`
  have hne1 : (fixedPts H T).Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (by rw [hT2]; norm_num)
  obtain ⟨σ₁, hσ₁⟩ := hne1
  obtain ⟨σ₂, hσ₂, hσ₂ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := fixedPts H T) (by rw [hT2]; norm_num) σ₁
  have hfix : fixedBySub T = ({σ₁, σ₂} : Set (Omega H)) := by
    have hsub : ({σ₁, σ₂} : Set (Omega H)) ⊆ fixedBySub T := by
      intro y hy
      rcases hy with rfl | rfl
      · exact hσ₁
      · exact hσ₂
    have hcard : ({σ₁, σ₂} : Set (Omega H)).ncard = 2 := Set.ncard_pair hσ₂ne.symm
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact le_of_eq hT2)).symm
  -- Appendix II (1): a `p`-Sylow of `G` with exactly these two fixed points
  obtain ⟨S, -, -, hSfix, hSsyl⟩ :=
    Work.DoubleTransitivity.App2.app2_1 (p := p) hTp hσ₂ne.symm hfix
  have hSsyl' : IsSylowSub p S := hSsyl hp2'
  have hS2 : (fixedPts H S).ncard = 2 := by
    rw [show fixedPts H S = ({σ₁, σ₂} : Set (Omega H)) from hSfix, Set.ncard_pair hσ₂ne.symm]
  -- the `Rp` witness and a maximal `Q ⊇ Q₀`
  obtain ⟨ω₁, ω₂, hω₂₁, Q₀, hQ₀syl, hQ₀even⟩ := hRp
  have hQ₀2 : 2 ≤ (fixedPts H Q₀).ncard := by
    have hsub : ({ω₁, ω₂} : Set (Omega H)) ⊆ fixedPts H Q₀ := by
      intro y hy
      rcases hy with rfl | rfl
      · exact mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hQ₀syl.1 inf_le_left)
      · exact mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hQ₀syl.1 inf_le_right)
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_pair hω₂₁.symm] at hle
    exact hle
  have hQ₀3 : 3 ≤ (fixedPts H Q₀).ncard :=
    three_le_fixedPts_of_even_normalizer hBender
      (mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hQ₀syl.1 inf_le_left)) hQ₀even hQ₀2
  obtain ⟨Q, hQ₀Q, hQmax⟩ := exists_maxFixesThree_le ⟨Q₀, hQ₀syl.2.1, hQ₀3, le_rfl⟩
  have hQinv : TwoPointSylowData p H Q := ⟨ω₁, ω₂, hω₂₁, Q₀, hQ₀syl, hQ₀Q⟩
  -- conjugate `S` into a `p`-Sylow containing `Q`
  obtain ⟨g, hQg⟩ := exists_le_conj_of_isPGroup_isSylowSub (p := p) hQmax.1 hSsyl'
  set S' : Subgroup G := conj g S with hS'def
  have hS'2 : (fixedPts H S').ncard = 2 := by
    rw [hS'def, ncard_fixedPts_conj]
    exact hS2
  -- two fixed points of `S'`, which are also fixed by `Q`
  have hne1' : (fixedPts H S').Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (by rw [hS'2]; norm_num)
  obtain ⟨σ₁', hσ₁'⟩ := hne1'
  obtain ⟨σ₂', hσ₂', hσ₂'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := fixedPts H S') (by rw [hS'2]; norm_num) σ₁'
  have hσ₁'Q : σ₁' ∈ fixedPts H Q := fixedBySub_antitone hQg hσ₁'
  have hσ₂'Q : σ₂' ∈ fixedPts H Q := fixedBySub_antitone hQg hσ₂'
  -- Ch. I §4 Lemma 2: `Q` is a `p`-Sylow of the two-point stabiliser
  have hQsyl : IsSylowSubgroupOf p Q
      (MulAction.stabilizer G σ₁' ⊓ MulAction.stabilizer G σ₂') :=
    (hL2 Q hQmax hQinv σ₁' σ₂' hσ₂'ne
      (mem_fixedPts_iff_le_stabilizer_aux.mp hσ₁'Q)
      (mem_fixedPts_iff_le_stabilizer_aux.mp hσ₂'Q)).1
  have hS'le : S' ≤ MulAction.stabilizer G σ₁' ⊓ MulAction.stabilizer G σ₂' :=
    le_inf (mem_fixedPts_iff_le_stabilizer_aux.mp hσ₁')
      (mem_fixedPts_iff_le_stabilizer_aux.mp hσ₂')
  -- hence `S' = Q`, contradicting `|Ω_{S'}| = 2 < 3 ≤ |Ω_Q|`
  have hS'eqQ : S' = Q := by
    have hQp : IsPGroup p (Q.subgroupOf
        (MulAction.stabilizer G σ₁' ⊓ MulAction.stabilizer G σ₂')) :=
      hQsyl.2.1.comap_of_injective _ Subtype.coe_injective
    have hQidx : ¬ p ∣ (Q.subgroupOf
        (MulAction.stabilizer G σ₁' ⊓ MulAction.stabilizer G σ₂')).index := hQsyl.2.2
    have hS'p : IsPGroup p (S'.subgroupOf
        (MulAction.stabilizer G σ₁' ⊓ MulAction.stabilizer G σ₂')) :=
      ((hSsyl'.1.map (MulAut.conj g).toMonoidHom).comap_of_injective _ Subtype.coe_injective)
    have hmax : S'.subgroupOf (MulAction.stabilizer G σ₁' ⊓ MulAction.stabilizer G σ₂') =
        Q.subgroupOf (MulAction.stabilizer G σ₁' ⊓ MulAction.stabilizer G σ₂') :=
      (hQp.toSylow hQidx).is_maximal' hS'p
        (Subgroup.subgroupOf_mono _ ((hS'def ▸ hQg : Q ≤ S')))
    calc S' = (S'.subgroupOf (MulAction.stabilizer G σ₁' ⊓ MulAction.stabilizer G σ₂')).map
            (MulAction.stabilizer G σ₁' ⊓ MulAction.stabilizer G σ₂').subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hS'le).symm
      _ = Q := by rw [hmax, Subgroup.map_subgroupOf_eq_of_le hQsyl.1]
  have h3 : 3 ≤ (fixedPts H S').ncard := by
    rw [hS'eqQ]
    exact hQmax.2.1
  rw [hS'2] at h3
  omega

end Work.ThreePoints.EvenCardSource
