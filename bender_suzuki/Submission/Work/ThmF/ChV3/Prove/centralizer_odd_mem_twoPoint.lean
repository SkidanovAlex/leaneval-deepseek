import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmG.centralizer_le_twoPoint_of_fixedPts_card_two
import Submission.Work.ThmF.ChV3.Prove.mem_of_sq_mem_of_odd_orderOf
import Submission.Work.ThmF.ChV3.Prove.fixedPts_zpowers_eq_pair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.centralizer_odd_mem_twoPoint` — Peterfalvi II, Ch. V §3

Let `H` be strongly embedded with split rank-one data `H = Q ⋊ D`, `D = H ⊓ Hᵗ`
(`IsSplitRankOne H Q t`), `k ∈ K#` where `K = J(D,t) = Kset H t` (`k ≠ 1`).  Then every
element `y` of **odd order** centralising `k` lies in `D = twoPoint H t`.

This is the "`C_G(k)` has only the two points `H`, `Hᵗ`" observation of the source
(`Ch. II §4 Prop. 2 (c)`: `k ∈ K#` fixes exactly two points of `Ω = G ⧸ H`), used as the first
step of leaf 13b (`Prove/cent_Kelem_order3_mem_W`).

Proof.  `Ch. II §4 Prop. 2 (c)` (`ChIIFourProp`, applied at `hS`, `h`, `t`) gives that the fixed
point set `Fix(⟨k⟩)` of `Ω = G ⧸ H` has exactly two elements.  Since `k ∈ D = H ⊓ Hᵗ`, the
two points `∞ = H` and `t • ∞` are fixed by `⟨k⟩`, so `Fix(⟨k⟩) = {∞, t • ∞}`
(`fixedPts_zpowers_eq_pair`).  As `y` centralises `k`, the whole of `⟨y⟩` permutes `Fix(⟨k⟩)`;
thus `y • ∞ ∈ {∞, t • ∞}`, and the same for `y • (t • ∞)`.  Therefore `y²` fixes both (a
bijection of a two-element set has square the identity: if `y` fixes `∞` then `y² • ∞ = y • ∞ = ∞`,
and otherwise `y • ∞ = t • ∞` forces `y • (t • ∞) = ∞`), so `y²` fixes `∞`, i.e. `y² ∈ H`.
Finally `Odd (orderOf y)` together with `y² ∈ H` gives `y ∈ H`
(`mem_of_sq_mem_of_odd_orderOf`: `y = (y²)^((orderOf y + 1)/2)`), and
`C_G(k) ⊓ H ≤ D` is the point-stabiliser lemma
`Work.ThmG.centralizer_le_twoPoint_of_fixedPts_card_two`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3.Prove

theorem centralizer_odd_mem_twoPoint {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Submission.Blueprint.Situation G) (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    {k y : G} (hk : k ∈ Work.ThmF.Kset H t) (hk1 : k ≠ 1)
    (hy : y ∈ Subgroup.centralizer ({k} : Set G)) (hodd : Odd (orderOf y)) :
    y ∈ Submission.Blueprint.twoPoint H t := by
  -- `Ch. II §4 Prop. 2 (c)`: `⟨k⟩` fixes exactly two points of `Ω = G ⧸ H`
  have h2c : (fixedPts H (Subgroup.zpowers k)).ncard = 2 :=
    (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).2.2.1 k hk hk1
  have hkD : k ∈ twoPoint H t := Work.ThmF.Kset_subset H t hk
  -- the two fixed points are `∞ = H` and `t • ∞`
  have hfix : fixedPts H (Subgroup.zpowers k) = {((1:G) : G ⧸ H), ((t:G) : G ⧸ H)} :=
    fixedPts_zpowers_eq_pair h.not_mem hkD h2c
  -- the two points are distinct because `t ∉ H`
  have ht_ne : ((1:G) : G ⧸ H) ≠ ((t:G) : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact h.not_mem (by simpa using hcon)
  have hmem1 : ((1:G) : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers k) := by rw [hfix]; simp
  have hmemt : ((t:G) : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers k) := by rw [hfix]; simp
  -- `y` commutes with every element of `⟨k⟩`
  have hky : k * y = y * k := (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  have hyc : ∀ x ∈ Subgroup.zpowers k, x * y = y * x := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hky) hx)
  -- hence `y` preserves the two fixed points
  have hyF : ∀ ω ∈ fixedPts H (Subgroup.zpowers k), y • ω ∈ fixedPts H (Subgroup.zpowers k) := by
    intro ω hω
    rw [fixedPts] at hω ⊢
    intro x hx
    rw [← mul_smul, hyc x hx, mul_smul, hω x hx]
  have h1 : y • ((1:G):G⧸H) ∈ fixedPts H (Subgroup.zpowers k) := hyF _ hmem1
  have ht' : y • ((t:G):G⧸H) ∈ fixedPts H (Subgroup.zpowers k) := hyF _ hmemt
  rw [hfix] at h1 ht'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ht'
  -- a permutation of a two-element set has square the identity, so `y²` fixes `∞`
  have hy2H : y ^ 2 ∈ H := by
    have hgoal : y ^ 2 • ((1:G):G⧸H) = ((1:G):G⧸H) := by
      rw [pow_two, mul_smul]
      rcases h1 with h1' | h1'
      · rw [h1', h1']
      · rw [h1']
        rcases ht' with h2' | h2'
        · exact h2'
        · exact absurd (smul_left_cancel_iff y |>.mp (h1'.trans h2'.symm)) ht_ne
    rw [show y ^ 2 • ((1:G):G⧸H) = ((y^2 : G) : G ⧸ H) by simp, QuotientGroup.eq] at hgoal
    simpa using hgoal
  -- odd order promotes `y² ∈ H` to `y ∈ H`
  have hyH : y ∈ H := mem_of_sq_mem_of_odd_orderOf hy2H hodd
  -- the point-stabiliser lemma of area `ThmG` finishes
  exact Work.ThmG.centralizer_le_twoPoint_of_fixedPts_card_two hkD hk1 h2c ⟨hy, hyH⟩

end Work.ThmF.ChV3.Prove
