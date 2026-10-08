import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.ThreePoints.EvenCardSource.lemma2_propagation_uncond
import Submission.Work.DoubleTransitivity.App2.app2_3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.EvenCardSource.not_rp_twoTransitive_uncond`

Peterfalvi I, Ch. I §4 Prop. 1 (a) (p. 156), with the Brauer–Suzuki hypothesis removed: if
`𝓡_p = ∅` then `G` acts `2`-transitively on `Ω = G ⧸ H`.

This is a transcription of `Work.DoubleTransitivity.Sec4.not_rp_twoTransitive` with `hBrSz` deleted;
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

/-- **Peterfalvi I, Ch. I §4 Prop. 1 (a)** (p. 156), without the Brauer–Suzuki hypothesis, in the
vocabulary of `Submission/Work/DoubleTransitivity/Sec4/RpDefs.lean`.

Setting: `H` strongly embedded in a finite group `G`, `p ≠ 2` a prime, `Ω = G ⧸ H`.  Write
`Rp p H` for `𝓡_p ≠ ∅`: there are distinct points `ω₁ ≠ ω₂` of `Ω` and a `p`-Sylow `P` of
`Stab ω₁ ⊓ Stab ω₂` with `|N_G(P) ⊓ Stab ω₁|` even.  Conclusion: if `¬ Rp p H`, then `G` acts
`2`-transitively on `Ω`.

Mathematically: for distinct `a c : Ω` let `P` be a `p`-Sylow of `Stab a ⊓ Stab c`; if `P` had
at least three fixed points, a maximal `p`-subgroup `Q ⊇ P` with at least three fixed points
would satisfy Ch. I §4 Lemma 2 (this workspace's `Work.DoubleTransitivity.Sec4.Sec4Lemma2 p H`,
obtained from `h1 : Sec4Lemma2Part1 p H` through `sec4_lemma2_of_part1_uncond`), producing a pair
with an even-order normaliser, i.e. `Rp p H`, a contradiction; hence `P` fixes exactly `{a,c}`, and
Appendix II (3) (`Work.DoubleTransitivity.App2.app2_3`) gives `2`-transitivity. -/
theorem not_rp_twoTransitive_uncond
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : Sec4Lemma2Part1 p H) :
    ¬ Rp p H → MulAction.IsMultiplyPretransitive G (Omega H) 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Omega H) := Fintype.ofFinite _
  intro hRp
  have hL2 : Sec4Lemma2 p H := sec4_lemma2_of_part1_uncond hH hp hp2 h1
  have hstabH : MulAction.stabilizer G (pt H) = H := stabilizer_pt_eq H
  -- every two-point stabiliser has a `p`-subgroup fixing exactly those two points
  have key : ∀ a c : Omega H, c ≠ a → ∃ P : Subgroup G, IsPGroup p P ∧
      fixedBySub P = ({a, c} : Set (Omega H)) := by
    intro a c hca
    obtain ⟨P, hPsyl⟩ := exists_isSylowSubgroupOf_of_subgroup (p := p)
      (MulAction.stabilizer G a ⊓ MulAction.stabilizer G c)
    have ha : a ∈ fixedPts H P :=
      mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hPsyl.1 inf_le_left)
    have hc : c ∈ fixedPts H P :=
      mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hPsyl.1 inf_le_right)
    have hle2 : (fixedPts H P).ncard ≤ 2 := by
      by_contra hcon
      have hgt : 2 < (fixedPts H P).ncard := not_le.mp hcon
      have hP3 : FixesThree H P := by
        show 3 ≤ (fixedPts H P).ncard
        omega
      obtain ⟨Q, hPQ, hQmax⟩ := exists_maxFixesThree_le ⟨P, hPsyl.2.1, hP3, le_rfl⟩
      have hQinv : TwoPointSylowData p H Q := ⟨a, c, hca, P, hPsyl, hPQ⟩
      have hQ3 : 3 ≤ (fixedPts H Q).ncard := hQmax.2.1
      obtain ⟨ω₁, hω₁, -⟩ :=
        Set.exists_ne_of_one_lt_ncard (s := fixedPts H Q) (by omega) a
      obtain ⟨ω₂, hω₂, hω₂ne⟩ :=
        Set.exists_ne_of_one_lt_ncard (s := fixedPts H Q) (by omega) ω₁
      have hω₁' : Q ≤ MulAction.stabilizer G ω₁ := mem_fixedPts_iff_le_stabilizer_aux.mp hω₁
      have hω₂' : Q ≤ MulAction.stabilizer G ω₂ := mem_fixedPts_iff_le_stabilizer_aux.mp hω₂
      obtain ⟨-, P', hP'syl, hP'even⟩ := hL2 Q hQmax hQinv ω₁ ω₂ hω₂ne hω₁' hω₂'
      exact hRp ⟨ω₁, ω₂, hω₂ne, P', hP'syl, hP'even⟩
    have hset : fixedBySub P = ({a, c} : Set (Omega H)) := by
      have hsub : ({a, c} : Set (Omega H)) ⊆ fixedBySub P := by
        intro y hy
        rcases hy with rfl | rfl
        · exact ha
        · exact hc
      have hcard : ({a, c} : Set (Omega H)).ncard = 2 := Set.ncard_pair hca.symm
      exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact hle2)).symm
    exact ⟨P, hPsyl.2.1, hset⟩
  refine Work.DoubleTransitivity.App2.app2_3 (X := G) (E := Omega H) (p := p) (a := pt H) ?_ ?_
  · intro c hc
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
    obtain ⟨P, hPp, hPfix⟩ := key (pt H) c hc
    exact ⟨P, hPp, hPfix⟩
  · intro hcon
    have htop : (⊤ : Subgroup G) ≤ MulAction.stabilizer G (pt H) := fun g _ =>
      MulAction.mem_stabilizer_iff.mpr (hcon g)
    rw [stabilizer_pt_eq] at htop
    exact hH.1 (top_le_iff.mp htop)

end Work.ThreePoints.EvenCardSource
