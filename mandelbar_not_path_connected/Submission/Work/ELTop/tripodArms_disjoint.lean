/-
# The three arms of the tripod at `b₂` are pairwise disjoint

The tripod of the EL argument is the triple of rays of angles `22/63`, `25/63`, `37/63` of the
dynamical plane, all landing at the same branch point `y = T.y`.  Its three arms are the far
sides of the three co-landing pairs

* `pairA T = (22/63, 25/63, y)`, `pairB T = (25/63, 37/63, y)`,
  `pairC T = (37/63, 85/63, y)` with `85/63 = 22/63 + 1` (so that `paramRay (85/63) =
  paramRay (22/63)`),

and `armA T = pairSide (pairA T)`, etc.

Two ingredients make the disjointness formal.

* `Work.ELTop.pairSide_disjoint` (in `pairSides_decomposition.lean`): the far and the near side
  of one co-landing pair are disjoint, so an arm (`= pairSide`) never meets the *near* side of
  its own pair.

* The angle-side lemmas: a ray whose angle lies in the far arc `(a, b)` of a pair is contained in
  its far side (`mem_pairSide_of_farArc`), and a ray whose angle lies in the near arc
  `(b, a + 1)` is contained in its near side (`paramRay_subset_pairSideNear_of_InArc`).

The pattern, for each of the three unordered pairs of arms, is:

1. the arm `armQ = pairSide Q` misses `pairCurve P` (for the neighbouring pair `P`): each of the
   two rays of `pairCurve P` is either a ray of `pairCurve Q` (hence off `pairSide Q`) or lies in
   the near side of `Q` (hence off `pairSide Q` by `pairSide_disjoint Q`), and the landing point
   `y` lies on `pairCurve Q`;
2. hence, `pairSide Q` being preconnected and `(pairCurve P)ᶜ` being the union of the two disjoint
   sides of `P` (`pairCurve_compl_eq`), the arm `armQ` lies in `pairSide P` or in
   `pairSideNear P`;
3. an explicit ray point of the arm `armQ` is shown to lie in `pairSideNear P`, which rules out
   the first alternative.

The explicit ray points are `rayPt hN (31/63) 2` for `armB ∩ pairSideNear (pairA T)`,
`rayPt hN (55/63) 2` for `armC ∩ pairSideNear (pairB T)`, and
`rayPt hN (47/126) 2 = rayPt hN (47/126 + 1) 2` for `armA ∩ pairSideNear (pairC T)`.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.isOpen_pairSide

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ}

/-- An angle strictly inside the interval `(a, b)`, with `b < a + 1`, lies in the open cyclic arc
`(a, b)`. -/
theorem InArc_of_mem_Ioo {a b x : ℝ} (h1 : a < x) (h2 : x < b) (h3 : b < a + 1) :
    Work.EL.InArc x a b := by
  have hx : Int.fract (x - a) = x - a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hb : Work.EL.arcLen a b = b - a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [Work.EL.InArc, hx, hb]
  exact ⟨by linarith, by linarith⟩

/-- The parameter rays are `1`-periodic in the angle, with the real number `1`. -/
theorem paramRay_add_one_real (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Work.EL.paramRay hN (θ + 1) = Work.EL.paramRay hN θ := by
  simpa using Work.ELTop.paramRay_add_int hN θ (1 : ℤ)

/-- The ray points are `1`-periodic in the angle, with the real number `1`. -/
theorem rayPt_add_one_real (hN : Work.EL.DynB c φ) (θ t : ℝ) :
    Work.EL.rayPt hN (θ + 1) t = Work.EL.rayPt hN θ t := by
  simpa using Work.ELTop.rayPt_add_int hN θ t (1 : ℤ)

/-- The far side of a pair `Q` misses the pair curve of `P`, provided each of the two rays of
`pairCurve P` is either a ray of `pairCurve Q` or contained in the near side of `Q`, and the
landing point of `P` lies on `pairCurve Q`. -/
theorem pairSide_subset_compl_pairCurve (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    (P Q : Work.EL.CoPair hN) (hab : Q.a < Q.b) (hb1 : Q.b < Q.a + 1)
    (hPa : Work.EL.paramRay hN P.a ⊆ Work.EL.pairCurve Q ∪ Work.EL.pairSideNear Q)
    (hPb : Work.EL.paramRay hN P.b ⊆ Work.EL.pairCurve Q ∪ Work.EL.pairSideNear Q)
    (hy : P.y ∈ Work.EL.pairCurve Q) :
    Work.EL.pairSide Q ⊆ (Work.EL.pairCurve P)ᶜ := by
  intro z hz
  have hzQ : z ∉ Work.EL.pairCurve Q := connectedComponentIn_subset _ _ hz
  have hd := Work.ELTop.pairSide_disjoint hN hJ Q hab hb1
  have hzN : z ∉ Work.EL.pairSideNear Q := fun h => (Set.disjoint_right.mp hd) h hz
  intro hzP
  rw [Work.EL.mem_pairCurve_iff] at hzP
  rcases hzP with h | h | h
  · rcases hPa h with h' | h'
    · exact hzQ h'
    · exact hzN h'
  · exact hzQ (h ▸ hy)
  · rcases hPb h with h' | h'
    · exact hzQ h'
    · exact hzN h'

/-- If the far side of `Q` misses the pair curve of `P` and contains a point of the near side of
`P`, then the two far sides are disjoint. -/
theorem disjoint_pairSide_of_witness (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    (P Q : Work.EL.CoPair hN) (habP : P.a < P.b) (hb1P : P.b < P.a + 1)
    (hsub : Work.EL.pairSide Q ⊆ (Work.EL.pairCurve P)ᶜ)
    (hwit : ∃ x : ℂ, x ∈ Work.EL.pairSide Q ∧ x ∈ Work.EL.pairSideNear P) :
    Disjoint (Work.EL.pairSide P) (Work.EL.pairSide Q) := by
  have hdP := Work.ELTop.pairSide_disjoint hN hJ P habP hb1P
  have hopen := Work.ELTop.isOpen_pairSide hN P
  have hsub' : Work.EL.pairSide Q ⊆ Work.EL.pairSide P ∪ Work.EL.pairSideNear P := by
    rw [← Work.ELTop.pairCurve_compl_eq hN P habP hb1P]
    exact hsub
  rcases IsPreconnected.subset_or_subset hopen.1 hopen.2 hdP hsub'
      isPreconnected_connectedComponentIn with h | h
  · obtain ⟨x, hxQ, hxN⟩ := hwit
    exact absurd (h hxQ) ((Set.disjoint_right.mp hdP) hxN)
  · exact Set.disjoint_of_subset_right h hdP

theorem tripodArms_disjoint {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (T : Work.EL.Tripod hN) :
    Disjoint (Work.EL.Tripod.armA T) (Work.EL.Tripod.armB T) ∧
    Disjoint (Work.EL.Tripod.armB T) (Work.EL.Tripod.armC T) ∧
    Disjoint (Work.EL.Tripod.armC T) (Work.EL.Tripod.armA T) := by
  -- the three pairs of the tripod, and their angle data
  have habA : (Work.EL.Tripod.pairA T).a < (Work.EL.Tripod.pairA T).b := by
    norm_num [Work.EL.Tripod.pairA]
  have hb1A : (Work.EL.Tripod.pairA T).b < (Work.EL.Tripod.pairA T).a + 1 := by
    norm_num [Work.EL.Tripod.pairA]
  have habB : (Work.EL.Tripod.pairB T).a < (Work.EL.Tripod.pairB T).b := by
    norm_num [Work.EL.Tripod.pairB]
  have hb1B : (Work.EL.Tripod.pairB T).b < (Work.EL.Tripod.pairB T).a + 1 := by
    norm_num [Work.EL.Tripod.pairB]
  have habC : (Work.EL.Tripod.pairC T).a < (Work.EL.Tripod.pairC T).b := by
    norm_num [Work.EL.Tripod.pairC]
  have hb1C : (Work.EL.Tripod.pairC T).b < (Work.EL.Tripod.pairC T).a + 1 := by
    norm_num [Work.EL.Tripod.pairC]
  -- the landing points of the three pairs are the same point `T.y`
  have hyA : (Work.EL.Tripod.pairA T).y = T.y := rfl
  have hyB : (Work.EL.Tripod.pairB T).y = T.y := rfl
  have hyC : (Work.EL.Tripod.pairC T).y = T.y := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- `armA ∩ armB = ∅`
    refine disjoint_pairSide_of_witness hN hJ (Work.EL.Tripod.pairA T) (Work.EL.Tripod.pairB T)
      habA hb1A ?_ ?_
    · -- `armB ⊆ (pairCurve (pairA T))ᶜ`
      refine pairSide_subset_compl_pairCurve hN hJ (Work.EL.Tripod.pairA T) (Work.EL.Tripod.pairB T)
        habB hb1B ?_ ?_ ?_
      · -- the ray `22/63` of `pairA` lies in the near side of `pairB` (`85/63 ∈ (37/63, 88/63)`)
        intro z hz
        refine Or.inr ?_
        have hIn : Work.EL.InArc ((Work.EL.Tripod.pairA T).a + 1) (Work.EL.Tripod.pairB T).b
            ((Work.EL.Tripod.pairB T).a + 1) :=
          InArc_of_mem_Ioo (by norm_num [Work.EL.Tripod.pairA, Work.EL.Tripod.pairB])
            (by norm_num [Work.EL.Tripod.pairA, Work.EL.Tripod.pairB])
            (by norm_num [Work.EL.Tripod.pairA, Work.EL.Tripod.pairB])
        have hsub := Work.ELTop.paramRay_subset_pairSideNear_of_InArc hN (Work.EL.Tripod.pairB T)
          habB hb1B hIn
        rw [paramRay_add_one_real hN (Work.EL.Tripod.pairA T).a] at hsub
        exact hsub hz
      · -- the ray `25/63` of `pairA` is the first ray of `pairB`
        intro z hz
        exact Or.inl ((Work.EL.mem_pairCurve_iff (Work.EL.Tripod.pairB T) z).mpr (Or.inl hz))
      · -- the landing point lies on `pairCurve (pairB T)`
        rw [hyA]
        exact Work.ELTop.self_mem_pairCurve (Work.EL.Tripod.pairB T)
    · -- the witness `rayPt (31/63) 2`
      refine ⟨Work.EL.rayPt hN (31/63) 2, ?_, ?_⟩
      · exact Work.ELTop.mem_pairSide_of_farArc hN (Work.EL.Tripod.pairB T) habB hb1B
          (θ := 31/63) ⟨by norm_num [Work.EL.Tripod.pairB],
            by norm_num [Work.EL.Tripod.pairB]⟩ (by norm_num)
      · exact Work.ELTop.mem_pairSideNear_of_nearArc hN (Work.EL.Tripod.pairA T) habA
          (θ := 31/63) ⟨by norm_num [Work.EL.Tripod.pairA],
            by norm_num [Work.EL.Tripod.pairA]⟩ (by norm_num)
  · -- `armB ∩ armC = ∅`
    refine disjoint_pairSide_of_witness hN hJ (Work.EL.Tripod.pairB T) (Work.EL.Tripod.pairC T)
      habB hb1B ?_ ?_
    · -- `armC ⊆ (pairCurve (pairB T))ᶜ`
      refine pairSide_subset_compl_pairCurve hN hJ (Work.EL.Tripod.pairB T) (Work.EL.Tripod.pairC T)
        habC hb1C ?_ ?_ ?_
      · -- the ray `25/63` of `pairB` lies in the near side of `pairC` (`88/63 ∈ (85/63, 100/63)`)
        intro z hz
        refine Or.inr ?_
        have hIn : Work.EL.InArc ((Work.EL.Tripod.pairB T).a + 1) (Work.EL.Tripod.pairC T).b
            ((Work.EL.Tripod.pairC T).a + 1) :=
          InArc_of_mem_Ioo (by norm_num [Work.EL.Tripod.pairB, Work.EL.Tripod.pairC])
            (by norm_num [Work.EL.Tripod.pairB, Work.EL.Tripod.pairC])
            (by norm_num [Work.EL.Tripod.pairB, Work.EL.Tripod.pairC])
        have hsub := Work.ELTop.paramRay_subset_pairSideNear_of_InArc hN (Work.EL.Tripod.pairC T)
          habC hb1C hIn
        rw [paramRay_add_one_real hN (Work.EL.Tripod.pairB T).a] at hsub
        exact hsub hz
      · -- the ray `37/63` of `pairB` is the first ray of `pairC`
        intro z hz
        exact Or.inl ((Work.EL.mem_pairCurve_iff (Work.EL.Tripod.pairC T) z).mpr (Or.inl hz))
      · rw [hyB]
        exact Work.ELTop.self_mem_pairCurve (Work.EL.Tripod.pairC T)
    · -- the witness `rayPt (55/63) 2`
      refine ⟨Work.EL.rayPt hN (55/63) 2, ?_, ?_⟩
      · exact Work.ELTop.mem_pairSide_of_farArc hN (Work.EL.Tripod.pairC T) habC hb1C
          (θ := 55/63) ⟨by norm_num [Work.EL.Tripod.pairC],
            by norm_num [Work.EL.Tripod.pairC]⟩ (by norm_num)
      · exact Work.ELTop.mem_pairSideNear_of_nearArc hN (Work.EL.Tripod.pairB T) habB
          (θ := 55/63) ⟨by norm_num [Work.EL.Tripod.pairB],
            by norm_num [Work.EL.Tripod.pairB]⟩ (by norm_num)
  · -- `armC ∩ armA = ∅`
    refine disjoint_pairSide_of_witness hN hJ (Work.EL.Tripod.pairC T) (Work.EL.Tripod.pairA T)
      habC hb1C ?_ ?_
    · -- `armA ⊆ (pairCurve (pairC T))ᶜ`
      refine pairSide_subset_compl_pairCurve hN hJ (Work.EL.Tripod.pairC T) (Work.EL.Tripod.pairA T)
        habA hb1A ?_ ?_ ?_
      · -- the ray `37/63` of `pairC` lies in the near side of `pairA` (`37/63 ∈ (25/63, 85/63)`)
        intro z hz
        refine Or.inr ?_
        have hIn : Work.EL.InArc (Work.EL.Tripod.pairC T).a (Work.EL.Tripod.pairA T).b
            ((Work.EL.Tripod.pairA T).a + 1) :=
          InArc_of_mem_Ioo (by norm_num [Work.EL.Tripod.pairA, Work.EL.Tripod.pairC])
            (by norm_num [Work.EL.Tripod.pairA, Work.EL.Tripod.pairC])
            (by norm_num [Work.EL.Tripod.pairA, Work.EL.Tripod.pairC])
        exact (Work.ELTop.paramRay_subset_pairSideNear_of_InArc hN (Work.EL.Tripod.pairA T)
          habA hb1A hIn) hz
      · -- the ray `85/63 = 22/63 + 1` of `pairC` is the first ray of `pairA`
        intro z hz
        refine Or.inl ((Work.EL.mem_pairCurve_iff (Work.EL.Tripod.pairA T) z).mpr (Or.inl ?_))
        have hz' : z ∈ Work.EL.paramRay hN ((Work.EL.Tripod.pairA T).a + 1) := hz
        rwa [paramRay_add_one_real hN (Work.EL.Tripod.pairA T).a] at hz'
      · rw [hyC]
        exact Work.ELTop.self_mem_pairCurve (Work.EL.Tripod.pairA T)
    · -- the witness `rayPt (47/126) 2 = rayPt (47/126 + 1) 2`
      refine ⟨Work.EL.rayPt hN (47/126) 2, ?_, ?_⟩
      · exact Work.ELTop.mem_pairSide_of_farArc hN (Work.EL.Tripod.pairA T) habA hb1A
          (θ := 47/126) ⟨by norm_num [Work.EL.Tripod.pairA],
            by norm_num [Work.EL.Tripod.pairA]⟩ (by norm_num)
      · have h := Work.ELTop.mem_pairSideNear_of_nearArc hN (Work.EL.Tripod.pairC T) habC
          (θ := 47/126 + 1) (t := 2) ⟨by norm_num [Work.EL.Tripod.pairC],
            by norm_num [Work.EL.Tripod.pairC]⟩ (by norm_num)
        rwa [rayPt_add_one_real hN (47/126) 2] at h

end Work.ELTop
