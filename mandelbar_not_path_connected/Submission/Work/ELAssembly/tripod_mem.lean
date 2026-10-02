import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.tripodArms_cover
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.paramRay_subset_pairSideNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set Filter
open scoped Topology

namespace Work.ELAssembly

/-!
# The arms of the tripod capture the rays of their arc

This file proves `Work.ELAssembly.tripod_mem`: the far-side arm of the tripod
`Work.EL.Tripod.armA T` (resp. `armB`, `armC`) at the branch point `T.y` captures the landing
point of every ray whose angle lies in the corresponding arc `(22/63, 25/63)`
(resp. `(25/63, 37/63)`, `(37/63, 22/63 + 1)`), and the near side of any co-landing pair `P`
captures the branch point `T.y` as soon as a ray of an angle in the near arc of `P` lands at
`T.y`.

The proof is the same in all four cases:

* `Work.ELTop.paramRay_subset_pairSide` (resp. `Work.ELTop.paramRay_subset_pairSideNear`) puts
  the whole ray of the given angle inside the relevant side of the relevant pair;
* the landing point of the ray is therefore in the *closure* of that side;
* the complement of the pair curve is the disjoint union of the two sides and each side has the
  pair curve as its frontier (`Work.ELTop.pairSides_decomposition`), so a point of the closure of
  a side which is not on the pair curve must already lie in the side.

The last step is where the hypothesis "the landing point is not the branch point" is used: it
excludes the only point of the pair curve which could be the landing point of a ray of an angle
which is not congruent modulo `1` to one of the two angles of the pair (the ray part of the pair
curve is disjoint from the filled Julia set, where every landing point lies).
-/

/-! ## A point of the closure of an open set, off its frontier -/

/-- If `s` is open, `frontier s = U`, `z ∈ closure s` and `z ∉ U`, then `z ∈ s`. -/
private theorem mem_of_mem_closure_of_frontier {X : Type*} [TopologicalSpace X] {s U : Set X}
    {z : X} (hopen : IsOpen s) (hfront : frontier s = U) (hzcl : z ∈ closure s)
    (hzU : z ∉ U) : z ∈ s := by
  by_contra hzs
  have hzfr : z ∈ frontier s := by
    rw [hopen.frontier_eq]
    exact ⟨hzcl, hzs⟩
  exact hzU (hfront ▸ hzfr)

/-! ## Elementary facts on the cyclic length `arcLen` -/

/-- `Int.fract` does not vanish on `(0, 1)`. -/
private theorem fract_ne_zero_of_mem_Ioo {x : ℝ} (h1 : 0 < x) (h2 : x < 1) :
    Int.fract x ≠ 0 := by
  rw [Int.fract_eq_self.mpr ⟨le_of_lt h1, h2⟩]
  linarith

/-- The length of the first arc of the tripod is nonzero. -/
private theorem arcLen_pairA_ne_zero {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (T : Work.EL.Tripod hN) : Work.EL.arcLen (T.pairA).a (T.pairA).b ≠ 0 := by
  show Work.EL.arcLen (22 / 63 : ℝ) (25 / 63) ≠ 0
  rw [Work.EL.arcLen, show (25 : ℝ) / 63 - 22 / 63 = 3 / 63 by norm_num]
  exact fract_ne_zero_of_mem_Ioo (by norm_num) (by norm_num)

/-- The length of the second arc of the tripod is nonzero. -/
private theorem arcLen_pairB_ne_zero {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (T : Work.EL.Tripod hN) : Work.EL.arcLen (T.pairB).a (T.pairB).b ≠ 0 := by
  show Work.EL.arcLen (25 / 63 : ℝ) (37 / 63) ≠ 0
  rw [Work.EL.arcLen, show (37 : ℝ) / 63 - 25 / 63 = 12 / 63 by norm_num]
  exact fract_ne_zero_of_mem_Ioo (by norm_num) (by norm_num)

/-- The length of the third arc of the tripod is nonzero. -/
private theorem arcLen_pairC_ne_zero {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (T : Work.EL.Tripod hN) : Work.EL.arcLen (T.pairC).a (T.pairC).b ≠ 0 := by
  show Work.EL.arcLen (37 / 63 : ℝ) (22 / 63 + 1) ≠ 0
  rw [Work.EL.arcLen, show (22 : ℝ) / 63 + 1 - 37 / 63 = 48 / 63 by norm_num]
  exact fract_ne_zero_of_mem_Ioo (by norm_num) (by norm_num)

/-- An angle in the near arc of a pair forces that arc to be nondegenerate: the near arc has
length `Int.fract (a - b)`, and `InArc θ b (a + 1)` forces `0 < Int.fract (a - b)`, whence
`Int.fract (b - a) = 1 - Int.fract (a - b) ≠ 0`. -/
private theorem arcLen_ne_zero_of_nearArc {a b θ : ℝ} (h : Work.EL.InArc θ b (a + 1)) :
    Work.EL.arcLen a b ≠ 0 := by
  have hpos : 0 < Int.fract (θ - b) := h.1
  have hlt : Int.fract (θ - b) < Work.EL.arcLen b (a + 1) := h.2
  have harc : Work.EL.arcLen b (a + 1) = Int.fract (a - b) := by
    rw [Work.EL.arcLen, show a + 1 - b = (a - b) + 1 by ring, Int.fract_add_one]
  have hab : 0 < Int.fract (a - b) := by rw [← harc]; linarith
  have hlt1 : Int.fract (a - b) < 1 := Int.fract_lt_one _
  have hneg := Int.fract_neg (x := a - b) (ne_of_gt hab)
  rw [Work.EL.arcLen, show b - a = -(a - b) by ring, hneg]
  linarith

/-! ## Landing points of rays in a side -/

/-- **A landing point of a ray inside the far side of a pair is in that far side.** -/
private theorem landing_mem_pairSide {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) {Q : Work.EL.CoPair hN} (hnd : Work.EL.arcLen Q.a Q.b ≠ 0)
    {θ : ℝ} {y : ℂ} (hlands : Work.EL.LandsN hN θ y)
    (hsub : Work.EL.paramRay hN θ ⊆ Work.EL.pairSide Q)
    (hyC : y ∉ Work.EL.pairCurve Q) : y ∈ Work.EL.pairSide Q := by
  have hcl : y ∈ closure (Work.EL.pairSide Q) :=
    closure_mono hsub (mem_closure_of_tendsto hlands (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact Work.EL.rayPt_mem_paramRay hN ht))
  have hdec := Work.ELTop.pairSides_decomposition hN hJ Q hnd
  have hAopen : IsOpen (Work.EL.pairSide Q) :=
    (Work.ELTop.isClosed_pairCurve_aux hN Q).isOpen_compl.connectedComponentIn
  exact mem_of_mem_closure_of_frontier hAopen hdec.2.2.1 hcl hyC

/-- **A landing point of a ray inside the near side of a pair is in that near side.** -/
private theorem landing_mem_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) {Q : Work.EL.CoPair hN} (hnd : Work.EL.arcLen Q.a Q.b ≠ 0)
    {θ : ℝ} {y : ℂ} (hlands : Work.EL.LandsN hN θ y)
    (hsub : Work.EL.paramRay hN θ ⊆ Work.EL.pairSideNear Q)
    (hyC : y ∉ Work.EL.pairCurve Q) : y ∈ Work.EL.pairSideNear Q := by
  have hcl : y ∈ closure (Work.EL.pairSideNear Q) :=
    closure_mono hsub (mem_closure_of_tendsto hlands (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact Work.EL.rayPt_mem_paramRay hN ht))
  have hdec := Work.ELTop.pairSides_decomposition hN hJ Q hnd
  have hBopen : IsOpen (Work.EL.pairSideNear Q) :=
    (Work.ELTop.isClosed_pairCurve_aux hN Q).isOpen_compl.connectedComponentIn
  exact mem_of_mem_closure_of_frontier hBopen hdec.2.2.2 hcl hyC

/-! ## The statement -/

theorem tripod_mem {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    (T : Work.EL.Tripod hN) :
    (∀ P : Work.EL.CoPair hN, Work.EL.InArc P.a (22 / 63) (25 / 63) → P.y ≠ T.y →
      P.y ∈ Work.EL.Tripod.armA T) ∧
    (∀ P : Work.EL.CoPair hN, Work.EL.InArc P.a (25 / 63) (37 / 63) → P.y ≠ T.y →
      P.y ∈ Work.EL.Tripod.armB T) ∧
    (∀ P : Work.EL.CoPair hN, Work.EL.InArc P.a (37 / 63) (22 / 63 + 1) → P.y ≠ T.y →
      P.y ∈ Work.EL.Tripod.armC T) ∧
    (∀ (θ : ℝ) (P : Work.EL.CoPair hN), Work.EL.LandsN hN θ T.y →
      Work.EL.InArc θ P.b (P.a + 1) → P.y ≠ T.y → T.y ∈ Work.EL.pairSideNear P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hIn hne
    have hsub : Work.EL.paramRay hN P.a ⊆ Work.EL.pairSide (T.pairA) :=
      Work.ELTop.paramRay_subset_pairSide hN hJ (T.pairA) hIn
    have hyK : P.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN P.lands_a
    have hyC : P.y ∉ Work.EL.pairCurve (T.pairA) := by
      rw [Work.EL.mem_pairCurve_iff]
      rintro (h | h | h)
      · exact (Work.EL.paramRay_subset_compl hN (22 / 63) h) hyK
      · exact hne h
      · exact (Work.EL.paramRay_subset_compl hN (25 / 63) h) hyK
    exact landing_mem_pairSide hN hJ (arcLen_pairA_ne_zero hN T) P.lands_a hsub hyC
  · intro P hIn hne
    have hsub : Work.EL.paramRay hN P.a ⊆ Work.EL.pairSide (T.pairB) :=
      Work.ELTop.paramRay_subset_pairSide hN hJ (T.pairB) hIn
    have hyK : P.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN P.lands_a
    have hyC : P.y ∉ Work.EL.pairCurve (T.pairB) := by
      rw [Work.EL.mem_pairCurve_iff]
      rintro (h | h | h)
      · exact (Work.EL.paramRay_subset_compl hN (25 / 63) h) hyK
      · exact hne h
      · exact (Work.EL.paramRay_subset_compl hN (37 / 63) h) hyK
    exact landing_mem_pairSide hN hJ (arcLen_pairB_ne_zero hN T) P.lands_a hsub hyC
  · intro P hIn hne
    have hsub : Work.EL.paramRay hN P.a ⊆ Work.EL.pairSide (T.pairC) :=
      Work.ELTop.paramRay_subset_pairSide hN hJ (T.pairC) hIn
    have hyK : P.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN P.lands_a
    have hyC : P.y ∉ Work.EL.pairCurve (T.pairC) := by
      rw [Work.EL.mem_pairCurve_iff]
      rintro (h | h | h)
      · exact (Work.EL.paramRay_subset_compl hN (37 / 63) h) hyK
      · exact hne h
      · exact (Work.EL.paramRay_subset_compl hN (22 / 63 + 1) h) hyK
    exact landing_mem_pairSide hN hJ (arcLen_pairC_ne_zero hN T) P.lands_a hsub hyC
  · intro θ P hL hIn hne
    have hsub : Work.EL.paramRay hN θ ⊆ Work.EL.pairSideNear P :=
      Work.ELTop.paramRay_subset_pairSideNear hN hJ P hIn
    have hyK : T.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN hL
    have hyC : T.y ∉ Work.EL.pairCurve P := by
      rw [Work.EL.mem_pairCurve_iff]
      rintro (h | h | h)
      · exact (Work.EL.paramRay_subset_compl hN P.a h) hyK
      · exact hne h.symm
      · exact (Work.EL.paramRay_subset_compl hN P.b h) hyK
    exact landing_mem_pairSideNear hN hJ (arcLen_ne_zero_of_nearArc hIn) hL hsub hyC

end Work.ELAssembly
