import Mathlib
import Submission.Work.Drive.bdry_label_parity

/-!
# The `τ`-face parity of a transversally cut-out family

This is the bookkeeping half of the mod-2 intersection form of `ℝP²`
(`Submission/Work/Drive/SURF_PLAN.md`): if `F : ℝ³ → ℝ²` is a smooth map on the cube `[0,1]³` whose
zeros are transversally cut out (the three hypotheses of `Submission.Drive.ParityProp`) and which has
no zeros on the four faces `x 1 = 0`, `x 1 = 1`, `x 2 = 0`, `x 2 = 1`, then the *two* faces `x 0 = 0`
and `x 0 = 1` carry an even total number of zeros.

Read as `x 0 = τ` (the homotopy parameter), `x 1 = s`, `x 2 = t`: for a one-parameter family
`(τ,s) ↦ A_τ s` of curves "against" a fixed curve `b`, the map `F (τ,s,t) = A_τ s - b t` has this
shape, and the statement says that **the number of intersections of `A_0` with `b` and the number of
intersections of `A_1` with `b` have the same parity**, provided the family is in general position —
the bordism invariance of the mod-2 intersection number of two curves in a surface
(`CHAIN_ROUTE_REDUCTION.md` §4, step 2 of the proof of `(SURF)`).

The engine is `Work.Drive.even_sum_ncard_labelMeet`: group the faces `x 0 = 0` and `x 0 = 1` under one
label and the four faces `x 1 ∈ {0,1}`, `x 2 ∈ {0,1}` under the other; the second group is empty by
assumption, and each boundary zero lies on exactly one face (`hface`).
-/

namespace Work.Surf

open Submission.Drive
open scoped Topology

noncomputable section

/-- The labelling of the three coordinates used below: the `x 0`-coordinate gets label `0`, the two
others get label `1`. -/
def tauLabel : Fin 3 → Fin 2 := ![0, 1, 1]

lemma tauLabel_eq_zero_iff (i : Fin 3) : tauLabel i = 0 ↔ i = 0 := by
  fin_cases i <;> decide

lemma tauLabel_ne_zero (i : Fin 3) (hi : i ≠ 0) : tauLabel i = 1 := by
  fin_cases i
  · exact absurd rfl hi
  · rfl
  · rfl

/-- **The two `τ`-faces carry an even total number of zeros.**  For a smooth
`F : ℝ³ → ℝ²` satisfying the three hypotheses of `Submission.Drive.ParityProp` on the cube `[0,1]³`
and having no zeros on the four faces `x 1 = 0`, `x 1 = 1`, `x 2 = 0`, `x 2 = 1`, the number of zeros
on the face `x 0 = 0` plus the number of zeros on the face `x 0 = 1` is even. -/
theorem even_ncard_tauFaces (F : Work.Drive.Amb 2 → Work.Drive.Tgt 2)
    (hF : ContDiff ℝ Work.Drive.Ctop F)
    (hreg : ∀ x ∈ unitBox 2, F x = 0 → Function.Surjective (fderiv ℝ F x))
    (hface : ∀ x ∈ unitBoxBdry 2, F x = 0 → ∃ i : Fin 3, (x i = 0 ∨ x i = 1) ∧
      (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Work.Drive.Amb 2 // v i = 0} => fderiv ℝ F x v.1))
    (hside : ∀ x ∈ unitBox 2, (x 1 = 0 ∨ x 1 = 1 ∨ x 2 = 0 ∨ x 2 = 1) → F x ≠ 0) :
    Even (({x ∈ unitBox 2 | x 0 = 0 ∧ F x = 0} : Set (Work.Drive.Amb 2)).ncard +
      ({x ∈ unitBox 2 | x 0 = 1 ∧ F x = 0} : Set (Work.Drive.Amb 2)).ncard) := by
  classical
  have heven := Work.Drive.even_sum_ncard_labelMeet F hF hreg hface tauLabel
  have heven' : Even ((Work.Drive.labelMeet F tauLabel 0).ncard +
      (Work.Drive.labelMeet F tauLabel 1).ncard) := by
    simpa [Fin.sum_univ_two] using heven
  -- the label-`0` piece is the union of the two `x 0`-faces
  have hA : (Work.Drive.labelMeet F tauLabel 0 : Set (Work.Drive.Amb 2)) =
      {x ∈ unitBox 2 | x 0 = 0 ∧ F x = 0} ∪ {x ∈ unitBox 2 | x 0 = 1 ∧ F x = 0} := by
    ext x
    constructor
    · rintro ⟨hx, i, hi, hxi⟩
      rw [Work.Drive.mem_bdyZeros] at hx
      have hi0 : i = 0 := (tauLabel_eq_zero_iff i).mp hi
      rw [hi0] at hxi
      rcases hxi with h | h
      · exact Or.inl ⟨hx.1.1, h, hx.2⟩
      · exact Or.inr ⟨hx.1.1, h, hx.2⟩
    · rintro (⟨hbox, h0, hzero⟩ | ⟨hbox, h1, hzero⟩)
      · exact ⟨⟨⟨hbox, ⟨0, Or.inl h0⟩⟩, hzero⟩, 0, rfl, Or.inl h0⟩
      · exact ⟨⟨⟨hbox, ⟨0, Or.inr h1⟩⟩, hzero⟩, 0, rfl, Or.inr h1⟩
  -- the label-`1` piece is empty
  have hB : (Work.Drive.labelMeet F tauLabel 1 : Set (Work.Drive.Amb 2)) = ∅ := by
    rw [Work.Drive.labelMeet, Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, i, hi, hxi⟩
    rw [Work.Drive.mem_bdyZeros] at hx
    have hi0 : i ≠ 0 := by
      intro h
      rw [h] at hi
      exact absurd hi (by decide)
    have hmem : x 1 = 0 ∨ x 1 = 1 ∨ x 2 = 0 ∨ x 2 = 1 := by
      by_cases h1 : i = 1
      · rw [h1] at hxi
        rcases hxi with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · have h2 : i = 2 := by
          fin_cases i
          · exact absurd rfl hi0
          · exact absurd rfl h1
          · rfl
        rw [h2] at hxi
        rcases hxi with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    exact hside x hx.1.1 hmem hx.2
  have hdisj : Disjoint ({x ∈ unitBox 2 | x 0 = 0 ∧ F x = 0} : Set (Work.Drive.Amb 2))
      {x ∈ unitBox 2 | x 0 = 1 ∧ F x = 0} := by
    rw [Set.disjoint_left]
    rintro x ⟨-, h0, -⟩ ⟨-, h1, -⟩
    exact absurd (h0.symm.trans h1) (by norm_num)
  have hfinA : (Work.Drive.labelMeet F tauLabel 0 : Set (Work.Drive.Amb 2)).Finite :=
    Work.Drive.finite_labelMeet F tauLabel hF hreg hface 0
  have hfin0 : ({x ∈ unitBox 2 | x 0 = 0 ∧ F x = 0} : Set (Work.Drive.Amb 2)).Finite :=
    hfinA.subset (by rw [hA]; exact Set.subset_union_left)
  have hfin1 : ({x ∈ unitBox 2 | x 0 = 1 ∧ F x = 0} : Set (Work.Drive.Amb 2)).Finite :=
    hfinA.subset (by rw [hA]; exact Set.subset_union_right)
  rw [hB, Set.ncard_empty, add_zero, hA, Set.ncard_union_eq hdisj hfin0 hfin1] at heven'
  exact heven'

end

end Work.Surf
