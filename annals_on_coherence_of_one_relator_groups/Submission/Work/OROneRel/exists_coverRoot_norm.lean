import Mathlib
import Submission.Work.OROneRel.coverRootDefs
import Submission.Work.OROneRel.gauge_walk_defs
import Submission.Work.OROneRel.gaugeLevelDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.gauge_cover_vertices_ncard

/-!
# A gauge whose truncated root is strictly shorter

Let `c : α → ℤ` be a weight function and `u : FreeGroup α`.  The decorated word
`decor c 0 (wordOf u)` is a walk on the levels `ℤ`, and for a *gauge* `W : ℤ → FreeGroup α` the
*loop class* of a decorated letter `p` is
`coverClass W c p = W (coverSrc c p) * coverLetter p * (W (coverTgt c p))⁻¹`
(`GaugeDefs.gauge_letter`).  The candidate root `coverRoot W c u` of the `ℤ`-cover decomposition is
the word spelled by the decorated letters of *non-trivial* loop class (`coverRootDefs`).

This file proves that, whenever the walk touches at least two levels (`2 ≤ #(coverLevelSet c u)`)
and the decorated word is non-empty, there is a gauge with `W 0 = 1` for which
`relatorNorm (coverRoot W c u) < relatorNorm u`.

The argument is shorter than the "one trivial letter per visited level" bound of
`gauge_walk_defs`: a single letter of non-zero `c`-weight can be gauged away by hand.  If the walk
touches two levels then some decorated letter has `c p.1.1 ≠ 0`, hence `coverSrc c p ≠ coverTgt c p`
(`coverSrc_ne_coverTgt_iff`); putting one of these two levels at `1` and the other at the loop class
of `p` makes that letter trivial.  The trivial letter is then deleted by `coverRootList`, so
`relatorNorm (coverRoot W c u) ≤ |decor| - 1 < |decor| = relatorNorm u`.
-/

namespace Work.OROneRel

universe u

/-! ## Auxiliary combinatorial lemmas -/

/-- `decor` keeps the generator of a letter: the generators of the decorated letters of `M` are the
generators of `M`. -/
private theorem decor_map_fst {α : Type u} (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) :
    (decor c i M).map (fun p => p.1.1) = M.map (fun q => q.1) := by
  induction M generalizing i with
  | nil => simp [decor]
  | cons p M ih =>
    obtain ⟨a, b⟩ := p
    cases b <;> simp [decor, ih]

/-- If every letter of `L` has vanishing `c`-weight then the running levels of `L` are all equal to
the starting level. -/
private theorem running_eq_replicate_of_forall {α : Type u} (c : α → ℤ) (L : List (α × Bool))
    (h : ∀ p ∈ L, c p.1 = 0) : ∀ i : ℤ, running c i L = List.replicate (L.length + 1) i := by
  induction L with
  | nil => intro i; simp [running]
  | cons p L ih =>
    intro i
    obtain ⟨a, b⟩ := p
    have ha : c a = 0 := h (a, b) (by simp)
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) i
    cases b
    · rw [show running c i ((a, false) :: L) = i :: running c (i - c a) L from rfl, ha, sub_zero,
        ih']
      simp [List.replicate_succ, List.length_cons]
    · rw [show running c i ((a, true) :: L) = i :: running c (i + c a) L from rfl, ha, add_zero,
        ih']
      simp [List.replicate_succ, List.length_cons]

/-- **A letter of non-zero weight exists.**  If the decorated word of `u` touches at least two levels
then some decorated letter has `c p.1.1 ≠ 0`.  Indeed, if all weights vanished the running levels
would be constantly `0`, so the level set would have at most one element. -/
private theorem exists_letter_weight_ne_zero {α : Type u} (c : α → ℤ) (u : FreeGroup α)
    (hV : 2 ≤ (coverLevelSet c u).ncard) :
    ∃ p ∈ decor c 0 (wordOf u), c p.1.1 ≠ 0 := by
  classical
  have hne : wordOf u ≠ [] := by
    intro h
    have h0 : coverLevelSet c u = ∅ := by
      rw [coverLevelSet, h]
      simp [decor]
    rw [h0] at hV
    simp at hV
  have hcard : (coverLevelSet c u).ncard = (running c 0 (wordOf u)).toFinset.card :=
    gauge_cover_vertices_ncard c u hne
  by_contra h
  simp only [not_exists, not_and, not_ne_iff] at h
  have hletters : ∀ q ∈ wordOf u, c q.1 = 0 := by
    intro q hq
    have hmem : q.1 ∈ (decor c 0 (wordOf u)).map (fun p => p.1.1) := by
      rw [decor_map_fst]
      exact List.mem_map_of_mem hq
    obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hmem
    rw [← hpq]
    exact h p hp
  have hrep := running_eq_replicate_of_forall c (wordOf u) hletters 0
  rw [hrep] at hcard
  have hle : (List.replicate ((wordOf u).length + 1) (0 : ℤ)).toFinset.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [List.mem_toFinset] at ha hb
    rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  omega

/-- A decorated letter has equal source and target level exactly when its `c`-weight vanishes. -/
private theorem coverSrc_ne_coverTgt_iff {α : Type u} (c : α → ℤ) (p : (α × ℤ) × Bool) :
    coverSrc c p ≠ coverTgt c p ↔ c p.1.1 ≠ 0 := by
  obtain ⟨⟨a, i⟩, b⟩ := p
  cases b
  · simp only [coverSrc, coverTgt, Bool.false_eq_true, if_false]
    omega
  · simp only [coverSrc, coverTgt, if_true]
    omega

/-- **A gauge with a decorated letter of trivial loop class.**  If the decorated word of `u` touches
at least two levels then some decorated letter `p` can be made trivial: take a letter of non-zero
weight and put its source level at `1` and its target level at the loop class (or vice versa,
according to whether the target level is `0`). -/
private theorem exists_trivial_coverClass {α : Type u} (c : α → ℤ) (u : FreeGroup α)
    (hV : 2 ≤ (coverLevelSet c u).ncard) :
    ∃ W : ℤ → FreeGroup α, W 0 = 1 ∧
      ∃ p ∈ decor c 0 (wordOf u), coverClass W c p = 1 := by
  obtain ⟨p, hpD, hc⟩ := exists_letter_weight_ne_zero c u hV
  have hst : coverSrc c p ≠ coverTgt c p := (coverSrc_ne_coverTgt_iff c p).mpr hc
  have hcl : ∀ W : ℤ → FreeGroup α,
      coverClass W c p = W (coverSrc c p) * coverLetter p * (W (coverTgt c p))⁻¹ := by
    intro W
    rw [coverClass]
    exact gauge_letter W c p
  by_cases ht : coverTgt c p = 0
  · refine ⟨fun x => if x = coverSrc c p then (coverLetter p)⁻¹ else 1, ?_, p, hpD, ?_⟩
    · have h0 : (0 : ℤ) ≠ coverSrc c p := fun h => hst (by rw [← h, ht])
      simp [h0]
    · rw [hcl]
      have hs : (if coverSrc c p = coverSrc c p then (coverLetter p)⁻¹ else 1)
          = (coverLetter p)⁻¹ := by simp
      have htg : (if coverTgt c p = coverSrc c p then (coverLetter p)⁻¹ else 1)
          = 1 := by simp [Ne.symm hst]
      rw [hs, htg]
      group
  · refine ⟨fun x => if x = coverTgt c p then coverLetter p else 1, ?_, p, hpD, ?_⟩
    · have h0 : (0 : ℤ) ≠ coverTgt c p := fun h => ht h.symm
      simp [h0]
    · rw [hcl]
      have hs : (if coverSrc c p = coverTgt c p then coverLetter p else 1)
          = 1 := by simp [hst]
      have htg : (if coverTgt c p = coverTgt c p then coverLetter p else 1)
          = coverLetter p := by simp
      rw [hs, htg]
      group

/-- A `filterMap` that sends an element of its list to `none` drops at least one element. -/
private theorem length_filterMap_le_pred {β γ : Type*} (F : β → Option γ) :
    ∀ (l : List β) (x : β), x ∈ l → F x = none → (l.filterMap F).length ≤ l.length - 1 := by
  intro l
  induction l with
  | nil => intro x hx _; exact absurd hx (by simp)
  | cons y t ih =>
    intro x hx hF
    rcases List.mem_cons.mp hx with rfl | hxt
    · have heq : List.filterMap F (x :: t) = List.filterMap F t := by
        rw [List.filterMap_cons, hF]
      rw [heq, List.length_cons]
      exact le_trans (List.length_filterMap_le F t) (by omega)
    · have h1 : (List.filterMap F (y :: t)).length ≤ (List.filterMap F t).length + 1 := by
        rw [List.filterMap_cons]; cases h : F y <;> simp
      have h2 := ih x hxt hF
      have htne : t ≠ [] := by rintro rfl; exact absurd hxt (by simp)
      have htpos : 1 ≤ t.length := by
        have := List.length_pos_iff.mpr htne
        omega
      rw [List.length_cons]
      omega

/-- **The truncated root is shorter.**  If a decorated letter of `u` has trivial loop class then the
`coverRootList` deletes at least one of the `|decor|` letters, so the relator norm of `coverRoot`
drops by at least one. -/
private theorem relatorNorm_coverRoot_le {α : Type u} (c : α → ℤ) (u : FreeGroup α)
    (W : ℤ → FreeGroup α)
    (h : ∃ p ∈ decor c 0 (wordOf u), coverClass W c p = 1) :
    relatorNorm (coverRoot W c u) ≤ (decor c 0 (wordOf u)).length - 1 := by
  classical
  obtain ⟨p, hpD, hp1⟩ := h
  have h1 : relatorNorm (coverRoot W c u) ≤ (coverRootList W c u).length := by
    rw [relatorNorm, coverRoot]
    exact FreeGroup.norm_mk_le
  have h2 : (coverRootList W c u).length ≤ (decor c 0 (wordOf u)).length - 1 := by
    let F : {x // x ∈ decor c 0 (wordOf u)} → Option (coverBeta W c u × Bool) :=
      fun q => if h : coverClass W c q.1 ≠ 1 then some (⟨q.1, q.2, h⟩, true) else none
    have hx : (⟨p, hpD⟩ : {x // x ∈ decor c 0 (wordOf u)}) ∈ (decor c 0 (wordOf u)).attach :=
      List.mem_attach _ _
    have hF : F ⟨p, hpD⟩ = none := by
      simp only [F]
      simp [hp1]
    have h3 := length_filterMap_le_pred F (decor c 0 (wordOf u)).attach ⟨p, hpD⟩ hx hF
    rw [List.length_attach] at h3
    rw [coverRootList]
    exact h3
  exact h1.trans h2

/-- The length of the decorated word of `u` is the relator norm of `u` (the length of its reduced
word). -/
private theorem decor_length_eq_relatorNorm {α : Type u} (c : α → ℤ) (u : FreeGroup α) :
    (decor c 0 (wordOf u)).length = relatorNorm u := by
  classical
  rw [decor_length, relatorNorm, wordOf, FreeGroup.norm]

theorem exists_coverRoot_norm {α : Type u} (c : α → ℤ) (u : FreeGroup α)
    (hV : 2 ≤ (Work.OROneRel.coverLevelSet c u).ncard)
    (hN : 0 < (Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u)).length) :
    ∃ W : ℤ → FreeGroup α, W 0 = 1 ∧
      Work.OROneRel.relatorNorm (Work.OROneRel.coverRoot W c u) < Work.OROneRel.relatorNorm u := by
  obtain ⟨W, hW, htriv⟩ := exists_trivial_coverClass c u hV
  refine ⟨W, hW, ?_⟩
  have h1 := relatorNorm_coverRoot_le c u W htriv
  have hD := decor_length_eq_relatorNorm c u
  rw [hD] at h1
  have hN' : 0 < relatorNorm u := by rw [← hD]; exact hN
  omega

end Work.OROneRel
