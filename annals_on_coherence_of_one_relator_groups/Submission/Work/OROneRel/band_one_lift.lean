import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.levels_ncard_two

/-!
# The band of a decorated word

Let `c : α → ℤ` be a weight function and `u : FreeGroup α`.  The decorated word
`decor c 0 (wordOf u)` is a walk on the levels `ℤ`: the letter `(x, i)` read by `decor` at running
level `i` stands for the *edge* running from the level `i` to the level `i + c x`, and a negative
letter traverses that edge backwards.  The pair of endpoints of a decorated letter `p` is therefore
`(p.1.2, p.1.2 + c p.1.1)`.

`band_one_lift` says that the decorated word fits into a *minimal* band: there are `lo < hi` with all
the edges of the walk inside `[lo, hi]`, and with the property that no non-zero translate of the walk
fits into `[lo, hi]`.  Equivalently, `[lo, hi]` is the convex hull of the edges of the walk and the
walk is not confined to a proper sub-interval of its convex hull.  The strictness `lo < hi` is
exactly the content of the hypothesis `hnd`: some letter of `u` has non-zero weight, so the walk
contains an edge of positive length.

This is the arithmetic input for the "domain" (`Z`) picture of the weighted Magnus step: the band of
`u` supports a lift of the 2-cell for `u ^ l`, and `band_one_lift` says that the band supports
*exactly one* such lift.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

set_option linter.unusedVariables false

/-- The decorated word carries exactly the letters of the original word, in the same order: only the
level of a letter is changed by `decor`. -/
theorem decor_map_letter (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    (decor c i L).map (fun p : (α × ℤ) × Bool => (p.1.1, p.2)) = L := by
  induction L generalizing i with
  | nil => rfl
  | cons q L ih =>
    obtain ⟨a, b⟩ := q
    cases b
    · rw [show decor c i ((a, false) :: L) = ((a, i - c a), false) :: decor c (i - c a) L from rfl,
        List.map_cons, ih (i - c a)]
    · rw [show decor c i ((a, true) :: L) = ((a, i), true) :: decor c (i + c a) L from rfl,
        List.map_cons, ih (i + c a)]

theorem band_one_lift {α : Type u} [DecidableEq α] (c : α → ℤ) (u : FreeGroup α)
    (hu : u ≠ 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hnd : ∃ x : α, x ∈ Work.OROneRel.relatorLetters u ∧ c x ≠ 0) :
    ∃ lo hi : ℤ, lo < hi ∧
      (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
        lo ≤ p.1.2 ∧ lo ≤ p.1.2 + c p.1.1 ∧ p.1.2 ≤ hi ∧ p.1.2 + c p.1.1 ≤ hi) ∧
      (∀ k : ℤ, k ≠ 0 →
        ¬ (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
            lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
              p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi)) := by
  classical
  obtain ⟨x, hx, hcx⟩ := hnd
  have hx' : ∃ b : Bool, (x, b) ∈ wordOf u := by
    simpa only [relatorLetters, wordOf, Set.mem_ofPred_eq] using hx
  obtain ⟨b, hb⟩ := hx'
  -- a decorated letter of non-zero weight
  obtain ⟨j, hj⟩ := exists_mem_decor_of_mem c 0 (wordOf u) x b hb
  obtain ⟨p, hpL, hpx⟩ : ∃ p : (α × ℤ) × Bool,
      p ∈ decor c 0 (wordOf u) ∧ p.1.1 = x := ⟨_, hj, rfl⟩
  have hcp : c p.1.1 ≠ 0 := by rw [hpx]; exact hcx
  -- the set of endpoints of the edges of the walk
  set S : Finset ℤ := ((decor c 0 (wordOf u)).map (fun p : (α × ℤ) × Bool => p.1.2)).toFinset ∪
      ((decor c 0 (wordOf u)).map (fun p : (α × ℤ) × Bool => p.1.2 + c p.1.1)).toFinset with hS
  have hSmem : ∀ q ∈ decor c 0 (wordOf u), q.1.2 ∈ S ∧ q.1.2 + c q.1.1 ∈ S := by
    intro q hq
    constructor
    · rw [hS]
      exact Finset.mem_union_left _
        (List.mem_toFinset.mpr (List.mem_map_of_mem (f := fun p : (α × ℤ) × Bool => p.1.2) hq))
    · rw [hS]
      exact Finset.mem_union_right _
        (List.mem_toFinset.mpr
          (List.mem_map_of_mem (f := fun p : (α × ℤ) × Bool => p.1.2 + c p.1.1) hq))
  have hSne : S.Nonempty := ⟨p.1.2, (hSmem p hpL).1⟩
  refine ⟨S.min' hSne, S.max' hSne, ?_, ?_, ?_⟩
  · -- the band is non-degenerate
    obtain ⟨ha, hb'⟩ := hSmem p hpL
    have hne : p.1.2 ≠ p.1.2 + c p.1.1 := by
      intro h
      exact hcp (by linarith)
    rcases lt_trichotomy p.1.2 (p.1.2 + c p.1.1) with h | h | h
    · exact lt_of_le_of_lt (Finset.min'_le S _ ha) (lt_of_lt_of_le h (Finset.le_max' S _ hb'))
    · exact absurd h hne
    · exact lt_of_le_of_lt (Finset.min'_le S _ hb') (lt_of_lt_of_le h (Finset.le_max' S _ ha))
  · -- the walk is inside the band
    intro q hq
    obtain ⟨ha, hb'⟩ := hSmem q hq
    exact ⟨Finset.min'_le S _ ha, Finset.min'_le S _ hb', Finset.le_max' S _ ha,
      Finset.le_max' S _ hb'⟩
  · -- no non-zero translate of the walk is inside the band
    intro k hk hcon
    -- letters attaining the top and the bottom of the band
    have htop : ∃ q ∈ decor c 0 (wordOf u),
        q.1.2 = S.max' hSne ∨ q.1.2 + c q.1.1 = S.max' hSne := by
      have hm : S.max' hSne ∈ S := Finset.max'_mem S hSne
      have hm' : S.max' hSne ∈ ((decor c 0 (wordOf u)).map
            (fun p : (α × ℤ) × Bool => p.1.2)).toFinset ∪
          ((decor c 0 (wordOf u)).map (fun p : (α × ℤ) × Bool => p.1.2 + c p.1.1)).toFinset := by
        rw [← hS]
        exact hm
      rcases Finset.mem_union.mp hm' with hm | hm
      · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
        exact ⟨q, hq, Or.inl hqe⟩
      · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
        exact ⟨q, hq, Or.inr hqe⟩
    have hbot : ∃ q ∈ decor c 0 (wordOf u),
        q.1.2 = S.min' hSne ∨ q.1.2 + c q.1.1 = S.min' hSne := by
      have hm : S.min' hSne ∈ S := Finset.min'_mem S hSne
      have hm' : S.min' hSne ∈ ((decor c 0 (wordOf u)).map
            (fun p : (α × ℤ) × Bool => p.1.2)).toFinset ∪
          ((decor c 0 (wordOf u)).map (fun p : (α × ℤ) × Bool => p.1.2 + c p.1.1)).toFinset := by
        rw [← hS]
        exact hm
      rcases Finset.mem_union.mp hm' with hm | hm
      · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
        exact ⟨q, hq, Or.inl hqe⟩
      · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
        exact ⟨q, hq, Or.inr hqe⟩
    rcases lt_trichotomy k 0 with hkneg | hk0 | hkpos
    · obtain ⟨q, hq, hqlo⟩ := hbot
      have h1 := (hcon q hq).1
      have h2 := (hcon q hq).2.1
      rcases hqlo with h | h <;> omega
    · exact hk hk0
    · obtain ⟨q, hq, hqhi⟩ := htop
      have h1 := (hcon q hq).2.2.1
      have h2 := (hcon q hq).2.2.2
      rcases hqhi with h | h <;> omega

end Work.OROneRel
