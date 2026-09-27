import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull
import Submission.Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace
import Submission.Work.Generic.exists_mem_ball_notMem_finset
import Submission.Work.Generic.getElem_notMem_take_of_le

namespace Work.PL.Generic

open Set Metric

variable {n : ℕ} {ι : Type*}

/-- The avoidance condition required at a single free vertex `i` of a partial vertex placement `y`,
relative to a set `T` of already-placed vertices: either `y i` lies in the affine span of `y '' T`
and that span is everything, or `y i` misses that span entirely -- and likewise for the span of
`y '' T` together with each fixed finite vertex set.  This is the per-vertex form of the conclusion
of `exists_avoiding_list`. -/
def AvoidCond [DecidableEq ι] (Fixed : Finset (Finset (PL.E n))) (y : ι → PL.E n) (i : ι)
    (T : Finset ι) : Prop :=
  (y i ∈ (affineSpan ℝ (y '' (T : Set ι)) : Set (PL.E n)) →
      affineSpan ℝ (y '' (T : Set ι)) = ⊤) ∧
    (∀ S ∈ Fixed, y i ∈
        (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n)) →
      affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) = ⊤)

/-- Finset form of the `toFinset` statement of `Work.Generic.getElem_notMem_take_of_le`. -/
private lemma getElem_notMem_toFinset_take_aux {α : Type*} [DecidableEq α] {l : List α}
    (hl : l.Nodup) {j k : ℕ} (hj : j ≤ k) (hk : k < l.length) :
    l[k] ∉ (l.take j).toFinset := by
  rw [List.mem_toFinset]
  exact Work.Generic.getElem_notMem_take_of_le hl hj hk

/-- Invariant of the recursion of `exists_avoiding_list`: `y` is frozen on `fz`, is within `ε` of
`y₀` on the first `k` free vertices of the enumeration `l`, and the avoidance conditions at the
earlier free vertices already hold. -/
private def Good [DecidableEq ι] (fz : Finset ι) (y₀ : ι → PL.E n) (l : List ι)
    (Fixed : Finset (Finset (PL.E n))) (ε : ℝ) (k : ℕ) (y : ι → PL.E n) : Prop :=
  (∀ i ∈ fz, y i = y₀ i) ∧
    (∀ i ∈ (l.take k).toFinset, dist (y i) (y₀ i) < ε) ∧
    (∀ j (hj : j < l.length), j < k → ∀ T : Finset ι, T ⊆ fz ∪ (l.take j).toFinset →
      AvoidCond Fixed y (l[j]) T)

/-- One step of the recursion: move the free vertex `l[k]` inside the `ε`-ball of its old position
while keeping all other values and avoiding every affine span (of a `T` inside the already-placed
vertices, with or without a fixed vertex set adjoined) that is not all of `ℝⁿ`. -/
private lemma exists_step [DecidableEq ι] (fz : Finset ι) (y₀ : ι → PL.E n) (l : List ι)
    (hl' : l.Nodup) (Fixed : Finset (Finset (PL.E n))) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (hkl : k < l.length) (hlk_fz : l[k] ∉ fz) (y : ι → PL.E n) :
    ∃ y' : ι → PL.E n, y' (l[k]) ∈ Metric.ball (y₀ (l[k])) ε ∧
      (∀ i, i ≠ l[k] → y' i = y i) ∧
      (∀ T : Finset ι, T ⊆ fz ∪ (l.take k).toFinset → AvoidCond Fixed y' (l[k]) T) := by
  classical
  have hnt : l[k] ∉ (l.take k).toFinset := getElem_notMem_toFinset_take_aux hl' le_rfl hkl
  set badT : Finset (AffineSubspace ℝ (PL.E n)) :=
    (((fz ∪ (l.take k).toFinset).powerset).image
      (fun T : Finset ι => affineSpan ℝ (y '' (T : Set ι)))).filter (fun F => F ≠ ⊤) with hbadT
  set badS : Finset (AffineSubspace ℝ (PL.E n)) :=
    (((fz ∪ (l.take k).toFinset).powerset).biUnion (fun T : Finset ι =>
      Fixed.image (fun S : Finset (PL.E n) =>
        affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n)))))).filter
      (fun F => F ≠ ⊤) with hbadS
  set bad : Finset (AffineSubspace ℝ (PL.E n)) := badT ∪ badS with hbad
  have hbadne : ∀ F ∈ bad, F ≠ ⊤ := by
    intro F hF
    rw [hbad, Finset.mem_union] at hF
    rcases hF with hF | hF
    · rw [hbadT, Finset.mem_filter] at hF
      exact hF.2
    · rw [hbadS, Finset.mem_filter] at hF
      exact hF.2
  obtain ⟨x, hxball, hxav⟩ := Work.Generic.exists_mem_ball_notMem_finset bad hbadne (y₀ (l[k])) hε
  refine ⟨Function.update y (l[k]) x, ?_, ?_, ?_⟩
  · rw [Function.update_self]
    exact hxball
  · intro i hi
    exact Function.update_of_ne hi x y
  · intro T hT
    have hTne : ∀ i ∈ T, i ≠ l[k] := by
      intro i hi hieq
      have hmem : l[k] ∈ fz ∪ (l.take k).toFinset := by
        rw [← hieq]
        exact hT hi
      rw [Finset.mem_union] at hmem
      rcases hmem with hmem | hmem
      · exact hlk_fz hmem
      · exact hnt hmem
    have himg : (Function.update y (l[k]) x) '' (T : Set ι) = y '' (T : Set ι) :=
      Set.image_congr (fun i hi => Function.update_of_ne (hTne i hi) x y)
    constructor
    · intro hmem
      have hmem' : Function.update y (l[k]) x (l[k]) ∈
          (affineSpan ℝ (y '' (T : Set ι)) : Set (PL.E n)) := by
        simpa only [himg] using hmem
      by_cases htop : affineSpan ℝ (y '' (T : Set ι)) = ⊤
      · simpa only [himg] using htop
      · have hxmem : x ∈ (affineSpan ℝ (y '' (T : Set ι)) : Set (PL.E n)) := by
          simpa only [Function.update_self] using hmem'
        have hmem_bad : affineSpan ℝ (y '' (T : Set ι)) ∈ bad := by
          rw [hbad, Finset.mem_union]
          left
          rw [hbadT, Finset.mem_filter]
          exact ⟨Finset.mem_image.mpr ⟨T, Finset.mem_powerset.mpr hT, rfl⟩, htop⟩
        exact absurd hxmem (hxav _ hmem_bad)
    · intro S hS hmem
      have hmem' : Function.update y (l[k]) x (l[k]) ∈
          (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n)) := by
        simpa only [himg] using hmem
      by_cases htop : affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) = ⊤
      · simpa only [himg] using htop
      · have hxmem : x ∈
            (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n)) := by
          simpa only [Function.update_self] using hmem'
        have hmem_bad : affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) ∈ bad := by
          rw [hbad, Finset.mem_union]
          right
          rw [hbadS, Finset.mem_filter]
          refine ⟨?_, htop⟩
          rw [Finset.mem_biUnion]
          exact ⟨T, Finset.mem_powerset.mpr hT, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩
        exact absurd hxmem (hxav _ hmem_bad)

/-- The recursion: there is a placement satisfying the invariant for all `l.length` steps. -/
private lemma exists_prefix_good [DecidableEq ι] (fz : Finset ι) (y₀ : ι → PL.E n) (l : List ι)
    (hl : ∀ i, i ∈ l ↔ i ∉ fz) (hl' : l.Nodup) (Fixed : Finset (Finset (PL.E n))) (ε : ℝ)
    (hε : 0 < ε) : ∃ y : ι → PL.E n, Good fz y₀ l Fixed ε l.length y := by
  classical
  have key : ∀ k ≤ l.length, ∃ y : ι → PL.E n, Good fz y₀ l Fixed ε k y := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨y₀, ?_, ?_, ?_⟩
      · intro i _
        rfl
      · intro i hi
        exact absurd hi (by simp)
      · intro j hj hlt
        omega
    | succ k ih =>
      intro hk
      have hkl : k < l.length := by omega
      obtain ⟨y, hy1, hy2, hy3⟩ := ih (by omega)
      have hlk_fz : l[k] ∉ fz := (hl (l[k])).mp (List.getElem_mem hkl)
      obtain ⟨y', hy'ball, hy'agree, hy'av⟩ :=
        exists_step fz y₀ l hl' Fixed ε hε k hkl hlk_fz y
      refine ⟨y', ?_, ?_, ?_⟩
      · intro i hi
        have hine : i ≠ l[k] := by
          intro h
          rw [h] at hi
          exact hlk_fz hi
        rw [hy'agree i hine]
        exact hy1 i hi
      · intro i hi
        have htake : l.take (k + 1) = l.take k ++ [l[k]] := by
          rw [← List.take_append_getElem hkl]
        have hsplit : i ∈ (l.take k).toFinset ∨ i = l[k] := by
          have hi' : i ∈ l.take k ++ [l[k]] := by
            rw [← htake]
            exact (List.mem_toFinset).mp hi
          rw [List.mem_append, List.mem_singleton] at hi'
          rcases hi' with h | h
          · exact Or.inl ((List.mem_toFinset).mpr h)
          · exact Or.inr h
        rcases hsplit with hi | hik
        · have hine : i ≠ l[k] := by
            intro h
            rw [h] at hi
            exact getElem_notMem_toFinset_take_aux hl' le_rfl hkl hi
          rw [hy'agree i hine]
          exact hy2 i hi
        · subst hik
          exact Metric.mem_ball.mp hy'ball
      · intro j hj hjk T hT
        rcases lt_or_ge j k with hlt | hge
        · have h1 : AvoidCond Fixed y (l[j]) T := hy3 j hj hlt T hT
          have hlj_ne : l[j] ≠ l[k] := by
            intro h
            have : j = k := (List.Nodup.getElem_inj_iff hl').mp h
            omega
          have hTne : ∀ i ∈ T, i ≠ l[k] := by
            intro i hi hieq
            have hmem : l[k] ∈ fz ∪ (l.take j).toFinset := by
              rw [← hieq]
              exact hT hi
            rw [Finset.mem_union] at hmem
            rcases hmem with hmem | hmem
            · exact hlk_fz hmem
            · exact getElem_notMem_toFinset_take_aux hl' (le_of_lt hlt) hkl hmem
          have himg : y' '' (T : Set ι) = y '' (T : Set ι) :=
            Set.image_congr (fun i hi => hy'agree i (hTne i hi))
          simp only [AvoidCond] at h1 ⊢
          rw [himg, hy'agree (l[j]) hlj_ne]
          exact h1
        · have hjk' : j = k := by omega
          subst hjk'
          exact hy'av T hT
  exact key l.length le_rfl

/-- Generic-position perturbation, one free vertex at a time along an enumeration `l` of the free
vertices (`fz` = frozen, kept fixed).  At step `j`, the already-placed vertices are `fz ∪ l.take j`,
and the finitely many affine spans of `y '' T ∪ S` (`T ⊆ fz ∪ l.take j`, `S ∈ Fixed`) are either
already everything (no condition) or proper, hence avoidable inside the ε-ball by
`Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace` (a proper affine subspace of `ℝⁿ` is
closed with empty interior).  Implement by recursion on `l` (`List.rec` or `List.foldl`), keeping the
already-placed coordinates fixed.  `l.Nodup` is needed so that `l[j] ∉ (l.take j).toFinset`. -/
theorem exists_avoiding_list {n : ℕ} {ι : Type*} [DecidableEq ι]
    (fz : Finset ι) (y₀ : ι → PL.E n) (l : List ι) (hl : ∀ i, i ∈ l ↔ i ∉ fz) (hl' : l.Nodup)
    (Fixed : Finset (Finset (PL.E n))) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ι → PL.E n, (∀ i, dist (y i) (y₀ i) < ε) ∧ (∀ i ∈ fz, y i = y₀ i) ∧
      ∀ j (hj : j < l.length), ∀ T : Finset ι, T ⊆ fz ∪ (l.take j).toFinset →
        (y (l[j]) ∈ (affineSpan ℝ (y '' (T : Set ι)) : Set (PL.E n)) →
            affineSpan ℝ (y '' (T : Set ι)) = ⊤) ∧
        (∀ S ∈ Fixed, y (l[j]) ∈
            (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n)) →
          affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) = ⊤) := by
  classical
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_prefix_good fz y₀ l hl hl' Fixed ε hε
  refine ⟨y, ?_, hy1, ?_⟩
  · intro i
    by_cases hi : i ∈ fz
    · rw [hy1 i hi, dist_self]
      exact hε
    · have hmem : i ∈ (l.take l.length).toFinset := by
        rw [List.take_length]
        exact (List.mem_toFinset).mpr ((hl i).mpr hi)
      exact hy2 i hmem
  · intro j hj T hT
    exact hy3 j hj hj T hT

end Work.PL.Generic
