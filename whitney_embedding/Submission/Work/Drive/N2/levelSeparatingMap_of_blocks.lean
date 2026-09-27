import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.GoodDrawingFamily

/-!
# `levelSeparatingMap_of_blocks`: the global assembly of the compact `n = 2` movie (H7's lane)

The value axis is covered by the blocks attached to the critical values `s : Fin (n+1) → ℝ` — the
first `n` entries being the sorted critical values and `s (last)` a dummy above all of them — with a
single `η > 0`:

| index | block | values |
|---|---|---|
| `(j, 0)` | lower collar of `s j` | `(s j - η, s j - η/2)` |
| `(j, 1)` | window of `s j`      | `(s j - 5η/8, s j + 5η/8)` |
| `(j, 2)` | upper collar of `s j`| `(s j + η/2, s j + η)` |
| `(j, 3)` | band above `s j`     | `(s j + 3η/4, s (j+1) - 3η/4)` |

Consecutive blocks overlap, and any two blocks *not* consecutive are disjoint — the overlap graph is
the path `(0,0)-(0,1)-(0,2)-(0,3)-(1,0)-…-((n-1),3)`.  Hence `goodDrawing_of_family` applies as soon
as each block carries a good drawing and *consecutive* blocks agree on their overlap; the agreements
of non-consecutive pairs are vacuous.  Every endpoint is `s (something) ± const`, so all the interval
arithmetic is linear.

This file contains the value-axis bookkeeping: the blocks are open, every value of `f` in the range
lies in a block (`exists_mem_blockSet`), non-consecutive blocks are separated
(`blockHi_le_blockLo_of_separated`) and the assembly (`levelSeparatingMap_of_blocks`) reduces the
target to the per-block `GoodDrawingOn` rows and the consecutive agreements.
-/

namespace Work.Drive.N2

open Set Filter
open scoped Topology ContDiff Manifold

variable {n : ℕ}

/-- The lower end of the `q`-th block of the value cover. -/
noncomputable def blockLo {n : ℕ} (s : Fin (n + 1) → ℝ) (η : ℝ) : Fin n × Fin 4 → ℝ :=
  fun q =>
    match q.2.val with
    | 0 => s (Fin.castSucc q.1) - η
    | 1 => s (Fin.castSucc q.1) - 5 * η / 8
    | 2 => s (Fin.castSucc q.1) + η / 2
    | _ => s (Fin.castSucc q.1) + 3 * η / 4

/-- The upper end of the `q`-th block of the value cover. -/
noncomputable def blockHi {n : ℕ} (s : Fin (n + 1) → ℝ) (η : ℝ) : Fin n × Fin 4 → ℝ :=
  fun q =>
    match q.2.val with
    | 0 => s (Fin.castSucc q.1) - η / 2
    | 1 => s (Fin.castSucc q.1) + 5 * η / 8
    | 2 => s (Fin.castSucc q.1) + η
    | _ => s (Fin.succ q.1) - 3 * η / 4

/-- The `q`-th block of the value cover. -/
noncomputable def blockSet {n : ℕ} (s : Fin (n + 1) → ℝ) (η : ℝ) (q : Fin n × Fin 4) : Set ℝ :=
  Set.Ioo (blockLo s η q) (blockHi s η q)

lemma isOpen_blockSet (s : Fin (n + 1) → ℝ) (η : ℝ) (q : Fin n × Fin 4) :
    IsOpen (blockSet s η q) := isOpen_Ioo

lemma blockSet_zero (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockSet s η (j, 0) = Set.Ioo (s (Fin.castSucc j) - η) (s (Fin.castSucc j) - η / 2) := rfl

lemma blockSet_one (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockSet s η (j, 1) = Set.Ioo (s (Fin.castSucc j) - 5 * η / 8)
      (s (Fin.castSucc j) + 5 * η / 8) := rfl

lemma blockSet_two (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockSet s η (j, 2) = Set.Ioo (s (Fin.castSucc j) + η / 2) (s (Fin.castSucc j) + η) := rfl

lemma blockSet_three (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockSet s η (j, 3) = Set.Ioo (s (Fin.castSucc j) + 3 * η / 4) (s (Fin.succ j) - 3 * η / 4) :=
  rfl

lemma blockLo_zero (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockLo s η (j, 0) = s (Fin.castSucc j) - η := rfl

lemma blockLo_one (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockLo s η (j, 1) = s (Fin.castSucc j) - 5 * η / 8 := rfl

lemma blockLo_two (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockLo s η (j, 2) = s (Fin.castSucc j) + η / 2 := rfl

lemma blockLo_three (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockLo s η (j, 3) = s (Fin.castSucc j) + 3 * η / 4 := rfl

lemma blockHi_zero (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockHi s η (j, 0) = s (Fin.castSucc j) - η / 2 := rfl

lemma blockHi_one (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockHi s η (j, 1) = s (Fin.castSucc j) + 5 * η / 8 := rfl

lemma blockHi_two (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockHi s η (j, 2) = s (Fin.castSucc j) + η := rfl

lemma blockHi_three (s : Fin (n + 1) → ℝ) (η : ℝ) (j : Fin n) :
    blockHi s η (j, 3) = s (Fin.succ j) - 3 * η / 4 := rfl

open Classical in
/-- **The cover.**  Every value between `s 0` and `s (last)` lies in one of the blocks. -/
theorem exists_mem_blockSet {s : Fin (n + 1) → ℝ} {η : ℝ} (hs : StrictMono s) (hn : 0 < n)
    (hη : 0 < η) {t : ℝ} (hlo : s 0 ≤ t)
    (hhi : t ≤ s (Fin.castSucc ⟨n - 1, by omega⟩)) :
    ∃ q : Fin n × Fin 4, t ∈ blockSet s η q := by
  classical
  let J : Finset (Fin n) := Finset.univ.filter (fun j => s (Fin.castSucc j) ≤ t)
  have hJ : J.Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hlo⟩⟩
  let j : Fin n := J.max' hJ
  have hjmem : s (Fin.castSucc j) ≤ t := (Finset.mem_filter.mp (Finset.max'_mem J hJ)).2
  have hjmax : ∀ i : Fin n, s (Fin.castSucc i) ≤ t → i ≤ j := fun i hi =>
    Finset.le_max' J i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hnext : t < s (Fin.succ j) := by
    by_cases hjlt : (j : ℕ) + 1 < n
    · have h1 : Fin.castSucc (⟨(j : ℕ) + 1, hjlt⟩ : Fin n) = Fin.succ j := by
        ext; simp [Fin.castSucc, Fin.succ]
      have h2 : ¬ (s (Fin.succ j) ≤ t) := by
        intro hcon
        have h3 : (⟨(j : ℕ) + 1, hjlt⟩ : Fin n) ≤ j := hjmax _ (by rw [h1]; exact hcon)
        have h4 : ((j : ℕ) + 1) ≤ (j : ℕ) := Fin.le_def.mp h3
        omega
      exact not_le.mp h2
    · have hjeq : (j : ℕ) = n - 1 := by have := j.isLt; omega
      have hjcast : j = ⟨n - 1, by omega⟩ := Fin.ext (by simp [hjeq])
      have hlt : s (Fin.castSucc j) < s (Fin.succ j) := hs (Fin.castSucc_lt_succ (i := j))
      exact lt_of_le_of_lt (hjcast ▸ hhi) hlt
  by_cases h1 : t ≤ s (Fin.castSucc j) + η / 2
  · refine ⟨(j, 1), ?_⟩
    rw [blockSet_one]
    exact ⟨by linarith [hjmem, hη], by linarith [h1, hη]⟩
  · push_neg at h1
    by_cases h2 : t ≤ s (Fin.castSucc j) + 3 * η / 4
    · refine ⟨(j, 2), ?_⟩
      rw [blockSet_two]
      exact ⟨h1, by linarith [h2, hη]⟩
    · push_neg at h2
      by_cases h3 : t < s (Fin.succ j) - 3 * η / 4
      · refine ⟨(j, 3), ?_⟩
        rw [blockSet_three]
        exact ⟨h2, h3⟩
      · push_neg at h3
        -- now `j` is not the last index
        have hjn : (j : ℕ) + 1 < n := by
          by_contra hcon
          have hjeq : (j : ℕ) = n - 1 := by have := j.isLt; omega
          have hjcast : j = ⟨n - 1, by omega⟩ := Fin.ext (by simp [hjeq])
          have ht : t ≤ s (Fin.castSucc j) := by rw [hjcast]; exact hhi
          linarith
        have hsucc : (Fin.succ j : Fin (n + 1)) = Fin.castSucc (⟨(j : ℕ) + 1, hjn⟩ : Fin n) := by
          ext; simp [Fin.succ, Fin.castSucc]
        by_cases h4 : t < s (Fin.succ j) - η / 2
        · refine ⟨(⟨(j : ℕ) + 1, hjn⟩, 0), ?_⟩
          rw [blockSet_zero, ← hsucc]
          exact ⟨by linarith [h3, hη], h4⟩
        · push_neg at h4
          refine ⟨(⟨(j : ℕ) + 1, hjn⟩, 1), ?_⟩
          rw [blockSet_one, ← hsucc]
          exact ⟨by linarith [h4, hη], by linarith [hnext, hη]⟩

/-- The position of a block along the value axis: `(j,0),(j,1),(j,2),(j,3),(j+1,0),…`. -/
def blkIndex (q : Fin n × Fin 4) : ℕ := 4 * (q.1 : ℕ) + q.2.val

/-- Two blocks are **consecutive** when their positions along the value axis differ by one: those are
exactly the pairs whose value intervals overlap. -/
def Consecutive (q q' : Fin n × Fin 4) : Prop :=
  blkIndex q + 1 = blkIndex q' ∨ blkIndex q' + 1 = blkIndex q

/-- The position determines the block. -/
lemma blkIndex_inj : Function.Injective (blkIndex (n := n)) := by
  intro q q' h
  obtain ⟨j, c⟩ := q
  obtain ⟨j', c'⟩ := q'
  simp only [blkIndex] at h
  have hc : c.val < 4 := c.isLt
  have hc' : c'.val < 4 := c'.isLt
  have h1 : c.val = c'.val := by omega
  have h2 : (j : ℕ) = (j' : ℕ) := by omega
  rw [Fin.ext h2, Fin.ext h1]

/-- The gap hypothesis, in the form used below. -/
lemma gapAt {s : Fin (n + 1) → ℝ} {η : ℝ}
    (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j)) (i : Fin n) :
    s (Fin.castSucc i) + 4 * η < s (Fin.succ i) := hgap i

/-- **The two-step separation of blocks.**  With the gap hypothesis `s j + 4η < s (j+1)`, a block and
any block two or more positions later have disjoint value intervals. -/
theorem blockHi_le_blockLo_of_separated {s : Fin (n + 1) → ℝ} {η : ℝ} (hs : StrictMono s)
    (hη : 0 < η) (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j))
    {q q' : Fin n × Fin 4} (h : blkIndex q + 2 ≤ blkIndex q') :
    blockHi s η q ≤ blockLo s η q' := by
  obtain ⟨j, c⟩ := q
  obtain ⟨j', c'⟩ := q'
  simp only [blkIndex] at h
  have hc : c.val < 4 := c.isLt
  have hc' : c'.val < 4 := c'.isLt
  have hjle : (j : ℕ) ≤ (j' : ℕ) := by omega
  -- the lower end of any block is at least `s j' - η`; at least `s j' - 5η/8` when `c' ≥ 1`
  have hLo : s (Fin.castSucc j') - η ≤ blockLo s η (j', c') := by
    rcases (show c'.val = 0 ∨ c'.val = 1 ∨ c'.val = 2 ∨ c'.val = 3 by omega)
      with h0 | h1 | h2 | h3
    · rw [show c' = 0 from Fin.ext h0, blockLo_zero] <;> linarith [hη]
    · rw [show c' = 1 from Fin.ext h1, blockLo_one] <;> linarith [hη]
    · rw [show c' = 2 from Fin.ext h2, blockLo_two] <;> linarith [hη]
    · rw [show c' = 3 from Fin.ext h3, blockLo_three] <;> linarith [hη]
  have hLo' : 1 ≤ c'.val → s (Fin.castSucc j') - 5 * η / 8 ≤ blockLo s η (j', c') := by
    intro hc1
    rcases (show c'.val = 1 ∨ c'.val = 2 ∨ c'.val = 3 by omega) with h1 | h2 | h3
    · rw [show c' = 1 from Fin.ext h1, blockLo_one] <;> linarith [hη]
    · rw [show c' = 2 from Fin.ext h2, blockLo_two] <;> linarith [hη]
    · rw [show c' = 3 from Fin.ext h3, blockLo_three] <;> linarith [hη]
  -- the upper end of a block with `c ≤ 2` is at most `s j + η`
  have hHi2 : c.val ≤ 2 → blockHi s η (j, c) ≤ s (Fin.castSucc j) + η := by
    intro hc2
    rcases (show c.val = 0 ∨ c.val = 1 ∨ c.val = 2 by omega) with h0 | h1 | h2
    · rw [show c = 0 from Fin.ext h0, blockHi_zero] <;> linarith [hη]
    · rw [show c = 1 from Fin.ext h1, blockHi_one] <;> linarith [hη]
    · rw [show c = 2 from Fin.ext h2, blockHi_two] <;> linarith [hη]
  rcases lt_trichotomy ((j : ℕ) + 1) ((j' : ℕ)) with h1 | h1 | h1
  · -- `j + 1 < j'`: the gap leaves room in both cases
    have hmono1 : s (Fin.castSucc j) + η ≤ s (Fin.castSucc j') - η := by
      have h2 : s (Fin.castSucc j) + 4 * η < s (Fin.castSucc j') := by
        have h3 : s (Fin.castSucc j) + 4 * η < s (Fin.succ j) := gapAt hgap j
        have h4 : s (Fin.succ j) ≤ s (Fin.castSucc j') := by
          refine hs.monotone ?_
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          omega
        linarith
      linarith
    have hmono2 : s (Fin.succ j) - 3 * η / 4 ≤ s (Fin.castSucc j') - η := by
      have hjn : (j : ℕ) + 1 < n := by omega
      have hj2 : (j : ℕ) + 2 < n := by omega
      have h3 : s (Fin.castSucc (⟨(j : ℕ) + 1, hjn⟩ : Fin n)) + 4 * η <
          s (Fin.succ (⟨(j : ℕ) + 1, hjn⟩ : Fin n)) := gapAt hgap ⟨(j : ℕ) + 1, hjn⟩
      have h4 : Fin.succ (⟨(j : ℕ) + 1, hjn⟩ : Fin n) = ⟨(j : ℕ) + 2, by omega⟩ := Fin.ext rfl
      have h5 : (⟨(j : ℕ) + 1, hjn⟩ : Fin n).castSucc = Fin.succ j := Fin.ext rfl
      rw [h4] at h3
      have h6 : s ⟨(j : ℕ) + 2, by omega⟩ ≤ s (Fin.castSucc j') := by
        refine hs.monotone ?_
        simp only [Fin.le_def, Fin.val_castSucc]
        omega
      rw [h5] at h3
      linarith
    by_cases hc2 : c.val ≤ 2
    · exact le_trans (le_trans (hHi2 hc2) hmono1) hLo
    · have hce : c = 3 := Fin.ext (by omega)
      rw [hce, blockHi_three]
      exact le_trans hmono2 hLo
  · -- `j + 1 = j'`
    have hcast : (⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ : Fin n) = j' := Fin.ext (by simp [h1])
    have hsucc : Fin.succ j = Fin.castSucc (⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ : Fin n) :=
      Fin.ext (by simp [Fin.succ, Fin.castSucc])
    by_cases hc2 : c.val ≤ 2
    · have hkey : s (Fin.castSucc j) + η ≤ s (Fin.castSucc j') - η := by
        have hjn : (j : ℕ) + 1 < n := by omega
        have h2 : s (Fin.castSucc j) + 4 * η < s (Fin.succ j) := gapAt hgap j
        rw [show Fin.succ j = Fin.castSucc (⟨(j : ℕ) + 1, hjn⟩ : Fin n) from Fin.ext rfl,
          hcast] at h2
        linarith
      exact le_trans (le_trans (hHi2 hc2) hkey) hLo
    · have hce : c = 3 := Fin.ext (by omega)
      have hc1 : 1 ≤ c'.val := by omega
      rw [hce, blockHi_three, hsucc, hcast]
      linarith [hLo' hc1, hη]
  · -- `j' ≤ j`, hence `j = j'` and only the same-index pairs remain
    have h2 : (j : ℕ) = (j' : ℕ) := by omega
    have hjeq : j = j' := Fin.ext h2
    subst hjeq
    have hc2 : c.val ≤ 2 := by omega
    by_cases hc1 : c.val ≤ 1
    · by_cases h3 : c.val = 0
      · have hce : c = 0 := Fin.ext h3
        rw [hce, blockHi_zero]
        have h4 : c'.val = 2 ∨ c'.val = 3 := by omega
        rcases h4 with h4 | h4
        · rw [show c' = 2 from Fin.ext h4, blockLo_two] <;> linarith [hη]
        · rw [show c' = 3 from Fin.ext h4, blockLo_three] <;> linarith [hη]
      · have hce : c = 1 := Fin.ext (by omega)
        rw [hce, blockHi_one]
        have h4 : c'.val = 3 := by omega
        rw [show c' = 3 from Fin.ext h4, blockLo_three] <;> linarith [hη]
    · have hce : c = 3 := Fin.ext (by omega)
      rw [hce, blockHi_three]
      have h4 : c'.val = 0 ∨ c'.val = 1 := by omega
      rcases h4 with h4 | h4
      · rw [show c' = 0 from Fin.ext h4, blockLo_zero]
        linarith [hs (Fin.castSucc_lt_succ (i := j)), hη]
      · rw [show c' = 1 from Fin.ext h4, blockLo_one]
        linarith [hs (Fin.castSucc_lt_succ (i := j)), hη]

/-- **Non-consecutive blocks are disjoint.** -/
theorem disjoint_blockSet_of_not_consecutive {s : Fin (n + 1) → ℝ} {η : ℝ} (hs : StrictMono s)
    (hη : 0 < η) (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j))
    {q q' : Fin n × Fin 4} (hne : q ≠ q') (h : ¬ Consecutive q q') :
    Disjoint (blockSet s η q) (blockSet s η q') := by
  have hab : blkIndex q ≠ blkIndex q' := fun hc => hne (blkIndex_inj hc)
  rcases lt_or_ge (blkIndex q) (blkIndex q') with hlt | hle
  · have hsep : blockHi s η q ≤ blockLo s η q' :=
      blockHi_le_blockLo_of_separated hs hη hgap (by
        have h1 : blkIndex q + 1 ≠ blkIndex q' := fun hc => h (Or.inl hc)
        omega)
    refine Set.disjoint_left.mpr fun t ht ht' => ?_
    rw [blockSet] at ht ht'
    linarith [ht.2, hsep, ht'.1]
  · have hlt' : blkIndex q' < blkIndex q := lt_of_le_of_ne hle (Ne.symm hab)
    have hsep : blockHi s η q' ≤ blockLo s η q :=
      blockHi_le_blockLo_of_separated hs hη hgap (by
        have h1 : blkIndex q' + 1 ≠ blkIndex q := fun hc => h (Or.inr hc)
        omega)
    refine Set.disjoint_left.mpr fun t ht ht' => ?_
    rw [blockSet] at ht ht'
    linarith [ht'.2, hsep, ht.1]

/-- **The global assembly.**  With the blocks of the value cover, the per-block good-drawing rows,
the *consecutive* agreements and the separation of non-consecutive blocks, the target's conclusion
follows: `goodDrawing_of_family` pastes the blocks, every non-consecutive agreement being vacuous.

The separation of non-consecutive blocks (`disjoint_blockSet_of_not_consecutive`, from
`blockHi_le_blockLo_of_separated`) holds as soon as the critical values satisfy `s j + 4η < s (j+1)`;
all the endpoints are `s (·) ± const`, so it is linear arithmetic. -/
theorem levelSeparatingMap_of_blocks {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {n : ℕ} (hn : 0 < n) (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f)
    (s : Fin (n + 1) → ℝ) (hs : StrictMono s) (η : ℝ) (hη : 0 < η)
    (hlo : ∀ x : M, s 0 ≤ f x)
    (hhi : ∀ x : M, f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩))
    (g : Fin n × Fin 4 → M → EuclideanSpace ℝ (Fin 3))
    (hrows : ∀ q : Fin n × Fin 4, GoodDrawingOn f (blockSet s η q) (g q))
    (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j))
    (hadj : ∀ q q' : Fin n × Fin 4, Consecutive q q' → ∀ x : M,
      f x ∈ blockSet s η q → f x ∈ blockSet s η q' → g q x = g q' x) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ∞ G ∧
      (∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) G x v = 0 → v = 0) ∧
      (∀ x y : M, f x = f y → G x = G y → x = y) := by
  classical
  let e : Fin n × Fin 4 ≃ Fin (n * 4) := finProdFinEquiv
  have hmain := goodDrawing_of_family f hf.1 (fun k : Fin (n * 4) => blockSet s η (e.symm k))
    (fun k => isOpen_blockSet s η _) (fun k => g (e.symm k))
    (fun x => by
      obtain ⟨q, hq⟩ := exists_mem_blockSet hs hn hη (hlo x) (hhi x)
      exact ⟨e q, by simpa using hq⟩)
    (fun k => hrows _)
    (fun k l hkl x hx hy => by
      by_cases hc : Consecutive (e.symm k) (e.symm l)
      · exact hadj _ _ hc x hx hy
      · exact (Set.disjoint_left.mp (disjoint_blockSet_of_not_consecutive hs hη hgap (fun hcc => hkl (e.symm.injective hcc)) hc)
          hx hy).elim)
  exact hmain

end Work.Drive.N2
