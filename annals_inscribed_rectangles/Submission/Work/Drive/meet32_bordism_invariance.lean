import Mathlib
import Submission.Work.Drive.SeamMeetDefs
import Submission.Work.Drive.manifold_triple_inter_boundary_parity
import Submission.Work.Drive.manifold_triple_seam_cancel

/-!
# The `3 + 2 + 2` bordism invariance of the triple intersection number in a `3`-manifold

`Work.Drive.manifold_triple_inter_boundary_parity` gives the parity of the *total* boundary triple
intersection count of three `3`-chains in a smooth `4`-manifold, and
`Work.Drive.manifold_triple_seam_cancel` shows that the seam contributions cancel when each chain is
invariant under the antipodal involution of its parameter square.  This file draws the conclusion that
the chain route needs: for the chains of the **`3 + 2 + 2`** pattern — one `3`-chain (`D 0`) whose `x 2`
direction is the bordism direction, and two further chains (`D 1`, `D 2`) which are *closed* surfaces
whose parameter never reaches the slices `x 2 = 0`, `x 2 = 1` (the situation obtained by encoding a
bordism of `2`-cycles in a `3`-manifold into a `4`-manifold with a pinned interior time coordinate, see
`Submission/Work/Drive/MANIFOLD_PARITY_ENCODING.md`) — the **two ends of the bordism have the same
triple intersection number**:

> `Even ((topBdryMeet M D 0).ncard + (bottomBdryMeet M D 0).ncard)`.

This is the *manifold* form of the vector-space theorem
`Work.Drive.even_ncard_wFaceMeet_add_wFaceMeet`/`tri3Count_eq_of_bordism_closed` of
`Submission/Work/Drive/intersection_bordism3.lean`, i.e. the bordism invariance of the mod-2 triple
intersection number of `2`-cycles in a `3`-manifold.  It is what the *end contribution* of the chain
route needs (`ENDS_AND_SEAMS_NOTES.md`, `TRI3_BORDISM_STATUS.md`): it is what allows the bottom faces of
the sweeps to be replaced by *linear* projective planes, where the count is `1` by
`Work.Drive.projective_planes_meet_oddly`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## The boundary of the parameter cube: seams and the two slices -/

/-- **The boundary of the parameter cube, split into the seam and the two sweep faces.**  For a point of
the box, being on the boundary is the same as being on one of the four seam faces `x 0, x 1 ∈ {0,1}` or
on one of the two slices `x 2 = 0`, `x 2 = 1`. -/
theorem mem_unitBoxBdry_three_iff {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ Submission.Drive.unitBox 2) :
    x ∈ Submission.Drive.unitBoxBdry 2 ↔ onSeam x ∨ x 2 = 0 ∨ x 2 = 1 := by
  constructor
  · rintro ⟨_, i, hi⟩
    fin_cases i
    · rcases hi with h | h
      · exact Or.inl (Or.inl (by simpa using h))
      · exact Or.inl (Or.inr (Or.inl (by simpa using h)))
    · rcases hi with h | h
      · exact Or.inl (Or.inr (Or.inr (Or.inl (by simpa using h))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (by simpa using h))))
    · rcases hi with h | h
      · exact Or.inr (Or.inl (by simpa using h))
      · exact Or.inr (Or.inr (by simpa using h))
  · intro h
    refine ⟨hx, ?_⟩
    rcases h with (h | h | h | h) | h | h
    · exact ⟨0, Or.inl h⟩
    · exact ⟨0, Or.inr h⟩
    · exact ⟨1, Or.inl h⟩
    · exact ⟨1, Or.inr h⟩
    · exact ⟨2, Or.inl h⟩
    · exact ⟨2, Or.inr h⟩

/-- **The boundary triple intersections split into the seams and the two slices.** -/
theorem tripleBdryMeet_eq_union (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) :
    tripleBdryMeet M D k
      = seamBdryMeet M D k ∪ topBdryMeet M D k ∪ bottomBdryMeet M D k := by
  ext x
  constructor
  · intro hx
    obtain ⟨hbox, h01, h02, hbdy⟩ := hx
    have hsplit := (mem_unitBoxBdry_three_iff (x := x k) (hbox k)).mp hbdy
    have htbm : x ∈ tripleBdryMeet M D k := ⟨hbox, h01, h02, hbdy⟩
    rcases hsplit with h | h | h
    · exact Or.inl (Or.inl ⟨htbm, h⟩)
    · exact Or.inr ⟨htbm, h⟩
    · exact Or.inl (Or.inr ⟨htbm, h⟩)
  · intro hx
    simp only [Set.mem_union] at hx
    rcases hx with (hx | hx) | hx <;> exact hx.1

/-! ## The three kinds of boundary triple intersection are disjoint -/

/-- **Uniqueness of the face coordinate.**  This is the consequence of the face hypothesis `hface` of
`Work.Drive.manifold_triple_inter_boundary_parity` that is used for the bookkeeping: at a boundary triple
intersection exactly one coordinate of exactly one parameter is on a face, everything else strictly
interior. -/
def FaceUnique (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) : Prop :=
  ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3), x ∈ tripleBdryMeet M D 0 ∨
      x ∈ tripleBdryMeet M D 1 ∨ x ∈ tripleBdryMeet M D 2 →
    ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
      (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1)

/-- **The seam and the two slices are disjoint at boundary triple intersections.** -/
theorem disjoint_seam_top_bottom (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3)
    (huniq : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3), x ∈ tripleBdryMeet M D k →
      ∃ (k' : Fin 3) (i : Fin 3), (x k' i = 0 ∨ x k' i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k'' : Fin 3, k'' ≠ k' → ∀ j : Fin 3, x k'' j ∈ Set.Ioo (0 : ℝ) 1)) :
    Disjoint (seamBdryMeet M D k) (topBdryMeet M D k) ∧
      Disjoint (seamBdryMeet M D k) (bottomBdryMeet M D k) ∧
      Disjoint (topBdryMeet M D k) (bottomBdryMeet M D k) := by
  -- a boundary triple with a seam coordinate and a slice coordinate would have two face coordinates
  have key : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3), x ∈ tripleBdryMeet M D k →
      ¬ (onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1)) := by
    rintro x hx ⟨hseam, hslice⟩
    obtain ⟨k', i, hfacei, hrest, hother⟩ := huniq x hx
    -- the seam coordinate forces `k' = k` and `i ∈ {0,1}`
    have hk' : k' = k := by
      by_contra hne
      have hne' : k ≠ k' := fun h => hne h.symm
      rcases hseam with h | h | h | h
      · have hlt := (hother k hne' 0).1
        rw [h] at hlt; exact absurd hlt (lt_irrefl 0)
      · have hlt := (hother k hne' 0).2
        rw [h] at hlt; exact absurd hlt (lt_irrefl 1)
      · have hlt := (hother k hne' 1).1
        rw [h] at hlt; exact absurd hlt (lt_irrefl 0)
      · have hlt := (hother k hne' 1).2
        rw [h] at hlt; exact absurd hlt (lt_irrefl 1)
    subst hk'
    have hi : i ≠ 2 := by
      intro hi2
      subst hi2
      have h0 := hrest 0 (by decide)
      have h1 := hrest 1 (by decide)
      rcases hseam with h | h | h | h
      · exact absurd h0.1 (by rw [h]; norm_num)
      · exact absurd h0.2 (by rw [h]; norm_num)
      · exact absurd h1.1 (by rw [h]; norm_num)
      · exact absurd h1.2 (by rw [h]; norm_num)
    have h2 := hrest 2 (Ne.symm hi)
    rcases hslice with h | h
    · rw [h] at h2; exact absurd h2.1 (lt_irrefl 0)
    · rw [h] at h2; exact absurd h2.2 (lt_irrefl 1)
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro x ⟨hx, hs⟩ ⟨-, ht⟩
    exact key x hx ⟨hs, Or.inr ht⟩
  · rw [Set.disjoint_left]
    rintro x ⟨hx, hs⟩ ⟨-, hb⟩
    exact key x hx ⟨hs, Or.inl hb⟩
  · rw [Set.disjoint_left]
    rintro x ⟨-, ht⟩ ⟨-, hb⟩
    rw [ht] at hb
    exact absurd hb (by norm_num)


/-! ## The `3 + 2 + 2` bordism invariance -/

/-- **The bordism invariance of the triple intersection number of `2`-cycles in a `3`-manifold**, in the
manifold form used by the end contribution of the chain route.

If the three chains `D 0`, `D 1`, `D 2` of `Work.Drive.manifold_triple_inter_boundary_parity` satisfy the
additional structural hypotheses of the `3 + 2 + 2` pattern,

* `D 1` and `D 2` meet their own `x 2`-slices in no boundary triple intersection (their boundary triples
  are all seams: `tripleBdryMeet M D k ⊆ seamBdryMeet M D k` for `k = 1, 2`) — which is what the encoding
  of a bordism of `2`-cycles with a pinned interior time coordinate produces —

then the two ends of the bordism `D 0` have the same triple intersection number with `D 1` and `D 2`:

`Even ((topBdryMeet M D 0).ncard + (bottomBdryMeet M D 0).ncard)`.

This is the manifold form of `Work.Drive.even_ncard_wFaceMeet_add_wFaceMeet`
(`Submission/Work/Drive/intersection_bordism3.lean`). -/
theorem even_ncard_topBdryMeet_add_bottomBdryMeet (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      Work.Drive.TripleTransverse
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)))
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
      ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          Work.Drive.TripleCommonDir
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)) v ∧
          v k i ≠ 0)
    (hseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), Work.Drive.onSeam x →
      D k x = D k (Work.Drive.seamInv x))
    (h₁ : tripleBdryMeet M D 1 ⊆ seamBdryMeet M D 1)
    (h₂ : tripleBdryMeet M D 2 ⊆ seamBdryMeet M D 2) :
    Even ((topBdryMeet M D 0).ncard + (bottomBdryMeet M D 0).ncard) := by
  classical
  obtain ⟨hfin, hpar⟩ := manifold_triple_inter_boundary_parity M D hD htrans hface
  obtain ⟨hseamfin, hseameven⟩ := manifold_triple_seam_cancel M D hD htrans hface hseam
  -- uniqueness of the face coordinate at every boundary triple intersection
  have huniq : ∀ k : Fin 3, ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      x ∈ tripleBdryMeet M D k →
      ∃ (k' : Fin 3) (i : Fin 3), (x k' i = 0 ∨ x k' i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k'' : Fin 3, k'' ≠ k' → ∀ j : Fin 3, x k'' j ∈ Set.Ioo (0 : ℝ) 1) := by
    intro k x hx
    obtain ⟨hbox, h01, h02, hbdy⟩ := hx
    obtain ⟨k', i, hi, hrest, hother, -⟩ := hface x hbox h01 h02 ⟨k, hbdy⟩
    exact ⟨k', i, hi, hrest, hother⟩
  -- finiteness of the pieces
  have hfinTop : ∀ k : Fin 3, (topBdryMeet M D k).Finite :=
    fun k => (hfin k).subset (fun x hx => hx.1)
  have hfinBot : ∀ k : Fin 3, (bottomBdryMeet M D k).Finite :=
    fun k => (hfin k).subset (fun x hx => hx.1)
  -- disjointness of the three kinds of boundary triple intersection
  have hdisj : ∀ k : Fin 3, Disjoint (seamBdryMeet M D k) (topBdryMeet M D k) ∧
      Disjoint (seamBdryMeet M D k) (bottomBdryMeet M D k) ∧
      Disjoint (topBdryMeet M D k) (bottomBdryMeet M D k) :=
    fun k => disjoint_seam_top_bottom M D k (huniq k)
  -- the decomposition of the boundary count
  have hdec : ∀ k : Fin 3, (tripleBdryMeet M D k).ncard
      = (seamBdryMeet M D k).ncard + (topBdryMeet M D k).ncard
        + (bottomBdryMeet M D k).ncard := by
    intro k
    have hd : Disjoint (seamBdryMeet M D k ∪ topBdryMeet M D k) (bottomBdryMeet M D k) := by
      rw [Set.disjoint_left]
      intro x hx hc
      rcases hx with hx | hx
      · exact (Set.disjoint_left.mp (hdisj k).2.1) hx hc
      · exact (Set.disjoint_left.mp (hdisj k).2.2) hx hc
    rw [tripleBdryMeet_eq_union M D k, Set.ncard_union_eq hd
        ((hseamfin k).union (hfinTop k)) (hfinBot k),
      Set.ncard_union_eq (hdisj k).1 (hseamfin k) (hfinTop k)]
  -- the two outer chains have no top and bottom boundary triple intersections
  have hempty_of : ∀ k : Fin 3, tripleBdryMeet M D k ⊆ seamBdryMeet M D k →
      topBdryMeet M D k = ∅ ∧ bottomBdryMeet M D k = ∅ := by
    intro k hk
    constructor
    · refine Set.subset_empty_iff.mp (fun x hx => ?_)
      exact (Set.disjoint_left.mp (hdisj k).1) (hk hx.1) hx
    · refine Set.subset_empty_iff.mp (fun x hx => ?_)
      exact (Set.disjoint_left.mp (hdisj k).2.1) (hk hx.1) hx
  obtain ⟨htop1, hbot1⟩ := hempty_of 1 h₁
  obtain ⟨htop2, hbot2⟩ := hempty_of 2 h₂
  have hn1 : (topBdryMeet M D 1).ncard = 0 := by rw [htop1, Set.ncard_empty]
  have hn1' : (bottomBdryMeet M D 1).ncard = 0 := by rw [hbot1, Set.ncard_empty]
  have hn2 : (topBdryMeet M D 2).ncard = 0 := by rw [htop2, Set.ncard_empty]
  have hn2' : (bottomBdryMeet M D 2).ncard = 0 := by rw [hbot2, Set.ncard_empty]
  -- the other two boundary counts are the seam counts, hence even
  have heven1 : Even (tripleBdryMeet M D 1).ncard := by
    rw [hdec 1, hn1, hn1']; simpa using hseameven 1
  have heven2 : Even (tripleBdryMeet M D 2).ncard := by
    rw [hdec 2, hn2, hn2']; simpa using hseameven 2
  -- the total boundary count is even, so the first block's count is even
  have h011 : Even ((tripleBdryMeet M D 0).ncard + (tripleBdryMeet M D 1).ncard) :=
    (Nat.even_add.mp hpar).mpr heven2
  have heven0 : Even (tripleBdryMeet M D 0).ncard :=
    (Nat.even_add.mp h011).mpr heven1
  -- and removing the (even) seam contribution gives the two ends
  rw [hdec 0] at heven0
  have hassoc : Even ((seamBdryMeet M D 0).ncard
      + ((topBdryMeet M D 0).ncard + (bottomBdryMeet M D 0).ncard)) := by
    simpa [Nat.add_assoc] using heven0
  exact (Nat.even_add.mp hassoc).mp (hseameven 0)


/-! ## The encoding of a bordism of `2`-cycles in a `3`-manifold

`Work.Drive.encodedChains` is the family of three chains of the `4`-manifold `M × ℝ` produced by a
bordism `W` of `2`-cycles in a `3`-manifold `M` and two `2`-cycles `A`, `B`: the bordism is put in the
slice `M × {c}` with `c` a fixed *interior* value, and the two `2`-cycles are thickened by their third
parameter, which is then pinned to `c` by the triple intersection condition.  See
`Submission/Work/Drive/MANIFOLD_PARITY_ENCODING.md`. -/

/-- The point `(a, b)` of the parameter square, as an element of `EuclideanSpace ℝ (Fin 2)`. -/
def pt2 (a b : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i : Fin 2 => if i = 0 then a else b

@[simp] lemma pt2_zero (a b : ℝ) : pt2 a b 0 = a := by simp [pt2]
@[simp] lemma pt2_one (a b : ℝ) : pt2 a b 1 = b := by simp [pt2]

/-- **The encoded chains of a bordism of `2`-cycles.**  `encodedChains W A B c 0` is the bordism `W`
(taken at the interior time `c`), and `encodedChains W A B c 1`, `encodedChains W A B c 2` are the two
`2`-cycles `A`, `B`, thickened by their third parameter. -/
def encodedChains {M : Type*} (W : EuclideanSpace ℝ (Fin 3) → M)
    (A B : EuclideanSpace ℝ (Fin 2) → M) (c : ℝ) :
    Fin 3 → EuclideanSpace ℝ (Fin 3) → M × ℝ :=
  fun k => if k = 0 then fun x => (W x, c)
    else if k = 1 then fun x => (A (pt2 (x 0) (x 1)), x 2)
    else fun x => (B (pt2 (x 0) (x 1)), x 2)

@[simp] lemma encodedChains_zero {M : Type*} (W : EuclideanSpace ℝ (Fin 3) → M)
    (A B : EuclideanSpace ℝ (Fin 2) → M) (c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    encodedChains W A B c 0 x = (W x, c) := by
  simp [encodedChains]

@[simp] lemma encodedChains_one {M : Type*} (W : EuclideanSpace ℝ (Fin 3) → M)
    (A B : EuclideanSpace ℝ (Fin 2) → M) (c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    encodedChains W A B c 1 x = (A (pt2 (x 0) (x 1)), x 2) := by
  simp [encodedChains]

@[simp] lemma encodedChains_two {M : Type*} (W : EuclideanSpace ℝ (Fin 3) → M)
    (A B : EuclideanSpace ℝ (Fin 2) → M) (c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    encodedChains W A B c 2 x = (B (pt2 (x 0) (x 1)), x 2) := by
  simp [encodedChains]


/-! ## A packaged interface for the hypotheses of the triple-intersection engine

The engine `Work.Drive.manifold_triple_inter_boundary_parity` (and the invariance theorem above) take
four long hypotheses on the three chains: smoothness, transversality, the face condition and the seam
invariance.  Packaging them as a `Prop`-valued structure makes them a single object, which is what the
*applications* (concrete chains built from plane presentations, and the encoded chains of
`Work.Drive.encodedChains`) have to produce. -/

/-- **The hypotheses of the manifold triple-intersection parity, packaged**: smoothness of the three
chains, transversality of the triple at every meeting point of the box, the face condition (at every
boundary meeting point exactly one coordinate of exactly one parameter is on a face, and the
intersection curve crosses it) and the invariance of each chain under the antipodal involution of its
parameter square on the seam. -/
structure Meet3Hyp (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) : Prop where
  smooth : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k)
  trans : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      TripleTransverse
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2))
  face : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
      ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          TripleCommonDir
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)) v ∧
          v k i ≠ 0
  seam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), onSeam x → D k x = D k (seamInv x)

/-- **The bordism invariance of the triple intersection number, for chains satisfying the packaged
hypotheses and whose last two blocks meet the slices only on their seams.**  This is
`Work.Drive.even_ncard_topBdryMeet_add_bottomBdryMeet` with the hypotheses grouped in `Meet3Hyp`. -/
theorem even_ncard_topBdryMeet_add_bottomBdryMeet' (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (h : Meet3Hyp M D)
    (h₁ : tripleBdryMeet M D 1 ⊆ seamBdryMeet M D 1)
    (h₂ : tripleBdryMeet M D 2 ⊆ seamBdryMeet M D 2) :
    Even ((topBdryMeet M D 0).ncard + (bottomBdryMeet M D 0).ncard) :=
  even_ncard_topBdryMeet_add_bottomBdryMeet M D h.smooth h.trans h.face h.seam h₁ h₂

end

end Work.Drive
