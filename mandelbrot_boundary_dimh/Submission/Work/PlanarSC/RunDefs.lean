import Mathlib
import Submission.Work.PlanarSC.PolyTools

/-!
# Vertical runs of a polyomino

The vocabulary for the "run/tree" route to `Work.PlanarSC.polyomino_isRetract`.

For a finite set `S : Finset (ℤ × ℤ)` of *unit* lattice cells (`(k,m)` standing for the closed square
`[k,k+1] × [m,m+1]`), the maximal vertical blocks of `S` are called **runs**.  Each run is a closed
rectangle (a union of consecutive cells in one column); the runs cover the polyomino `polyK S`, and
two runs meet (in a rectangle, possibly degenerate) exactly when they lie in adjacent columns and
their row intervals overlap.
-/

open Set

namespace Work.PlanarSC

noncomputable section

/-! ## The vertical block through a cell -/

/-- Candidate bottoms of the maximal vertical block of `S` through `p`. -/
def blkBotAux (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) : Finset ℤ :=
  ((S.filter (fun q => q.1 = p.1)).image (fun q => q.2)).filter
    (fun m => m ≤ p.2 ∧ ∀ m' ∈ Finset.Icc m p.2, (p.1, m') ∈ S)

theorem p2_mem_blkBotAux (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ S) :
    p.2 ∈ blkBotAux S p := by
  rw [blkBotAux, Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩, le_rfl, ?_⟩
  intro m' hm'
  rw [Finset.mem_Icc] at hm'
  have h : m' = p.2 := le_antisymm hm'.2 hm'.1
  subst h; exact hp

/-- The bottom row of the maximal vertical block of `S` through the cell `p`. -/
def blkBot (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ S) : ℤ :=
  (blkBotAux S p).min' ⟨p.2, p2_mem_blkBotAux S p hp⟩

theorem blkBot_mem (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ S) :
    blkBot S p hp ∈ blkBotAux S p := by
  rw [blkBot]; exact Finset.min'_mem _ _

theorem blkBot_le (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ S) : blkBot S p hp ≤ p.2 :=
  ((Finset.mem_filter.mp (blkBot_mem S p hp)).2).1

theorem blkBot_cell (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ S) :
    (p.1, blkBot S p hp) ∈ S := by
  have h := (Finset.mem_filter.mp (blkBot_mem S p hp)).1
  obtain ⟨q, hq, hq2⟩ := Finset.mem_image.mp h
  rw [← hq2]
  have hq1 : q.1 = p.1 := (Finset.mem_filter.mp hq).2
  rw [← hq1]; exact (Finset.mem_filter.mp hq).1

theorem blkBot_all (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ S) :
    ∀ m ∈ Finset.Icc (blkBot S p hp) p.2, (p.1, m) ∈ S :=
  ((Finset.mem_filter.mp (blkBot_mem S p hp)).2).2

theorem blkBot_min (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ S) {m : ℤ} (hm : m ≤ p.2)
    (hall : ∀ m' ∈ Finset.Icc m p.2, (p.1, m') ∈ S) : blkBot S p hp ≤ m := by
  refine Finset.min'_le _ _ ?_
  rw [blkBotAux, Finset.mem_filter, Finset.mem_image]
  exact ⟨⟨(p.1, m), Finset.mem_filter.mpr ⟨hall m (Finset.mem_Icc.mpr ⟨le_rfl, hm⟩), rfl⟩, rfl⟩,
    hm, hall⟩

/-! ## The top of the block -/

/-- Top row of the maximal vertical block of `S` starting at the row of `r` in column `r.1`. -/
def runTopRow (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) : ℤ :=
  (insert r.2 ((Finset.Icc r.2 (r.2 + S.card)).filter
      (fun m => ∀ m' ∈ Finset.Icc r.2 m, (r.1, m') ∈ S))).max'
    (Finset.insert_nonempty r.2 _)

theorem runTopRow_ge (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) : r.2 ≤ runTopRow S r :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem runTopRow_mem (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) :
    runTopRow S r = r.2 ∨ (r.2 ≤ runTopRow S r ∧ runTopRow S r ≤ r.2 + S.card ∧
      ∀ m' ∈ Finset.Icc r.2 (runTopRow S r), (r.1, m') ∈ S) := by
  have h := Finset.max'_mem (insert r.2 ((Finset.Icc r.2 (r.2 + S.card)).filter
      (fun m => ∀ m' ∈ Finset.Icc r.2 m, (r.1, m') ∈ S))) (Finset.insert_nonempty r.2 _)
  rw [Finset.mem_insert] at h
  rcases h with h | h
  · left; rw [runTopRow, h]
  · right
    rw [Finset.mem_filter, Finset.mem_Icc] at h
    rw [runTopRow]
    exact ⟨h.1.1, h.1.2, h.2⟩

theorem runTopRow_all (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) (hr : r ∈ S) :
    ∀ m' ∈ Finset.Icc r.2 (runTopRow S r), (r.1, m') ∈ S := by
  rcases runTopRow_mem S r with h | ⟨-, -, h⟩
  · intro m' hm'
    rw [Finset.mem_Icc, h] at hm'
    have : m' = r.2 := le_antisymm hm'.2 hm'.1
    subst this; exact hr
  · exact h

theorem runTopRow_length (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) {m : ℤ} (hm : r.2 ≤ m)
    (hall : ∀ m' ∈ Finset.Icc r.2 m, (r.1, m') ∈ S) : m ≤ r.2 + S.card := by
  have hsub : (Finset.Icc r.2 m).image (fun m' => (r.1, m')) ⊆ S := by
    intro q hq
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hq
    exact hall m' hm'
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Int.card_Icc] at hcard
  have h1 : m - r.2 + 1 ≤ (S.card : ℤ) := by omega
  omega

theorem runTopRow_max (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) (hr : r ∈ S) {m : ℤ} (hm : r.2 ≤ m)
    (hall : ∀ m' ∈ Finset.Icc r.2 m, (r.1, m') ∈ S) : m ≤ runTopRow S r := by
  have hle := runTopRow_length S r hm hall
  rw [runTopRow]
  refine Finset.le_max' _ _ ?_
  rw [Finset.mem_insert]
  right
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hm, hle⟩, hall⟩

/-! ## The run bottoms -/

/-- The run bottoms of `S`: the occupied cells with the cell below them (in the same column)
unoccupied. -/
def runBottoms (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S.filter (fun p => (p.1, p.2 - 1) ∉ S)

theorem mem_runBottoms (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    p ∈ runBottoms S ↔ p ∈ S ∧ (p.1, p.2 - 1) ∉ S := Finset.mem_filter

theorem runBottoms_subset (S : Finset (ℤ × ℤ)) : runBottoms S ⊆ S :=
  Finset.filter_subset _ _

/-- The bottom cell of the run through `p` is a run bottom. -/
theorem blkBot_mem_runBottoms (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ S) :
    (p.1, blkBot S p hp) ∈ runBottoms S := by
  rw [mem_runBottoms]
  refine ⟨blkBot_cell S p hp, ?_⟩
  intro h
  have hb := blkBot_le S p hp
  have hmin := blkBot_min S p hp (m := blkBot S p hp - 1) (by omega) (fun m' hm' => ?_)
  · omega
  · rw [Finset.mem_Icc] at hm'
    by_cases hcase : m' = blkBot S p hp - 1
    · rw [hcase]; exact h
    · exact blkBot_all S p hp m' (Finset.mem_Icc.mpr ⟨by omega, hm'.2⟩)

/-! ## The rectangle of a run -/

/-- The closed rectangle of the maximal vertical block of `S` *starting at* the cell `r`. -/
def runRect (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (r.1 : ℝ) ≤ z.re ∧ z.re ≤ (r.1 : ℝ) + 1 ∧ (r.2 : ℝ) ≤ z.im ∧
    z.im ≤ (runTopRow S r : ℝ) + 1}

theorem mem_runRect {S : Finset (ℤ × ℤ)} {r : ℤ × ℤ} {z : ℂ} :
    z ∈ runRect S r ↔ (r.1 : ℝ) ≤ z.re ∧ z.re ≤ (r.1 : ℝ) + 1 ∧ (r.2 : ℝ) ≤ z.im ∧
      z.im ≤ (runTopRow S r : ℝ) + 1 := Iff.rfl

theorem isClosed_runRect (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) : IsClosed (runRect S r) := by
  have h : runRect S r = {z : ℂ | (r.1 : ℝ) ≤ z.re} ∩ {z : ℂ | z.re ≤ (r.1 : ℝ) + 1} ∩
      {z : ℂ | (r.2 : ℝ) ≤ z.im} ∩ {z : ℂ | z.im ≤ (runTopRow S r : ℝ) + 1} := by
    ext z; simp only [runRect, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]
  exact IsClosed.inter (IsClosed.inter (IsClosed.inter
    (isClosed_le continuous_const Complex.continuous_re)
    (isClosed_le Complex.continuous_re continuous_const))
    (isClosed_le continuous_const Complex.continuous_im))
    (isClosed_le Complex.continuous_im continuous_const)

/-- Convexity of an axis-parallel box in `ℂ`. -/
theorem convex_box {a b c d : ℝ} :
    Convex ℝ {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hre : (s • x + t • y).re = s * x.re + t * y.re := by simp [Complex.add_re]
  have him : (s • x + t • y).im = s * x.im + t * y.im := by simp [Complex.add_im]
  have key : ∀ (u v B : ℝ), B ≤ u → B ≤ v → B ≤ s * u + t * v := by
    intro u v B hu hv
    have h1 : s * B ≤ s * u := mul_le_mul_of_nonneg_left hu hs
    have h2 : t * B ≤ t * v := mul_le_mul_of_nonneg_left hv ht
    have h3 : s * B + t * B = B := by
      have : s * B + t * B = (s + t) * B := by ring
      rw [this, hst, one_mul]
    linarith
  have key' : ∀ (u v B : ℝ), u ≤ B → v ≤ B → s * u + t * v ≤ B := by
    intro u v B hu hv
    have h1 : s * u ≤ s * B := mul_le_mul_of_nonneg_left hu hs
    have h2 : t * v ≤ t * B := mul_le_mul_of_nonneg_left hv ht
    have h3 : s * B + t * B = B := by
      have : s * B + t * B = (s + t) * B := by ring
      rw [this, hst, one_mul]
    linarith
  exact ⟨by rw [hre]; exact key x.re y.re a hx.1 hy.1,
         by rw [hre]; exact key' x.re y.re b hx.2.1 hy.2.1,
         by rw [him]; exact key x.im y.im c hx.2.2.1 hy.2.2.1,
         by rw [him]; exact key' x.im y.im d hx.2.2.2 hy.2.2.2⟩

theorem convex_runRect (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) : Convex ℝ (runRect S r) :=
  convex_box

theorem runRect_nonempty (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) : (runRect S r).Nonempty := by
  refine ⟨⟨(r.1 : ℝ), (r.2 : ℝ)⟩, ?_⟩
  rw [mem_runRect]
  refine ⟨le_rfl, by norm_num, le_rfl, ?_⟩
  have h : (r.2 : ℤ) ≤ runTopRow S r := runTopRow_ge S r
  have h' : (r.2 : ℝ) ≤ (runTopRow S r : ℝ) := by exact_mod_cast h
  linarith

/-- A cell of `S` is contained in the rectangle of its own run. -/
theorem cell_subset_runRect (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ S) :
    Commons.Topology.Plane.unitSqAt p ⊆ runRect S (p.1, blkBot S p hp) := by
  intro z hz
  rw [Commons.Topology.Plane.mem_unitSqAt] at hz
  rw [mem_runRect]
  have htop := runTopRow_max S (p.1, blkBot S p hp) (blkBot_cell S p hp)
    (blkBot_le S p hp) (blkBot_all S p hp)
  have hbot := blkBot_le S p hp
  refine ⟨hz.1, hz.2.1, le_trans (by exact_mod_cast hbot) hz.2.2.1, ?_⟩
  have h2 : ((p.2 : ℤ) : ℝ) + 1 ≤ ((runTopRow S (p.1, blkBot S p hp) : ℤ) : ℝ) + 1 := by
    exact_mod_cast (by omega : (p.2 : ℤ) + 1 ≤ runTopRow S (p.1, blkBot S p hp) + 1)
  linarith [hz.2.2.2, h2]

theorem runRect_subset_polyK (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) (hr : r ∈ S) :
    runRect S r ⊆ Commons.Topology.Plane.polyK S := by
  intro z hz
  rw [Commons.Topology.Plane.polyK, Set.mem_iUnion₂]
  rw [mem_runRect] at hz
  set m := min ⌊z.im⌋ (runTopRow S r) with hm
  have hm1 : r.2 ≤ m := le_min (Int.le_floor.mpr hz.2.2.1) (runTopRow_ge S r)
  have hm2 : m ≤ runTopRow S r := min_le_right _ _
  have hmem : (r.1, m) ∈ S := runTopRow_all S r hr m (Finset.mem_Icc.mpr ⟨hm1, hm2⟩)
  refine ⟨(r.1, m), hmem, ?_⟩
  rw [Commons.Topology.Plane.mem_unitSqAt]
  refine ⟨hz.1, hz.2.1, ?_, ?_⟩
  · rw [hm]
    exact le_trans (by exact_mod_cast min_le_left ⌊z.im⌋ (runTopRow S r)) (Int.floor_le z.im)
  · rcases min_cases ⌊z.im⌋ (runTopRow S r) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hm, h]; exact le_of_lt (Int.lt_floor_add_one z.im)
    · rw [hm, h]
      have hge : runTopRow S r ≤ ⌊z.im⌋ := by omega
      have h2 : ((runTopRow S r : ℤ) : ℝ) + 1 ≤ (⌊z.im⌋ : ℝ) := by
        exact_mod_cast (by omega : runTopRow S r + 1 ≤ ⌊z.im⌋)
      linarith [hz.2.2.2, h2]

theorem iUnion_runRect_eq_polyK (S : Finset (ℤ × ℤ)) :
    (Set.iUnion fun r : ↥(runBottoms S) => runRect S (r : ℤ × ℤ)) =
      Commons.Topology.Plane.polyK S := by
  apply Subset.antisymm
  · intro z hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨r, hz⟩ := hz
    exact runRect_subset_polyK S (r : ℤ × ℤ) (runBottoms_subset S r.2) hz
  · intro z hz
    rw [Commons.Topology.Plane.polyK, Set.mem_iUnion₂] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    rw [Set.mem_iUnion]
    exact ⟨⟨(p.1, blkBot S p hp), blkBot_mem_runBottoms S p hp⟩,
      cell_subset_runRect S p hp hzp⟩


/-! ## The cells of a run, and adjacency -/

/-- The cells of the run with bottom `r`. -/
def runCellSet (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc r.2 (runTopRow S r)).image (fun m => (r.1, m))

theorem mem_runCellSet (S : Finset (ℤ × ℤ)) (r q : ℤ × ℤ) :
    q ∈ runCellSet S r ↔ q.1 = r.1 ∧ r.2 ≤ q.2 ∧ q.2 ≤ runTopRow S r := by
  rw [runCellSet, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Finset.mem_Icc] at hm
    exact ⟨rfl, hm.1, hm.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨q.2, Finset.mem_Icc.mpr ⟨h2, h3⟩, by rw [← h1]⟩

theorem runCellSet_subset (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) (hr : r ∈ S) :
    runCellSet S r ⊆ S := by
  intro q hq
  obtain ⟨h1, h2, h3⟩ := (mem_runCellSet S r q).mp hq
  have hq' : q = (r.1, q.2) := by rw [← h1]
  rw [hq']
  exact runTopRow_all S r hr q.2 (Finset.mem_Icc.mpr ⟨h2, h3⟩)

theorem self_mem_runCellSet (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) (hr : r ∈ S) :
    r ∈ runCellSet S r :=
  (mem_runCellSet S r r).mpr ⟨rfl, le_rfl, runTopRow_ge S r⟩

/-- The rectangle of a run is the union of its cells. -/
theorem runRect_eq_iUnion_unitSqAt (S : Finset (ℤ × ℤ)) (r : ℤ × ℤ) :
    runRect S r = ⋃ q ∈ runCellSet S r, Commons.Topology.Plane.unitSqAt q := by
  ext z
  rw [mem_runRect, Set.mem_iUnion₂]
  constructor
  · intro hz
    refine ⟨(r.1, min ⌊z.im⌋ (runTopRow S r)), ?_, ?_⟩
    · rw [mem_runCellSet]
      exact ⟨rfl, le_min (Int.le_floor.mpr hz.2.2.1) (runTopRow_ge S r), min_le_right _ _⟩
    · rw [Commons.Topology.Plane.mem_unitSqAt]
      refine ⟨hz.1, hz.2.1, ?_, ?_⟩
      · exact le_trans (by exact_mod_cast min_le_left ⌊z.im⌋ (runTopRow S r)) (Int.floor_le z.im)
      · rcases min_cases ⌊z.im⌋ (runTopRow S r) with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; exact le_of_lt (Int.lt_floor_add_one z.im)
        · rw [h]
          have hge : runTopRow S r ≤ ⌊z.im⌋ := by omega
          have h2 : ((runTopRow S r : ℤ) : ℝ) + 1 ≤ (⌊z.im⌋ : ℝ) := by
            exact_mod_cast (by omega : runTopRow S r + 1 ≤ ⌊z.im⌋)
          linarith [hz.2.2.2, h2]
  · rintro ⟨q, hq, hzq⟩
    obtain ⟨hq1, hq2, hq3⟩ := (mem_runCellSet S r q).mp hq
    rw [Commons.Topology.Plane.mem_unitSqAt] at hzq
    rw [← hq1]
    exact ⟨hzq.1, hzq.2.1, le_trans (by exact_mod_cast hq2) hzq.2.2.1,
      le_trans hzq.2.2.2 (by exact_mod_cast (by omega : q.2 + 1 ≤ runTopRow S r + 1))⟩

/-- Two runs *meet* when they are distinct and their rectangles intersect. -/
def runAdj (S : Finset (ℤ × ℤ)) (r r' : ℤ × ℤ) : Prop :=
  r ≠ r' ∧ (runRect S r ∩ runRect S r').Nonempty

theorem runAdj_symm {S : Finset (ℤ × ℤ)} {r r' : ℤ × ℤ} (h : runAdj S r r') :
    runAdj S r' r :=
  ⟨Ne.symm h.1, h.2.mono (fun z hz => ⟨hz.2, hz.1⟩)⟩

/-! ## The graph of unoccupied cells -/

/-- The centre of the closed unit cell `p`. -/
def cellCenter (p : ℤ × ℤ) : ℂ := ((p.1 : ℝ) + 1/2 : ℂ) + ((p.2 : ℝ) + 1/2 : ℂ) * Complex.I

theorem cellCenter_re (p : ℤ × ℤ) : (cellCenter p).re = (p.1 : ℝ) + 1/2 := by
  simp [cellCenter]

theorem cellCenter_im (p : ℤ × ℤ) : (cellCenter p).im = (p.2 : ℝ) + 1/2 := by
  simp [cellCenter]

theorem cellCenter_mem_unitSqAt (p : ℤ × ℤ) :
    cellCenter p ∈ Commons.Topology.Plane.unitSqAt p := by
  rw [Commons.Topology.Plane.mem_unitSqAt]
  refine ⟨by rw [cellCenter_re]; linarith, by rw [cellCenter_re]; linarith,
    by rw [cellCenter_im]; linarith, by rw [cellCenter_im]; linarith⟩

/-- Two lattice cells are *edge-adjacent*. -/
def CellAdj (a b : ℤ × ℤ) : Prop :=
  b = (a.1 + 1, a.2) ∨ b = (a.1 - 1, a.2) ∨ b = (a.1, a.2 + 1) ∨ b = (a.1, a.2 - 1)

end

end Work.PlanarSC

