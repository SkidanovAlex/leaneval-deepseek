import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.GridCycleDefs
import Submission.Work.HornSC.CellBoundaryJordan.GridCycleAux
import Submission.Work.PlanarSC.exists_circleMap_of_loop

/-!
# A grid cycle spans an embedded circle

A closed walk `u 0, u 1, …, u k = u 0` of the unit grid whose first `k` vertices are pairwise
distinct bounds a simple closed polygonal curve, the union of the unit segments
`adjSeg (u i) (u (i+1))`, `i < k`.  This module proves that this union is the image of an
*injective* continuous map of the circle.

The parametrisation is the constant-speed one of `GridCycleDefs` (`gridCurve u k`): the `i`-th edge
is traversed during the parameter interval `[i/k, (i+1)/k]`.  The main point is `gridCurve_inj`:
two parameter values with the same image are equal, unless they are the two ends of `[0,1]`.  This
rests on the elementary geometry of unit grid segments (in `GridCycleAux`): two distinct unit
segments meet only in lattice points, so a common value of the curve on two distinct edges can only
be a common vertex, and the vertices of the cycle are pairwise distinct.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- **The parametrisation of a vertex-simple grid cycle is injective up to the seam.**  If the
images of two parameter values `s, t ∈ [0,1]` under the constant-speed parametrisation `gridCurve`
agree, then either `s = t` or `{s, t} = {0, 1}` (the closed walk begins and ends at `u 0`). -/
theorem gridCurve_inj {k : ℕ} (hk : 3 ≤ k) (u : ℕ → ℤ × ℤ)
    (hper : ∀ i, u (i + k) = u i)
    (hinj : ∀ i j, i < k → j < k → u i = u j → i = j)
    (hstep : ∀ i, i < k → IsUnitAdj (u i) (u (i + 1)))
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (hst : gridCurve u k s = gridCurve u k t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  have hk1 : 1 ≤ k := by omega
  have hkne : ((k : ℕ) : ℝ) ≠ 0 := by positivity
  set i := cIdx k s with hi
  set j := cIdx k t with hj
  have hik : i < k := by rw [hi]; exact cIdx_lt hk1 s
  have hjk : j < k := by rw [hj]; exact cIdx_lt hk1 t
  -- non-degeneracy of the two edges
  have hne_s : lpt (u (cIdx k s)) ≠ lpt (u (cIdx k s + 1)) := by
    have h := (hstep (cIdx k s) (cIdx_lt hk1 s)).ne
    intro hc
    exact h (by simpa using hc)
  have hne_t : lpt (u (cIdx k t)) ≠ lpt (u (cIdx k t + 1)) := by
    have h := (hstep (cIdx k t) (cIdx_lt hk1 t)).ne
    intro hc
    exact h (by simpa using hc)
  have hnei : lpt (u i) ≠ lpt (u (i + 1)) := by
    have h := (hstep i hik).ne
    intro hc
    exact h (by simpa using hc)
  have hnej : lpt (u j) ≠ lpt (u (j + 1)) := by
    have h := (hstep j hjk).ne
    intro hc
    exact h (by simpa using hc)
  -- the common value lies on both edges
  have hz1 : gridCurve u k s ∈ adjSeg (u i) (u (i + 1)) := by
    have h := gridCurve_mem_adjSeg (k := k) (u := u) hk1 hs.1 hs.2
    rwa [← hi] at h
  have hz2 : gridCurve u k t ∈ adjSeg (u j) (u (j + 1)) := by
    have h := gridCurve_mem_adjSeg (k := k) (u := u) hk1 ht.1 ht.2
    rwa [← hj] at h
  -- the parameter of a vertex of the current edge
  have hs_of : ∀ {a : ℕ}, (a = i ∨ a = i + 1) → gridCurve u k s = lpt (u a) →
      s * (k : ℝ) = (a : ℝ) := by
    intro a ha hz
    refine mul_eq_of_gridCurve_eq (k := k) (u := u) (t := s) ?_ hne_s hz
    rcases ha with h | h
    · exact Or.inl (by rw [h, hi])
    · exact Or.inr (by rw [h, hi])
  have ht_of : ∀ {b : ℕ}, (b = j ∨ b = j + 1) → gridCurve u k t = lpt (u b) →
      t * (k : ℝ) = (b : ℝ) := by
    intro b hb hz
    refine mul_eq_of_gridCurve_eq (k := k) (u := u) (t := t) ?_ hne_t hz
    rcases hb with h | h
    · exact Or.inl (by rw [h, hj])
    · exact Or.inr (by rw [h, hj])
  rcases eq_or_ne i j with hij | hij
  · -- both parameters lie on the same edge
    left
    have hidx : cIdx k s = cIdx k t := by rw [← hi, ← hj, hij]
    have hmul := mul_eq_of_gridCurve_eq_same (k := k) (u := u) (s := s) (t := t) hidx hne_s hst
    exact mul_right_cancel₀ hkne hmul
  · by_cases hlat : ∃ p : ℤ × ℤ, gridCurve u k s = lpt p
    · -- the common value is a lattice point, hence a common vertex
      obtain ⟨p, hp⟩ := hlat
      have hp1 : p = u i ∨ p = u (i + 1) := eq_lpt_of_mem_adjSeg (hstep i hik) hz1 hp
      have hp2 : p = u j ∨ p = u (j + 1) :=
        eq_lpt_of_mem_adjSeg (hstep j hjk) hz2 (by rw [← hst]; exact hp)
      rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
      · -- p = u i = u j, contradicting the distinctness of the vertices
        exfalso
        have huv : u i = u j := by rw [← h1, ← h2]
        rcases (vertex_eq_iff hk1 u hper hinj (le_of_lt hik) (le_of_lt hjk)).mp huv
          with h | ⟨h, h'⟩ | ⟨h, h'⟩
        · exact hij h
        · omega
        · omega
      · -- p = u i = u (j + 1)
        have hsa : s * (k : ℝ) = (i : ℝ) := hs_of (Or.inl rfl) (by rw [hp, h1])
        have htb : t * (k : ℝ) = ((j + 1 : ℕ) : ℝ) := ht_of (Or.inr rfl) (by rw [← hst, hp, h2])
        have hu : u i = u (j + 1) := by rw [← h1, ← h2]
        rcases (vertex_eq_iff hk1 u hper hinj (le_of_lt hik) (by omega : j + 1 ≤ k)).mp hu
          with h | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · left
          have : s * (k : ℝ) = t * (k : ℝ) := by rw [hsa, htb, h]
          exact mul_right_cancel₀ hkne this
        · right; left
          refine ⟨?_, ?_⟩
          · have hz : s * (k : ℝ) = 0 := by rw [hsa, h1']; norm_num
            exact (mul_eq_zero.mp hz).resolve_right hkne
          · refine mul_right_cancel₀ hkne ?_
            rw [htb, h2']
            ring
        · exfalso; omega
      · -- p = u (i + 1) = u j
        have hsa : s * (k : ℝ) = ((i + 1 : ℕ) : ℝ) := hs_of (Or.inr rfl) (by rw [hp, h1])
        have htb : t * (k : ℝ) = (j : ℝ) := ht_of (Or.inl rfl) (by rw [← hst, hp, h2])
        have hu : u (i + 1) = u j := by rw [← h1, ← h2]
        rcases (vertex_eq_iff hk1 u hper hinj (by omega : i + 1 ≤ k) (le_of_lt hjk)).mp hu
          with h | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · left
          have : s * (k : ℝ) = t * (k : ℝ) := by rw [hsa, htb, h]
          exact mul_right_cancel₀ hkne this
        · exfalso; omega
        · right; right
          refine ⟨?_, ?_⟩
          · refine mul_right_cancel₀ hkne ?_
            rw [hsa, h1']
            ring
          · have hz : t * (k : ℝ) = 0 := by rw [htb, h2']; norm_num
            exact (mul_eq_zero.mp hz).resolve_right hkne
      · -- p = u (i + 1) = u (j + 1), contradicting the distinctness of the vertices
        exfalso
        have huv : u (i + 1) = u (j + 1) := by rw [← h1, ← h2]
        rcases (vertex_eq_iff hk1 u hper hinj (by omega : i + 1 ≤ k) (by omega : j + 1 ≤ k)).mp huv
          with h | ⟨h, h'⟩ | ⟨h, h'⟩
        · omega
        · omega
        · omega
    · -- the common value is not a lattice point: the two edges coincide
      exfalso
      have hS : adjSeg (u i) (u (i + 1)) = adjSeg (u j) (u (j + 1)) :=
        adjSeg_eq_of_mem_of_not_lattice (hstep i hik) (hstep j hjk) hz1
          (by rw [hst]; exact hz2) (fun p hp => hlat ⟨p, hp⟩)
      have hin1 : lpt (u i) ∈ adjSeg (u j) (u (j + 1)) := by
        rw [← hS]; exact left_mem_segment ℝ _ _
      have hin2 : lpt (u (i + 1)) ∈ adjSeg (u j) (u (j + 1)) := by
        rw [← hS]; exact right_mem_segment ℝ _ _
      have h1 : u i = u j ∨ u i = u (j + 1) := eq_lpt_of_mem_adjSeg (hstep j hjk) hin1 rfl
      have h2 : u (i + 1) = u j ∨ u (i + 1) = u (j + 1) :=
        eq_lpt_of_mem_adjSeg (hstep j hjk) hin2 rfl
      rcases h1 with h | h
      · rcases (vertex_eq_iff hk1 u hper hinj (le_of_lt hik) (le_of_lt hjk)).mp h
          with h' | ⟨h', h''⟩ | ⟨h', h''⟩
        · exact hij h'
        · omega
        · omega
      · rcases (vertex_eq_iff hk1 u hper hinj (le_of_lt hik) (by omega : j + 1 ≤ k)).mp h
          with h' | ⟨h', h''⟩ | ⟨h', h''⟩
        · rcases h2 with h2 | h2
          · have hw := (vertex_eq_iff hk1 u hper hinj (by omega : i + 1 ≤ k)
              (le_of_lt hjk)).mp h2
            rcases hw with hw1 | ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩ <;> omega
          · have hw := (vertex_eq_iff hk1 u hper hinj (by omega : i + 1 ≤ k)
              (by omega : j + 1 ≤ k)).mp h2
            rcases hw with hw1 | ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩ <;> omega
        · rcases h2 with h2 | h2
          · have hw := (vertex_eq_iff hk1 u hper hinj (by omega : i + 1 ≤ k)
              (le_of_lt hjk)).mp h2
            rcases hw with hw1 | ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩ <;> omega
          · have hw := (vertex_eq_iff hk1 u hper hinj (by omega : i + 1 ≤ k)
              (by omega : j + 1 ≤ k)).mp h2
            rcases hw with hw1 | ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩ <;> omega
        · omega

theorem exists_injective_circle_map_of_grid_cycle {k : ℕ} (hk : 3 ≤ k) (u : ℕ → ℤ × ℤ)
    (hper : ∀ i, u (i + k) = u i)
    (hinj : ∀ i j, i < k → j < k → u i = u j → i = j)
    (hstep : ∀ i, i < k → IsUnitAdj (u i) (u (i + 1))) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      Set.range γ = ⋃ i ∈ {i : ℕ | i < k}, adjSeg (u i) (u (i + 1)) := by
  have hk1 : 1 ≤ k := by omega
  have hcl : u k = u 0 := by simpa using hper 0
  have hcont : Continuous fun x : unitInterval => gridCurve u k (x : ℝ) :=
    (continuousOn_gridCurve hk1 u).comp_continuous continuous_subtype_val (fun x => x.2)
  -- the closed walk as a loop
  let loop : Path (lpt (u 0)) (lpt (u 0)) :=
    { toFun := fun x : unitInterval => gridCurve u k (x : ℝ)
      continuous_toFun := hcont
      source' := by
        have h : ((0 : unitInterval) : ℝ) = (0 : ℝ) := rfl
        rw [h]
        exact gridCurve_zero hk1 u
      target' := by
        have h : ((1 : unitInterval) : ℝ) = (1 : ℝ) := rfl
        rw [h, gridCurve_one hk1 u, hcl] }
  have hloop : ∀ x : unitInterval, loop x = gridCurve u k (x : ℝ) := fun x => rfl
  have hsimple : Work.PlanarSC.IsSimpleLoop loop := by
    intro s t hst
    have hst' : gridCurve u k (s : ℝ) = gridCurve u k (t : ℝ) := by
      simpa [hloop] using hst
    rcases gridCurve_inj hk u hper hinj hstep s.2 t.2 hst' with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact Subtype.ext h
    · right; left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
    · right; right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  obtain ⟨γ, hγinj, hγeq⟩ := Work.PlanarSC.exists_circleMap_of_loop loop hsimple
  refine ⟨γ, hγinj, ?_⟩
  have hrange : Set.range γ = Set.range (fun x : unitInterval => gridCurve u k (x : ℝ)) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨x, hx⟩ := Work.PlanarSC.circlePt_surjective w
      refine ⟨x, ?_⟩
      show gridCurve u k (x : ℝ) = γ w
      rw [← hx, hγeq x, hloop x]
    · rintro ⟨x, rfl⟩
      refine ⟨Work.PlanarSC.circlePt x, ?_⟩
      show γ (Work.PlanarSC.circlePt x) = gridCurve u k (x : ℝ)
      rw [hγeq x, hloop x]
  rw [hrange, range_gridCurve_eq hk1 u]

end

end Work.HornSC.CellBoundaryJordan
