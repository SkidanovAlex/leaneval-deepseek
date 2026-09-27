import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Submission.Commons.Topology.Plane.exists_dyadic_exhaustion_of_isOpen_complex
import Submission.Commons.Topology.Plane.dyadicCell_grid_avoidance
import Submission.Commons.Topology.Plane.maxCell_mem_of_mem

namespace Commons.Topology.Plane

/-!
# Maximal dyadic cells have disjoint interiors

A dyadic cell `dyadicCell n p ⊆ U` is *maximal* (for `U`) when its parent cell is not
contained in `U`.  Two maximal cells whose interiors meet must be equal.

The proof rests on two elementary facts:

* a fine dyadic cell is contained in its coarser ancestor
  (`dyadicCell_subset_ancestor`);
* a point of the interior of a cell determines its index at that level
  (`eq_of_mem_interior_of_mem_cell`).
-/

/-- A dyadic cell of level `n + k` with index `a` is contained in its ancestor of level `n`,
whose index is `a` divided by `2 ^ k` (coordinatewise, floor division on `ℤ`). -/
lemma dyadicCell_subset_ancestor (n k : ℕ) (a : ℤ × ℤ) :
    dyadicCell (n + k) a ⊆ dyadicCell n (a.1 / 2 ^ k, a.2 / 2 ^ k) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
      intro z hz
      have h1 : dyadicCell (n + (k + 1)) a ⊆ dyadicCell (n + k) (a.1 / 2, a.2 / 2) := by
        have hnk : n + (k + 1) = (n + k) + 1 := by omega
        rw [hnk]
        exact dyadicCell_subset_parent (n + k) a
      have hz1 : z ∈ dyadicCell (n + k) (a.1 / 2, a.2 / 2) := h1 hz
      have hz2 : z ∈ dyadicCell n ((a.1 / 2) / 2 ^ k, (a.2 / 2) / 2 ^ k) :=
        ih (a.1 / 2, a.2 / 2) hz1
      have e1 : (a.1 / 2) / 2 ^ k = a.1 / 2 ^ (k + 1) := by
        rw [Int.ediv_ediv_of_nonneg (x := a.1) (y := 2) (z := 2 ^ k) (by norm_num)]
        congr 1
        rw [pow_succ]
        ring
      have e2 : (a.2 / 2) / 2 ^ k = a.2 / 2 ^ (k + 1) := by
        rw [Int.ediv_ediv_of_nonneg (x := a.2) (y := 2) (z := 2 ^ k) (by norm_num)]
        congr 1
        rw [pow_succ]
        ring
      rwa [e1, e2] at hz2

/-- A point of the interior of a level-`n` cell lies in exactly one level-`n` cell. -/
lemma eq_of_mem_interior_of_mem_cell {n : ℕ} {p q : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ interior (dyadicCell n p)) (hz' : z ∈ dyadicCell n q) : p = q := by
  obtain ⟨h1, h2, h3, h4⟩ := interior_dyadicCell_strict hz
  obtain ⟨g1, g2, g3, g4⟩ := hz'
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hle1 : q.1 ≤ p.1 := by
    by_contra h
    have hge : p.1 + 1 ≤ q.1 := by omega
    have hcast : ((p.1 : ℝ) + 1) / 2 ^ n ≤ (q.1 : ℝ) / 2 ^ n := by
      apply div_le_div_of_nonneg_right _ (le_of_lt h2n)
      exact_mod_cast hge
    linarith
  have hle2 : p.1 ≤ q.1 := by
    by_contra h
    have hge : q.1 + 1 ≤ p.1 := by omega
    have hcast : ((q.1 : ℝ) + 1) / 2 ^ n ≤ (p.1 : ℝ) / 2 ^ n := by
      apply div_le_div_of_nonneg_right _ (le_of_lt h2n)
      exact_mod_cast hge
    linarith
  have hle3 : q.2 ≤ p.2 := by
    by_contra h
    have hge : p.2 + 1 ≤ q.2 := by omega
    have hcast : ((p.2 : ℝ) + 1) / 2 ^ n ≤ (q.2 : ℝ) / 2 ^ n := by
      apply div_le_div_of_nonneg_right _ (le_of_lt h2n)
      exact_mod_cast hge
    linarith
  have hle4 : p.2 ≤ q.2 := by
    by_contra h
    have hge : q.2 + 1 ≤ p.2 := by omega
    have hcast : ((q.2 : ℝ) + 1) / 2 ^ n ≤ (p.2 : ℝ) / 2 ^ n := by
      apply div_le_div_of_nonneg_right _ (le_of_lt h2n)
      exact_mod_cast hge
    linarith
  exact Prod.ext (le_antisymm hle2 hle1) (le_antisymm hle4 hle3)

/-- If `n < m` and the interiors of `dyadicCell n p` and `dyadicCell m q` meet, then the
parent of `dyadicCell m q` (a cell of level `m - 1`) is contained in `dyadicCell n p`. -/
lemma parent_subset_cell_of_interior_inter {n m : ℕ} (hlt : n < m) {p q : ℤ × ℤ} {z : ℂ}
    (hzp : z ∈ interior (dyadicCell n p)) (hzq : z ∈ interior (dyadicCell m q)) :
    dyadicCell (m - 1) (q.1 / 2, q.2 / 2) ⊆ dyadicCell n p := by
  have hanc : dyadicCell m q ⊆ dyadicCell n (q.1 / 2 ^ (m - n), q.2 / 2 ^ (m - n)) := by
    have h := dyadicCell_subset_ancestor n (m - n) q
    have e : n + (m - n) = m := by omega
    rwa [e] at h
  have hp_eq : p = (q.1 / 2 ^ (m - n), q.2 / 2 ^ (m - n)) :=
    eq_of_mem_interior_of_mem_cell hzp (hanc (interior_subset hzq))
  rw [hp_eq]
  have hk : m - n = (m - 1 - n) + 1 := by omega
  have hm1 : m - 1 = n + (m - 1 - n) := by omega
  have hsub : dyadicCell (n + (m - 1 - n)) (q.1 / 2, q.2 / 2) ⊆
      dyadicCell n ((q.1 / 2) / 2 ^ (m - 1 - n), (q.2 / 2) / 2 ^ (m - 1 - n)) :=
    dyadicCell_subset_ancestor n (m - 1 - n) (q.1 / 2, q.2 / 2)
  rw [← hm1] at hsub
  refine subset_trans hsub ?_
  have e1 : (q.1 / 2) / 2 ^ (m - 1 - n) = q.1 / 2 ^ (m - n) := by
    rw [Int.ediv_ediv_of_nonneg (x := q.1) (y := 2) (z := 2 ^ (m - 1 - n)) (by norm_num)]
    congr 1
    rw [hk, pow_succ]
    ring
  have e2 : (q.2 / 2) / 2 ^ (m - 1 - n) = q.2 / 2 ^ (m - n) := by
    rw [Int.ediv_ediv_of_nonneg (x := q.2) (y := 2) (z := 2 ^ (m - 1 - n)) (by norm_num)]
    congr 1
    rw [hk, pow_succ]
    ring
  rw [e1, e2]

theorem maxCell_interior_disjoint (U : Set ℂ) (n m : ℕ) (p q : ℤ × ℤ) (hp : Commons.Topology.Plane.dyadicCell n p ⊆ U) (hn : n = 0 ∨ ¬ Commons.Topology.Plane.dyadicCell (n - 1) (p.1 / 2, p.2 / 2) ⊆ U) (hq : Commons.Topology.Plane.dyadicCell m q ⊆ U) (hm : m = 0 ∨ ¬ Commons.Topology.Plane.dyadicCell (m - 1) (q.1 / 2, q.2 / 2) ⊆ U) (hint : (interior (Commons.Topology.Plane.dyadicCell n p) ∩ interior (Commons.Topology.Plane.dyadicCell m q)).Nonempty) : n = m ∧ p = q := by
  obtain ⟨z, hz⟩ := hint
  have hzp : z ∈ interior (dyadicCell n p) := hz.1
  have hzq : z ∈ interior (dyadicCell m q) := hz.2
  have hnm : n = m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hparent := parent_subset_cell_of_interior_inter (p := p) (q := q) hlt hzp hzq
      have hU : dyadicCell (m - 1) (q.1 / 2, q.2 / 2) ⊆ U := subset_trans hparent hp
      rcases hm with h0 | hnot
      · omega
      · exact hnot hU
    · have hparent := parent_subset_cell_of_interior_inter (p := q) (q := p) hlt hzq hzp
      have hU : dyadicCell (n - 1) (p.1 / 2, p.2 / 2) ⊆ U := subset_trans hparent hq
      rcases hn with h0 | hnot
      · omega
      · exact hnot hU
  rw [hnm] at hzp
  exact ⟨hnm, eq_of_mem_interior_of_mem_cell hzp (interior_subset hzq)⟩

end Commons.Topology.Plane