import Mathlib
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.PlanarSC.Brick
import Submission.Work.PlanarSC.Brick.WallCircleDefs
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs
import Submission.Work.HornSC.CellBoundaryJordan.exists_generic_ray_direction
import Submission.Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle
import Submission.Work.HornSC.CellBoundaryJordan.ray_wall_crossings_odd
import Submission.Work.HornSC.CellBoundaryJordan.ray_crossings_sum
import Submission.Work.HornSC.CellBoundaryJordan.ball_subset_cellUnion_of_notMem_wallSet
import Submission.Work.PlanarSC.JC.RayBasic
import Submission.Work.PlanarSC.JC.cycle_decomposition_disjoint
import Submission.Work.PlanarSC.JC.grid_cycle_crossing_parity
import Submission.Work.PlanarSC.JC.crossing_wallSet_finite
import Submission.Work.PlanarSC.JC.crossing_adjSeg_finite
import Submission.Lib.Unif2.Commons.Topology.Jordan.plane_separation

namespace Work.PlanarSC.Brick

open Set

/-! ## Elementary geometry of the unit lattice -/

/-- The closed unit cell is the product of the two closed unit intervals in the real and imaginary
parts. -/
lemma cell_eq_reProdIm (p : ℤ × ℤ) :
    Work.HornSC.cell p = (Set.Icc (p.1 : ℝ) ((p.1 : ℝ) + 1)) ×ℂ
      (Set.Icc (p.2 : ℝ) ((p.2 : ℝ) + 1)) := by
  ext z
  simp only [Complex.mem_reProdIm, Work.HornSC.mem_cell, Set.mem_Icc]
  tauto

/-- The interior of a closed unit cell is the corresponding open cell. -/
lemma interior_cell (p : ℤ × ℤ) :
    interior (Work.HornSC.cell p) = Work.HornSC.CellBoundaryJordan.iCell p := by
  rw [cell_eq_reProdIm, Complex.interior_reProdIm, interior_Icc, interior_Icc]
  ext z
  simp only [Complex.mem_reProdIm, Set.mem_Ioo, Work.HornSC.CellBoundaryJordan.iCell,
    Set.mem_ofPred_eq]
  tauto

lemma isOpen_iCell (p : ℤ × ℤ) : IsOpen (Work.HornSC.CellBoundaryJordan.iCell p) :=
  interior_cell p ▸ isOpen_interior

/-- The closed unit cell is convex. -/
lemma convex_cell (p : ℤ × ℤ) : Convex ℝ (Work.HornSC.cell p) := by
  rw [cell_eq_reProdIm, Complex.reProdIm]
  exact ((convex_Icc _ _).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)).inter
    ((convex_Icc _ _).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ))

/-- Points of the open cell `iCell q` are arbitrarily close to a point of the closed cell
`cell q`. -/
lemma exists_mem_iCell_dist_lt {q : ℤ × ℤ} {z : ℂ} (hz : z ∈ Work.HornSC.cell q) {r : ℝ}
    (hr : 0 < r) : ∃ w : ℂ, w ∈ Work.HornSC.CellBoundaryJordan.iCell q ∧ dist z w < r := by
  set c : ℂ := Work.PlanarSC.Brick.cellCenter q with hc
  have hcint : c ∈ interior (Work.HornSC.cell q) :=
    Work.PlanarSC.Brick.cellCenter_mem_interior_cell q
  set t : ℝ := min 1 (r / (2 * (‖c - z‖ + 1))) with ht
  have htpos : 0 < t := by
    rw [ht]; exact lt_min one_pos (by positivity)
  have htle1 : t ≤ 1 := by rw [ht]; exact min_le_left _ _
  have hkey : t * (2 * (‖c - z‖ + 1)) ≤ r := by
    have h2 : t ≤ r / (2 * (‖c - z‖ + 1)) := by rw [ht]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (‖c - z‖ + 1))] at h2
    linarith
  refine ⟨t • c + (1 - t) • z, ?_, ?_⟩
  · have h := Convex.combo_interior_self_mem_interior (convex_cell q) hcint hz
      (a := t) (b := 1 - t) htpos (by linarith) (by ring)
    rw [interior_cell] at h
    exact h
  · have hsub : t • c + (1 - t) • z - z = t • (c - z) := by module
    rw [dist_eq_norm, norm_sub_rev, hsub, norm_smul, Real.norm_of_nonneg htpos.le]
    have hD : ‖c - z‖ < 2 * (‖c - z‖ + 1) := by nlinarith [norm_nonneg (c - z)]
    have := mul_lt_mul_of_pos_left hD htpos
    linarith

/-! ## Walls of a finite union of cells -/

lemma hSeg_subset_cell_below (u : ℤ × ℤ) :
    Work.HornSC.CellBoundaryJordan.hSeg u ⊆ Work.HornSC.cell (u.1, u.2 - 1) := by
  intro z hz
  rw [Work.HornSC.CellBoundaryJordan.mem_hSeg] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  rw [Work.HornSC.mem_cell]
  exact ⟨h2, h3, by push_cast; linarith, by push_cast; linarith⟩

lemma vSeg_subset_cell_same (u : ℤ × ℤ) :
    Work.HornSC.CellBoundaryJordan.vSeg u ⊆ Work.HornSC.cell (u.1, u.2) := by
  intro z hz
  rw [Work.HornSC.CellBoundaryJordan.mem_vSeg] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  rw [Work.HornSC.mem_cell]
  exact ⟨by push_cast; linarith, by push_cast; linarith, h2, h3⟩

lemma vSeg_subset_cell_right (u : ℤ × ℤ) :
    Work.HornSC.CellBoundaryJordan.vSeg u ⊆ Work.HornSC.cell (u.1 - 1, u.2) := by
  intro z hz
  rw [Work.HornSC.CellBoundaryJordan.mem_vSeg] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  rw [Work.HornSC.mem_cell]
  exact ⟨by push_cast; linarith, by push_cast; linarith, h2, h3⟩

/-- Every point of a wall of `A` lies both in a cell of `A` and in a cell outside `A`. -/
lemma exists_cell_mem_and_notMem {A : Finset (ℤ × ℤ)} {z : ℂ}
    (hz : z ∈ Work.HornSC.CellBoundaryJordan.wallSet A) :
    (∃ p ∈ A, z ∈ Work.HornSC.cell p) ∧ (∃ q ∉ A, z ∈ Work.HornSC.cell q) := by
  rw [Work.HornSC.CellBoundaryJordan.mem_wallSet] at hz
  rcases hz with ⟨u, hu, hzu⟩ | ⟨u, hu, hzu⟩
  · rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨(u.1, u.2), h1, Work.HornSC.CellBoundaryJordan.hSeg_subset_cell_left u hzu⟩,
        ⟨(u.1, u.2 - 1), h2, hSeg_subset_cell_below u hzu⟩⟩
    · exact ⟨⟨(u.1, u.2 - 1), h2, hSeg_subset_cell_below u hzu⟩,
        ⟨(u.1, u.2), h1, Work.HornSC.CellBoundaryJordan.hSeg_subset_cell_left u hzu⟩⟩
  · rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨(u.1, u.2), h1, vSeg_subset_cell_same u hzu⟩,
        ⟨(u.1 - 1, u.2), h2, vSeg_subset_cell_right u hzu⟩⟩
    · exact ⟨⟨(u.1 - 1, u.2), h2, vSeg_subset_cell_right u hzu⟩,
        ⟨(u.1, u.2), h1, vSeg_subset_cell_same u hzu⟩⟩

/-- The wall set is contained in the union of the cells. -/
lemma wallSet_subset_cellUnion (A : Finset (ℤ × ℤ)) :
    Work.HornSC.CellBoundaryJordan.wallSet A ⊆ Work.HornSC.cellUnion A := by
  intro z hz
  obtain ⟨⟨p, hp, hzp⟩, _⟩ := exists_cell_mem_and_notMem hz
  exact Work.HornSC.cell_subset_cellUnion hp hzp

/-- Every wall point is a limit point of the interior of the cell union. -/
lemma wallSet_subset_closure_interior (A : Finset (ℤ × ℤ)) :
    Work.HornSC.CellBoundaryJordan.wallSet A ⊆ closure (interior (Work.HornSC.cellUnion A)) := by
  intro z hz
  obtain ⟨⟨p, hp, hzp⟩, _⟩ := exists_cell_mem_and_notMem hz
  refine Metric.mem_closure_iff.mpr fun r hr => ?_
  obtain ⟨w, hw, hdist⟩ := exists_mem_iCell_dist_lt hzp hr
  refine ⟨w, ?_, hdist⟩
  exact interior_maximal (fun y hy => Work.HornSC.cell_subset_cellUnion hp
    (Work.PlanarSC.JC.iCell_subset_cell p hy)) (isOpen_iCell p) hw

/-- Every wall point is a limit point of the complement of the cell union. -/
lemma wallSet_subset_closure_compl (A : Finset (ℤ × ℤ)) :
    Work.HornSC.CellBoundaryJordan.wallSet A ⊆ closure ((Work.HornSC.cellUnion A)ᶜ) := by
  intro z hz
  obtain ⟨_, ⟨q, hq, hzq⟩⟩ := exists_cell_mem_and_notMem hz
  refine Metric.mem_closure_iff.mpr fun r hr => ?_
  obtain ⟨w, hw, hdist⟩ := exists_mem_iCell_dist_lt hzq hr
  refine ⟨w, ?_, hdist⟩
  simp only [Set.mem_compl_iff]
  rw [Work.PlanarSC.JC.mem_iCell_cellUnion_iff hw]
  exact hq

/-- No point of the interior of the cell union is a wall point. -/
lemma interior_disjoint_wallSet (A : Finset (ℤ × ℤ)) :
    Disjoint (interior (Work.HornSC.cellUnion A)) (Work.HornSC.CellBoundaryJordan.wallSet A) := by
  rw [Set.disjoint_left]
  intro z hzi hzw
  have h := wallSet_subset_closure_compl A hzw
  rw [closure_compl, Set.mem_compl_iff] at h
  exact h hzi


/-! ## The interior of a cell union is preconnected (from the sibling module) -/

/-! ## A wall circle enclosing a prescribed interior point -/

set_option maxHeartbeats 1600000 in
lemma exists_wall_circle_of_interior_point {B : Finset (ℤ × ℤ)} {z : ℂ}
    (hz : z ∈ interior (Work.HornSC.cellUnion B)) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      Set.range γ ⊆ Work.HornSC.CellBoundaryJordan.wallSet B ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z) := by
  classical
  obtain ⟨ε, hεpos, hgen⟩ := Work.HornSC.CellBoundaryJordan.exists_generic_ray_direction z
  -- the crossings of the ray with the wall set are odd
  have hfinW : {t : ℝ | 0 < t ∧ Work.HornSC.CellBoundaryJordan.rayPt z ε t ∈
      Work.HornSC.CellBoundaryJordan.wallSet B}.Finite :=
    Work.PlanarSC.JC.crossing_wallSet_finite B hεpos
  have hoddW : Odd hfinW.toFinset.card :=
    Work.HornSC.CellBoundaryJordan.ray_wall_crossings_odd B hεpos hz hgen hfinW
  -- the cycle decomposition of the wall set
  obtain ⟨m, k, u, hk3, hcl, hstep, hinj, hdisj, hunion⟩ :=
    Work.PlanarSC.JC.cycle_decomposition_disjoint B
  -- the crossings split among the cycles
  obtain ⟨S, T, hS, hT, hcard, hScov⟩ :=
    Work.HornSC.CellBoundaryJordan.ray_crossings_sum B hstep hdisj hunion hεpos hgen
  have hSe : hfinW.toFinset = S := by
    refine Finset.ext fun t => ?_
    rw [Set.Finite.mem_toFinset, hS t, Set.mem_ofPred_eq]
    simp only [Work.HornSC.CellBoundaryJordan.rayPt, Work.HornSC.CellBoundaryJordan.rayDir]
  have hoddS : Odd S.card := hSe ▸ hoddW
  -- some cycle is crossed oddly
  have hex : ∃ i : Fin m, Odd (T i).card := by
    by_contra hcon
    push_neg at hcon
    have hev : Even S.card := by
      rw [hcard]
      exact Finset.even_sum (s := Finset.univ) (fun i : Fin m => (T i).card)
        (fun i _ => Nat.not_odd_iff_even.mp (hcon i))
    exact (Nat.not_even_iff_odd.mpr hoddS) hev
  obtain ⟨i₀, hi₀⟩ := hex
  -- periodise the cycle
  set v : ℕ → ℤ × ℤ := (fun t => u i₀ (t % (k i₀))) with hvdef
  have hper' : ∀ t : ℕ, v (t + k i₀) = v t := by
    intro t
    have hmod : (t + k i₀) % k i₀ = t % k i₀ := by
      simpa using Nat.add_mul_mod_self_left t 1 (k i₀)
    rw [hvdef]
    simp only [hmod]
  have hvinj : ∀ j j', j < k i₀ → j' < k i₀ → v j = v j' → j = j' := by
    intro j j' hj hj' h
    rw [hvdef] at h
    simp only at h
    rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h
    exact hinj i₀ j j' hj hj' h
  have keyU : ∀ j, j < k i₀ → u i₀ (j % (k i₀)) = u i₀ j := by
    intro j hj; rw [Nat.mod_eq_of_lt hj]
  have keyU1 : ∀ j, j < k i₀ → u i₀ ((j + 1) % (k i₀)) = u i₀ (j + 1) := by
    intro j hj
    rcases lt_or_eq_of_le (show j + 1 ≤ k i₀ by omega) with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt]
    · rw [heq, Nat.mod_self, ← hcl i₀]
  have hvstep : ∀ j, j < k i₀ → Work.HornSC.CellBoundaryJordan.IsUnitAdj (v j) (v (j + 1)) := by
    intro j hj
    rw [hvdef]
    simp only
    rw [keyU j hj, keyU1 j hj]
    exact hstep i₀ j hj
  have hcycle_eq : (⋃ i ∈ {i : ℕ | i < k i₀}, Work.HornSC.CellBoundaryJordan.adjSeg (v i) (v (i + 1))) =
      (⋃ j ∈ {j : ℕ | j < k i₀},
        Work.HornSC.CellBoundaryJordan.adjSeg (u i₀ j) (u i₀ (j + 1))) := by
    ext w
    constructor
    · intro hw
      rw [Set.mem_iUnion] at hw
      obtain ⟨i, hw⟩ := hw
      rw [Set.mem_iUnion] at hw
      obtain ⟨hi, hw⟩ := hw
      rw [Set.mem_setOf_eq] at hi
      rw [hvdef] at hw
      simp only at hw
      rw [keyU i hi, keyU1 i hi] at hw
      rw [Set.mem_iUnion]
      exact ⟨i, Set.mem_iUnion.mpr ⟨by rw [Set.mem_setOf_eq]; exact hi, hw⟩⟩
    · intro hw
      rw [Set.mem_iUnion] at hw
      obtain ⟨j, hw⟩ := hw
      rw [Set.mem_iUnion] at hw
      obtain ⟨hj, hw⟩ := hw
      rw [Set.mem_setOf_eq] at hj
      rw [Set.mem_iUnion]
      refine ⟨j, Set.mem_iUnion.mpr ⟨by rw [Set.mem_setOf_eq]; exact hj, ?_⟩⟩
      rw [hvdef]
      simp only
      rw [keyU j hj, keyU1 j hj]
      exact hw
  have hsub₀ : (⋃ j ∈ {j : ℕ | j < k i₀},
      Work.HornSC.CellBoundaryJordan.adjSeg (u i₀ j) (u i₀ (j + 1))) ⊆
      Work.HornSC.CellBoundaryJordan.wallSet B := by
    rw [← hunion]
    intro w hw
    exact Set.mem_iUnion.mpr ⟨i₀, hw⟩
  have hzNotWall : z ∉ Work.HornSC.CellBoundaryJordan.wallSet B :=
    fun hw => (Set.disjoint_left.mp (interior_disjoint_wallSet B) hz) hw
  have ha : z ∉ (⋃ i ∈ {i : ℕ | i < k i₀},
      Work.HornSC.CellBoundaryJordan.adjSeg (v i) (v (i + 1))) :=
    fun h => hzNotWall (hsub₀ (hcycle_eq ▸ h))
  have hfinI : {t : ℝ | 0 < t ∧ Work.HornSC.CellBoundaryJordan.rayPt z ε t ∈
      (⋃ i ∈ {i : ℕ | i < k i₀},
        Work.HornSC.CellBoundaryJordan.adjSeg (v i) (v (i + 1)))}.Finite :=
    Work.PlanarSC.JC.crossing_adjSeg_finite (k := k i₀) v hvstep hεpos
  have hpar := Work.PlanarSC.JC.grid_cycle_crossing_parity (hk3 i₀) v hper' hvinj hvstep
    hεpos ha hgen hfinI
  have hoddI : Odd hfinI.toFinset.card := by
    have hTeq : hfinI.toFinset = T i₀ := by
      refine Finset.ext fun t => ?_
      rw [Set.Finite.mem_toFinset, hT i₀ t, Set.mem_ofPred_eq]
      simp only [Work.HornSC.CellBoundaryJordan.rayPt, Work.HornSC.CellBoundaryJordan.rayDir]
      rw [hcycle_eq]
    rw [hTeq]; exact hi₀
  have hbdd : Bornology.IsBounded (connectedComponentIn
      ((⋃ i ∈ {i : ℕ | i < k i₀},
        Work.HornSC.CellBoundaryJordan.adjSeg (v i) (v (i + 1)))ᶜ) z) :=
    hpar.mp hoddI
  obtain ⟨γ, hγinj, hγrange⟩ :=
    Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle (hk3 i₀) v
      hper' hvinj hvstep
  exact ⟨γ, hγinj, fun w hw => hsub₀ (hcycle_eq ▸ (hγrange ▸ hw)),
    (hγrange ▸ hcycle_eq ▸ hbdd)⟩


/-- A point of the cell union which is not a wall point is an interior point. -/
lemma interior_of_notMem_wallSet {A : Finset (ℤ × ℤ)} {z : ℂ}
    (hz : z ∈ Work.HornSC.cellUnion A)
    (hw : z ∉ Work.HornSC.CellBoundaryJordan.wallSet A) :
    z ∈ interior (Work.HornSC.cellUnion A) := by
  obtain ⟨r, hr, hball⟩ :=
    Work.HornSC.CellBoundaryJordan.ball_subset_cellUnion_of_notMem_wallSet hz hw
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  exact ⟨r, hr, fun w hw' => hball w (by rwa [Metric.mem_ball, dist_eq_norm] at hw')⟩

/-! ## The edge-adjacency graph of a pinch-free connected polyomino is connected -/

/-- Two closed unit cells that meet differ by at most one in each coordinate. -/
lemma cell_inter_delta {p q : ℤ × ℤ} (h : (Work.HornSC.cell p ∩ Work.HornSC.cell q).Nonempty) :
    (q.1 - p.1 = -1 ∨ q.1 - p.1 = 0 ∨ q.1 - p.1 = 1) ∧
      (q.2 - p.2 = -1 ∨ q.2 - p.2 = 0 ∨ q.2 - p.2 = 1) := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨hzp, hzq⟩ := hz
  rw [Work.HornSC.mem_cell] at hzp hzq
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hzp
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hzq
  have e1 : (q.1 : ℝ) ≤ (p.1 : ℝ) + 1 := by linarith
  have e2 : (p.1 : ℝ) ≤ (q.1 : ℝ) + 1 := by linarith
  have e3 : (q.2 : ℝ) ≤ (p.2 : ℝ) + 1 := by linarith
  have e4 : (p.2 : ℝ) ≤ (q.2 : ℝ) + 1 := by linarith
  have f1 : q.1 ≤ p.1 + 1 := by exact_mod_cast e1
  have f2 : p.1 ≤ q.1 + 1 := by exact_mod_cast e2
  have f3 : q.2 ≤ p.2 + 1 := by exact_mod_cast e3
  have f4 : p.2 ≤ q.2 + 1 := by exact_mod_cast e4
  constructor <;> omega

/-- At a lattice vertex, if the two cells `(i-1, j-1)` and `(i, j)` belong to `B`, then so does one
of the two cells sharing an edge with each of them. -/
lemma noPinchAt_or_SE_NW {B : Finset (ℤ × ℤ)} (hnp : Work.HornSC.NoPinch B) (i j : ℤ)
    (h1 : (i - 1, j - 1) ∈ B) (h2 : (i, j) ∈ B) :
    (i, j - 1) ∈ B ∨ (i - 1, j) ∈ B := by
  have hnot := hnp (i, j)
  rw [Work.HornSC.noPinchAt] at hnot
  by_contra hcon
  push_neg at hcon
  exact hnot (Or.inl ⟨h1, h2, hcon.1, hcon.2⟩)

/-- At a lattice vertex, if the two cells `(i-1, j)` and `(i, j-1)` belong to `B`, then so does one
of the two cells sharing an edge with each of them. -/
lemma noPinchAt_or_NE_SW {B : Finset (ℤ × ℤ)} (hnp : Work.HornSC.NoPinch B) (i j : ℤ)
    (h1 : (i - 1, j) ∈ B) (h2 : (i, j - 1) ∈ B) :
    (i, j) ∈ B ∨ (i - 1, j - 1) ∈ B := by
  have hnot := hnp (i, j)
  rw [Work.HornSC.noPinchAt] at hnot
  by_contra hcon
  push_neg at hcon
  exact hnot (Or.inr ⟨h1, h2, hcon.1, hcon.2⟩)

/-- A pinch-free cell set containing two diagonally opposite cells around a lattice vertex also
contains a cell sharing an edge with each of them. -/
lemma exists_common_adj4_of_diag {B : Finset (ℤ × ℤ)} (hnp : Work.HornSC.NoPinch B) {c d : ℤ × ℤ}
    (hc : c ∈ B) (hd : d ∈ B)
    (hx : d.1 - c.1 = -1 ∨ d.1 - c.1 = 1) (hy : d.2 - c.2 = -1 ∨ d.2 - c.2 = 1) :
    ∃ e ∈ B, Work.HornSC.CellBoundaryJordan.Adj4 c e ∧
      Work.HornSC.CellBoundaryJordan.Adj4 e d := by
  have hcc : (((c.1, c.2)) : ℤ × ℤ) ∈ B := by
    have h : (((c.1, c.2)) : ℤ × ℤ) = c := by ext <;> rfl
    rwa [h]
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · -- `d = (c.1 - 1, c.2 - 1)`, corner `c`
    have h1 : (((c.1 - 1, c.2 - 1)) : ℤ × ℤ) ∈ B := by
      have h : (((c.1 - 1, c.2 - 1)) : ℤ × ℤ) = d := by ext <;> omega
      rwa [h]
    rcases noPinchAt_or_SE_NW hnp c.1 c.2 h1 hcc with hE | hF
    · exact ⟨(c.1, c.2 - 1), hE, Or.inr (Or.inr (Or.inr (by ext <;> omega))),
        Or.inr (Or.inl (by ext <;> omega))⟩
    · exact ⟨(c.1 - 1, c.2), hF, Or.inr (Or.inl (by ext <;> omega)),
        Or.inr (Or.inr (Or.inr (by ext <;> omega)))⟩
  · -- `d = (c.1 - 1, c.2 + 1)`, corner `(c.1, c.2 + 1)`
    have h1 : (((c.1 - 1, c.2 + 1)) : ℤ × ℤ) ∈ B := by
      have h : (((c.1 - 1, c.2 + 1)) : ℤ × ℤ) = d := by ext <;> omega
      rwa [h]
    have h2 : (((c.1, (c.2 + 1) - 1)) : ℤ × ℤ) ∈ B := by
      have h : (((c.1, (c.2 + 1) - 1)) : ℤ × ℤ) = c := by ext <;> omega
      rwa [h]
    rcases noPinchAt_or_NE_SW hnp c.1 (c.2 + 1) h1 h2 with hE | hF
    · exact ⟨(c.1, c.2 + 1), hE, Or.inr (Or.inr (Or.inl (by ext <;> omega))),
        Or.inr (Or.inl (by ext <;> omega))⟩
    · exact ⟨(c.1 - 1, (c.2 + 1) - 1), hF, Or.inr (Or.inl (by ext <;> omega)),
        Or.inr (Or.inr (Or.inl (by ext <;> omega)))⟩
  · -- `d = (c.1 + 1, c.2 - 1)`, corner `(c.1 + 1, c.2)`
    have h1 : ((((c.1 + 1) - 1, c.2)) : ℤ × ℤ) ∈ B := by
      have h : ((((c.1 + 1) - 1, c.2)) : ℤ × ℤ) = c := by ext <;> omega
      rwa [h]
    have h2 : (((c.1 + 1, c.2 - 1)) : ℤ × ℤ) ∈ B := by
      have h : (((c.1 + 1, c.2 - 1)) : ℤ × ℤ) = d := by ext <;> omega
      rwa [h]
    rcases noPinchAt_or_NE_SW hnp (c.1 + 1) c.2 h1 h2 with hE | hF
    · exact ⟨(c.1 + 1, c.2), hE, Or.inl (by ext <;> omega),
        Or.inr (Or.inr (Or.inr (by ext <;> omega)))⟩
    · exact ⟨((c.1 + 1) - 1, c.2 - 1), hF, Or.inr (Or.inr (Or.inr (by ext <;> omega))),
        Or.inl (by ext <;> omega)⟩
  · -- `d = (c.1 + 1, c.2 + 1)`, corner `(c.1 + 1, c.2 + 1)`
    have h1 : ((((c.1 + 1) - 1, (c.2 + 1) - 1)) : ℤ × ℤ) ∈ B := by
      have h : ((((c.1 + 1) - 1, (c.2 + 1) - 1)) : ℤ × ℤ) = c := by ext <;> omega
      rwa [h]
    have h2 : (((c.1 + 1, c.2 + 1)) : ℤ × ℤ) ∈ B := by
      have h : (((c.1 + 1, c.2 + 1)) : ℤ × ℤ) = d := by ext <;> omega
      rwa [h]
    rcases noPinchAt_or_SE_NW hnp (c.1 + 1) (c.2 + 1) h1 h2 with hE | hF
    · exact ⟨(c.1 + 1, (c.2 + 1) - 1), hE, Or.inl (by ext <;> omega),
        Or.inr (Or.inr (Or.inl (by ext <;> omega)))⟩
    · exact ⟨((c.1 + 1) - 1, c.2 + 1), hF, Or.inr (Or.inr (Or.inl (by ext <;> omega))),
        Or.inl (by ext <;> omega)⟩

/-- In a connected pinch-free polyomino any two cells are joined by a chain of edge-adjacent
cells. -/
lemma adj4_reach_of_isConnected {B : Finset (ℤ × ℤ)} (hnp : Work.HornSC.NoPinch B)
    (hconn : IsConnected (Work.HornSC.cellUnion B)) {p q : ℤ × ℤ} (hp : p ∈ B) (hq : q ∈ B) :
    Relation.ReflTransGen
      (fun a b => Work.HornSC.CellBoundaryJordan.Adj4 a b ∧ b ∈ B) p q := by
  classical
  by_contra hcon
  let C : Finset (ℤ × ℤ) := B.filter (fun r => Relation.ReflTransGen
    (fun a b => Work.HornSC.CellBoundaryJordan.Adj4 a b ∧ b ∈ B) p r)
  have hCmem : ∀ r : ℤ × ℤ, r ∈ C ↔ r ∈ B ∧ Relation.ReflTransGen
      (fun a b => Work.HornSC.CellBoundaryJordan.Adj4 a b ∧ b ∈ B) p r :=
    fun r => Finset.mem_filter
  set D : Finset (ℤ × ℤ) := B \ C with hDdef
  have hpC : p ∈ C := (hCmem p).mpr ⟨hp, Relation.ReflTransGen.refl⟩
  have hqD : q ∈ D := by
    rw [hDdef, Finset.mem_sdiff]
    exact ⟨hq, fun h => hcon ((hCmem q).mp h).2⟩
  have hstep : ∀ a b : ℤ × ℤ, a ∈ C → b ∈ B →
      Work.HornSC.CellBoundaryJordan.Adj4 a b → b ∈ C := by
    intro a b ha hb hab
    rw [hCmem] at ha ⊢
    exact ⟨hb, ha.2.tail ⟨hab, hb⟩⟩
  have hdisj : Disjoint (Work.HornSC.cellUnion C) (Work.HornSC.cellUnion D) := by
    rw [Set.disjoint_left]
    intro z hzC hzD
    obtain ⟨c, hcC, hzc⟩ := Set.mem_iUnion₂.mp hzC
    obtain ⟨d, hdD, hzd⟩ := Set.mem_iUnion₂.mp hzD
    obtain ⟨hdB, hdC⟩ := Finset.mem_sdiff.mp hdD
    obtain ⟨hcB, _⟩ := (hCmem c).mp hcC
    rcases cell_inter_delta ⟨z, hzc, hzd⟩ with ⟨hx, hy⟩
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
    · -- `d = (c.1 - 1, c.2 - 1)`
      obtain ⟨e, heB, hce, hed⟩ := exists_common_adj4_of_diag hnp hcB hdB (Or.inl hx) (Or.inl hy)
      exact hdC (hstep e d (hstep c e hcC heB hce) hdB hed)
    · -- `d = (c.1 - 1, c.2)`
      exact hdC (hstep c d hcC hdB (Or.inr (Or.inl (by ext <;> omega))))
    · -- `d = (c.1 - 1, c.2 + 1)`
      obtain ⟨e, heB, hce, hed⟩ := exists_common_adj4_of_diag hnp hcB hdB (Or.inl hx) (Or.inr hy)
      exact hdC (hstep e d (hstep c e hcC heB hce) hdB hed)
    · -- `d = (c.1, c.2 - 1)`
      exact hdC (hstep c d hcC hdB (Or.inr (Or.inr (Or.inr (by ext <;> omega)))))
    · -- `d = c`
      exact hdC (by rw [show d = c by ext <;> omega]; exact hcC)
    · -- `d = (c.1, c.2 + 1)`
      exact hdC (hstep c d hcC hdB (Or.inr (Or.inr (Or.inl (by ext <;> omega)))))
    · -- `d = (c.1 + 1, c.2 - 1)`
      obtain ⟨e, heB, hce, hed⟩ := exists_common_adj4_of_diag hnp hcB hdB (Or.inr hx) (Or.inl hy)
      exact hdC (hstep e d (hstep c e hcC heB hce) hdB hed)
    · -- `d = (c.1 + 1, c.2)`
      exact hdC (hstep c d hcC hdB (Or.inl (by ext <;> omega)))
    · -- `d = (c.1 + 1, c.2 + 1)`
      obtain ⟨e, heB, hce, hed⟩ := exists_common_adj4_of_diag hnp hcB hdB (Or.inr hx) (Or.inr hy)
      exact hdC (hstep e d (hstep c e hcC heB hce) hdB hed)
  have hsub : Work.HornSC.cellUnion B ⊆
      Work.HornSC.cellUnion C ∪ Work.HornSC.cellUnion D := by
    intro z hz
    obtain ⟨r, hr, hzr⟩ := Set.mem_iUnion₂.mp hz
    by_cases hrC : r ∈ C
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨r, hrC, hzr⟩)
    · refine Or.inr (Set.mem_iUnion₂.mpr ⟨r, ?_, hzr⟩)
      rw [hDdef]; exact Finset.mem_sdiff.mpr ⟨hr, hrC⟩
  have hneC : (Work.HornSC.cellUnion B ∩ Work.HornSC.cellUnion C).Nonempty :=
    ⟨cellCenter p, Work.HornSC.cell_subset_cellUnion hp (cellCenter_mem_cell p),
      Work.HornSC.cell_subset_cellUnion hpC (cellCenter_mem_cell p)⟩
  have hneD : (Work.HornSC.cellUnion B ∩ Work.HornSC.cellUnion D).Nonempty :=
    ⟨cellCenter q, Work.HornSC.cell_subset_cellUnion hq (cellCenter_mem_cell q),
      Work.HornSC.cell_subset_cellUnion hqD (cellCenter_mem_cell q)⟩
  obtain ⟨z, -, hzC, hzD⟩ := isPreconnected_closed_iff.mp hconn.isPreconnected
    (Work.HornSC.cellUnion C) (Work.HornSC.cellUnion D)
    (Work.HornSC.isClosed_cellUnion C) (Work.HornSC.isClosed_cellUnion D) hsub hneC hneD
  exact (Set.disjoint_left.mp hdisj hzC) hzD

/-! ## From edge-connectivity of the cell graph to preconnectedness of the interior -/

/-- Every closed cell is contained in the closure of its open cell. -/
lemma cell_subset_closure_iCell (p : ℤ × ℤ) :
    Work.HornSC.cell p ⊆ closure (Work.HornSC.CellBoundaryJordan.iCell p) :=
  fun z hz => Metric.mem_closure_iff.mpr fun r hr =>
    let ⟨w, hw, hd⟩ := exists_mem_iCell_dist_lt hz hr
    ⟨w, hw, hd⟩

/-- Points of the open cell `iCell p` (for `p ∈ B`) are interior points of `cellUnion B`. -/
lemma iCell_subset_interior_cellUnion {B : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ B) :
    Work.HornSC.CellBoundaryJordan.iCell p ⊆ interior (Work.HornSC.cellUnion B) :=
  interior_maximal (fun y hy => Work.HornSC.cell_subset_cellUnion hp
    (Work.PlanarSC.JC.iCell_subset_cell p hy)) (isOpen_iCell p)

/-- A small ball about the midpoint of the unit vertical segment at `(m, j)` is covered by the two
cells sharing that segment. -/
lemma ball_subset_cell_union_vertical (m j : ℤ) :
    Metric.ball ((m : ℝ) + ((j : ℝ) + 1 / 2) * Complex.I) (1 / 4) ⊆
      Work.HornSC.cell (m - 1, j) ∪ Work.HornSC.cell (m, j) := by
  intro v hv
  rw [Metric.mem_ball, Complex.dist_eq] at hv
  have hwre : ((m : ℝ) + ((j : ℝ) + 1 / 2) * Complex.I).re = (m : ℝ) := by simp
  have hwim : ((m : ℝ) + ((j : ℝ) + 1 / 2) * Complex.I).im = (j : ℝ) + 1 / 2 := by simp
  have hre : |v.re - (m : ℝ)| < 1 / 4 := by
    have h1 := Complex.abs_re_le_norm (v - ((m : ℝ) + ((j : ℝ) + 1 / 2) * Complex.I))
    have h2 : (v - ((m : ℝ) + ((j : ℝ) + 1 / 2) * Complex.I)).re = v.re - (m : ℝ) := by
      rw [Complex.sub_re, hwre]
    rw [h2] at h1
    linarith
  have him : |v.im - ((j : ℝ) + 1 / 2)| < 1 / 4 := by
    have h1 := Complex.abs_im_le_norm (v - ((m : ℝ) + ((j : ℝ) + 1 / 2) * Complex.I))
    have h2 : (v - ((m : ℝ) + ((j : ℝ) + 1 / 2) * Complex.I)).im =
        v.im - ((j : ℝ) + 1 / 2) := by
      rw [Complex.sub_im, hwim]
    rw [h2] at h1
    linarith
  rw [abs_lt] at hre him
  by_cases h : v.re ≤ (m : ℝ)
  · left
    rw [Work.HornSC.mem_cell]
    push_cast
    exact ⟨by linarith [hre.1], by linarith [h], by linarith [him.1], by linarith [him.2]⟩
  · push_neg at h
    right
    rw [Work.HornSC.mem_cell]
    exact ⟨by linarith [h], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩

/-- A small ball about the midpoint of the unit horizontal segment at `(i, n)` is covered by the two
cells sharing that segment. -/
lemma ball_subset_cell_union_horizontal (i n : ℤ) :
    Metric.ball ((i : ℝ) + 1 / 2 + (n : ℝ) * Complex.I) (1 / 4) ⊆
      Work.HornSC.cell (i, n - 1) ∪ Work.HornSC.cell (i, n) := by
  intro v hv
  rw [Metric.mem_ball, Complex.dist_eq] at hv
  have hwre : ((i : ℝ) + 1 / 2 + (n : ℝ) * Complex.I).re = (i : ℝ) + 1 / 2 := by simp
  have hwim : ((i : ℝ) + 1 / 2 + (n : ℝ) * Complex.I).im = (n : ℝ) := by simp
  have hre : |v.re - ((i : ℝ) + 1 / 2)| < 1 / 4 := by
    have h1 := Complex.abs_re_le_norm (v - ((i : ℝ) + 1 / 2 + (n : ℝ) * Complex.I))
    have h2 : (v - ((i : ℝ) + 1 / 2 + (n : ℝ) * Complex.I)).re =
        v.re - ((i : ℝ) + 1 / 2) := by
      rw [Complex.sub_re, hwre]
    rw [h2] at h1
    linarith
  have him : |v.im - (n : ℝ)| < 1 / 4 := by
    have h1 := Complex.abs_im_le_norm (v - ((i : ℝ) + 1 / 2 + (n : ℝ) * Complex.I))
    have h2 : (v - ((i : ℝ) + 1 / 2 + (n : ℝ) * Complex.I)).im = v.im - (n : ℝ) := by
      rw [Complex.sub_im, hwim]
    rw [h2] at h1
    linarith
  rw [abs_lt] at hre him
  by_cases h : v.im ≤ (n : ℝ)
  · left
    rw [Work.HornSC.mem_cell]
    push_cast
    exact ⟨by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [h]⟩
  · push_neg at h
    right
    rw [Work.HornSC.mem_cell]
    push_cast
    exact ⟨by linarith [hre.1], by linarith [hre.2], by linarith [h], by linarith [him.2]⟩

/-- Two edge-adjacent cells of `B` have a common edge whose relative interior consists of interior
points of `cellUnion B`. -/
lemma exists_mem_interior_common_edge {B : Finset (ℤ × ℤ)} {a b : ℤ × ℤ}
    (hab : Work.HornSC.CellBoundaryJordan.Adj4 a b) (ha : a ∈ B) (hb : b ∈ B) :
    ∃ w : ℂ, w ∈ interior (Work.HornSC.cellUnion B) ∧ w ∈ Work.HornSC.cell a ∧
      w ∈ Work.HornSC.cell b := by
  have key : ∀ w : ℂ, w ∈ Work.HornSC.cell a → w ∈ Work.HornSC.cell b →
      Metric.ball w (1 / 4) ⊆ Work.HornSC.cell a ∪ Work.HornSC.cell b →
      ∃ w : ℂ, w ∈ interior (Work.HornSC.cellUnion B) ∧ w ∈ Work.HornSC.cell a ∧
        w ∈ Work.HornSC.cell b := by
    intro w hwa hwb hball
    refine ⟨w, ?_, hwa, hwb⟩
    refine interior_maximal (fun v hv => ?_) Metric.isOpen_ball
      (Metric.mem_ball_self (ε := 1 / 4) (by norm_num))
    rcases hball hv with h | h
    · exact Work.HornSC.cell_subset_cellUnion ha h
    · exact Work.HornSC.cell_subset_cellUnion hb h
  rcases hab with h | h | h | h
  · -- `b = (a.1 + 1, a.2)`: vertical common edge at `x = a.1 + 1`
    subst h
    set w : ℂ := (((a.1 + 1 : ℤ) : ℝ)) + ((a.2 : ℝ) + 1 / 2) * Complex.I with hwdef
    have hwre : w.re = ((a.1 + 1 : ℤ) : ℝ) := by rw [hwdef]; simp
    have hwim : w.im = (a.2 : ℝ) + 1 / 2 := by rw [hwdef]; simp
    refine key w ?_ ?_ ?_
    · rw [Work.HornSC.mem_cell, hwre, hwim]
      push_cast
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rw [Work.HornSC.mem_cell, hwre, hwim]
      push_cast
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · intro v hv
      rw [hwdef] at hv
      have hv' := ball_subset_cell_union_vertical (a.1 + 1) a.2 hv
      have hidx : (((a.1 + 1 - 1), a.2) : ℤ × ℤ) = a := by ext <;> omega
      rcases hv' with h' | h'
      · left; rwa [hidx] at h'
      · right; exact h'
  · -- `b = (a.1 - 1, a.2)`: vertical common edge at `x = a.1`
    subst h
    set w : ℂ := ((a.1 : ℤ) : ℝ) + ((a.2 : ℝ) + 1 / 2) * Complex.I with hwdef
    have hwre : w.re = ((a.1 : ℤ) : ℝ) := by rw [hwdef]; simp
    have hwim : w.im = (a.2 : ℝ) + 1 / 2 := by rw [hwdef]; simp
    refine key w ?_ ?_ ?_
    · rw [Work.HornSC.mem_cell, hwre, hwim]
      push_cast
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rw [Work.HornSC.mem_cell, hwre, hwim]
      push_cast
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · intro v hv
      rw [hwdef] at hv
      have h := ball_subset_cell_union_vertical a.1 a.2 hv
      rwa [Set.union_comm] at h
  · -- `b = (a.1, a.2 + 1)`: horizontal common edge at `y = a.2 + 1`
    subst h
    set w : ℂ := ((a.1 : ℝ) + 1 / 2) + (((a.2 + 1 : ℤ) : ℝ)) * Complex.I with hwdef
    have hwre : w.re = (a.1 : ℝ) + 1 / 2 := by rw [hwdef]; simp
    have hwim : w.im = ((a.2 + 1 : ℤ) : ℝ) := by rw [hwdef]; simp
    refine key w ?_ ?_ ?_
    · rw [Work.HornSC.mem_cell, hwre, hwim]
      push_cast
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rw [Work.HornSC.mem_cell, hwre, hwim]
      push_cast
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · intro v hv
      rw [hwdef] at hv
      have hv' := ball_subset_cell_union_horizontal a.1 (a.2 + 1) hv
      have hidx : ((a.1, (a.2 + 1 - 1)) : ℤ × ℤ) = a := by ext <;> omega
      rcases hv' with h' | h'
      · left; rwa [hidx] at h'
      · right; exact h'
  · -- `b = (a.1, a.2 - 1)`: horizontal common edge at `y = a.2`
    subst h
    set w : ℂ := ((a.1 : ℝ) + 1 / 2) + ((a.2 : ℤ) : ℝ) * Complex.I with hwdef
    have hwre : w.re = (a.1 : ℝ) + 1 / 2 := by rw [hwdef]; simp
    have hwim : w.im = ((a.2 : ℤ) : ℝ) := by rw [hwdef]; simp
    refine key w ?_ ?_ ?_
    · rw [Work.HornSC.mem_cell, hwre, hwim]
      push_cast
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rw [Work.HornSC.mem_cell, hwre, hwim]
      push_cast
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · intro v hv
      rw [hwdef] at hv
      have h := ball_subset_cell_union_horizontal a.1 a.2 hv
      rwa [Set.union_comm] at h

/-- If the cells of `B` are edge-connected then the interior of `cellUnion B` is preconnected. -/
lemma isPreconnected_interior_of_graph {B : Finset (ℤ × ℤ)}
    (hgraph : ∀ p ∈ B, ∀ q ∈ B, Relation.ReflTransGen
      (fun a b => Work.HornSC.CellBoundaryJordan.Adj4 a b ∧ b ∈ B) p q) :
    IsPreconnected (interior (Work.HornSC.cellUnion B)) := by
  classical
  have hpiece : ∀ p ∈ (B : Set (ℤ × ℤ)),
      IsPreconnected (interior (Work.HornSC.cellUnion B) ∩ Work.HornSC.cell p) := by
    intro p hp
    refine IsPreconnected.subset_closure (interior_cell p ▸
      ((convex_cell p).interior).isPreconnected) ?_ ?_
    · intro z hz
      exact ⟨iCell_subset_interior_cellUnion hp hz,
        Work.PlanarSC.JC.iCell_subset_cell p hz⟩
    · exact fun z hz => cell_subset_closure_iCell p hz.2
  have hglue : ∀ a b : ℤ × ℤ, a ∈ B → b ∈ B → Work.HornSC.CellBoundaryJordan.Adj4 a b →
      ((interior (Work.HornSC.cellUnion B) ∩ Work.HornSC.cell a) ∩
        (interior (Work.HornSC.cellUnion B) ∩ Work.HornSC.cell b)).Nonempty := by
    intro a b ha hb hab
    obtain ⟨w, hw1, hw2, hw3⟩ := exists_mem_interior_common_edge hab ha hb
    exact ⟨w, ⟨⟨hw1, hw2⟩, hw1, hw3⟩⟩
  have hK : ∀ p ∈ (B : Set (ℤ × ℤ)), ∀ q ∈ (B : Set (ℤ × ℤ)), Relation.ReflTransGen
      (fun i j => ((interior (Work.HornSC.cellUnion B) ∩ Work.HornSC.cell i) ∩
        (interior (Work.HornSC.cellUnion B) ∩ Work.HornSC.cell j)).Nonempty ∧
        i ∈ B) p q := by
    intro p hp q hq
    have hgen : ∀ c : ℤ × ℤ, Relation.ReflTransGen
        (fun a b => Work.HornSC.CellBoundaryJordan.Adj4 a b ∧ b ∈ B) p c → c ∈ B ∧
        Relation.ReflTransGen (fun i j => ((interior (Work.HornSC.cellUnion B) ∩
          Work.HornSC.cell i) ∩ (interior (Work.HornSC.cellUnion B) ∩
          Work.HornSC.cell j)).Nonempty ∧ i ∈ B) p c := by
      intro c hc
      induction hc with
      | refl => exact ⟨hp, Relation.ReflTransGen.refl⟩
      | tail hab hbc ih =>
          exact ⟨hbc.2, ih.2.tail ⟨hglue _ _ ih.1 hbc.2 hbc.1, ih.1⟩⟩
    exact (hgen q (hgraph p hp q hq)).2
  have hU : IsPreconnected (⋃ p ∈ (B : Set (ℤ × ℤ)),
      interior (Work.HornSC.cellUnion B) ∩ Work.HornSC.cell p) :=
    IsPreconnected.biUnion_of_reflTransGen hpiece hK
  have heq : (⋃ p ∈ (B : Set (ℤ × ℤ)),
      interior (Work.HornSC.cellUnion B) ∩ Work.HornSC.cell p) =
      interior (Work.HornSC.cellUnion B) := by
    refine Set.Subset.antisymm (Set.iUnion₂_subset fun p _ => Set.inter_subset_left) ?_
    intro z hz
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp (interior_subset hz)
    exact Set.mem_iUnion₂.mpr ⟨p, hp, hz, hzp⟩
  rwa [heq] at hU

theorem exists_enclosing_wall_circle {B : Finset (ℤ × ℤ)} (hne : B.Nonempty)
    (hnp : Work.HornSC.NoPinch B) (hconn : IsConnected (Work.HornSC.cellUnion B)) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      Set.range γ ⊆ Work.HornSC.CellBoundaryJordan.wallSet B ∧
      ∀ z ∈ Work.HornSC.cellUnion B,
        Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hne
  set z₀ : ℂ := cellCenter p₀ with hz₀def
  have hz₀ : z₀ ∈ interior (Work.HornSC.cellUnion B) := by
    rw [hz₀def]; exact cellCenter_mem_interior_cellUnion hp₀
  obtain ⟨γ, hγinj, hγsub, hbdd₀⟩ := exists_wall_circle_of_interior_point hz₀
  -- the two pieces of the complement of the curve
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hUV, hUb, hVunb, hUVc⟩ :=
    Commons.Topology.Jordan.plane_separation γ hγinj
  have hUF : U ⊆ (Set.range γ)ᶜ := hUVc ▸ subset_union_left
  have hVF : V ⊆ (Set.range γ)ᶜ := hUVc ▸ subset_union_right
  have hz₀F : z₀ ∈ (Set.range γ)ᶜ := by
    simp only [Set.mem_compl_iff]
    intro hmem
    exact (Set.disjoint_left.mp (interior_disjoint_wallSet B) hz₀) (hγsub hmem)
  -- the component of `z₀` is the bounded piece `U`
  have hcompU : connectedComponentIn ((Set.range γ)ᶜ) z₀ ⊆ U := by
    have hsuv : connectedComponentIn ((Set.range γ)ᶜ) z₀ ⊆ U ∪ V :=
      fun w hw => hUVc.symm ▸ (connectedComponentIn_subset _ _ hw)
    rcases IsPreconnected.subset_or_subset hUo hVo hUV hsuv
      (isPreconnected_connectedComponentIn (F := (Set.range γ)ᶜ) (x := z₀)) with hsub | hsub
    · exact hsub
    · exfalso
      have hz₀V : z₀ ∈ V := hsub (mem_connectedComponentIn hz₀F)
      have hVsub : V ⊆ connectedComponentIn ((Set.range γ)ᶜ) z₀ :=
        hVc.isPreconnected.subset_connectedComponentIn hz₀V hVF
      exact hVunb (hbdd₀.subset hVsub)
  have hz₀U : z₀ ∈ U := hcompU (mem_connectedComponentIn hz₀F)
  have hcompU' : connectedComponentIn ((Set.range γ)ᶜ) z₀ = U :=
    Set.Subset.antisymm hcompU
      (hUc.isPreconnected.subset_connectedComponentIn hz₀U hUF)
  -- the interior of the cell union is contained in the bounded piece
  have hpre : IsPreconnected (interior (Work.HornSC.cellUnion B)) :=
    isPreconnected_interior_of_graph (fun p hp q hq => adj4_reach_of_isConnected hnp hconn hp hq)
  have hintF : interior (Work.HornSC.cellUnion B) ⊆ (Set.range γ)ᶜ := by
    intro w hw
    simp only [Set.mem_compl_iff]
    intro hmem
    exact (Set.disjoint_left.mp (interior_disjoint_wallSet B) hw) (hγsub hmem)
  have hintU : interior (Work.HornSC.cellUnion B) ⊆ U :=
    (IsPreconnected.subset_connectedComponentIn hpre hz₀ hintF).trans (le_of_eq hcompU')
  -- and so is the closure of the cell union minus the curve
  have hFsdiff : (Set.range γ)ᶜ \ U = V := by
    rw [← hUVc]
    ext w
    simp only [Set.mem_sdiff, Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1 with h | h
      · exact absurd h h2
      · exact h
    · intro h
      exact ⟨Or.inr h, fun hc => Set.disjoint_left.mp hUV hc h⟩
  have hclU : closure U ⊆ U ∪ Set.range γ := by
    have hVopen' : IsOpen ((Set.range γ)ᶜ \ U) := hFsdiff ▸ hVo
    intro w hw
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hwU, hwγ⟩ := hcon
    have hmem : w ∈ (Set.range γ)ᶜ \ U :=
      ⟨by simpa only [Set.mem_compl_iff] using hwγ, hwU⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVopen' w hmem
    obtain ⟨y, hyU, hydist⟩ := Metric.mem_closure_iff.mp hw r hr
    have hy : y ∈ (Set.range γ)ᶜ \ U :=
      hball (by rw [Metric.mem_ball, dist_comm]; exact hydist)
    exact hy.2 hyU
  refine ⟨γ, hγinj, hγsub, ?_⟩
  intro z hz
  by_cases hzE : z ∈ Set.range γ
  · rw [connectedComponentIn_eq_empty (F := (Set.range γ)ᶜ) (x := z) (by simpa using hzE)]
    exact Bornology.isBounded_empty
  · have hzU : z ∈ U := by
      by_cases hzi : z ∈ interior (Work.HornSC.cellUnion B)
      · exact hintU hzi
      · have hzw : z ∈ Work.HornSC.CellBoundaryJordan.wallSet B := by
          by_contra hcon
          exact hzi (interior_of_notMem_wallSet hz hcon)
        exact (hclU (closure_mono hintU (wallSet_subset_closure_interior B hzw))).resolve_right hzE
    have hmem : z ∈ connectedComponentIn ((Set.range γ)ᶜ) z₀ := hcompU'.symm ▸ hzU
    rw [← connectedComponentIn_eq (F := (Set.range γ)ᶜ) hmem, hcompU']
    exact hUb



end Work.PlanarSC.Brick