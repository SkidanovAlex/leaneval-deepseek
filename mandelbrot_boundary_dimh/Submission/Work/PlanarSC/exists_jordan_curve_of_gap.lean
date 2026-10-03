import Mathlib
import Submission.Work.PlanarSC.Tools
import Submission.Work.PlanarSC.Defs
import Submission.Work.PlanarSC.isClosed_connectedComponentIn_of_isCompact
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs
import Submission.Work.HornSC.CellBoundaryJordan.exists_generic_ray_direction
import Submission.Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle
import Submission.Work.HornSC.DilInterior.cellUnion_subset_interior_dil3
import Submission.Work.HornSC.CellDistBound.dist_le_of_mem_cellUnion_dil3
import Submission.Work.HornSC.ScaleComponent.isBounded_connectedComponentIn_mul
import Submission.Work.PlanarSC.JC.adjSeg_inter_subset_lpt
import Submission.Work.PlanarSC.JC.crossing_adjSeg_finite
import Submission.Work.PlanarSC.JC.crossing_wallSet_finite
import Submission.Work.PlanarSC.JC.grid_cycle_crossing_parity
import Submission.Work.PlanarSC.JC.cycle_decomposition_disjoint
import Submission.Work.PlanarSC.JC.cellUnion_local_interior
import Submission.Work.PlanarSC.JC.rayPt_escapes_cellUnion
import Submission.Work.PlanarSC.JC.flip_crossing_wallSet
import Submission.Work.PlanarSC.Brick.exists_circleMap_of_bUnion_unbounded
import Submission.Work.PlanarSC.JC.wallSet_subset_closure_compl_aux
import Submission.Work.HornSC.CellBoundaryJordan.ray_crossing_parity

/-!
# A Jordan curve enclosing a compact set, avoiding a separated closed set

Target: `Work.PlanarSC.exists_jordan_curve_of_gap`.

The proof has two halves.

* **The polyomino half** (`cellUnion_jordan_curve`).  For a nonempty finite family `A` of unit
  lattice cells whose union is connected and an interior point `a` of that union, the wall set
  `wallSet A = frontier (cellUnion A)` contains a Jordan curve about `a` (as the range of an
  injective circle map).  The proof picks a generic ray from `a` (meeting no lattice point),
  decomposes the wall set into edge-disjoint simple grid cycles, and counts crossings: the ray
  crosses the whole wall set an odd number of times (`ray_wall_crossings_odd`), hence crosses one
  of the cycles an odd number of times (`grid_cycle_crossing_parity`), and that cycle is the
  required Jordan curve (`exists_injective_circle_map_of_grid_cycle`).

* **The reduction** (`exists_jordan_curve_of_gap`).  Scale the plane by `1/h` with `h = δ/8`, so
  that the gap becomes `> 4`; cover the image of `S` by unit cells, and consider the connected
  component `P` of the union of the `3 × 3` dilations of those cells that contains the image of
  `a`.  Every point of `S` lies in the interior of `P`, so the frontier of `P` misses `S`, while
  every point of `P` is within `2√2 < 4` of `S`, so it misses `S'`.  The polyomino half now gives a
  Jordan curve in `frontier P` enclosing `a`; scaling back by `h` gives the curve for `S`, `S'`.
-/

namespace Work.PlanarSC

open Set Metric
open scoped Complex

noncomputable section

open Work.HornSC.CellBoundaryJordan (adjSeg IsUnitAdj rayPt rayDir NonLattice)

/-! ## Bookkeeping: parity of a sum -/

private lemma even_not_odd {n : ℕ} (h : Even n) : ¬ Odd n := by
  obtain ⟨k, hk⟩ := h
  rintro ⟨l, hl⟩
  omega

private lemma even_sum_finset {ι : Type*} (s : Finset ι) {f : ι → ℕ}
    (h : ∀ i ∈ s, Even (f i)) : Even (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- If a sum of natural numbers is odd then some summand is odd. -/
private lemma exists_odd_of_odd_sum {m : ℕ} {f : Fin m → ℕ} (h : Odd (∑ i, f i)) :
    ∃ i, Odd (f i) := by
  by_contra hc
  push_neg at hc
  have hev : Even (∑ i, f i) := by
    have := even_sum_finset (Finset.univ : Finset (Fin m)) (f := f) (fun i _ =>
      (Nat.even_or_odd (f i)).resolve_right (hc i))
    simpa using this
  exact even_not_odd hev h

/-! ## Elementary cell lemmas -/

/-- Every point of the plane lies in a unit lattice cell. -/
private lemma exists_cell_mem (z : ℂ) :
    ∃ p : ℤ × ℤ, z ∈ Work.HornSC.cell p :=
  ⟨(⌊z.re⌋, ⌊z.im⌋), Work.HornSC.mem_cell.mpr
    ⟨Int.floor_le z.re, le_of_lt (Int.lt_floor_add_one z.re),
     Int.floor_le z.im, le_of_lt (Int.lt_floor_add_one z.im)⟩⟩

private lemma convex_cell (p : ℤ × ℤ) : Convex ℝ (Work.HornSC.cell p) := by
  have h1 : Convex ℝ {z : ℂ | (p.1 : ℝ) ≤ z.re} :=
    (convex_Ici _).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ {z : ℂ | z.re ≤ (p.1 : ℝ) + 1} :=
    (convex_Iic _).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h3 : Convex ℝ {z : ℂ | (p.2 : ℝ) ≤ z.im} :=
    (convex_Ici _).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  have h4 : Convex ℝ {z : ℂ | z.im ≤ (p.2 : ℝ) + 1} :=
    (convex_Iic _).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  have h := h1.inter (h2.inter (h3.inter h4))
  convert h using 1
  ext z
  simp only [Work.HornSC.mem_cell, Set.mem_inter_iff, Set.mem_setOf_eq]

/-- The finite family of lattice cells meeting `C` inside the box of cells `[-N,N]²`. -/
private noncomputable def cellsMeeting (N : ℕ) (C : Set ℂ) : Finset (ℤ × ℤ) := by
  classical
  exact (Finset.Icc (-(N : ℤ), -(N : ℤ)) (N, N)).filter (fun p => (Work.HornSC.cell p ∩ C).Nonempty)

/-- The square `[-N,N]²` of the plane. -/
private def boxSet (N : ℕ) : Set ℂ :=
  {z : ℂ | -(N : ℝ) ≤ z.re ∧ z.re ≤ (N : ℝ) ∧ -(N : ℝ) ≤ z.im ∧ z.im ≤ (N : ℝ)}

private lemma mem_cellsMeeting {N : ℕ} {C : Set ℂ} {p : ℤ × ℤ} :
    p ∈ cellsMeeting N C ↔
      p ∈ Finset.Icc (-(N : ℤ), -(N : ℤ)) (N, N) ∧ (Work.HornSC.cell p ∩ C).Nonempty := by
  classical
  rw [cellsMeeting]
  exact Finset.mem_filter

/-- Every point of the box `[-N,N]²` lies in one of the cells with indices in `[-N,N]²`. -/
private lemma exists_cell_mem_Icc {N : ℕ} {z : ℂ} (hz : z ∈ boxSet N) :
    ∃ p : ℤ × ℤ, p ∈ Finset.Icc (-(N : ℤ), -(N : ℤ)) (N, N) ∧ z ∈ Work.HornSC.cell p := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have e1 : ⌊(-(N : ℝ))⌋ = -(N : ℤ) := by rw [Int.floor_neg, Int.ceil_natCast]
  have e2 : ⌊((N : ℝ))⌋ = (N : ℤ) := Int.floor_intCast N
  refine ⟨(⌊z.re⌋, ⌊z.im⌋), ?_, ?_⟩
  · rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [Prod.mk_le_mk]
      exact ⟨le_trans (le_of_eq e1.symm) (Int.floor_mono h1),
        le_trans (le_of_eq e1.symm) (Int.floor_mono h3)⟩
    · rw [Prod.mk_le_mk]
      exact ⟨le_trans (Int.floor_mono h2) (le_of_eq e2),
        le_trans (Int.floor_mono h4) (le_of_eq e2)⟩
  · refine Work.HornSC.mem_cell.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact Int.floor_le z.re
    · exact le_of_lt (Int.lt_floor_add_one z.re)
    · exact Int.floor_le z.im
    · exact le_of_lt (Int.lt_floor_add_one z.im)

private lemma boxSet_subset_cellUnion (N : ℕ) :
    boxSet N ⊆ Work.HornSC.cellUnion (Finset.Icc (-(N : ℤ), -(N : ℤ)) (N, N)) := by
  intro z hz
  obtain ⟨p, hp, hzp⟩ := exists_cell_mem_Icc hz
  exact Set.mem_iUnion₂.mpr ⟨p, hp, hzp⟩

private lemma subset_cellUnion_cellsMeeting {N : ℕ} {C : Set ℂ} (hC : C ⊆ boxSet N) :
    C ⊆ Work.HornSC.cellUnion (cellsMeeting N C) := by
  intro c hc
  obtain ⟨p, hp, hcp⟩ := exists_cell_mem_Icc (hC hc)
  exact Set.mem_iUnion₂.mpr
    ⟨p, (mem_cellsMeeting.mpr ⟨hp, ⟨c, hcp, hc⟩⟩), hcp⟩

private lemma cellsMeeting_nonempty {N : ℕ} {C : Set ℂ} (hne : C.Nonempty) (hC : C ⊆ boxSet N) :
    (cellsMeeting N C).Nonempty := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨p, hp, hcp⟩ := exists_cell_mem_Icc (hC hc)
  exact ⟨p, mem_cellsMeeting.mpr ⟨hp, ⟨c, hcp, hc⟩⟩⟩

end

open Work.HornSC.CellBoundaryJordan (adjSeg IsUnitAdj rayPt rayDir NonLattice)

/- TEMPORARY stubs for the delegated lemmas (to be replaced by imports). -/
private lemma exists_delta_of_open {γ : ℝ → ℂ} (hγ : Continuous γ) {U : Set ℂ} (hU : IsOpen U)
    {t : ℝ} (ht : γ t ∈ U) : ∃ δ > 0, ∀ s : ℝ, |s - t| < δ → γ s ∈ U := by
  have hopen : IsOpen (γ ⁻¹' U) := hU.preimage hγ
  obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen t ht
  exact ⟨δ, hδpos, fun s hs => hδ (show s ∈ Metric.ball t δ from by
    rw [Metric.mem_ball, Real.dist_eq]; exact hs)⟩

/-- **A ray from an interior point crosses the wall set an odd number of times.** -/
private lemma ray_crossings_odd_aux (A : Finset (ℤ × ℤ)) {a : ℂ} {ε : ℝ} (hε : 0 < ε)
    (ha : a ∈ interior (Work.HornSC.cellUnion A))
    (hgen : ∀ t : ℝ, 0 < t → ∀ m n : ℤ,
      a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ≠ (m : ℂ) + (n : ℂ) * Complex.I)
    (hfin : {t : ℝ | 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈
      Work.HornSC.CellBoundaryJordan.wallSet A}.Finite) :
    Odd hfin.toFinset.card := by
  classical
  set S := hfin.toFinset with hSdef
  have hSmem : ∀ t : ℝ, t ∈ S ↔ 0 < t ∧
      rayPt a ε t ∈ Work.HornSC.CellBoundaryJordan.wallSet A := by
    intro t
    simp [hSdef, Set.Finite.mem_toFinset, rayPt, rayDir]
  have hSpos : ∀ t ∈ S, 0 < t := fun t ht => ((hSmem t).mp ht).1
  obtain ⟨Tesc, hTesc⟩ := Work.PlanarSC.JC.rayPt_escapes_cellUnion A a ε
  set T : ℝ := max Tesc ((∑ s ∈ S, s) + 1) with hTdef
  have hTS : ∀ t ∈ S, 0 < t ∧ t < T := by
    intro t ht
    refine ⟨hSpos t ht, ?_⟩
    have h1 : t ≤ ∑ s ∈ S, s :=
      Finset.single_le_sum (fun s hs => le_of_lt (hSpos s hs)) ht
    rw [hTdef]
    have h2 : (∑ s ∈ S, s) + 1 ≤ max Tesc ((∑ s ∈ S, s) + 1) := le_max_right _ _
    linarith
  have hTpos : 0 < T := by
    rw [hTdef]
    have h1 : 0 ≤ ∑ s ∈ S, s := Finset.sum_nonneg (fun s hs => le_of_lt (hSpos s hs))
    have h2 : (∑ s ∈ S, s) + 1 ≤ max Tesc ((∑ s ∈ S, s) + 1) := le_max_right _ _
    linarith
  have hTescT : Tesc ≤ T := by rw [hTdef]; exact le_max_left _ _
  have hγcont : Continuous (fun s : ℝ => rayPt a ε s) := by
    simp only [rayPt]; fun_prop
  have hloc : ∀ t ∈ Set.Icc (0 : ℝ) T, t ∉ S → ∃ δ > 0, ∀ s, |s - t| < δ →
      ((rayPt a ε s ∈ Work.HornSC.cellUnion A) ↔
        (rayPt a ε t ∈ Work.HornSC.cellUnion A)) := by
    intro t ht htS
    have hgood : rayPt a ε t ∈ interior (Work.HornSC.cellUnion A) ∨
        rayPt a ε t ∉ Work.HornSC.cellUnion A := by
      rcases eq_or_lt_of_le ht.1 with h0 | htpos
      · left
        rw [← h0]
        simpa [rayPt, rayDir] using ha
      · by_cases hineq : rayPt a ε t ∈ Work.HornSC.cellUnion A
        · left
          have hnotwall : rayPt a ε t ∉ Work.HornSC.CellBoundaryJordan.wallSet A := by
            intro hw
            exact htS ((hSmem t).mpr ⟨htpos, hw⟩)
          obtain ⟨r, hr, hball⟩ := Work.PlanarSC.JC.cellUnion_local_interior hineq hnotwall
          have hball' : Metric.ball (rayPt a ε t) r ⊆ Work.HornSC.cellUnion A := fun w hw =>
            hball w (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
          exact interior_maximal hball' Metric.isOpen_ball (Metric.mem_ball_self hr)
        · right; exact hineq
    rcases hgood with hint | hout
    · obtain ⟨δ, hδpos, hδ⟩ := exists_delta_of_open hγcont isOpen_interior hint
      exact ⟨δ, hδpos, fun s hs =>
        ⟨fun _ => interior_subset hint, fun _ => interior_subset (hδ s hs)⟩⟩
    · obtain ⟨δ, hδpos, hδ⟩ :=
        exists_delta_of_open hγcont (Work.HornSC.isClosed_cellUnion A).isOpen_compl hout
      exact ⟨δ, hδpos, fun s hs => ⟨fun hc => absurd hc (hδ s hs), fun hc => absurd hc hout⟩⟩
  have hflip : ∀ t ∈ S, ∃ δ > 0, ∀ s, 0 < s → s < δ →
      ((rayPt a ε (t + s) ∈ Work.HornSC.cellUnion A) ↔
        ¬ (rayPt a ε (t - s) ∈ Work.HornSC.cellUnion A)) := by
    intro t htS
    have htpos : 0 < t := ((hSmem t).mp htS).1
    have hzw : rayPt a ε t ∈ Work.HornSC.CellBoundaryJordan.wallSet A := ((hSmem t).mp htS).2
    have hnl : NonLattice (rayPt a ε t) := by
      intro m n hc
      exact hgen t htpos m n (by simpa [rayPt, rayDir] using hc)
    have hvr : 0 < (rayDir ε).re := by simp [rayDir]
    have hvi : 0 < (rayDir ε).im := by simpa [rayDir] using hε
    obtain ⟨δ, hδpos, hδ⟩ := Work.PlanarSC.JC.flip_crossing_wallSet hzw hnl hvr hvi
    refine ⟨δ, hδpos, fun s hs0 hsδ => ?_⟩
    have e1 : rayPt a ε (t + s) = rayPt a ε t + (s : ℂ) * rayDir ε := by
      simp only [rayPt, Complex.ofReal_add]; ring_nf
    have e2 : rayPt a ε (t - s) = rayPt a ε t - (s : ℂ) * rayDir ε := by
      simp only [rayPt, Complex.ofReal_sub]; ring_nf
    rw [e1, e2]
    exact hδ s hs0 hsδ
  have hP0 : rayPt a ε 0 ∈ Work.HornSC.cellUnion A := by
    simpa [rayPt, rayDir] using interior_subset ha
  have hPT : ¬ (rayPt a ε T ∈ Work.HornSC.cellUnion A) := hTesc T hTescT
  have hodd : Odd S.card :=
    Work.HornSC.CellBoundaryJordan.odd_card_of_flip hTpos hTS hloc hflip hP0 hPT
  exact hSdef ▸ hodd

/-- **The frontier of a finite union of lattice cells is its wall set.** -/
private lemma frontier_eq_wallSet_aux (A : Finset (ℤ × ℤ)) :
    frontier (Work.HornSC.cellUnion A) = Work.HornSC.CellBoundaryJordan.wallSet A := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    by_contra hzw
    have hcl : closure (Work.HornSC.cellUnion A) = Work.HornSC.cellUnion A :=
      closure_eq_iff_isClosed.mpr (Work.HornSC.isClosed_cellUnion A)
    have hzc : z ∈ Work.HornSC.cellUnion A := hcl ▸ hz.1
    obtain ⟨r, hr, hball⟩ := Work.PlanarSC.JC.cellUnion_local_interior hzc hzw
    exact hz.2 (mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Metric.ball_mem_nhds z hr)
        (fun w hw => hball w (by simpa [Metric.mem_ball, dist_eq_norm] using hw))))
  · intro z hz
    refine ⟨?_, ?_⟩
    · exact subset_closure (Work.PlanarSC.Brick.wallSet_subset_cellUnion A hz)
    · intro hzint
      have h2 : z ∈ closure (Work.HornSC.cellUnion A)ᶜ :=
        Work.PlanarSC.JC.wallSet_subset_closure_compl_aux A hz
      rw [closure_compl] at h2
      exact h2 hzint

/-- **The Jordan curve through the wall set of a polyomino.** -/
theorem cellUnion_jordan_curve {A : Finset (ℤ × ℤ)} (hA : A.Nonempty)
    (hconn : IsConnected (Work.HornSC.cellUnion A)) {a : ℂ}
    (ha : a ∈ interior (Work.HornSC.cellUnion A)) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      Set.range γ ⊆ frontier (Work.HornSC.cellUnion A) ∧ a ∉ Set.range γ ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) := by
  classical
  have hfront : frontier (Work.HornSC.cellUnion A) =
      Work.HornSC.CellBoundaryJordan.wallSet A := frontier_eq_wallSet_aux A
  have haW : a ∉ Work.HornSC.CellBoundaryJordan.wallSet A := by
    rw [← hfront]; exact fun h => h.2 ha
  obtain ⟨ε, hεpos, hgen⟩ := Work.HornSC.CellBoundaryJordan.exists_generic_ray_direction a
  obtain ⟨m, k, u, hk, hperu, hstepu, hinju, hdisj, hunion⟩ :=
    Work.PlanarSC.JC.cycle_decomposition_disjoint A
  set v : Fin m → ℕ → ℤ × ℤ := fun i j => u i (j % k i) with hv
  have hv_def : ∀ (i : Fin m) (j : ℕ), v i j = u i (j % k i) := fun i j => rfl
  have hvk : ∀ i, v i (k i) = u i (k i) := by
    intro i; rw [hv_def, Nat.mod_self, ← hperu i]
  have hperv : ∀ i j, v i (j + k i) = v i j := by
    intro i j; rw [hv_def, hv_def, Nat.add_mod_right]
  have hv_eq : ∀ {i : Fin m} {j : ℕ}, j < k i → v i j = u i j := by
    intro i j hj; rw [hv_def, Nat.mod_eq_of_lt hj]
  have hinjv : ∀ i j j', j < k i → j' < k i → v i j = v i j' → j = j' := by
    intro i j j' hj hj' h
    rw [hv_eq hj, hv_eq hj'] at h
    exact hinju i j j' hj hj' h
  have hstepv : ∀ i j, j < k i → IsUnitAdj (v i j) (v i (j + 1)) := by
    intro i j hj
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with h | h
    · rw [hv_eq hj, hv_eq h]; exact hstepu i j hj
    · have hj1 : j + 1 = k i := by omega
      have h1 : v i (j + 1) = u i (j + 1) := by rw [hj1, hvk i]
      rw [hv_eq hj, h1]
      exact hstepu i j hj
  have hsegv : ∀ i j, j < k i → adjSeg (v i j) (v i (j + 1)) = adjSeg (u i j) (u i (j + 1)) := by
    intro i j hj
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with h | h
    · rw [hv_eq hj, hv_eq h]
    · have hj1 : j + 1 = k i := by omega
      have h1 : v i (j + 1) = u i (j + 1) := by rw [hj1, hvk i]
      rw [hv_eq hj, h1]
  -- the point set of each cycle
  let C : Fin m → Set ℂ := fun i => ⋃ j ∈ {j : ℕ | j < k i}, adjSeg (v i j) (v i (j + 1))
  have hC_eq : ∀ i, C i = ⋃ j ∈ {j : ℕ | j < k i}, adjSeg (u i j) (u i (j + 1)) := by
    intro i
    refine le_antisymm ?_ ?_
    · intro z hz
      simp only [C, Set.mem_iUnion, Set.mem_setOf_eq] at hz
      obtain ⟨j, hj, hzj⟩ := hz
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨j, hj, by rw [← hsegv i j hj]; exact hzj⟩
    · intro z hz
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz
      obtain ⟨j, hj, hzj⟩ := hz
      simp only [C, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨j, hj, by rw [hsegv i j hj]; exact hzj⟩
  have hwall : (⋃ i, C i) = Work.HornSC.CellBoundaryJordan.wallSet A := by
    rw [← hunion]
    exact Set.iUnion_congr fun i => hC_eq i
  -- the crossing sets
  have hSfin : {t : ℝ | 0 < t ∧ rayPt a ε t ∈
      Work.HornSC.CellBoundaryJordan.wallSet A}.Finite :=
    Work.PlanarSC.JC.crossing_wallSet_finite A hεpos
  have hodd : Odd hSfin.toFinset.card := ray_crossings_odd_aux A hεpos ha hgen hSfin
  have hSifin : ∀ i : Fin m, {t : ℝ | 0 < t ∧ rayPt a ε t ∈ C i}.Finite :=
    fun i => Work.PlanarSC.JC.crossing_adjSeg_finite (v i) (hstepv i) hεpos
  let F : Fin m → Finset ℝ := fun i => (hSifin i).toFinset
  have hSunion : hSfin.toFinset = Finset.biUnion (Finset.univ : Finset (Fin m)) F := by
    ext t
    simp only [F, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨htpos, htW⟩
      have hmem : rayPt a ε t ∈ (⋃ i, C i) := by rwa [hwall]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
      exact ⟨i, htpos, hi⟩
    · rintro ⟨i, htpos, hi⟩
      refine ⟨htpos, ?_⟩
      rw [← hwall]
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hdisjF : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ i' ∈ Finset.univ, i ≠ i' →
      Disjoint (F i) (F i') := by
    intro i _ i' _ hne
    rw [Finset.disjoint_left]
    intro t ht ht'
    simp only [F, C, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_setOf_eq] at ht ht'
    obtain ⟨j, hj, htj⟩ := ht.2
    obtain ⟨j', hj', ht'j'⟩ := ht'.2
    have hseg_ne : adjSeg (v i j) (v i (j + 1)) ≠ adjSeg (v i' j') (v i' (j' + 1)) := by
      rw [hsegv i j hj, hsegv i' j' hj']
      exact hdisj i i' hne j j' hj hj'
    obtain ⟨w, hw⟩ := Work.PlanarSC.JC.adjSeg_inter_subset_lpt (hstepv i j hj) (hstepv i' j' hj')
      hseg_ne htj ht'j'
    exact hgen t ht.1 w.1 w.2 (by
      have h2 : rayPt a ε t = (w.1 : ℂ) + (w.2 : ℂ) * Complex.I :=
        hw.trans (Work.HornSC.CellBoundaryJordan.lpt_eq_iff' w.1 w.2)
      simpa only [Work.HornSC.CellBoundaryJordan.rayPt,
        Work.HornSC.CellBoundaryJordan.rayDir] using h2)
  have hcard : hSfin.toFinset.card = ∑ i : Fin m, (F i).card := by
    rw [hSunion, Finset.card_biUnion hdisjF]
  have hodd_sum : Odd (∑ i : Fin m, (F i).card) := by
    rw [← hcard]; exact hodd
  obtain ⟨i₀, hi₀⟩ := exists_odd_of_odd_sum hodd_sum
  have ha_cycle : a ∉ C i₀ := by
    intro hcon
    apply haW
    rw [← hwall]
    exact Set.mem_iUnion.mpr ⟨i₀, hcon⟩
  have hbdd : Bornology.IsBounded (connectedComponentIn ((C i₀)ᶜ) a) :=
    (Work.PlanarSC.JC.grid_cycle_crossing_parity (hk i₀) (v i₀) (hperv i₀) (hinjv i₀) (hstepv i₀)
      hεpos ha_cycle hgen (hSifin i₀)).mp hi₀
  obtain ⟨γ, hγinj, hγrange⟩ :=
    Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle (hk i₀) (v i₀)
      (hperv i₀) (hinjv i₀) (hstepv i₀)
  have hγC : Set.range γ = C i₀ := hγrange
  refine ⟨γ, hγinj, ?_, ?_, ?_⟩
  · intro z hz
    rw [hγC] at hz
    rw [hfront, ← hwall]
    exact Set.mem_iUnion.mpr ⟨i₀, hz⟩
  · rw [hγC]; exact ha_cycle
  · rw [hγC]; exact hbdd

/-- **The main theorem.** -/
theorem exists_jordan_curve_of_gap {S S' : Set ℂ} (hS : IsCompact S) (hSne : S.Nonempty)
    (hS' : IsClosed S') (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ S', δ ≤ dist s s')
    {a : ℂ} (ha : a ∈ S) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧ Set.range γ ⊆ (S ∪ S')ᶜ ∧
      a ∉ Set.range γ ∧ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) := by
  classical
  obtain ⟨δ, hδpos, hgap⟩ := hgap
  have hsqrt2 : Real.sqrt 2 < (2 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  set h : ℝ := δ / 8 with hhdef
  have hhpos : 0 < h := by rw [hhdef]; positivity
  have hgap8 : 2 * Real.sqrt 2 < δ / h := by
    have hdiv : δ / h = 8 := by rw [hhdef]; field_simp
    rw [hdiv]; nlinarith
  set c : ℂ := ((h⁻¹ : ℝ) : ℂ) with hcdef
  have hcne : c ≠ 0 := by
    simp only [hcdef, ne_eq, Complex.ofReal_eq_zero]
    exact inv_ne_zero (ne_of_gt hhpos)
  have hcinv : c * (h : ℂ) = 1 := by
    rw [hcdef, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hhpos), Complex.ofReal_one]
  set S₁ : Set ℂ := (fun z : ℂ => c * z) '' S with hS₁def
  set S'₁ : Set ℂ := (fun z : ℂ => c * z) '' S' with hS'₁def
  set a₁ : ℂ := c * a with ha₁def
  have hS₁cpt : IsCompact S₁ := hS.image (by fun_prop)
  have hS₁ne : S₁.Nonempty := hSne.image _
  have ha₁ : a₁ ∈ S₁ := ⟨a, ha, rfl⟩
  -- the gap survives the scaling
  have hgap₁ : ∀ y ∈ S₁, ∀ z ∈ S'₁, 2 * Real.sqrt 2 < dist y z := by
    rintro y ⟨u, hu, rfl⟩ z ⟨v, hv, rfl⟩
    have h1 : dist (c * u) (c * v) = h⁻¹ * dist u v := by
      have hy : c * u = (h⁻¹ : ℝ) • u := by rw [hcdef, ← Complex.real_smul]
      have hz : c * v = (h⁻¹ : ℝ) • v := by rw [hcdef, ← Complex.real_smul]
      rw [hy, hz, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hhpos)]
    rw [h1]
    have h2 : h⁻¹ * δ ≤ h⁻¹ * dist u v :=
      mul_le_mul_of_nonneg_left (hgap u hu v hv) (le_of_lt (inv_pos.mpr hhpos))
    have h3 : 2 * Real.sqrt 2 < h⁻¹ * δ := by
      have : h⁻¹ * δ = δ / h := by rw [div_eq_inv_mul]
      rw [this]; exact hgap8
    linarith
  -- a box containing `S₁`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ S₁ ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hS₁cpt.isBounded
    exact ⟨max R 0, le_max_right _ _, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, S₁ ⊆ boxSet N := by
    refine ⟨⌈R⌉₊, fun z hz => ?_⟩
    have hzR : ‖z‖ ≤ R := by
      have := hR.2 hz
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hre : |z.re| ≤ R := le_trans (Complex.abs_re_le_norm z) hzR
    have him : |z.im| ≤ R := le_trans (Complex.abs_im_le_norm z) hzR
    have hN' : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
    exact ⟨by linarith [(abs_le.mp hre).1, hN'], by linarith [(abs_le.mp hre).2, hN'],
      by linarith [(abs_le.mp him).1, hN'], by linarith [(abs_le.mp him).2, hN']⟩
  set A₀ : Finset (ℤ × ℤ) := cellsMeeting N S₁ with hA₀def
  have hA_sub : S₁ ⊆ Work.HornSC.cellUnion A₀ := subset_cellUnion_cellsMeeting hN
  have hA_spec : ∀ p ∈ A₀, (Work.HornSC.cell p ∩ S₁).Nonempty :=
    fun p hp => (mem_cellsMeeting.mp hp).2
  have hAne : A₀.Nonempty := cellsMeeting_nonempty hS₁ne hN
  have hS₁_int : S₁ ⊆ interior (Work.HornSC.cellUnion (Work.HornSC.dil3 A₀)) :=
    fun z hz => Work.HornSC.DilInterior.cellUnion_subset_interior_dil3 A₀ (hA_sub hz)
  -- the connected component of `a₁`
  set P : Set ℂ := connectedComponentIn (Work.HornSC.cellUnion (Work.HornSC.dil3 A₀)) a₁ with hPdef
  have ha₁P : a₁ ∈ Work.HornSC.cellUnion (Work.HornSC.dil3 A₀) :=
    interior_subset (hS₁_int ha₁)
  have hPconn : IsConnected P := isConnected_connectedComponentIn_iff.mpr ha₁P
  have hPsub : P ⊆ Work.HornSC.cellUnion (Work.HornSC.dil3 A₀) := connectedComponentIn_subset _ _
  have hPcl : IsClosed P :=
    isClosed_connectedComponentIn_of_isCompact
      (Work.HornSC.isCompact_cellUnion (Work.HornSC.dil3 A₀)) a₁
  -- the cells contained in `P`
  set B : Finset (ℤ × ℤ) := (Work.HornSC.dil3 A₀).filter (fun p => Work.HornSC.cell p ⊆ P)
    with hBdef
  have mem_B {p : ℤ × ℤ} : p ∈ B ↔ p ∈ Work.HornSC.dil3 A₀ ∧ Work.HornSC.cell p ⊆ P := by
    classical
    rw [hBdef]; exact Finset.mem_filter
  have hBeq : Work.HornSC.cellUnion B = P := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
      exact (mem_B.mp hp).2 hzp
    · intro z hz
      have hzP : z ∈ Work.HornSC.cellUnion (Work.HornSC.dil3 A₀) := hPsub hz
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hzP
      have hcell : Work.HornSC.cell p ⊆ P := by
        have h1 : Work.HornSC.cell p ⊆
            connectedComponentIn (Work.HornSC.cellUnion (Work.HornSC.dil3 A₀)) z :=
          (convex_cell p).isPreconnected.subset_connectedComponentIn (x := z) hzp
            (fun w hw => Set.mem_iUnion₂.mpr ⟨p, hp, hw⟩)
        have h2 : connectedComponentIn (Work.HornSC.cellUnion (Work.HornSC.dil3 A₀)) z = P :=
          (connectedComponentIn_eq hz).symm.trans hPdef.symm
        rwa [h2] at h1
      exact Set.mem_iUnion₂.mpr ⟨p, mem_B.mpr ⟨hp, hcell⟩, hzp⟩
  have hBne : B.Nonempty := by
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp ha₁P
    have hcell : Work.HornSC.cell p ⊆ P :=
      (convex_cell p).isPreconnected.subset_connectedComponentIn hzp
        (fun w hw => Set.mem_iUnion₂.mpr ⟨p, hp, hw⟩)
    exact ⟨p, mem_B.mpr ⟨hp, hcell⟩⟩
  have ha₁int : a₁ ∈ interior (Work.HornSC.cellUnion B) := by
    rw [hBeq]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a₁ (hS₁_int ha₁)
    refine mem_interior_iff_mem_nhds.mpr ?_
    refine Filter.mem_of_superset (Metric.ball_mem_nhds a₁ hε) ?_
    exact (convex_ball a₁ ε).isPreconnected.subset_connectedComponentIn (Metric.mem_ball_self hε)
      (fun w hw => interior_subset (hball hw))
  -- the polyomino half
  obtain ⟨γ₁, hγ₁inj, hγ₁rng, hγ₁a, hγ₁bdd⟩ :=
    cellUnion_jordan_curve hBne (hBeq ▸ hPconn) ha₁int
  -- the frontier of `P` avoids `S₁`
  have hS₁_disj : ∀ z ∈ S₁, z ∉ frontier P := by
    intro z hz hzfr
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z (hS₁_int hz)
    obtain ⟨w, hwP, hwdist⟩ := Metric.mem_closure_iff.mp hzfr.1 ε hε
    have hwb : w ∈ Metric.ball z ε := by rw [Metric.mem_ball]; rwa [dist_comm]
    have hsub : Metric.ball z ε ⊆ P := by
      have h1 : Metric.ball z ε ⊆
          connectedComponentIn (Work.HornSC.cellUnion (Work.HornSC.dil3 A₀)) w :=
        (convex_ball z ε).isPreconnected.subset_connectedComponentIn hwb
          (fun u hu => interior_subset (hball hu))
      have h2 : connectedComponentIn (Work.HornSC.cellUnion (Work.HornSC.dil3 A₀)) w = P :=
        (connectedComponentIn_eq hwP).symm.trans hPdef.symm
      rwa [h2] at h1
    exact hzfr.2 (mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Metric.ball_mem_nhds z hε) hsub))
  have hγ₁fr : Set.range γ₁ ⊆ frontier P := by
    rw [← hBeq]; exact hγ₁rng
  have hγnotS₁ : ∀ w : Circle, γ₁ w ∉ S₁ := by
    intro w hw
    exact hS₁_disj (γ₁ w) hw (hγ₁fr (Set.mem_range_self w))
  have hγnotS₁' : ∀ w : Circle, γ₁ w ∉ S'₁ := by
    intro w hw
    have hfr_sub : frontier P ⊆ P := by
      have h1 : closure P ⊆ P := (IsClosed.closure_subset_iff hPcl).mpr subset_rfl
      exact subset_trans frontier_subset_closure h1
    have hmem : γ₁ w ∈ Work.HornSC.cellUnion (Work.HornSC.dil3 A₀) :=
      hPsub (hfr_sub (hγ₁fr (Set.mem_range_self w)))
    have hbdd : Metric.infDist (γ₁ w) S₁ ≤ 2 * Real.sqrt 2 :=
      Work.HornSC.CellDistBound.dist_le_of_mem_cellUnion_dil3 hA_spec hmem
    obtain ⟨y₀, hy₀S, hy₀eq⟩ := hS₁cpt.exists_infDist_eq_dist hS₁ne (γ₁ w)
    have hlt : 2 * Real.sqrt 2 < dist (γ₁ w) y₀ := by
      rw [dist_comm]; exact hgap₁ y₀ hy₀S (γ₁ w) hw
    rw [hy₀eq] at hbdd
    exact absurd (lt_of_lt_of_le hlt hbdd) (lt_irrefl _)
  -- scale back
  have hkey : ∀ z : ℂ, c * ((h : ℂ) * z) = z := by
    intro z; rw [← mul_assoc, hcinv, one_mul]
  have hhne : ((h : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hhpos
  refine ⟨⟨fun w : Circle => ((h : ℝ) : ℂ) * γ₁ w, by fun_prop⟩, ?_, ?_, ?_, ?_⟩
  · rintro w w' hww
    exact hγ₁inj (mul_left_cancel₀ hhne hww)
  · rintro z ⟨w, hwz⟩
    rw [← hwz]
    intro hz
    rcases hz with hz | hz
    · exact hγnotS₁ w (by
        have h1 : c * (((h : ℝ) : ℂ) * γ₁ w) ∈ S₁ := ⟨((h : ℝ) : ℂ) * γ₁ w, hz, rfl⟩
        rwa [hkey] at h1)
    · exact hγnotS₁' w (by
        have h1 : c * (((h : ℝ) : ℂ) * γ₁ w) ∈ S'₁ := ⟨((h : ℝ) : ℂ) * γ₁ w, hz, rfl⟩
        rwa [hkey] at h1)
  · intro hcon
    obtain ⟨w, hw⟩ := hcon
    have h1 : c * a = γ₁ w := by
      have h2 : c * a = c * (((h : ℝ) : ℂ) * γ₁ w) := congrArg (fun t => c * t) hw.symm
      rw [h2, ← mul_assoc, hcinv, one_mul]
    have h2 : a₁ = γ₁ w := by rw [ha₁def]; exact h1
    exact hγ₁a ⟨w, h2.symm⟩
  · have hbdd2 := Work.HornSC.ScaleComponent.isBounded_connectedComponentIn_mul
      (c := h) hhpos hγ₁bdd
    have himg : (fun z : ℂ => ((h : ℝ) : ℂ) * z) '' Set.range γ₁
        = Set.range (fun w : Circle => ((h : ℝ) : ℂ) * γ₁ w) :=
      (Set.range_comp (fun z : ℂ => ((h : ℝ) : ℂ) * z) γ₁).symm
    have haeq : ((h : ℝ) : ℂ) * a₁ = a := by
      rw [ha₁def]
      calc ((h : ℝ) : ℂ) * (c * a) = (((h : ℝ) : ℂ) * c) * a := by rw [mul_assoc]
        _ = 1 * a := by rw [mul_comm ((h : ℝ) : ℂ) c, hcinv]
        _ = a := one_mul a
    rwa [himg, haeq] at hbdd2

end Work.PlanarSC
