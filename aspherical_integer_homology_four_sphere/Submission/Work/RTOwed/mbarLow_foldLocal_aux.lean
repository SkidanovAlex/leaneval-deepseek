import Mathlib
import Submission.Work.RTOwed.mbarLow_foldLocal_defs
import Submission.Work.RTOwed.cellMat_reflWall
import Submission.Work.RTOwed.ceilH_wallNb_reflWall
import Submission.Work.RTOwed.cellLift_base_mem_Dvor
import Submission.Work.RTOwed.wall_step_lift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Set Topology Function Matrix
open scoped Matrix RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-! ## The fractional coordinates of the walk -/

/-- The offset of the horizontal coordinate `j` of `x` from the floor level of `q`. -/
def fracq (q x : CuspE4) (j : Fin 3) : ℝ := (uhsXj x) j - (⌊(uhsXj q) j⌋ : ℝ)

/-- The crossed set of `x` relative to `q`: the coordinates whose offset is negative. -/
def crossSet (q x : CuspE4) : Finset (Fin 3) := Finset.univ.filter (fun j => fracq q x j < 0)

theorem mem_crossSet {q x : CuspE4} {j : Fin 3} : j ∈ crossSet q x ↔ fracq q x j < 0 := by
  simp [crossSet]

/-- `x` is close to `q` in the three horizontal uhs coordinates and in the height. -/
def closeTo (q x : CuspE4) (ε : ℝ) : Prop :=
  (∀ j : Fin 3, |(uhsXj x) j - (uhsXj q) j| < ε) ∧ |x 3 - q 3| < ε

theorem closeTo_self {q : CuspE4} {ε : ℝ} (hε : 0 < ε) : closeTo q q ε :=
  ⟨fun j => by simpa using hε, by simpa using hε⟩

/-- **The horizontal coordinates of the wall reflection of `x`.** -/
theorem uhsXj_wallRefl_coord {v : Fin 5} {q : CuspE4} {m : Fin 3} (x : CuspE4) (j : Fin 3) :
    (uhsXj (wallRefl q m x)) j
      = if j = m then 2 * (⌊(uhsXj q) m⌋ : ℝ) - (uhsXj x) m else (uhsXj x) j := by
  have hw := uhsXj_wallRefl (v := v) (q := q) (S := ∅) (m := m) (Finset.notMem_empty m) x
  have hbase : (Work.Cusp.cubeCorner (walkCube v q ∅) m : ℝ)
      + (cuspCert.lamV v (walkK v q ∅)) m = (⌊(uhsXj q) m⌋ : ℝ) := by
    have h := walkFloor_eq v q ∅ m
    rw [if_neg (Finset.notMem_empty m), add_zero] at h
    linarith
  have hpt : ∀ i : Fin 3, (uhsXj (wallRefl q m x)) i - (cuspCert.lamV v (walkK v q ∅)) i
      = (reflWall m (Work.Cusp.cubeCorner (walkCube v q ∅) m)
          (uhsXj x - cuspCert.lamV v (walkK v q ∅))) i := by
    intro i
    have h := congrArg (fun z : CuspE3 => z i) hw
    simpa only [PiLp.sub_apply] using h
  have hgoal : (uhsXj (wallRefl q m x)) j
      = (reflWall m (Work.Cusp.cubeCorner (walkCube v q ∅) m)
          (uhsXj x - cuspCert.lamV v (walkK v q ∅))) j + (cuspCert.lamV v (walkK v q ∅)) j := by
    rw [← hpt j]; ring
  rw [hgoal, reflWall_apply]
  by_cases hj : j = m
  · rw [if_pos hj, if_pos hj, hj]
    simp only [PiLp.sub_apply]
    linarith [hbase]
  · rw [if_neg hj, if_neg hj]
    simp only [PiLp.sub_apply]
    ring

theorem fracq_wallRefl {v : Fin 5} {q : CuspE4} {m : Fin 3} (x : CuspE4) (j : Fin 3) :
    fracq q (wallRefl q m x) j = if j = m then -fracq q x m else fracq q x j := by
  simp only [fracq]
  rw [uhsXj_wallRefl_coord (v := v) (q := q) (m := m) x j]
  by_cases hj : j = m
  · rw [if_pos hj, if_pos hj, hj]
    ring
  · rw [if_neg hj, if_neg hj]

theorem fracq_wallRefl_lt {v : Fin 5} {q : CuspE4} {m : Fin 3} (x : CuspE4) {j : Fin 3}
    (hj : j ≠ m) : fracq q (wallRefl q m x) j < 0 ↔ fracq q x j < 0 := by
  rw [fracq_wallRefl (v := v), if_neg hj]

theorem abs_fracq_wallRefl {v : Fin 5} {q : CuspE4} {m : Fin 3} (x : CuspE4) (j : Fin 3) :
    |fracq q (wallRefl q m x) j| = |fracq q x j| := by
  rw [fracq_wallRefl (v := v)]
  by_cases hj : j = m
  · rw [if_pos hj, hj, abs_neg]
  · rw [if_neg hj]

/-- The wall reflection preserves the closeness to `q` when the reflected coordinate is pinned at
the floor of `q`. -/
theorem closeTo_wallRefl {v : Fin 5} {q x : CuspE4} {ε : ℝ} {m : Fin 3}
    (hm : (uhsXj q) m = (⌊(uhsXj q) m⌋ : ℝ)) (hx : closeTo q x ε) :
    closeTo q (wallRefl q m x) ε := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun j => ?_, by rw [wallRefl_three]; exact h2⟩
  have hdiff : ∀ y : CuspE4, ∀ i : Fin 3,
      (uhsXj y) i - (uhsXj q) i = fracq q y i - fracq q q i := by
    intro y i
    rw [fracq, fracq]
    ring
  rw [hdiff (wallRefl q m x) j, fracq_wallRefl (v := v)]
  by_cases hj : j = m
  · rw [if_pos hj, hj]
    have hq : fracq q q m = 0 := by
      rw [fracq]; linarith [hm]
    have hxq : fracq q x m = (uhsXj x) m - (uhsXj q) m := by
      rw [fracq]; linarith [hm]
    rw [hq, sub_zero, abs_neg, hxq]
    exact h1 m
  · rw [if_neg hj, ← hdiff x j]
    exact h1 j

theorem floorV_eq_floor_fracq (q x : CuspE4) (j : Fin 3) :
    (uhsXj x) j = fracq q x j + ((⌊(uhsXj q) j⌋ : ℤ) : ℝ) := by
  rw [fracq]; ring

/-- The floor vector of the walk at the crossed set of `x` is the floor vector of `x`. -/
theorem walkFloor_eq_floorV {q x : CuspE4} {S : Finset (Fin 3)}
    (hS : ∀ j : Fin 3, (j ∈ S ↔ fracq q x j < 0)) (habs : ∀ j : Fin 3, |fracq q x j| < 1) :
    walkFloor q S = floorV (uhsXj x) := by
  funext j
  rw [walkFloor, floorV, floorV_eq_floor_fracq q x j]
  rw [Int.floor_add_intCast]
  by_cases hjS : j ∈ S
  · have hlt : fracq q x j < 0 := (hS j).mp hjS
    have h1 : (-1 : ℝ) ≤ fracq q x j := by
      have := (abs_lt.mp (habs j)).1; linarith
    have hfl : ⌊fracq q x j⌋ = -1 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; linarith
      · push_cast; linarith
    rw [hfl, if_pos hjS]; ring
  · have hge : (0 : ℝ) ≤ fracq q x j := not_lt.mp (fun h => hjS ((hS j).mpr h))
    have hlt : fracq q x j < 1 := by
      have := (abs_lt.mp (habs j)).2; linarith
    have hfl : ⌊fracq q x j⌋ = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; linarith
      · push_cast; linarith
    rw [hfl, if_neg hjS]; ring

/-- **The cell condition of the walk.** -/
theorem cell_of_frac {v : Fin 5} {q x : CuspE4} {S : Finset (Fin 3)}
    (hS : ∀ j : Fin 3, (j ∈ S ↔ fracq q x j < 0)) (habs : ∀ j : Fin 3, |fracq q x j| < 1) :
    uhsXj x - cuspCert.lamV v (walkK v q S) ∈ cuspCert.halfopenBox (walkCube v q S) := by
  have hfl := walkFloor_eq_floorV hS habs
  have hcube : walkCube v q S = Work.RTOwed.cubeOf v (uhsXj x) := by
    rw [walkCube, hfl, Work.RTOwed.cubeOf]
  have hK : walkK v q S = cuspCert.floorK v (uhsXj x) := by
    funext j
    simp only [walkK, cuspCert.floorK]
    rw [hfl, hcube]
  rw [hK, hcube]
  rw [cuspCert.sub_lamV_floorK v (uhsXj x) (fun i => cuspCert.floorV_dvd v (uhsXj x) i)]
  exact cuspCert.redV_mem_halfopenBox v (uhsXj x)

/-! ## The ceiling transfer -/

/-- The ceiling of the walk cell is unchanged by a wall crossing. -/
theorem ceil_walk_insert {v : Fin 5} {q : CuspE4} {S' : Finset (Fin 3)} {m : Fin 3}
    (hmS' : m ∉ S') {k₀ : Fin 3 → ℤ}
    (hk₀ : cuspCert.lamV v k₀ = wallLamV (walkCube v q S') m 0) (x : CuspE4) :
    ceilH (walkCube v q (insert m S')) (uhsXj x - cuspCert.lamV v (walkK v q (insert m S')))
      = ceilH (walkCube v q S')
          (uhsXj (wallRefl q m x) - cuspCert.lamV v (walkK v q S')) := by
  have h1 := ceilH_wallNb_reflWall (walkCube v q S') m
    (uhsXj x - cuspCert.lamV v (walkK v q S'))
  rw [← walkCube_insert v q S' hmS'] at h1
  have h2 : (uhsXj x - cuspCert.lamV v (walkK v q S')) - wallLamV (walkCube v q S') m 0
      = uhsXj x - cuspCert.lamV v (walkK v q (insert m S')) := by
    rw [walkK_insert_sub v q S' hmS' k₀ hk₀, cuspWall_lamV_add, hk₀]
    abel
  rw [h2] at h1
  rw [← uhsXj_wallRefl hmS' x] at h1
  exact h1

/-! ## The group element of a wall crossing -/

/-- The group element of the wall of the walk cell `S'` in the direction `m` is the wall sum of the
fold class attached to that wall. -/
theorem wallGam_eq_wallSum {v : Fin 5} {i : Fin 98}
    {r : Fin (Work.FoldInst.foldCodim i) → Bool} {q : CuspE4} {S' : Finset (Fin 3)} {m : Fin 3}
    (hmS' : m ∉ S') {t : Fin (Work.FoldInst.foldCodim i)}
    (ht : Work.FoldInst.foldWalls i r t = wallLo (walkCube v q ∅) m) :
    wallGam (walkCube v q S') m 0 = Work.FoldInst.wallSum i {t} := by
  have h1 : ((wallGamK (walkCube v q S') m 0, wallGamFlip (walkCube v q S') m 0) : Work.FoldInst.Gg)
      = Work.FoldInst.sideType (wallLo (walkCube v q S') m) := by
    have h := cuspWallTableCerts.1 (walkCube v q S') m 0
    rw [if_pos rfl] at h
    exact h
  have h2 : Work.FoldInst.sideType (wallLo (walkCube v q S') m)
      = Work.FoldInst.sideType (wallLo (walkCube v q ∅) m) :=
    wallLo_walkCube_type v q S' hmS'
  have h3 : Work.FoldInst.sideType (wallLo (walkCube v q ∅) m)
      = Work.FoldInst.sideType (Work.FoldInst.foldWalls i r t) := by rw [ht]
  have h4 : Work.FoldInst.sideType (Work.FoldInst.foldWalls i r t)
      = Work.FoldInst.foldGen i t := (foldGen_eq_sideType i r t).symm
  have h5 : Work.FoldInst.foldGen i t = Work.FoldInst.wallSum i {t} := by
    rw [Work.FoldInst.wallSum, Finset.sum_singleton]
  show ((wallGamK (walkCube v q S') m 0, wallGamFlip (walkCube v q S') m 0) : Work.FoldInst.Gg) = _
  rw [h1, h2, h3, h4, h5]

/-! ## The walk -/

/-- The height coordinate in the uhs model. -/
theorem uhsXj_castSucc (z : CuspE4) (i : Fin 3) : (uhsXj z) i = z (Fin.castSucc i) + 1 / 2 := by
  simp only [uhsXj, cuspH, xOf4, PiLp.add_apply]
  fin_cases i <;> simp

theorem e4_eq_uhsXj (z : CuspE4) (i : Fin 3) : z (Fin.castSucc i) = (uhsXj z) i - 1 / 2 := by
  rw [uhsXj_castSucc z i]; ring

theorem abs_castSucc_sub (q x : CuspE4) (i : Fin 3) :
    |x (Fin.castSucc i) - q (Fin.castSucc i)| = |(uhsXj x) i - (uhsXj q) i| := by
  rw [e4_eq_uhsXj x i, e4_eq_uhsXj q i]
  rw [show (uhsXj x) i - 1 / 2 - ((uhsXj q) i - 1 / 2) = (uhsXj x) i - (uhsXj q) i from by ring]

theorem closeTo_four {q x : CuspE4} {ε : ℝ} (h : closeTo q x ε) : ∀ j : Fin 4, |x j - q j| < ε := by
  intro j
  have hdec : j = 3 ∨ ∃ i : Fin 3, j = Fin.castSucc i := by
    fin_cases j
    · exact Or.inr ⟨0, by rw [Fin.castSucc]; rfl⟩
    · exact Or.inr ⟨1, by rw [Fin.castSucc]; rfl⟩
    · exact Or.inr ⟨2, by rw [Fin.castSucc]; rfl⟩
    · exact Or.inl rfl
  rcases hdec with h3 | ⟨i, hi⟩
  · rw [h3]; simpa using h.2
  · rw [hi, abs_castSucc_sub q x i]; exact h.1 i

theorem closeTo_of_four {q x : CuspE4} {ε : ℝ} (h : ∀ j : Fin 4, |x j - q j| < ε) :
    closeTo q x ε := by
  refine ⟨fun i => ?_, ?_⟩
  · have h' := h (Fin.castSucc i)
    rwa [abs_castSucc_sub q x i] at h'
  · have h' := h 3
    simpa using h'

/-- The ceiling of the walk cell at `x` is `beta (xOf x)` when `S` is its crossed set. -/
theorem ceilH_walk_eq_beta {v : Fin 5} {q x : CuspE4} {S : Finset (Fin 3)}
    (hS : ∀ j : Fin 3, (j ∈ S ↔ fracq q x j < 0)) (habs : ∀ j : Fin 3, |fracq q x j| < 1) :
    ceilH (walkCube v q S) (uhsXj x - cuspCert.lamV v (walkK v q S))
      = Work.Cusp.beta (Work.Cusp.xOf x) := by
  have hfl := walkFloor_eq_floorV hS habs
  have hcube : walkCube v q S = Work.RTOwed.cubeOf v (uhsXj x) := by
    rw [walkCube, hfl, Work.RTOwed.cubeOf]
  have hK : walkK v q S = cuspCert.floorK v (uhsXj x) := by
    funext j
    simp only [walkK, cuspCert.floorK]
    rw [hfl, hcube]
  rw [hK, hcube, cuspCert.sub_lamV_floorK v (uhsXj x) (fun i => cuspCert.floorV_dvd v (uhsXj x) i)]
  exact ceilH_chartRed v x

/-- **The walk.**  If the base piece `r` contains the base lift of `q` (in the sense of `hbase`)
and the walls of the base cube at the pinned coordinates are walls of `r`, then on the cell of the
crossed set `S` the fold chart of `mbarLow v` is the single Möbius map `cellMat v i r a k`. -/
theorem walk_eval (v : Fin 5) (i : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (q : CuspE4) (ε : ℝ)
    (hbase : ∀ x : CuspE4, closeTo q x ε →
      uhsXj x - cuspCert.lamV v (walkK v q ∅) ∈ cuspCert.halfopenBox (walkCube v q ∅) →
      11 / 10 ≤ x 3 →
      x 3 ≤ ceilH (walkCube v q ∅) (uhsXj x - cuspCert.lamV v (walkK v q ∅)) →
      cellLift v (walkCube v q ∅) (walkK v q ∅) x ∈ Work.FoldInst.Dvor i r)
    (htex : ∀ m : Fin 3, (uhsXj q) m = (⌊(uhsXj q) m⌋ : ℝ) →
      ∃ t : Fin (Work.FoldInst.foldCodim i),
        Work.FoldInst.foldWalls i r t = wallLo (walkCube v q ∅) m)
    (S : Finset (Fin 3)) :
    ∀ x : CuspE4, (∀ m : Fin 3, m ∈ S → (uhsXj q) m = (⌊(uhsXj q) m⌋ : ℝ)) →
      closeTo q x ε →
      (∀ j : Fin 3, (j ∈ S ↔ fracq q x j < 0)) →
      (∀ j : Fin 3, |fracq q x j| < 1) →
      11 / 10 ≤ x 3 →
      x 3 ≤ ceilH (walkCube v q S) (uhsXj x - cuspCert.lamV v (walkK v q S)) →
      (∃ r' : Fin (Work.FoldInst.foldCodim i) → Bool,
        cellLift v (walkCube v q S) (walkK v q S) x ∈ Work.FoldInst.Dvor i r') ∧
      Work.FoldInst.foldChart i (mbarLow v x)
        = Work.HypModel.mobius (cellMat v i r (walkCube v q ∅) (walkK v q ∅)) x := by
  refine Finset.induction_on S ?base ?step
  · intro x hpin hclose hS habs hs1 hceil
    have hbox := cell_of_frac (v := v) (q := q) (x := x) (S := ∅) hS habs
    have hmem := hbase x hclose hbox hs1 hceil
    refine ⟨⟨r, hmem⟩, ?_⟩
    have hcb := cuspCert.halfopenBox_subset_cubeBox _ hbox
    have hmemQ : chartKlein (walkCube v q ∅) (mkE4 (uhsXj x - cuspCert.lamV v (walkK v q ∅)) (x 3))
        ∈ Work.FoldInst.Qbar := chartKlein_mem _ hcb hs1 hceil
    have hmk : mbarLow v x = Work.FoldInst.mk (cellLift v (walkCube v q ∅) (walkK v q ∅) x) :=
      mbarLow_eq_cellLift v (walkCube v q ∅) (walkK v q ∅)
        (cuspCert.cubeCusp_cubeOfMod v (walkFloor q ∅)) hcb hs1 hceil
    rw [hmk, Work.FoldInst.foldChart_apply i r _ hmem, cellLift_eq hmemQ]
    exact foldTheta_chartKlein_eq_mobius v i r (walkCube v q ∅) (walkK v q ∅) x (by linarith)
  · intro m S' hmS' ih x hpin hclose hS habs hs1 hceil
    have hpinS : ∀ m' : Fin 3, m' ∈ S' → (uhsXj q) m' = (⌊(uhsXj q) m'⌋ : ℝ) :=
      fun m' hm' => hpin m' (Finset.mem_insert_of_mem hm')
    have hpinm : (uhsXj q) m = (⌊(uhsXj q) m⌋ : ℝ) := hpin m (Finset.mem_insert_self m S')
    obtain ⟨t, htw⟩ := htex m hpinm
    obtain ⟨k₀, hk₀0⟩ := cuspWallTableCerts.2.2.2.2.2 (walkCube v q S') m 0
    have hk₀ : cuspCert.lamV v k₀ = wallLamV (walkCube v q S') m 0 := by
      have hcv : Cusp.cubeCusp (walkCube v q S') = v := cuspCert.cubeCusp_cubeOfMod v (walkFloor q S')
      rw [hk₀0, hcv]
    set x₁ : CuspE4 := wallRefl q m x with hx₁def
    have hclose₁ : closeTo q x₁ ε := by
      rw [hx₁def]; exact closeTo_wallRefl (v := v) hpinm hclose
    have hS₁ : ∀ j : Fin 3, (j ∈ S' ↔ fracq q x₁ j < 0) := by
      intro j
      rw [hx₁def, fracq_wallRefl (v := v)]
      by_cases hj : j = m
      · rw [if_pos hj, hj]
        have hlt : fracq q x m < 0 := (hS m).mp (Finset.mem_insert_self m S')
        constructor
        · intro hm'; exact absurd hm' hmS'
        · intro h; linarith
      · rw [if_neg hj]
        have hmem' : (j ∈ insert m S') ↔ (j ∈ S') := by
          rw [Finset.mem_insert]
          constructor
          · rintro (h | h)
            · exact absurd h hj
            · exact h
          · intro h; exact Or.inr h
        exact hmem'.symm.trans (hS j)
    have habs₁ : ∀ j : Fin 3, |fracq q x₁ j| < 1 := by
      intro j; rw [hx₁def, abs_fracq_wallRefl (v := v)]; exact habs j
    have hs1₁ : 11 / 10 ≤ x₁ 3 := by rw [hx₁def, wallRefl_three]; exact hs1
    have hceil₁ : x₁ 3 ≤ ceilH (walkCube v q S') (uhsXj x₁ - cuspCert.lamV v (walkK v q S')) := by
      rw [hx₁def, wallRefl_three, ← ceil_walk_insert (v := v) (q := q) hmS' hk₀ x]
      exact hceil
    obtain ⟨⟨r', hr'⟩, hF₁⟩ := ih x₁ hpinS hclose₁ hS₁ habs₁ hs1₁ hceil₁
    -- the cell conditions of the two cells at `x` and `x₁`
    have hboxF : uhsXj x - cuspCert.lamV v (walkK v q (insert m S'))
        ∈ cuspCert.halfopenBox (walkCube v q (insert m S')) :=
      cell_of_frac (v := v) (q := q) (x := x) (S := insert m S') hS habs
    have hcbF := cuspCert.halfopenBox_subset_cubeBox _ hboxF
    have hmemF : chartKlein (walkCube v q (insert m S'))
        (mkE4 (uhsXj x - cuspCert.lamV v (walkK v q (insert m S'))) (x 3))
        ∈ Work.FoldInst.Qbar := chartKlein_mem _ hcbF hs1 hceil
    have hboxN : uhsXj x₁ - cuspCert.lamV v (walkK v q S')
        ∈ cuspCert.halfopenBox (walkCube v q S') := cell_of_frac (S := S') hS₁ habs₁
    have hcbN := cuspCert.halfopenBox_subset_cubeBox _ hboxN
    have hmemN : chartKlein (walkCube v q S')
        (mkE4 (uhsXj x₁ - cuspCert.lamV v (walkK v q S')) (x₁ 3))
        ∈ Work.FoldInst.Qbar := chartKlein_mem _ hcbN hs1₁ hceil₁
    have hlw := wall_step_lift v q S' hmS' hk₀ hs1 (hF := hmemF) (hN := hmemN)
    have hlw₁ : cellLift v (walkCube v q (insert m S')) (walkK v q (insert m S')) x
        = Work.FoldInst.actX (wallGam (walkCube v q S') m 0)
            (cellLift v (walkCube v q S') (walkK v q S') x₁) := by
      rw [cellLift_eq hmemF, cellLift_eq hmemN]
      exact hlw
    have hγ : wallGam (walkCube v q S') m 0 = Work.FoldInst.wallSum i {t} :=
      wallGam_eq_wallSum (v := v) (i := i) (r := r) hmS' htw
    refine ⟨?_, ?_⟩
    · refine ⟨Work.FoldInst.flipSet r' ({t} : Finset (Fin (Work.FoldInst.foldCodim i))), ?_⟩
      rw [← Work.FoldInst.actX_image_Dvor i r' ({t} : Finset (Fin (Work.FoldInst.foldCodim i)))]
      refine ⟨cellLift v (walkCube v q S') (walkK v q S') x₁, hr', ?_⟩
      rw [← hγ]
      exact hlw₁.symm
    · have hmkF : mbarLow v x
          = Work.FoldInst.mk (cellLift v (walkCube v q (insert m S')) (walkK v q (insert m S')) x) :=
        mbarLow_eq_cellLift v _ _ (cuspCert.cubeCusp_cubeOfMod v (walkFloor q (insert m S')))
          hcbF hs1 hceil
      have hmkN : mbarLow v x₁
          = Work.FoldInst.mk (cellLift v (walkCube v q S') (walkK v q S') x₁) :=
        mbarLow_eq_cellLift v _ _ (cuspCert.cubeCusp_cubeOfMod v (walkFloor q S'))
          hcbN hs1₁ hceil₁
      have hstep : Work.FoldInst.mk (cellLift v (walkCube v q (insert m S')) (walkK v q (insert m S')) x)
          = Work.FoldInst.mk (Work.FoldInst.actX (Work.FoldInst.wallSum i {t})
              (cellLift v (walkCube v q S') (walkK v q S') x₁)) := by
        rw [hlw₁, ← hγ]
      have hcenter : (Work.Cusp.cubeCorner (walkCube v q ∅) m : ℝ)
          + (cuspCert.lamV v (walkK v q ∅)) m - 1 / 2 = (⌊(uhsXj q) m⌋ : ℝ) - 1 / 2 := by
        have h := walkFloor_eq v q ∅ m
        rw [if_neg (Finset.notMem_empty m), add_zero] at h
        linarith
      have hwall := cellMat_reflWall v i r (walkCube v q ∅) (walkK v q ∅) m t htw x (by linarith)
      have hx₁' : x₁ = reflWall4 m ((⌊(uhsXj q) m⌋ : ℝ) - 1 / 2) x := by
        rw [hx₁def, wallRefl]
      have hact : Work.FoldInst.foldChart i
            (Work.FoldInst.mk (Work.FoldInst.actX (Work.FoldInst.wallSum i {t})
              (cellLift v (walkCube v q S') (walkK v q S') x₁)))
          = Work.FoldInst.reflCoords ({t} : Finset (Fin (Work.FoldInst.foldCodim i)))
              (Work.FoldInst.foldChart i
                (Work.FoldInst.mk (cellLift v (walkCube v q S') (walkK v q S') x₁))) :=
        foldChart_actX (i := i) (x := cellLift v (walkCube v q S') (walkK v q S') x₁)
          (hx := Set.mem_iUnion.mpr ⟨r', hr'⟩) (Δ := {t})
      rw [hmkF, hstep, hact, ← hmkN, hF₁, hx₁', ← hcenter, hwall,
        Work.FoldInst.reflCoords_reflCoords]


/-! ## Openness of the neighbourhood -/

theorem continuous_uhsXj_apply (j : Fin 3) : Continuous (fun x : CuspE4 => (uhsXj x) j) := by
  rw [show (fun x : CuspE4 => (uhsXj x) j) = fun x : CuspE4 => x (Fin.castSucc j) + 1 / 2 from by
    funext x; rw [uhsXj_castSucc]]
  have hc : Continuous (fun x : CuspE4 => x (Fin.castSucc j)) :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 4 => ℝ) (Fin.castSucc j)
  exact hc.add continuous_const

theorem continuous_fracq (q : CuspE4) (j : Fin 3) : Continuous (fun x : CuspE4 => fracq q x j) := by
  rw [show (fun x : CuspE4 => fracq q x j)
      = fun x : CuspE4 => (uhsXj x) j - (⌊(uhsXj q) j⌋ : ℝ) from by
    funext x; rw [fracq]]
  exact Continuous.sub (continuous_uhsXj_apply j) continuous_const

theorem isOpen_closeTo (q : CuspE4) (δ : ℝ) : IsOpen {x : CuspE4 | closeTo q x δ} := by
  have h1 : IsOpen {x : CuspE4 | ∀ j : Fin 3, |(uhsXj x) j - (uhsXj q) j| < δ} := by
    rw [show {x : CuspE4 | ∀ j : Fin 3, |(uhsXj x) j - (uhsXj q) j| < δ}
        = ⋂ j : Fin 3, {x : CuspE4 | |(uhsXj x) j - (uhsXj q) j| < δ} from by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    refine isOpen_iInter_of_finite fun j => ?_
    have hc : Continuous (fun x : CuspE4 => |(uhsXj x) j - (uhsXj q) j|) :=
      Continuous.abs (Continuous.sub (continuous_uhsXj_apply j) continuous_const)
    exact isOpen_lt hc continuous_const
  rw [show {x : CuspE4 | closeTo q x δ}
      = ({x : CuspE4 | ∀ j : Fin 3, |(uhsXj x) j - (uhsXj q) j| < δ}
        ∩ {x : CuspE4 | |x 3 - q 3| < δ}) from by
    ext x; exact Iff.rfl]
  have hc : Continuous (fun x : CuspE4 => |x 3 - q 3|) := by
    have h3 : Continuous (fun x : CuspE4 => x 3) :=
      PiLp.continuous_apply (p := 2) (β := fun _ : Fin 4 => ℝ) (3 : Fin 4)
    exact Continuous.abs (Continuous.sub h3 continuous_const)
  exact h1.inter (isOpen_lt hc continuous_const)

theorem isOpen_fracq_pos (q : CuspE4) :
    IsOpen {x : CuspE4 | ∀ j : Fin 3, (uhsXj q) j ≠ (⌊(uhsXj q) j⌋ : ℝ) → 0 < fracq q x j} := by
  rw [show {x : CuspE4 | ∀ j : Fin 3, (uhsXj q) j ≠ (⌊(uhsXj q) j⌋ : ℝ) → 0 < fracq q x j}
      = ⋂ j : Fin 3, {x : CuspE4 | (uhsXj q) j ≠ (⌊(uhsXj q) j⌋ : ℝ) → 0 < fracq q x j} from by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
  refine isOpen_iInter_of_finite fun j => ?_
  by_cases hj : (uhsXj q) j = (⌊(uhsXj q) j⌋ : ℝ)
  · rw [show {x : CuspE4 | (uhsXj q) j ≠ (⌊(uhsXj q) j⌋ : ℝ) → 0 < fracq q x j} = Set.univ from by
      ext x
      exact ⟨fun _ => trivial, fun _ h => absurd hj h⟩]
    exact isOpen_univ
  · rw [show {x : CuspE4 | (uhsXj q) j ≠ (⌊(uhsXj q) j⌋ : ℝ) → 0 < fracq q x j}
        = {x : CuspE4 | 0 < fracq q x j} from by
      ext x
      exact ⟨fun h => h hj, fun h _ => h⟩]
    exact isOpen_lt continuous_const (continuous_fracq q j)

theorem isOpen_fracq_abs (q : CuspE4) : IsOpen {x : CuspE4 | ∀ j : Fin 3, |fracq q x j| < 1} := by
  rw [show {x : CuspE4 | ∀ j : Fin 3, |fracq q x j| < 1}
      = ⋂ j : Fin 3, {x : CuspE4 | |fracq q x j| < 1} from by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (Continuous.abs (continuous_fracq q j)) continuous_const

theorem isOpen_chimney : IsOpen {x : CuspE4 | x 3 < Work.Cusp.beta (Work.Cusp.xOf x)} :=
  isOpen_lt (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 4 => ℝ) (3 : Fin 4)) continuous_beta_xOf

/-! ## The target -/

theorem mbarLow_foldLocal_aux (v : Fin 5) (i : Fin 98) {q : Work.RTOwed.CuspE4}
    (h1 : 11 / 10 < q 3) (h2 : q 3 < Work.Cusp.beta (Work.Cusp.xOf q))
    (hsrc : Work.RTOwed.mbarLow v q ∈ (Work.FoldInst.foldChart i).source) :
    ∃ (V : Set Work.RTOwed.CuspE4) (B : Matrix (Fin 5) (Fin 5) ℝ), IsOpen V ∧ q ∈ V ∧
      Work.HypModel.IsLorentzMat B ∧
      ∀ q' ∈ V, Work.RTOwed.mbarLow v q' ∈ (Work.FoldInst.foldChart i).source →
        Work.FoldInst.foldChart i (Work.RTOwed.mbarLow v q') = Work.HypModel.mobius B q' := by
  classical
  -- the base cell of `q`
  have hcusp : Cusp.cubeCusp (walkCube v q ∅) = v := cuspCert.cubeCusp_cubeOfMod v (walkFloor q ∅)
  have hred : uhsXj q - cuspCert.lamV v (walkK v q ∅) = redV v (uhsXj q) := by
    rw [walkK_empty v q]
    exact cuspCert.sub_lamV_floorK v (uhsXj q) (fun i => cuspCert.floorV_dvd v (uhsXj q) i)
  have hboxq : uhsXj q - cuspCert.lamV v (walkK v q ∅) ∈ cubeBox (walkCube v q ∅) := by
    rw [hred, walkCube_empty v q]
    exact Work.RTOwed.redV_mem_cubeBox v (uhsXj q)
  have hhalfq : uhsXj q - cuspCert.lamV v (walkK v q ∅) ∈ cuspCert.halfopenBox (walkCube v q ∅) := by
    rw [hred, walkCube_empty v q]
    exact cuspCert.redV_mem_halfopenBox v (uhsXj q)
  have hceilq : q 3 ≤ ceilH (walkCube v q ∅) (uhsXj q - cuspCert.lamV v (walkK v q ∅)) := by
    rw [hred, walkCube_empty v q]
    have hch := ceilH_chartRed v q
    rw [show Work.RTOwed.chartCube v q = Work.RTOwed.cubeOf v (uhsXj q) from rfl,
      show Work.RTOwed.chartRed v q = redV v (uhsXj q) from rfl] at hch
    rw [hch]
    exact le_of_lt h2
  -- the base lift and the fold piece containing it
  have hmk0 : mbarLow v q = Work.FoldInst.mk (cellLift v (walkCube v q ∅) (walkK v q ∅) q) :=
    mbarLow_eq_cellLift v _ _ hcusp hboxq (le_of_lt h1) hceilq
  obtain ⟨r, hr⟩ : ∃ r : Fin (Work.FoldInst.foldCodim i) → Bool,
      cellLift v (walkCube v q ∅) (walkK v q ∅) q ∈ Work.FoldInst.Dvor i r := by
    have h := mem_iUnion_Dvor_of_mem_source (i := i)
      (z := cellLift v (walkCube v q ∅) (walkK v q ∅) q) (by rw [← hmk0]; exact hsrc)
    simpa using h
  -- the walls of the base cube at the pinned coordinates are walls of `r`
  have htex : ∀ m : Fin 3, (uhsXj q) m = (⌊(uhsXj q) m⌋ : ℝ) →
      ∃ t : Fin (Work.FoldInst.foldCodim i),
        Work.FoldInst.foldWalls i r t = wallLo (walkCube v q ∅) m := by
    intro m hm
    by_contra hcon
    have hzval : (cellLift v (walkCube v q ∅) (walkK v q ∅) q).2.1
        = chartKlein (walkCube v q ∅)
            (mkE4 (uhsXj q - cuspCert.lamV v (walkK v q ∅)) (q 3)) := by
      rw [cellLift_eq (chartKlein_mem _ hboxq (le_of_lt h1) hceilq)]
      rfl
    have hslack : Work.FoldInst.sideSlack (wallLo (walkCube v q ∅) m)
        (cellLift v (walkCube v q ∅) (walkK v q ∅) q).2.1 = 0 := by
      rw [hzval, ← wallAt_zero (walkCube v q ∅) m]
      refine (wallAt_slack_zero_iff (walkCube v q ∅) m 0 hboxq (le_of_lt h1)).mpr ?_
      have hcoord : (uhsXj q - cuspCert.lamV v (walkK v q ∅)) m
          = (Work.Cusp.cubeCorner (walkCube v q ∅) m : ℝ) := by
        have hw := walkFloor_eq v q ∅ m
        rw [if_neg (Finset.notMem_empty m), add_zero] at hw
        simp only [PiLp.sub_apply]
        linarith [hw, hm]
      simpa using hcoord
    have hmemVor : 0 < Work.FoldInst.sideSlack (wallLo (walkCube v q ∅) m)
        (cellLift v (walkCube v q ∅) (walkK v q ∅) q).2.1 :=
      (hr.2.1 (wallLo (walkCube v q ∅) m) (fun t ht => hcon ⟨t, ht⟩)).1
    rw [hslack] at hmemVor
    exact absurd hmemVor (lt_irrefl 0)
  -- the Voronoi neighbourhood of the base cell
  obtain ⟨δ, hδpos, hδ⟩ := cellLift_base_mem_Dvor v i r hr (le_of_lt h1) hceilq
  set δ' : ℝ := min δ ((q 3 - 11 / 10) / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos (by linarith)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'q : δ' ≤ (q 3 - 11 / 10) / 2 := min_le_right _ _
  have hbase : ∀ x : CuspE4, closeTo q x δ' →
      uhsXj x - cuspCert.lamV v (walkK v q ∅) ∈ cuspCert.halfopenBox (walkCube v q ∅) →
      11 / 10 ≤ x 3 →
      x 3 ≤ ceilH (walkCube v q ∅) (uhsXj x - cuspCert.lamV v (walkK v q ∅)) →
      cellLift v (walkCube v q ∅) (walkK v q ∅) x ∈ Work.FoldInst.Dvor i r :=
    fun x hclose hbox hs1 hceil =>
      hδ x (fun j => lt_of_lt_of_le (closeTo_four hclose j) hδ'δ) hbox hs1 hceil
  -- the neighbourhood
  let V : Set CuspE4 := {q' | closeTo q q' δ'
      ∧ (∀ j : Fin 3, (uhsXj q) j ≠ (⌊(uhsXj q) j⌋ : ℝ) → 0 < fracq q q' j)
      ∧ (∀ j : Fin 3, |fracq q q' j| < 1)
      ∧ q' 3 < Work.Cusp.beta (Work.Cusp.xOf q')}
  refine ⟨V, cellMat v i r (walkCube v q ∅) (walkK v q ∅), ?_, ?_,
    cellMat_isLorentz v i r (walkCube v q ∅) (walkK v q ∅), ?_⟩
  · rw [show V = {x : CuspE4 | closeTo q x δ'}
        ∩ ({x : CuspE4 | ∀ j : Fin 3, (uhsXj q) j ≠ (⌊(uhsXj q) j⌋ : ℝ) → 0 < fracq q x j}
          ∩ ({x : CuspE4 | ∀ j : Fin 3, |fracq q x j| < 1}
            ∩ {x : CuspE4 | x 3 < Work.Cusp.beta (Work.Cusp.xOf x)})) from by
      ext x; simp [V]]
    exact (isOpen_closeTo q δ').inter ((isOpen_fracq_pos q).inter
      ((isOpen_fracq_abs q).inter isOpen_chimney))
  · refine ⟨closeTo_self hδ'pos, ?_, ?_, h2⟩
    · intro j hj
      have hge : (0 : ℝ) ≤ fracq q q j := by
        rw [fracq]
        exact sub_nonneg.mpr (Int.floor_le _)
      have hj' : fracq q q j ≠ 0 := by
        rw [fracq]; exact sub_ne_zero.mpr hj
      exact lt_of_le_of_ne' hge hj'
    · intro j
      rw [fracq]
      have h1' : (⌊(uhsXj q) j⌋ : ℝ) ≤ (uhsXj q) j := Int.floor_le _
      have h2' : (uhsXj q) j < (⌊(uhsXj q) j⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
  · intro q' hq'V hsrc'
    obtain ⟨hclose, hpos, habs, hchim⟩ := hq'V
    have hS : ∀ j : Fin 3, (j ∈ crossSet q q' ↔ fracq q q' j < 0) := fun j => mem_crossSet
    have hpin : ∀ m : Fin 3, m ∈ crossSet q q' → (uhsXj q) m = (⌊(uhsXj q) m⌋ : ℝ) := by
      intro m hm
      by_contra hne
      exact absurd (hpos m hne) (not_lt.mpr (le_of_lt ((hS m).mp hm)))
    have hs1 : 11 / 10 ≤ q' 3 := by
      have h := hclose.2
      rw [abs_lt] at h
      linarith [h.1, hδ'q]
    have hceil : q' 3 ≤ ceilH (walkCube v q (crossSet q q'))
        (uhsXj q' - cuspCert.lamV v (walkK v q (crossSet q q'))) := by
      rw [ceilH_walk_eq_beta hS habs]
      exact le_of_lt hchim
    exact (walk_eval v i r q δ' hbase htex (crossSet q q') q' hpin hclose hS habs hs1 hceil).2


end

end Work.RTOwed
