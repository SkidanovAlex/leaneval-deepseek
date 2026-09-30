import Mathlib
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspCert.CuspSupport
import Submission.Work.RTOwed.chartKlein_wall
import Submission.Work.RTOwed.cuspCert.covData
import Submission.Work.RTOwed.cuspCert.tsetCoverData
import Submission.Work.RTOwed.sideSlack_pos_of_not_wall
import Submission.Work.RTOwed.wallLo_slack_sign
import Submission.Work.RTOwed.wallHi_slack_sign
import Submission.Work.RTOwed.cuspWall_step
import Submission.Work.RTOwed.wallGam_sideType
import Submission.Work.RTOwed.cuspWallTableCerts
import Submission.Work.RTOwed.chartKlein_mem
import Submission.Work.FoldInst.Atlas

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

noncomputable section

open Set

/-! ## Auxiliary data: the pinned coordinates of a point of the closed unit cube -/

/-- The side of the cube `a` at which the coordinate `i` of `x` sits: `0` for the lower wall
`{x i = cubeCorner a i}`, `1` otherwise. -/
def sideOf (a : Fin 48) (x : CuspE3) : Fin 3 → Fin 2 :=
  fun i => if x i = (Work.Cusp.cubeCorner a i : ℝ) then 0 else 1

/-- The set of coordinates of `x` pinned at a wall of the cube `a`. -/
def pinSet (a : Fin 48) (x : CuspE3) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => x i = (Work.Cusp.cubeCorner a i : ℝ)
    ∨ x i = (Work.Cusp.cubeCorner a i : ℝ) + 1)

/-- The wall side of the cube `a` at the coordinate `i` and the side `side`. -/
def wallAt (a : Fin 48) (i : Fin 3) (side : Fin 2) : Fin 24 :=
  if side = 0 then wallLo a i else wallHi a i

theorem mem_pinSet {a : Fin 48} {x : CuspE3} {i : Fin 3} :
    i ∈ pinSet a x ↔ x i = (Work.Cusp.cubeCorner a i : ℝ)
      ∨ x i = (Work.Cusp.cubeCorner a i : ℝ) + 1 := by
  simp [pinSet]

theorem sideOf_eq_of_eq (a : Fin 48) {x : CuspE3} {i : Fin 3}
    (h : x i = (Work.Cusp.cubeCorner a i : ℝ)) : sideOf a x i = 0 := by
  simp only [sideOf]
  rw [ite_eq_left h]

theorem sideOf_eq_of_eq_add_one (a : Fin 48) {x : CuspE3} {i : Fin 3}
    (h : x i = (Work.Cusp.cubeCorner a i : ℝ) + 1) : sideOf a x i = 1 := by
  simp only [sideOf]
  rw [ite_eq_right (by rw [h]; norm_num)]

theorem wallAt_zero (a : Fin 48) (i : Fin 3) : wallAt a i 0 = wallLo a i := by
  simp [wallAt]

theorem wallAt_one (a : Fin 48) (i : Fin 3) : wallAt a i 1 = wallHi a i := by
  simp [wallAt]

/-- **The pinned coordinates carry the correct side.** -/
theorem sideOf_spec (a : Fin 48) (x : CuspE3) {i : Fin 3} (hi : i ∈ pinSet a x) :
    x i = (Work.Cusp.cubeCorner a i : ℝ)
      + (if (sideOf a x i : ℕ) = 0 then 0 else 1) := by
  have h := (Finset.mem_filter.mp hi).2
  rcases h with h | h
  · have hz : sideOf a x i = 0 := sideOf_eq_of_eq a h
    rw [hz]
    simp only [Fin.val_zero, reduceIte, add_zero]
    exact h
  · have hz : sideOf a x i = 1 := sideOf_eq_of_eq_add_one a h
    rw [hz]
    simp only [Fin.val_one]
    norm_num
    exact h

/-- **The group element of a wall is the type of its side.** -/
theorem wallGam_eq_sideType (a : Fin 48) (i : Fin 3) (side : Fin 2) :
    wallGam a i side = Work.FoldInst.sideType (wallAt a i side) := by
  simpa [wallGam, wallAt] using (cuspWallTableCerts.1 a i side)

/-- **The wall slack vanishes exactly on the corresponding face of the cube.** -/
theorem wallAt_slack_zero_iff (a : Fin 48) (i : Fin 3) (side : Fin 2) {x : CuspE3}
    (hx : x ∈ cubeBox a) {s : ℝ} (hs1 : 11 / 10 ≤ s) :
    Work.FoldInst.sideSlack (wallAt a i side) (chartKlein a (mkE4 x s)) = 0 ↔
      x i = (Work.Cusp.cubeCorner a i : ℝ) + (if (side : ℕ) = 0 then 0 else 1) := by
  have hbox : ∀ j : Fin 3, (Work.Cusp.cubeCorner a j : ℝ) - 1 ≤ x j
      ∧ x j ≤ (Work.Cusp.cubeCorner a j : ℝ) + 2 := by
    intro j; have h := hx j; constructor <;> linarith [h.1, h.2]
  fin_cases side
  · simp only [wallAt, reduceIte]
    simpa using (wallLo_slack_sign a i hs1 hbox).2.1
  · simp only [wallAt]
    norm_num
    simpa using (wallHi_slack_sign a i hs1 hbox).2.1

/-- **The only sides of `Q̄` that can be tight at a cube chart point are the walls of the cube.** -/
theorem tight_is_wall_closed {a : Fin 48} {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ}
    (hs1 : 11 / 10 ≤ s) (hs2 : s ≤ ceilH a x) {S : Fin 24}
    (hS : Work.FoldInst.sideSlack S (chartKlein a (mkE4 x s)) = 0) :
    (∃ i : Fin 3, S = wallLo a i) ∨ (∃ i : Fin 3, S = wallHi a i) := by
  by_contra hcon
  have h1 : ∀ i : Fin 3, S ≠ wallLo a i := fun i hi => hcon (Or.inl ⟨i, hi⟩)
  have h2 : ∀ i : Fin 3, S ≠ wallHi a i := fun i hi => hcon (Or.inr ⟨i, hi⟩)
  have hpos := sideSlack_pos_of_not_wall a hx hs1 hs2 (fun i => ⟨h1 i, h2 i⟩)
  rw [hS] at hpos
  exact lt_irrefl _ hpos

/-- **Crossing a wall does not change the type of the walls it does not meet.** -/
theorem wallGam_wallNb_ne (a : Fin 48) (i : Fin 3) (si : Fin 2) (j : Fin 3) (sj : Fin 2)
    (hj : j ≠ i) : wallGam (wallNb a i si) j sj = wallGam a j sj := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cuspWallTableCerts
  have h := h5 a i si j sj
  rw [ite_eq_right hj] at h
  rw [show wallGam (wallNb a i si) j sj
        = Work.FoldInst.sideType (if sj = 0 then wallLo (wallNb a i si) j
            else wallHi (wallNb a i si) j) from by simpa [wallGam] using h1 (wallNb a i si) j sj,
    show wallGam a j sj = Work.FoldInst.sideType (if sj = 0 then wallLo a j else wallHi a j)
      from by simpa [wallGam] using h1 a j sj]
  exact h

/-- **The wall vector of the far cube is the shift of the wall vector of the near cube.** -/
theorem intVec_wallLam (a : Fin 48) (i : Fin 3) (side : Fin 2) :
    cuspCert.intVec (wallLam a i side) = wallLamV a i side := rfl

/-- **The components of the wall vector are lattice vectors.** -/
theorem latMod_dvd_wallLam (a : Fin 48) (i : Fin 3) (side : Fin 2) (t : Fin 3) :
    (Work.Cusp.latMod (Work.Cusp.cubeCusp a) t : ℤ) ∣ wallLam a i side t := by
  obtain ⟨k, hk⟩ := (cuspWallTableCerts.2.2.2.2.2) a i side
  have h := congrFun (congrArg (fun v : CuspE3 => v.ofLp) hk) t
  simp only [wallLamV, cuspCert.lamV, cuspCert.lamK, PiLp.toLp_apply] at h
  refine ⟨k t, ?_⟩
  have h' : ((wallLam a i side t : ℤ) : ℝ)
      = ((((Work.Cusp.latMod (Work.Cusp.cubeCusp a) t : ℤ)) * k t : ℤ) : ℝ) := by
    simpa using h
  exact_mod_cast h'

/-- **Crossing a wall preserves the ceiling.** -/
theorem ceilH_wallNb (a : Fin 48) (i : Fin 3) (side : Fin 2) {x : CuspE3}
    (hwall : x i = (Work.Cusp.cubeCorner a i : ℝ) + (if (side : ℕ) = 0 then 0 else 1)) :
    ceilH (wallNb a i side) (x - wallLamV a i side) = ceilH a x := by
  have hwall' : x i = (Work.Cusp.cubeCorner a i : ℝ) + (if side = 0 then 0 else 1) := by
    rw [hwall, cuspWall_ite_side_zero]
  rw [ceilH, ceilH]
  congr 1
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j = i
  · rw [hj]
    rw [cuspWall_norm_coord a i side hwall', hwall]
    simp only [cuspWall_ite_side_zero side (1:ℝ) 0]
    split_ifs <;> ring
  · rw [cuspWall_tan_coord a i side hj]
    congr 1
    ring

/-! ## Subset sums of a finite set of generators of `Gg` -/

/-- The sum over the symmetric difference of two finsets. -/
theorem sum_symm_gen (t : Fin 3 → Work.FoldInst.Gg) (A B : Finset (Fin 3)) :
    ((A \ B) ∪ (B \ A)).sum t = A.sum t + B.sum t := by
  have hd1 : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  rw [Finset.sum_union hd1]
  have hA' : A.sum t = (A \ B).sum t + (A ∩ B).sum t := by
    have hs : A \ (A ∩ B) = A \ B :=
      Finset.ext fun i => by simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [← Finset.sum_sdiff (f := t) (s₁ := A ∩ B) (s₂ := A) Finset.inter_subset_left, hs]
  have hB' : B.sum t = (B \ A).sum t + (A ∩ B).sum t := by
    have hs : B \ (A ∩ B) = B \ A :=
      Finset.ext fun i => by simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [← Finset.sum_sdiff (f := t) (s₁ := A ∩ B) (s₂ := B) Finset.inter_subset_right, hs]
  rw [hA', hB']
  have hre : ((A \ B).sum t + (A ∩ B).sum t) + ((B \ A).sum t + (A ∩ B).sum t)
      = (A \ B).sum t + (B \ A).sum t + ((A ∩ B).sum t + (A ∩ B).sum t) := by abel
  rw [hre, cuspCert.zadd_self_gg, add_zero]

/-- **The subgroup generated by the values `t i`, `i ∈ I`, consists of the subset sums.** -/
theorem exists_subset_sum_of_mem_closure (t : Fin 3 → Work.FoldInst.Gg) (I : Finset (Fin 3))
    {γ : Work.FoldInst.Gg} (h : γ ∈ AddSubgroup.closure (t '' (↑I : Set (Fin 3)))) :
    ∃ A : Finset (Fin 3), A ⊆ I ∧ γ = ∑ i ∈ A, t i := by
  set H : AddSubgroup Work.FoldInst.Gg :=
    { carrier := {γ : Work.FoldInst.Gg | ∃ A : Finset (Fin 3), A ⊆ I ∧ γ = ∑ i ∈ A, t i}
      zero_mem' := ⟨∅, Finset.empty_subset _, by simp⟩
      add_mem' := by
        intro γ₁ γ₂ h₁ h₂
        obtain ⟨A₁, hA₁, rfl⟩ := h₁
        obtain ⟨A₂, hA₂, rfl⟩ := h₂
        refine ⟨(A₁ \ A₂) ∪ (A₂ \ A₁), ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_union.mp hi with h' | h'
          · exact hA₁ (Finset.mem_sdiff.mp h').1
          · exact hA₂ (Finset.mem_sdiff.mp h').1
        · exact (sum_symm_gen t A₁ A₂).symm
      neg_mem' := by
        intro γ hγ
        obtain ⟨A, hA, rfl⟩ := hγ
        refine ⟨A, hA, ?_⟩
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => cuspCert.zneg_gg (t i) } with hH
  have hsub : (t '' (↑I : Set (Fin 3))) ⊆ (H : Set Work.FoldInst.Gg) := by
    rintro z ⟨i, hi, rfl⟩
    exact ⟨{i}, Finset.singleton_subset_iff.mpr hi, (Finset.sum_singleton t i).symm⟩
  exact (AddSubgroup.closure_le H).mpr hsub h

/-! ## The walk -/

/-- **The walk of a subset sum of wall generators on the closed cubes.**  For a cube `a`, a point
`x` of its closed unit cube, a height `s ∈ [11/10, ceilH a x]`, a choice of side `side i` for each
coordinate and a set `A` of coordinates that are pinned at `x` (at the side `side i`), the sum of
the wall generators `wallGam a i (side i)`, `i ∈ A`, maps the chart point `chartKlein a (mkE4 x s)`
to the chart of a closed cube `b` at the lattice translate `x + L` at the same height, and the copy
bit is shifted by the flip bit of the sum.  The proof is the induction on `A`: crossing the wall at
a coordinate of `A` replaces `a` by the neighbouring cube `wallNb a i (side i)` and `x` by
`x - wallLamV a i (side i)`, keeping the height (`ceilH_wallNb`) and the wall types of the
remaining coordinates (`wallGam_wallNb_ne`). -/
theorem walk_aux :
    ∀ (A : Finset (Fin 3)) (a : Fin 48) (x : CuspE3) (s : ℝ) (side : Fin 3 → Fin 2),
      x ∈ cubeBox a → 11 / 10 ≤ s → s ≤ ceilH a x →
      (∀ i ∈ A, x i = (Work.Cusp.cubeCorner a i : ℝ)
        + (if (side i : ℕ) = 0 then 0 else 1)) →
      ∃ (b : Fin 48) (L : Fin 3 → ℤ),
        (∀ i, (Work.Cusp.latMod (Work.Cusp.cubeCusp a) i : ℤ) ∣ L i) ∧
        x + cuspCert.intVec L ∈ cubeBox b ∧
        cubeBit b = cubeBit a + (∑ i ∈ A, wallGam a i (side i)).2 ∧
        Work.FoldInst.act (∑ i ∈ A, wallGam a i (side i)).1 (chartKlein a (mkE4 x s)) =
          chartKlein b (mkE4 (x + cuspCert.intVec L) s) := by
  intro A
  refine Finset.induction_on A ?_ ?_
  · intro a x s side hx hs hceil hA
    have h0 : x + cuspCert.intVec (0 : Fin 3 → ℤ) = x := by
      apply PiLp.ext; intro i
      simp [cuspCert.intVec]
    have hsum0 : (∑ i ∈ (∅ : Finset (Fin 3)), wallGam a i (side i)) = 0 := by simp
    refine ⟨a, 0, ?_, ?_, ?_, ?_⟩
    · intro i; simp
    · rw [h0]; exact hx
    · rw [hsum0]; simp
    · rw [h0, hsum0]
      simp only [Prod.fst_zero, FoldInst.act_zero]
  · intro i A' hi ih a x s side hx hs hceil hA
    have hAi : x i = (Work.Cusp.cubeCorner a i : ℝ)
        + (if (side i : ℕ) = 0 then 0 else 1) := hA i (Finset.mem_insert_self i A')
    have hwall' : x i = (Work.Cusp.cubeCorner a i : ℝ) + (if side i = 0 then 0 else 1) := by
      rw [hAi, cuspWall_ite_side_zero]
    have hmem' : x - wallLamV a i (side i) ∈ cubeBox (wallNb a i (side i)) :=
      cuspWall_mem_box a i (side i) hx hwall'
    have hcusp : Work.Cusp.cubeCusp (wallNb a i (side i)) = Work.Cusp.cubeCusp a :=
      cuspWall_cubeCusp_wallNb a i (side i)
    have hceil' : s ≤ ceilH (wallNb a i (side i)) (x - wallLamV a i (side i)) := by
      rw [ceilH_wallNb a i (side i) hAi]; exact hceil
    have hA' : ∀ j ∈ A', (x - wallLamV a i (side i)) j
        = (Work.Cusp.cubeCorner (wallNb a i (side i)) j : ℝ)
          + (if (side j : ℕ) = 0 then 0 else 1) := by
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [cuspWall_tan_coord a i (side i) hji, hA j (Finset.mem_insert_of_mem hj)]
      ring
    obtain ⟨b, L', hL', hmem, hbit, hact⟩ :=
      ih (wallNb a i (side i)) (x - wallLamV a i (side i)) s side hmem' hs hceil' hA'
    have hsum : (∑ j ∈ insert i A', wallGam a j (side j))
        = wallGam a i (side i) + (∑ j ∈ A', wallGam (wallNb a i (side i)) j (side j)) := by
      rw [Finset.sum_insert hi]
      congr 1
      exact Finset.sum_congr rfl (fun j hj => (wallGam_wallNb_ne a i (side i) j (side j)
        (fun h => hi (h ▸ hj))).symm)
    have hxL : x + cuspCert.intVec (L' - wallLam a i (side i))
        = (x - wallLamV a i (side i)) + cuspCert.intVec L' := by
      rw [cuspCert.intVec_sub]; abel
    have hwallact : Work.FoldInst.act (wallGamK a i (side i)) (chartKlein a (mkE4 x s))
        = chartKlein (wallNb a i (side i)) (mkE4 (x - wallLamV a i (side i)) s) :=
      (chartKlein_wall a i (side i) hAi hx hs).symm
    have hbit2 : (∑ j ∈ insert i A', wallGam a j (side j)).2
        = wallGamFlip a i (side i)
          + (∑ j ∈ A', wallGam (wallNb a i (side i)) j (side j)).2 := by
      rw [hsum]; simp [wallGam]
    have hfst : (∑ j ∈ insert i A', wallGam a j (side j)).1
        = wallGamK a i (side i)
          + (∑ j ∈ A', wallGam (wallNb a i (side i)) j (side j)).1 := by
      rw [hsum]; simp [wallGam]
    refine ⟨b, L' - wallLam a i (side i), ?_, ?_, ?_, ?_⟩
    · intro t
      rcases hL' t with ⟨m, hm⟩
      exact dvd_sub (by rw [← hcusp]; exact ⟨m, hm⟩) (latMod_dvd_wallLam a i (side i) t)
    · rw [hxL]; exact hmem
    · rw [hbit2, hbit, (cuspWallTableCerts.2.1 a i (side i))]
      abel
    · rw [hfst, hxL,
        show wallGamK a i (side i)
            + (∑ j ∈ A', wallGam (wallNb a i (side i)) j (side j)).1
          = (∑ j ∈ A', wallGam (wallNb a i (side i)) j (side j)).1
            + wallGamK a i (side i) from add_comm _ _,
        ← Work.FoldInst.act_add, hwallact, hact]

/-- **The walk of the identification group on closed-cube chart points.**

Let `a : Fin 48` be a cube, `x` a point of its closed unit cube `cubeBox a` and `s ≥ 11/10` a
height at most the ceiling `ceilH a x` (so that `chartKlein a (mkE4 x s)` lies in `Q̄`).  Let
`γ ∈ Gg` be an element of the identification group `Ksub` at the Klein point
`chartKlein a (mkE4 x s)`.

Then the γ-image of that Klein point is again the chart of a *closed* cube `b`, taken at a
coordinate `x + λ` (a lattice translate of `x`), at the *same* height `s`:

  `act γ.1 (chartKlein a (mkE4 x s)) = chartKlein b (mkE4 (x + λ) s)`,   `x + λ ∈ cubeBox b`,

and the copy bit is carried along by γ: `cubeBit b = cubeBit a + γ.2`.

(Reviewed: two referees verified on the workspace data that `wallNb` preserves the cusp, that
`latMod (cubeCusp a) j ∣ wallLam a i side j`, that `x − λ ∈ cubeBox (wallNb a i side)` for all 288
walls, that the copy bit transforms by `wallGamFlip`, and that `Ksub` is generated by the wall
types at the pinned coordinates.)

Numerics supporting this: for `a = 0` with `x` pinned at `{0}`, `{0,1}`, `{0,2}` and `{0,1,2}` and
`s = 1.2`, the canonical representatives of the points `act γ.1 (chartKlein a (mkE4 x s))` over all
`γ` of the subgroup generated by the pinned lower walls were computed exactly: they are always
`(b, x + λ, 1.2)` with `λ` a lattice vector of `Λ_v = diag(latMod v)ℤ³`, i.e. the same height, a
lattice-shifted coordinate and a (possibly different) cube of the same cusp.  For instance for
`a = 0`, `x = (0,0,0)` (pinned in all three coordinates) the eight subgroup elements give
`(0,(0,0,0))`, `(1,(0,0,0))`, `(0,(0,1,0))`, `(1,(0,1,0))`, `(2,(0,0,0))`, `(3,(0,0,0))`,
`(2,(0,1,0))`, `(3,(0,1,0))` (all at height `1.2`).

Route: `Ksub` is generated by the *tight* sides at the point; the tight sides at
`chartKlein a (mkE4 x s)` are the wall facets at the coordinates of `x` sitting at a corner of the
cube (`sideSlack_wallLo`/`sideSlack_wallHi` identify those facets).  For a single such wall the
wall identity `chartKlein_wall` (`wallGam`/`wallNb`/`wallLam` of `cuspChartWalls.lean`,
re-expressed by the saturation tables `covB`/`covK`/`covS`/`covF` of `tsetCoverData.lean` for the
single-bit patterns) gives the conclusion with `λ = −wallLam`; the corrected corner identity is
`cubeCorner (wallNb a i side) j = cubeCorner a j − wallLam a i side j` for `j ≠ i`, while in the
pinned coordinate `j = i` it is `cubeCorner b i = cubeCorner a i − λ i − 1` for `side = 0` and
`cubeCorner b i = cubeCorner a i + 1 − λ i` for `side = 1` — which is what makes `x − λ` land on a
corner of `b`, hence in `cubeBox b`.  The general `γ` is a finite sum of such generators and one
iterates, each step keeping the height `s` and shifting the coordinate by a lattice vector; the
table identities of `covData.lean` (`covData_corner`, `covData_bit`, `covData_gam`) make the
iterated bookkeeping (which wall of which cube comes next, with which group element) a finite
verification.  `Gg` is abelian of exponent 2, so the order and the chosen representations of the
summands do not matter. -/
theorem actX_Ksub_walk {a : Fin 48} {x : Work.RTOwed.CuspE3} (hx : x ∈ Work.RTOwed.cubeBox a)
    {s : ℝ} (hs : 11 / 10 ≤ s) (hceil : s ≤ Work.RTOwed.ceilH a x) {γ : Work.FoldInst.Gg}
    (hγ : γ ∈ Work.FoldInst.Ksub (Work.RTOwed.chartKlein a (Work.RTOwed.mkE4 x s))) :
    ∃ (b : Fin 48) (L : Fin 3 → ℤ),
      (∀ i, (Work.Cusp.latMod (Work.Cusp.cubeCusp a) i : ℤ) ∣ L i) ∧
      x + Work.RTOwed.cuspCert.intVec L ∈ Work.RTOwed.cubeBox b ∧
      Work.RTOwed.cubeBit b = Work.RTOwed.cubeBit a + γ.2 ∧
      Work.FoldInst.act γ.1 (Work.RTOwed.chartKlein a (Work.RTOwed.mkE4 x s)) =
        Work.RTOwed.chartKlein b (Work.RTOwed.mkE4 (x + Work.RTOwed.cuspCert.intVec L) s) := by
  have hmem : chartKlein a (mkE4 x s) ∈ Work.FoldInst.Qbar := chartKlein_mem a hx hs hceil
  have hbox : ∀ j : Fin 3, (Work.Cusp.cubeCorner a j : ℝ) - 1 ≤ x j
      ∧ x j ≤ (Work.Cusp.cubeCorner a j : ℝ) + 2 := by
    intro j
    have h := hx j
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hle : Work.FoldInst.Ksub (chartKlein a (mkE4 x s))
      ≤ AddSubgroup.closure
          ((fun i => wallGam a i (sideOf a x i)) '' (↑(pinSet a x) : Set (Fin 3))) := by
    rw [Work.FoldInst.Ksub_eq_closure
      (⟨cubeBit a, ⟨chartKlein a (mkE4 x s), hmem⟩⟩ : Work.FoldInst.Xbar)]
    refine AddSubgroup.closure_mono ?_
    rintro ρ ⟨S, hS, rfl⟩
    have hS0 : Work.FoldInst.sideSlack S (chartKlein a (mkE4 x s)) = 0 := by
      have h := (Work.FoldInst.tightSides_spec
        (⟨cubeBit a, ⟨chartKlein a (mkE4 x s), hmem⟩⟩ : Work.FoldInst.Xbar) S).mp hS
      simpa using h
    rcases tight_is_wall_closed hx hs hceil hS0 with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have hxi : x i = (Work.Cusp.cubeCorner a i : ℝ) :=
        (wallLo_slack_sign a i hs hbox).2.1.mp hS0
      refine ⟨i, ?_, ?_⟩
      · change i ∈ pinSet a x
        rw [mem_pinSet]; exact Or.inl hxi
      · show wallGam a i (sideOf a x i) = Work.FoldInst.sideType (wallLo a i)
        rw [wallGam_eq_sideType,
          show wallAt a i (sideOf a x i) = wallLo a i from by
            rw [sideOf_eq_of_eq a hxi]; exact wallAt_zero a i]
    · have hxi : x i = (Work.Cusp.cubeCorner a i : ℝ) + 1 :=
        (wallHi_slack_sign a i hs hbox).2.1.mp hS0
      refine ⟨i, ?_, ?_⟩
      · change i ∈ pinSet a x
        rw [mem_pinSet]; exact Or.inr hxi
      · show wallGam a i (sideOf a x i) = Work.FoldInst.sideType (wallHi a i)
        rw [wallGam_eq_sideType,
          show wallAt a i (sideOf a x i) = wallHi a i from by
            rw [sideOf_eq_of_eq_add_one a hxi]; exact wallAt_one a i]
  obtain ⟨A, hAI, hγsum⟩ :=
    exists_subset_sum_of_mem_closure (fun i => wallGam a i (sideOf a x i)) (pinSet a x)
      (hle hγ)
  obtain ⟨b, L, hL, hmem', hbit, hact⟩ :=
    walk_aux A a x s (sideOf a x) hx hs hceil (fun i hi => sideOf_spec a x (hAI hi))
  exact ⟨b, L, hL, hmem', by rw [hγsum]; exact hbit, by rw [hγsum]; exact hact⟩

end

end Work.RTOwed
