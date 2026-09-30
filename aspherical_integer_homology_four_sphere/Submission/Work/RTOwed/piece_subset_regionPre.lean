import Mathlib
import Submission.Work.RTOwed.CuspPiece
import Submission.Work.RTOwed.cuspWall_step
import Submission.Work.RTOwed.sideSlack_pos_of_not_wall
import Submission.Work.RTOwed.wallLo_slack_sign
import Submission.Work.RTOwed.wallHi_slack_sign
import Submission.Work.RTOwed.chartKlein_self_facet
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspCert.CuspSupport
import Submission.Work.RTOwed.cuspCert.cubeOfMod_corner_dvd
import Submission.Work.RTOwed.cuspWallTableCerts
import Submission.Work.RTOwed.chartKlein_wall
import Submission.Work.RTOwed.sideSlack_wallHi_chartKlein
import Submission.Work.RTOwed.wallGam_sideType
import Submission.Work.RTOwed.wallNb_upper
import Submission.Work.RTOwed.cuspCert.mbarPt_continuous
import Submission.Work.RTOwed.ceilH_eq_beta
import Submission.Work.RTOwed.isOpen_piece

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed

open chartKleinMem

/-! ## The wall certificates at an arbitrary positive height

The certificates of `chartKlein_wall` and `sideSlack_wallHi_chartKlein` are proved from the fact that
the chart vector `cwVec` is a *polynomial* in the height `s`: the wall identity
`cwVec_wall` (resp. the numerator identity `Nside_wallHi_eq_zero`) holds for **every** `s`, and the
Klein map only needs `s ≠ 0`.  The hypotheses `11/10 ≤ s` of the two certificates are therefore
never used, and below we restate them for `0 < s`. -/

/-- **The wall gluing certificate of the cube charts at every positive height.** -/
theorem chartKlein_wall_pos (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3}
    (hy : y i = (Cusp.cubeCorner a i : ℝ) + (if (side : ℕ) = 0 then 0 else 1)) {s : ℝ}
    (hs : 0 < s) :
    chartKlein (wallNb a i side) (mkE4 (y - wallLamV a i side) s)
      = FoldInst.act (wallGamK a i side) (chartKlein a (mkE4 y s)) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  rw [cwChart _ _ _ hs0, cwChart _ _ _ hs0, cwVec_wall a i side y s hy, cwKlein_signExt]

/-- **The high wall of the cube chart is tight, at every positive height.** -/
theorem sideSlack_wallHi_chartKlein_pos (a : Fin 48) (i : Fin 3) {y : CuspE3} {s : ℝ}
    (hy : y ∈ cubeBox a) (hface : y i = (Cusp.cubeCorner a i : ℝ) + 1) (hs : 0 < s) :
    FoldInst.sideSlack (wallHi a i) (chartKlein a (mkE4 y s)) = 0 := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have h4 : 0 < chartVec a y s 4 := chartVec4_pos_any a y s
  rw [sideSlack_eq a (wallHi a i) y s hs0 h4.ne', Nside_wallHi_eq_zero a i hface]
  ring

/-- **The one-step wall bookkeeping at every positive height.** -/
theorem cuspWall_step_pos (v : Fin 5) {a : Fin 48} (hca : Cusp.cubeCusp a = v) (i : Fin 3)
    (side : Fin 2) {k : Fin 3 → ℤ} {q : CuspE4} (hs : 0 < q 3)
    (hu : uhsXj q - cuspCert.lamV v k ∈ cubeBox a)
    (hwall : (uhsXj q - cuspCert.lamV v k) i
      = (Cusp.cubeCorner a i : ℝ) + (if side = 0 then 0 else 1)) :
    ∃ k' : Fin 3 → ℤ, (cuspCert.lamV v k' = cuspCert.lamV v k + wallLamV a i side)
      ∧ cellPt v (wallNb a i side) k' q = FoldInst.act (wallGamK a i side) (cellPt v a k q)
      ∧ (uhsXj q - cuspCert.lamV v k') ∈ cubeBox (wallNb a i side)
      ∧ Cusp.cubeCusp (wallNb a i side) = v
      ∧ (uhsXj q - cuspCert.lamV v k') i = (Cusp.cubeCorner (wallNb a i side) i : ℝ)
          + (if side = 0 then 1 else 0)
      ∧ (∀ j : Fin 3, j ≠ i → ((uhsXj q - cuspCert.lamV v k') j
            = (Cusp.cubeCorner (wallNb a i side) j : ℝ) + 1
          ↔ (uhsXj q - cuspCert.lamV v k) j = (Cusp.cubeCorner a j : ℝ) + 1)) := by
  obtain ⟨_, _, _, _, _, hLat⟩ := cuspWallTableCerts
  obtain ⟨k₀, hk₀⟩ := hLat a i side
  rw [hca] at hk₀
  have hkey : uhsXj q - cuspCert.lamV v (k + k₀)
      = (uhsXj q - cuspCert.lamV v k) - wallLamV a i side := by
    rw [cuspWall_lamV_add, ← hk₀]
    abel
  have hlam : cuspCert.lamV v (k + k₀) = cuspCert.lamV v k + wallLamV a i side := by
    rw [hk₀]; exact cuspWall_lamV_add v k k₀
  have hwall' : (uhsXj q - cuspCert.lamV v k) i
      = (Cusp.cubeCorner a i : ℝ) + (if (side : ℕ) = 0 then 0 else 1) := by
    rw [hwall, cuspWall_ite_side_zero]
  refine ⟨k + k₀, hlam, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cellPt, hkey]
    exact chartKlein_wall_pos a i side hwall' hs
  · rw [hkey]; exact cuspWall_mem_box a i side hu hwall
  · rw [cuspWall_cubeCusp_wallNb, hca]
  · rw [hkey]; exact cuspWall_norm_coord a i side hwall
  · rw [hkey]; intro j hj; exact cuspWall_hi_iff a i side hj

/-! ## The ceiling of a cell -/

/-- **The ceiling is invariant under a lattice translation of the cube.** -/
theorem ceilH_sub_lamV' (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) {y : CuspE3}
    (hya : y ∈ cubeBox a) (hyb : y - cuspCert.lamV v k ∈ cubeBox b) :
    ceilH a y = ceilH b (y - cuspCert.lamV v k) := by
  have h1 : ceilH a y = Work.Cusp.beta (y - cuspH) := by
    have h := ceilH_eq_beta a (y := y - cuspH) (by rw [sub_add_cancel]; exact hya)
    rwa [sub_add_cancel] at h
  have h2 : ceilH b (y - cuspCert.lamV v k)
      = Work.Cusp.beta ((y - cuspCert.lamV v k) - cuspH) := by
    have h := ceilH_eq_beta b (y := (y - cuspCert.lamV v k) - cuspH)
      (by rw [sub_add_cancel]; exact hyb)
    rwa [sub_add_cancel] at h
  have h3 : (y - cuspCert.lamV v k) - cuspH
      = (y - cuspH) + Work.Cusp.ofInt3 (fun i => -(cuspCert.lamK v k i)) := by
    apply PiLp.ext; intro i
    fin_cases i <;>
      simp only [PiLp.sub_apply, PiLp.add_apply, cuspH, Work.Cusp.ofInt3, cuspCert.lamV,
        cuspCert.lamK, PiLp.toLp_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;>
      push_cast <;> ring
  rw [h1, h2, h3]
  exact (Work.Cusp.beta_add_int (y - cuspH) _).symm

/-- **The ceiling of a cell is the ceiling of the canonical cube over the point.** -/
theorem ceilH_cell_eq_chartRed' (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) {q : CuspE4}
    (hbox : uhsXj q - cuspCert.lamV v k ∈ cubeBox a) :
    ceilH a (uhsXj q - cuspCert.lamV v k) = ceilH (chartCube v q) (chartRed v q) := by
  have hfloor : uhsXj q - cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) = redV v (uhsXj q) :=
    cuspCert.sub_lamV_floorK v (uhsXj q) (fun i => cuspCert.floorV_dvd v (uhsXj q) i)
  have hlam : cuspCert.lamV v (fun i => cuspCert.floorK v (uhsXj q) i - k i)
      = cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) - cuspCert.lamV v k := by
    apply PiLp.ext; intro i
    simp only [cuspCert.lamV, PiLp.sub_apply, PiLp.toLp_apply]
    rw [cuspCert.lamK_sub]
    push_cast
    ring
  have hpoint : (uhsXj q - cuspCert.lamV v k)
      - cuspCert.lamV v (fun i => cuspCert.floorK v (uhsXj q) i - k i) = redV v (uhsXj q) := by
    rw [hlam]
    have : (uhsXj q - cuspCert.lamV v k)
        - (cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) - cuspCert.lamV v k)
        = uhsXj q - cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) := by abel
    rw [this, hfloor]
  have htrans := ceilH_sub_lamV' v a (cubeOf v (uhsXj q))
    (fun i => cuspCert.floorK v (uhsXj q) i - k i) hbox
    (by rw [hpoint]; exact redV_mem_cubeBox v (uhsXj q))
  rw [hpoint] at htrans
  rw [htrans, chartCube, chartRed]

/-- **Below the ceiling of its cube, from membership in `Q̄`.**

If the chart value of the cube `a` at the cube coordinate `u ∈ cubeBox a` and the positive height
`s` lies in the truncated 24-cell, then `s` is at most the ceiling `ceilH a u`.  For `s ≥ 11/10`
this is the own-facet certificate `chartKlein_self_facet`; for smaller `s` it is the trivial bound
`ceilH a u = β (u - cuspH) ≥ √(3/2) > 11/10 > s`. -/
theorem le_ceilH_of_mem_Qbar (a : Fin 48) {u : CuspE3} (hu : u ∈ cubeBox a) {s : ℝ}
    (hs : 0 < s) (hQ : chartKlein a (mkE4 u s) ∈ FoldInst.Qbar) : s ≤ ceilH a u := by
  by_cases h : 11 / 10 ≤ s
  · exact (chartKlein_self_facet a hu h).mp (hQ.2 (cubeVert a))
  · have hceil : ceilH a u = Work.Cusp.beta (u - cuspH) := by
      have hh := ceilH_eq_beta a (y := u - cuspH) (by rw [sub_add_cancel]; exact hu)
      rwa [sub_add_cancel] at hh
    have hb : 11 / 10 ≤ Work.Cusp.beta (u - cuspH) := s1_le_beta (u - cuspH)
    rw [hceil]
    exact le_trans (le_of_lt (lt_of_not_ge h)) hb

/-- **The source point of a cell chart lies below the ceiling of the cusp.** -/
theorem le_beta_of_mem_Qbar (v : Fin 5) {a : Fin 48} {k : Fin 3 → ℤ} {q : CuspE4}
    (hs : 0 < q 3) (hu : uhsXj q - cuspCert.lamV v k ∈ cubeBox a)
    (hQ : chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) ∈ FoldInst.Qbar) :
    q 3 ≤ Work.Cusp.beta (xOf4 q) := by
  have h1 := le_ceilH_of_mem_Qbar a hu hs hQ
  have h2 := ceilH_cell_eq_chartRed' v a k hu
  have h3 := ceilH_chartRed v q
  rw [h3] at h2
  linarith

/-! ## The walk to the canonical cell -/

/-- The finite check on the lookup table: the unit box with lower corner `cubeCorner a` selects
the cube `a`. -/
theorem cubeOfMod_cubeCorner_aux : ∀ a : Fin 48,
    Cusp.cubeOfMod (Cusp.cubeCusp a) (Cusp.cubeCorner a) = a := by
  decide

/-- **The floor identification of a half-open cell**: if the unfolded coordinate
`uhsXj q - lamV v k` lies in the half-open unit box of a cube `a` of the cusp `v`, then `a` is the
canonical cube `cubeOf v (uhsXj q)` of the point and the offset is the canonical one. -/
theorem cubeOf_halfopen_aux (v : Fin 5) {a : Fin 48} (hca : Cusp.cubeCusp a = v) {k : Fin 3 → ℤ}
    {q : CuspE4} (hu : uhsXj q - cuspCert.lamV v k ∈ cuspCert.halfopenBox a) :
    cubeOf v (uhsXj q) = a ∧ redV v (uhsXj q) = uhsXj q - cuspCert.lamV v k := by
  have hfloor : floorV (uhsXj q) = fun i => Cusp.cubeCorner a i + cuspCert.lamK v k i := by
    funext i
    have hu' := hu i
    have hfloor_u : ⌊(uhsXj q - cuspCert.lamV v k) i⌋ = Cusp.cubeCorner a i := by
      rw [Int.floor_eq_iff]
      exact ⟨hu'.1, hu'.2⟩
    have heq : (uhsXj q) i = (uhsXj q - cuspCert.lamV v k) i + (cuspCert.lamK v k i : ℝ) := by
      rw [show (uhsXj q) i = ((uhsXj q - cuspCert.lamV v k) + cuspCert.lamV v k) i from by
            rw [sub_add_cancel]]
      simp only [PiLp.add_apply, cuspCert.lamV]
    show ⌊(uhsXj q) i⌋ = _
    rw [heq, Int.floor_add_intCast, hfloor_u]
  have hcube : cubeOf v (uhsXj q) = a := by
    show Cusp.cubeOfMod v (floorV (uhsXj q)) = a
    rw [hfloor]
    rw [show (fun i => Cusp.cubeCorner a i + cuspCert.lamK v k i)
        = (fun i => Cusp.cubeCorner a i + (Cusp.latMod v i : ℤ) * k i) from rfl]
    rw [cuspCert.cubeOfMod_add_latMod]
    rw [← hca]
    exact cubeOfMod_cubeCorner_aux a
  refine ⟨hcube, ?_⟩
  apply PiLp.ext; intro i
  have hfl : ⌊(uhsXj q) i⌋ = Cusp.cubeCorner a i + cuspCert.lamK v k i := by
    have := congrFun hfloor i
    simpa only [floorV] using this
  simp only [redV, PiLp.toLp_apply]
  rw [hcube, hfl]
  simp only [PiLp.sub_apply, cuspCert.lamV]
  push_cast
  ring

/-- **The walk of a cell to the canonical cell.**  From a cell `(a,k)` whose unfolded coordinate
`uhsXj q - lamV v k` lies in the closed unit cube of `a`, a finite sequence of crossings of the
*upper* walls of the successive cubes reaches the *half-open* unit cube of a cube `a'` of the same
cusp, with a group element `Γ ∈ Ksub` of the chart point of `(a,k)` carrying the chart value of
`(a,k)` to the chart value of `(a',k')`. -/
theorem cellWalk_aux (v : Fin 5) (q : CuspE4) (hs : 0 < q 3) :
    ∀ (D : Finset (Fin 3)) (a : Fin 48) (k : Fin 3 → ℤ),
      Cusp.cubeCusp a = v →
      (uhsXj q - cuspCert.lamV v k) ∈ cubeBox a →
      (∀ i : Fin 3, (uhsXj q - cuspCert.lamV v k) i = (Cusp.cubeCorner a i : ℝ) + 1 →
        i ∈ D) →
      ∃ (a' : Fin 48) (k' : Fin 3 → ℤ) (Γ : FoldInst.Gg),
        Cusp.cubeCusp a' = v ∧
        (uhsXj q - cuspCert.lamV v k') ∈ cuspCert.halfopenBox a' ∧
        Γ ∈ FoldInst.Ksub (cellPt v a k q) ∧
        cubeBit a + Γ.2 = cubeBit a' ∧
        cellPt v a' k' q = FoldInst.act Γ.1 (cellPt v a k q) := by
  intro D
  induction D using Finset.induction with
  | empty =>
      intro a k hca hu hD
      have hne : ∀ i : Fin 3, (uhsXj q - cuspCert.lamV v k) i ≠ (Cusp.cubeCorner a i : ℝ) + 1 :=
        fun i h => Finset.notMem_empty i (hD i h)
      refine ⟨a, k, 0, hca, fun i => ⟨(hu i).1, lt_of_le_of_ne (hu i).2 (hne i)⟩,
        (FoldInst.Ksub _).zero_mem, ?_, ?_⟩
      · show cubeBit a + (0 : FoldInst.Gg).2 = cubeBit a
        rw [show (0 : FoldInst.Gg).2 = 0 from rfl, add_zero]
      · show cellPt v a k q = FoldInst.act (0 : FoldInst.Gg).1 (cellPt v a k q)
        rw [show (0 : FoldInst.Gg).1 = 0 from rfl, FoldInst.act_zero]
  | insert i D' hi ih =>
      intro a k hca hu hD
      by_cases hwall : (uhsXj q - cuspCert.lamV v k) i = (Cusp.cubeCorner a i : ℝ) + 1
      · have hwall' : (uhsXj q - cuspCert.lamV v k) i
            = (Cusp.cubeCorner a i : ℝ) + (if (1 : Fin 2) = 0 then 0 else 1) := by
          rw [hwall]
          norm_num
        obtain ⟨k₁, hlam, hact, hu₁, hc₁, hnorm, hhi⟩ :=
          cuspWall_step_pos v hca i 1 hs hu hwall'
        have hD' : ∀ j : Fin 3,
            (uhsXj q - cuspCert.lamV v k₁) j
              = (Cusp.cubeCorner (wallNb a i 1) j : ℝ) + 1 → j ∈ D' := by
          intro j hj
          by_cases hji : j = i
          · exfalso
            subst hji
            rw [hnorm] at hj
            have hif : (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by norm_num
            rw [hif, add_zero] at hj
            linarith
          · have hj' : (uhsXj q - cuspCert.lamV v k) j = (Cusp.cubeCorner a j : ℝ) + 1 :=
              (hhi j hji).mp hj
            have hmem := hD j hj'
            rw [Finset.mem_insert] at hmem
            rcases hmem with h | h
            · exact absurd h hji
            · exact h
        obtain ⟨a', k', Γ₁, hca', hhalf, hΓ₁, hbit₁, hact₁⟩ := ih (wallNb a i 1) k₁ hc₁ hu₁ hD'
        refine ⟨a', k', Γ₁ + (wallGamK a i 1, wallGamFlip a i 1), hca', hhalf, ?_, ?_, ?_⟩
        · have hΓ₁' : Γ₁ ∈ FoldInst.Ksub (cellPt v a k q) := by
            rw [← FoldInst.Ksub_act (wallGamK a i 1) (cellPt v a k q)]
            rw [← hact]
            exact hΓ₁
          have hγ : (wallGamK a i 1, wallGamFlip a i 1) ∈ FoldInst.Ksub (cellPt v a k q) := by
            rw [(wallGam_sideType a i).2]
            refine AddSubgroup.subset_closure ⟨wallHi a i, ?_, rfl⟩
            simpa only [cellPt] using sideSlack_wallHi_chartKlein_pos a i hu hwall hs
          exact AddSubgroup.add_mem _ hΓ₁' hγ
        · show cubeBit a + (Γ₁ + (wallGamK a i 1, wallGamFlip a i 1)).2 = cubeBit a'
          rw [show (Γ₁ + (wallGamK a i 1, wallGamFlip a i 1)).2
              = Γ₁.2 + wallGamFlip a i 1 from rfl]
          rw [← hbit₁, (wallGam_sideType a i).1]
          abel
        · have hone : (Γ₁ + (wallGamK a i 1, wallGamFlip a i 1)).1
              = Γ₁.1 + wallGamK a i 1 := rfl
          rw [hact₁, hact, hone, ← FoldInst.act_add]
      · have hD' : ∀ j : Fin 3, (uhsXj q - cuspCert.lamV v k) j = (Cusp.cubeCorner a j : ℝ) + 1 →
            j ∈ D' := by
          intro j hj
          have hmem := hD j hj
          rw [Finset.mem_insert] at hmem
          rcases hmem with h | h
          · exact absurd (h ▸ hj) hwall
          · exact h
        exact ih a k hca hu hD'

/-! ## The target -/

theorem piece_subset_regionPre (v : Fin 5) {B : Set CuspE4} (hB : IsOpen B)
    (hBpos : ∀ q ∈ B, 0 < q 3) {a : Fin 48} (hca : Cusp.cubeCusp a = v) (k : Fin 3 → ℤ) :
    piece v a k B ⊆ regionPre v B := by
  intro x hx
  obtain ⟨hx1, q, hpq, hqx⟩ := hx
  have hqB : q ∈ B := hpq.1
  have hs : 0 < q 3 := hBpos q hqB
  -- the chart value of the cell lies in the truncated 24-cell
  have hQ : cellPt v a k q ∈ FoldInst.Qbar := by rw [← hqx]; exact x.2.2
  have hQ' : chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) ∈ FoldInst.Qbar :=
    hQ
  -- the unfolded coordinate lies in the closed unit cube: the chamber fact
  have hu : uhsXj q - cuspCert.lamV v k ∈ cubeBox a :=
    cubeBox_of_mem_Qbar a hs hQ'
  -- the source point lies below the ceiling of its cusp
  have hceil : q 3 ≤ Cusp.beta (xOf4 q) := le_beta_of_mem_Qbar v hs hu hQ'
  -- the walk to the canonical cell
  obtain ⟨a', k', Γ, hca', hhalf, hΓ, hbit, hact⟩ :=
    cellWalk_aux v q hs Finset.univ a k hca hu (fun i _ => Finset.mem_univ i)
  obtain ⟨hcube, hred⟩ := cubeOf_halfopen_aux v hca' hhalf
  -- the chart value of the canonical cell is the reduced chart of `q`
  have hcanon : cellPt v a' k' q = redChart v (cubeOf v (uhsXj q)) q := by
    unfold cellPt redChart
    rw [hcube, hred]
  have hQcanon : cellPt v a' k' q ∈ FoldInst.Qbar := by
    rw [hact]
    exact (FoldInst.Qbar_act Γ.1 (cellPt v a k q)).mpr hQ
  have hbranch : redChart v (cubeOf v (uhsXj q)) q ∈ FoldInst.Qbar := by
    rw [← hcanon]; exact hQcanon
  -- `cuspLowPt v q` is the explicit chart point of the canonical cell
  have hlow : cuspLowPt v q
      = (cubeBit (cubeOf v (uhsXj q)), ⟨redChart v (cubeOf v (uhsXj q)) q, hbranch⟩) := by
    rw [cuspLowPt]
    exact dif_pos hbranch
  -- the group element carries `x` to it
  have hactX : FoldInst.actX Γ x = cuspLowPt v q := by
    rw [hlow]
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show x.1 + Γ.2 = cubeBit (cubeOf v (uhsXj q))
      rw [hx1, hbit, hcube]
    · show FoldInst.act Γ.1 x.2.1 = redChart v (cubeOf v (uhsXj q)) q
      rw [hqx, ← hact, hcanon]
  have hrel : FoldInst.rel x (cuspLowPt v q) :=
    ⟨Γ, by rw [hqx]; exact hΓ, hactX⟩
  rw [regionPre_eq v B]
  exact ⟨q, ⟨hqB, hceil⟩, FoldInst.rel_symm hrel⟩

end Work.RTOwed
