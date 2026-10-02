/-
# `Work.ELAssembly.Dnest_cl_of` — the strict nesting at level `1` of the `b₂`-nest

The certificate field `CertGeometry.Dnest_cl` (C4) asks that the *closure* of the level-`1`
region of the `b₂`-nest lie inside the level-`0` region:

```lean
closure (polyRegion [Za 1, Zb 1, Zc 1] (Dlev L 1)) ⊆ polyRegion [Za 0, Zb 0, Zc 0] (Dlev L 0)
```

Both regions are described by `Work.ELTop.polyRegion_eq_inter_pairSideNear` (applied through
`Work.ELAssembly.Dmem_of`): the level-`n` region is the intersection of the three *near sides*
`pairSideNear (Za n)`, `pairSideNear (Zb n)`, `pairSideNear (Zc n)` with the sublevel set
`{pot < log (Dlev L n)}`.  Hence the required inclusion has two ingredients.

* **The potential.**  `z ∈ closure (level 1)` gives `pot z ≤ log (Dlev L 1)`, and
  `Dlev L 1 = L^{1/64} < L = Dlev L 0` since `1 < L`; so `pot z < log (Dlev L 0)`.
* **The sides.**  `z ∈ closure (pairSideNear (Za 1))`, and the closure of a near side is the side
  together with the pair curve (`Work.ELTop.pairSides_decomposition`: the pair curve is the
  frontier of each side, and the sides are open).  The side itself is contained in the level-`0`
  near side by NEST (T6) in its orientation-complete form (`Work.ELAssembly.nest_side_of_nearArc`)
  applied to the level-`1`/level-`0` pair curves, which are disjoint
  (`Work.ELAssembly.Za_succ_curve_disjoint`), while the pair *curve* at level `1` is contained in
  the level-`0` near side because

  - the ray parts are put there by the angular data `InArc` (`Work.ELTop.paramRay_subset_pairSideNear`),
  - the landing point is put there by the closure argument of `Work.ELAssembly.tripod_mem`'s
    fourth component (a landing point of a ray inside a near side lies in that near side, the only
    obstruction being the pair curve, which meets the filled Julia set only at its own landing
    point).

The whole argument is *modulo the level-`1`/level-`0` angular data*
`Work.ELAssembly.DnestCl.inArc_levelOne`, which records that the level-`1` arm angles lie in the
near arcs of the level-`0` arm pairs (after an integer shift for the two "wrapping" angles
`armA1 1` and `armB1 1`, which lie below their tripod angle).
-/
import Mathlib
import Submission.Work.ELAssembly.Derived.Fields
import Submission.Work.ELAssembly.Derived.AssemblyFields
import Submission.Work.ELAssembly.armAngle_order
import Submission.Work.ELAssembly.tripod_mem
import Submission.Work.ELTop.RegionBasics
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.isOpen_polyRegion
import Submission.Work.ELTop.paramRay_subset_pairSideNear
import Submission.Work.ELTop.landsN_mem_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

namespace DnestCl

/-! ## The arc-length of a pair carrying a near arc -/

/-- If a ray of an angle in the near arc `(b, a + 1)` of a pair exists, then the pair is
non-degenerate: `arcLen a b ≠ 0`.  (Same argument as in `Work.ELAssembly.tripod_mem`.) -/
theorem arcLen_ne_zero_of_InArc_near {a b θ : ℝ} (h : Work.EL.InArc θ b (a + 1)) :
    Work.EL.arcLen a b ≠ 0 := by
  have hpos : 0 < Int.fract (θ - b) := h.1
  have hlt : Int.fract (θ - b) < Work.EL.arcLen b (a + 1) := h.2
  have harc : Work.EL.arcLen b (a + 1) = Int.fract (a - b) := by
    rw [Work.EL.arcLen, show a + 1 - b = (a - b) + 1 by ring, Int.fract_add_one]
  have hab : 0 < Int.fract (a - b) := by rw [← harc]; linarith
  have hlt1 : Int.fract (a - b) < 1 := Int.fract_lt_one _
  have hneg := Int.fract_neg (x := a - b) (ne_of_gt hab)
  rw [Work.EL.arcLen, show b - a = -(a - b) by ring, hneg]
  linarith

/-! ## The level-`1` angles in the level-`0` near arcs -/

/-- **The six level-`1` arm angles lie in the near arcs of the level-`0` arm pairs.**  The two
"wrapping" angles `armA1 1` and `armB1 1` lie *below* their tripod angle, so it is their unit
translate that sits in the near arc; `InArc` is invariant under integer translates. -/
theorem inArc_levelOne :
    Work.EL.InArc (Work.ELNest.armA1 1) (Work.ELNest.armA2 0) (Work.ELNest.armA1 0 + 1) ∧
    Work.EL.InArc (Work.ELNest.armA2 1) (Work.ELNest.armA2 0) (Work.ELNest.armA1 0 + 1) ∧
    Work.EL.InArc (Work.ELNest.armB1 1) (Work.ELNest.armB2 0) (Work.ELNest.armB1 0 + 1) ∧
    Work.EL.InArc (Work.ELNest.armB2 1) (Work.ELNest.armB2 0) (Work.ELNest.armB1 0 + 1) ∧
    Work.EL.InArc (Work.ELNest.armC1 1) (Work.ELNest.armC2 0 + 1) (Work.ELNest.armC1 0 + 1) ∧
    Work.EL.InArc (Work.ELNest.armC2 1 + 1) (Work.ELNest.armC2 0 + 1)
      (Work.ELNest.armC1 0 + 1) := by
  obtain ⟨hA10, hA20, -, -, -, -, -, -, -, -, -, -, -, -⟩ := armAngle_facts
  obtain ⟨hA1dec, -, hA1ge, hA2inc, -, hA2lt, hB1dec, hB1gt, -, hB2inc, -, hB2lt, hC1dec, hC1gt,
    hC1lt, hC2inc, hC2pos, hC2lt⟩ := armAngle_order
  have hα12 : Work.EL.alpha1 < Work.EL.alpha2 := by
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hB12 := armB1_lt_armB2 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : Work.EL.InArc (Work.ELNest.armA1 1 + 1) (Work.ELNest.armA2 0)
        (Work.ELNest.armA1 0 + 1) :=
      Work.ELTop.InArc_of_mem_Ioo (by linarith [hA2lt 0, hA1ge 1]) (by linarith [hA1dec 0])
        (by linarith [hα12, hA10, hA20])
    rw [← Work.ELTop.InArc_add_int (Work.ELNest.armA1 1) (Work.ELNest.armA2 0)
      (Work.ELNest.armA1 0 + 1) 1]
    simpa using h
  · exact Work.ELTop.InArc_of_mem_Ioo (by linarith [hA2inc 0]) (by linarith [hA2lt 1, hA1ge 0])
      (by linarith [hα12, hA10, hA20])
  · have h : Work.EL.InArc (Work.ELNest.armB1 1 + 1) (Work.ELNest.armB2 0)
        (Work.ELNest.armB1 0 + 1) :=
      Work.ELTop.InArc_of_mem_Ioo (by linarith [hB2lt 0, hB1gt 1]) (by linarith [hB1dec 0])
        (by linarith [hB12])
    rw [← Work.ELTop.InArc_add_int (Work.ELNest.armB1 1) (Work.ELNest.armB2 0)
      (Work.ELNest.armB1 0 + 1) 1]
    simpa using h
  · exact Work.ELTop.InArc_of_mem_Ioo (by linarith [hB2inc 0]) (by linarith [hB2lt 1, hB1gt 0])
      (by linarith [hB12])
  · have h : Work.EL.InArc (Work.ELNest.armC1 1 + 1) (Work.ELNest.armC2 0 + 1)
        (Work.ELNest.armC1 0 + 1) :=
      Work.ELTop.InArc_of_mem_Ioo (by linarith [hC2lt 0, hC1gt 1]) (by linarith [hC1dec 0])
        (by linarith [hC1lt 0, hC2pos 0])
    rw [← Work.ELTop.InArc_add_int (Work.ELNest.armC1 1) (Work.ELNest.armC2 0 + 1)
      (Work.ELNest.armC1 0 + 1) 1]
    simpa using h
  · exact Work.ELTop.InArc_of_mem_Ioo (by linarith [hC2inc 0]) (by linarith [hC2lt 1, hC1gt 0])
      (by linarith [hC1lt 0, hC2pos 0])

/-! ## The level arithmetic -/

/-- `Dlev L 0 = L`. -/
theorem dlev_zero (L : ℝ) : Work.ELNest.Dlev L 0 = L := by
  rw [Work.ELNest.Dlev]
  norm_num

/-- The level `1` is strictly below the level `0` when `L > 1`. -/
theorem dlev_one_lt_zero {L : ℝ} (hL : 1 < L) :
    Work.ELNest.Dlev L 1 < Work.ELNest.Dlev L 0 := by
  have h0 : Work.ELNest.Dlev L 0 = L ^ (1 : ℝ) := by rw [dlev_zero L, Real.rpow_one]
  have h1 : Work.ELNest.Dlev L 1 = L ^ ((1 : ℝ) / 64) := by
    rw [Work.ELNest.Dlev]
    norm_num
  rw [h0, h1]
  exact (Real.rpow_lt_rpow_left_iff (x := L) hL).mpr (by norm_num)

/-! ## Generic plane topology of the near sides -/

/-- **A landing point of a ray in the near side of a pair is in that near side.**  This is the
general form of the fourth component of `Work.ELAssembly.tripod_mem` (there `Q` is the tripod
pair). -/
theorem landing_mem_pairSideNear_of_InArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) {P Q : Work.EL.CoPair hN}
    (hθ : Work.EL.InArc Q.a P.b (P.a + 1)) (hne : Q.y ≠ P.y) :
    Q.y ∈ Work.EL.pairSideNear P := by
  have hnd : Work.EL.arcLen P.a P.b ≠ 0 := arcLen_ne_zero_of_InArc_near hθ
  have hsub : Work.EL.paramRay hN Q.a ⊆ Work.EL.pairSideNear P :=
    Work.ELTop.paramRay_subset_pairSideNear hN hJ P hθ
  have hcl : Q.y ∈ closure (Work.EL.pairSideNear P) :=
    closure_mono hsub (mem_closure_of_tendsto Q.lands_a (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact Work.EL.rayPt_mem_paramRay hN ht))
  have hopen : IsOpen (Work.EL.pairSideNear P) :=
    (Work.ELTop.isClosed_pairCurve_aux hN P).isOpen_compl.connectedComponentIn
  by_contra hy
  have hfr : Q.y ∈ frontier (Work.EL.pairSideNear P) := by
    rw [hopen.frontier_eq]
    exact ⟨hcl, hy⟩
  rw [(Work.ELTop.pairSides_decomposition hN hJ P hnd).2.2.2] at hfr
  have hK : Q.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN Q.lands_a
  have : Q.y = P.y := by
    simpa using (Work.ELTop.pairCurve_inter_K_subset hN P ⟨hfr, hK⟩)
  exact hne this

/-- **A pair curve whose two rays lie in the near arcs of another pair is contained in the near
side of that pair.** -/
theorem pairCurve_subset_pairSideNear_of_InArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P Q : Work.EL.CoPair hN)
    (hQa : Work.EL.InArc Q.a P.b (P.a + 1)) (hQb : Work.EL.InArc Q.b P.b (P.a + 1))
    (hne : Q.y ≠ P.y) :
    Work.EL.pairCurve Q ⊆ Work.EL.pairSideNear P := by
  intro z hz
  rw [Work.EL.mem_pairCurve_iff] at hz
  rcases hz with h | h | h
  · exact Work.ELTop.paramRay_subset_pairSideNear hN hJ P hQa h
  · rw [h]
    exact landing_mem_pairSideNear_of_InArc hN hJ hQa hne
  · exact Work.ELTop.paramRay_subset_pairSideNear hN hJ P hQb h

/-- **The closure of a near side is the side together with the pair curve.** -/
theorem closure_pairSideNear_subset {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P : Work.EL.CoPair hN) (hnd : Work.EL.arcLen P.a P.b ≠ 0) :
    closure (Work.EL.pairSideNear P) ⊆ Work.EL.pairSideNear P ∪ Work.EL.pairCurve P := by
  intro z hz
  by_cases hzP : z ∈ Work.EL.pairSideNear P
  · exact Or.inl hzP
  · refine Or.inr ?_
    have hopen : IsOpen (Work.EL.pairSideNear P) :=
      (Work.ELTop.isClosed_pairCurve_aux hN P).isOpen_compl.connectedComponentIn
    have hfr : z ∈ frontier (Work.EL.pairSideNear P) := by
      rw [hopen.frontier_eq]
      exact ⟨hz, hzP⟩
    rwa [(Work.ELTop.pairSides_decomposition hN hJ P hnd).2.2.2] at hfr

end DnestCl

open DnestCl

/-- **The strict nesting of the `b₂`-nest at level `1`** (the certificate field
`CertGeometry.Dnest_cl`, derived): the closure of the level-`1` region lies in the level-`0`
region. -/
theorem Dnest_cl_of {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d)
    (T : Work.EL.Tripod d.hN) {L : ℝ} (hL : 1 < L) :
    closure (Work.EL.polyRegion [N.Za 1, N.Zb 1, N.Zc 1] (Work.ELNest.Dlev L 1))
      ⊆ Work.EL.polyRegion [N.Za 0, N.Zb 0, N.Zc 0] (Work.ELNest.Dlev L 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnestA, hnestB, hnestC⟩ := armAngle_facts
  obtain ⟨hcA1, hcA2, hcB1, hcB2, hcC1, hcC2⟩ := DnestCl.inArc_levelOne
  have hnd := arm_arcLen_ne d N
  have hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [N.Za n, N.Zb n, N.Zc n] :=
    fun n => D_adm_of' d N T n
  have hD : ∀ n : ℕ, Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n)
      = Work.EL.pairSideNear (N.Za n) ∩ Work.EL.pairSideNear (N.Zb n)
        ∩ Work.EL.pairSideNear (N.Zc n)
        ∩ {z : ℂ | Work.EL.pot d.hN z < Real.log (Work.ELNest.Dlev L n)} :=
    fun n => Dmem_of d N hL hadm hnd.1 hnd.2.1 hnd.2.2 n
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  have hsideA : Work.EL.pairSideNear (N.Za 1) ⊆ Work.EL.pairSideNear (N.Za 0) :=
    nest_side_of_nearArc d.hN hJ (N.Za 1) (N.Za 0)
      (fun θ hθ => by
        rw [N.Zab 1, N.Zaa 1] at hθ
        rw [N.Zab 0, N.Zaa 0]
        exact hnestA 0 θ hθ)
      (Za_succ_curve_disjoint d N 0)
  have hsideB : Work.EL.pairSideNear (N.Zb 1) ⊆ Work.EL.pairSideNear (N.Zb 0) :=
    nest_side_of_nearArc d.hN hJ (N.Zb 1) (N.Zb 0)
      (fun θ hθ => by
        rw [N.Zbb 1, N.Zba 1] at hθ
        rw [N.Zbb 0, N.Zba 0]
        exact hnestB 0 θ hθ)
      (Zb_succ_curve_disjoint d N 0)
  have hsideC : Work.EL.pairSideNear (N.Zc 1) ⊆ Work.EL.pairSideNear (N.Zc 0) :=
    nest_side_of_nearArc d.hN hJ (N.Zc 1) (N.Zc 0)
      (fun θ hθ => by
        rw [N.Zcb 1, N.Zca 1] at hθ
        rw [N.Zcb 0, N.Zca 0]
        exact hnestC 0 θ hθ)
      (Zc_succ_curve_disjoint d N 0)
  intro z hz
  rw [hD 0]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · have hcl : z ∈ closure (Work.EL.pairSideNear (N.Za 1)) :=
      closure_mono (fun w hw => by rw [hD 1] at hw; exact hw.1.1.1) hz
    rcases DnestCl.closure_pairSideNear_subset d.hN hJ (N.Za 1) (hnd.1 1) hcl with h | h
    · exact hsideA h
    · refine DnestCl.pairCurve_subset_pairSideNear_of_InArc d.hN hJ (N.Za 0) (N.Za 1) ?_ ?_ ?_ h
      · rw [N.Zaa 1, N.Zab 0, N.Zaa 0]; exact hcA1
      · rw [N.Zab 1, N.Zab 0, N.Zaa 0]; exact hcA2
      · exact Za_succ_y_ne d N 0
  · have hcl : z ∈ closure (Work.EL.pairSideNear (N.Zb 1)) :=
      closure_mono (fun w hw => by rw [hD 1] at hw; exact hw.1.1.2) hz
    rcases DnestCl.closure_pairSideNear_subset d.hN hJ (N.Zb 1) (hnd.2.1 1) hcl with h | h
    · exact hsideB h
    · refine DnestCl.pairCurve_subset_pairSideNear_of_InArc d.hN hJ (N.Zb 0) (N.Zb 1) ?_ ?_ ?_ h
      · rw [N.Zba 1, N.Zbb 0, N.Zba 0]; exact hcB1
      · rw [N.Zbb 1, N.Zbb 0, N.Zba 0]; exact hcB2
      · exact Zb_succ_y_ne d N 0
  · have hcl : z ∈ closure (Work.EL.pairSideNear (N.Zc 1)) :=
      closure_mono (fun w hw => by rw [hD 1] at hw; exact hw.1.2) hz
    rcases DnestCl.closure_pairSideNear_subset d.hN hJ (N.Zc 1) (hnd.2.2 1) hcl with h | h
    · exact hsideC h
    · refine DnestCl.pairCurve_subset_pairSideNear_of_InArc d.hN hJ (N.Zc 0) (N.Zc 1) ?_ ?_ ?_ h
      · rw [N.Zca 1, N.Zcb 0, N.Zca 0]; exact hcC1
      · rw [N.Zcb 1, N.Zcb 0, N.Zca 0]; exact hcC2
      · exact Zc_succ_y_ne d N 0
  · have hpotle : Work.EL.pot d.hN z ≤ Real.log (Work.ELNest.Dlev L 1) :=
      closure_minimal (fun w hw => by
        rw [hD 1] at hw
        have : Work.EL.pot d.hN w < Real.log (Work.ELNest.Dlev L 1) := hw.2
        exact le_of_lt this)
        (isClosed_le d.hN.continuous_potential continuous_const) hz
    have hlt : Real.log (Work.ELNest.Dlev L 1) < Real.log (Work.ELNest.Dlev L 0) :=
      Real.log_lt_log (Real.rpow_pos_of_pos (lt_trans zero_lt_one hL) _)
        (DnestCl.dlev_one_lt_zero hL)
    exact lt_of_le_of_lt hpotle hlt

end Work.ELAssembly
