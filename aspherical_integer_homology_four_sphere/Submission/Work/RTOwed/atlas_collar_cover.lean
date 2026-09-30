import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.Cusp.collarLayer_subset_range_cuspCoordMTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Set Topology Function

/-!
# The collar charts of the filling atlas cover the collar layer of `M̂`

`Work.Cusp.collarLayer_subset_range_cuspCoordMTop` shows that every point of the collar layer
(`½ ≤ ‖p‖∞`) of a filling piece lies in the range of the collar coordinate inclusion
`Work.Cusp.cuspCoordMTop a v D c δ` for a *suitable* box `(c,δ)` — the box depends on the point.
The collar chart `Work.RTOwed.cChart` of the filling atlas however has the box cut at the junction
height `s_J` (`Work.RTOwed.cBoxR`), and the atlas used by the assembly only contains **finitely
many** charts.

This file supplies the finite family.  The mechanism is compactness: the cusp coordinate of a
filling point with layer parameter `t = ‖p‖∞` and torus coordinates `y` is

  `cuspX v u y = u σ_v + y₂λ₂ + y₃λ₃`,

and the range of `(u,y) ↦ cuspX v u y` over `[0,1] × Sq` (the perimeter parameter `u = u(p)` lies
in `[0,1)`, and the torus coordinates can be lifted to the fixed fundamental square `Sq = [-1,1]²`)
is compact, hence covered by finitely many boxes of side `1` (i.e. `δ = 1/2`).  Any such box which
contains the cusp coordinate `x` of the point also contains the lift `Θ_v(p,y) = (x, collarS)`,
which is a point of the collar source *strictly below* the junction `s_J` as soon as `‖p‖∞ > 1/2`
(the collar height is strictly antitone in the layer parameter, `collarHeight (1/2) b = s_J`).

That last inequality is the reason for the threshold `51/100 > 1/2` of the statement: it is what
puts the witness in `cBoxR`, i.e. in the source of the cut collar chart `cChart`.
-/

/-- Every point of the standard torus `(ℝ/ℤ)²` has a lift in the fundamental square `Sq = [-1,1]²`
(the *bounded* fundamental domain, which is what makes the compactness argument below finite). -/
theorem exists_lift_sq_RTO (t : Fin 2 → AddCircle (1 : ℝ)) :
    ∃ y : Work.Cusp.E2, y ∈ Work.Cusp.Sq ∧
      ∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = t i := by
  have h : ∀ i : Fin 2, ∃ s : ℝ, (s : AddCircle (1 : ℝ)) = t i :=
    fun i => QuotientAddGroup.mk'_surjective _ _
  choose s hs using h
  refine ⟨!₂[Int.fract (s 0), Int.fract (s 1)], ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show |Int.fract (s 0)| ≤ 1
      rw [abs_of_nonneg (Int.fract_nonneg (s 0))]; linarith [Int.fract_lt_one (s 0)]
    · show |Int.fract (s 1)| ≤ 1
      rw [abs_of_nonneg (Int.fract_nonneg (s 1))]; linarith [Int.fract_lt_one (s 1)]
  · intro i
    fin_cases i <;> simpa using (AddCircle.coe_fract (s _)).trans (hs _)

/-- **Finitely many boxes of side `1` cover the possible cusp coordinates of a filling point.**
For the `v`-th cusp there is a finite set `F` of centres of `E3` such that for every perimeter
parameter `u ∈ [0,1)` and every `y ∈ Sq` the cusp coordinate `cuspX v u y` lies within `1/2` (in
every coordinate) of some centre of `F`. -/
theorem exists_finset_cuspX_cover (v : Work.Space.Cusp) :
    ∃ F : Finset Work.Cusp.E3, ∀ (u : ℝ) (w : Work.Cusp.E2), 0 ≤ u → u < 1 → w ∈ Work.Cusp.Sq →
      ∃ c ∈ F, ∀ i, |(Work.Cusp.cuspX v u w) i - c i| < (1/2 : ℝ) := by
  have hK : IsCompact ((fun z : ℝ × Work.Cusp.E2 => Work.Cusp.cuspX v z.1 z.2) ''
      (Set.Icc 0 1 ×ˢ Work.Cusp.Sq)) := by
    refine IsCompact.image ?_ (Work.Cusp.continuous_cuspX v)
    exact isCompact_Icc.prod Work.Space.isCompact_sq
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover
    (fun c : Work.Cusp.E3 => {x : Work.Cusp.E3 | ∀ i, |x i - c i| < (1/2 : ℝ)})
    (fun c => by
      rw [show {x : Work.Cusp.E3 | ∀ i, |x i - c i| < (1/2:ℝ)}
          = ⋂ i : Fin 3, {x : Work.Cusp.E3 | |x i - c i| < (1/2:ℝ)} from by ext x; simp]
      refine isOpen_iInter_of_finite (fun i => ?_)
      refine isOpen_lt (continuous_abs.comp ?_) continuous_const
      exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i)).sub continuous_const)
    (by
      rintro x ⟨z, hz, rfl⟩
      exact Set.mem_iUnion.mpr ⟨_, by
        intro i
        rw [sub_self, abs_zero]
        norm_num⟩)
  refine ⟨F, fun u w h0 h1 hw => ?_⟩
  have hz : (u, w) ∈ Set.Icc (0:ℝ) 1 ×ˢ Work.Cusp.Sq := ⟨⟨h0, le_of_lt h1⟩, hw⟩
  have hx := hF ⟨(u, w), hz, rfl⟩
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨c, hcF, hc⟩ := hx
  exact ⟨c, hcF, hc⟩

/-- **A collar point lies in the source of the collar chart of any box that contains its cusp
coordinate.**  If `(c,1/2)` is a box containing the cusp coordinate `x = cuspX v (u p) y` of a
collar point `(p,y)` with layer parameter `> 1/2`, then the image `a.incW v (p, y₀)` of the filling
point under the assembly is in the image of the collar coordinate inclusion `cuspCoordMTop` of
that box, restricted to the part of the box cut at the junction height (`cBoxR`). -/
theorem incW_mem_cuspCoordMTop_image (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (p : Work.Space.SquarePt) (y0 : a.Torus v) (y : Work.Cusp.E2)
    (hp : 1/2 ≤ Work.Cusp.nrm (p : Work.Cusp.E2))
    (hgt : 1/2 < Work.Cusp.nrm (p : Work.Cusp.E2))
    (hy : ∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = (D v).tor y0 i)
    (c : Work.Cusp.E3)
    (hc : ∀ i, |(Work.Cusp.cuspX v (Work.Cusp.u (p : Work.Cusp.E2)) y) i - c i| < 1/2) :
    a.incW v (p, y0) ∈ Work.Cusp.cuspCoordMTop a v (D v) c (1/2) ''
      {q : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c (1/2)} |
        (q : Work.Cusp.E4) ∈ Work.RTOwed.cBoxR v c (1/2)} := by
  have hle1 : Work.Cusp.nrm (p : Work.Cusp.E2) ≤ 1 := Work.Space.sqNorm_le_one p
  have hpSq : (p : Work.Cusp.E2) ∈ Work.Cusp.Sq := p.2
  set q : Work.Cusp.E4 := Work.Cusp.ThetaOuter v (p : Work.Cusp.E2) y with hqdef
  have hx : Work.Cusp.xOf q = Work.Cusp.cuspX v (Work.Cusp.u (p : Work.Cusp.E2)) y := by
    rw [hqdef]; ext i; fin_cases i <;> simp [Work.Cusp.ThetaOuter, Work.Cusp.xOf]
  have hq3 : q 3 = Work.Cusp.collarS v (p : Work.Cusp.E2) y := by
    rw [hqdef]; simp [Work.Cusp.ThetaOuter]
  have hb0 : 0 < Work.Cusp.beta (Work.Cusp.cuspX v (Work.Cusp.u (p : Work.Cusp.E2)) y) :=
    Work.Cusp.beta_pos _
  have hb1 : Work.Cusp.beta (Work.Cusp.cuspX v (Work.Cusp.u (p : Work.Cusp.E2)) y) < Work.Cusp.sJ :=
    lt_of_le_of_lt (Work.Cusp.beta_le_max _) Work.Cusp.betaMax_lt_sJ
  have hcm := Work.Cusp.collarHeight_mem (Work.Cusp.nrm (p : Work.Cusp.E2))
    (Work.Cusp.beta (Work.Cusp.cuspX v (Work.Cusp.u (p : Work.Cusp.E2)) y)) hp hle1
    (Work.Cusp.beta_min_le _) (Work.Cusp.beta_le_max _)
  have hmem : q ∈ Work.Cusp.cuspBoxTop v c (1/2) := by
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [hx]; exact hc i
    · rw [hq3, Work.Cusp.collarS]; exact hcm.1
    · rw [hq3, Work.Cusp.collarS]; exact lt_of_le_of_lt hcm.2 Work.Cusp.sJ_lt_sTop
  have hR : q ∈ Work.RTOwed.cBoxR v c (1/2) := by
    refine ⟨hmem, ?_⟩
    show q 3 < Work.Cusp.sJ
    rw [hq3, Work.Cusp.collarS]
    have h := Work.Cusp.collarHeight_strictAntiOn
      (Work.Cusp.beta (Work.Cusp.cuspX v (Work.Cusp.u (p : Work.Cusp.E2)) y)) hb0 hb1
      (Set.mem_univ (1/2)) (Set.mem_univ (Work.Cusp.nrm (p : Work.Cusp.E2))) hgt
    beta_reduce at h
    rwa [Work.Cusp.collarHeight_half] at h
  have hbc : Work.Cusp.beta (Work.Cusp.xOf q) ≤ q 3 := by
    rw [hx, hq3, Work.Cusp.collarS]
    rcases lt_or_eq_of_le hle1 with hlt | heq
    · have h := Work.Cusp.collarHeight_strictAntiOn _ hb0 hb1
        (Set.mem_univ (Work.Cusp.nrm (p : Work.Cusp.E2))) (Set.mem_univ (1:ℝ)) hlt
      beta_reduce at h
      rw [Work.Cusp.collarHeight_one _ hb0] at h
      exact le_of_lt h
    · rw [heq, Work.Cusp.collarHeight_one _ hb0]
  have hio : Work.Cusp.cuspInvOuter v q = ((p : Work.Cusp.E2), y) := by
    rw [hqdef]
    exact Work.Cusp.cuspInvOuter_ThetaOuter_half v (p : Work.Cusp.E2) y hpSq hp hle1
  refine ⟨⟨q, hmem⟩, hR, ?_⟩
  show Work.Cusp.cuspCoordMTop a v (D v) c (1/2) ⟨q, hmem⟩ = a.incW v (p, y0)
  unfold Work.Cusp.cuspCoordMTop
  rw [dif_neg (not_lt.mpr hbc)]
  refine congrArg (a.incW v) ?_
  apply Prod.ext
  · have h1 : (Work.Cusp.cuspInvOuter v q).1 = (p : Work.Cusp.E2) := congrArg Prod.fst hio
    exact Subtype.ext (by simpa using h1)
  · show (D v).tor.symm (fun i => (((Work.Cusp.cuspInvOuter v q).2 i : ℝ) : AddCircle (1:ℝ))) = y0
    have h2 : (fun i : Fin 2 => (((Work.Cusp.cuspInvOuter v q).2 i : ℝ) : AddCircle (1:ℝ)))
        = (D v).tor y0 := by
      funext i
      rw [show (Work.Cusp.cuspInvOuter v q).2 = y from congrArg Prod.snd hio]
      exact hy i
    rw [h2, Homeomorph.symm_apply_apply]

/-- **The collar layer of every filling piece is covered by finitely many collar charts of the
atlas.**  The family consists of the boxes `(c, 1/2)` with centres `c` running over the finite
covering sets of `exists_finset_cuspX_cover`, one for each cusp; the witness is the lift
`Θ_v(p,y) = (cuspX v (u p) y, collarS v p y)`, which lies in the box and strictly below the
junction because the layer parameter of a point of the collar layer with `nrm > 51/100` is `> 1/2`.
-/
theorem atlas_collar_cover (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v) :
    ∃ (N : ℕ) (par : Fin N → Σ v : Work.Space.Cusp, (Work.Cusp.E3 × ℝ))
      (hδ : ∀ i, (par i).2.2 ≤ 1/2)
      (hne : ∀ i, Nonempty {q : Work.Cusp.E4 //
        q ∈ Work.Cusp.cuspBoxTop (par i).1 (par i).2.1 (par i).2.2}),
      ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
        q ∈ Work.Cusp.collarLayer (a.Torus v) → Work.Cusp.nrm (q.1 : Work.Cusp.E2) > 51/100 →
        ∃ i, (par i).1 = v ∧ a.incW v q ∈
          (Work.RTOwed.cChart a D (par i).1 (par i).2.1 (par i).2.2 (hδ i) (hne i)).source := by
  classical
  choose F hF using fun v => exists_finset_cuspX_cover v
  let ι := Σ v : Work.Space.Cusp, {c : Work.Cusp.E3 // c ∈ F v}
  haveI : Fintype ι := inferInstance
  let par : Fin (Fintype.card ι) → Σ v : Work.Space.Cusp, (Work.Cusp.E3 × ℝ) :=
    fun i => let x := (Fintype.equivFin ι).symm i
             ⟨x.1, ((x.2 : {c : Work.Cusp.E3 // c ∈ F x.1}).1, 1/2)⟩
  let hδF : ∀ i, (par i).2.2 ≤ 1/2 := fun _ => le_refl (1/2)
  let hneF : ∀ i, Nonempty {q : Work.Cusp.E4 //
      q ∈ Work.Cusp.cuspBoxTop (par i).1 (par i).2.1 (par i).2.2} :=
    fun i => ⟨⟨Work.Cusp.mkE4 (par i).2.1 (3/2), by
      refine ⟨fun j => ?_, ?_, ?_⟩
      · rw [Work.Cusp.xOf_mkE4, sub_self, abs_zero]; norm_num
      · norm_num [Work.Cusp.s1]
      · norm_num [Work.Cusp.sTop]⟩⟩
  refine ⟨Fintype.card ι, par, hδF, hneF, ?_⟩
  intro v q hq hgt
  obtain ⟨y, hySq, hy⟩ := exists_lift_sq_RTO ((D v).tor q.2)
  obtain ⟨c, hcF, hcc⟩ := hF v (Work.Cusp.u (q.1 : Work.Cusp.E2)) y
    (Work.Cusp.u_mem_univ _).1 (Work.Cusp.u_mem_univ _).2 hySq
  let x : ι := ⟨v, ⟨c, hcF⟩⟩
  refine ⟨Fintype.equivFin ι x, ?_, ?_⟩
  · show ((Fintype.equivFin ι).symm (Fintype.equivFin ι x)).1 = v
    rw [Equiv.symm_apply_apply]
  · have hpar1 : (par (Fintype.equivFin ι x)).1 = v := by
      show ((Fintype.equivFin ι).symm (Fintype.equivFin ι x)).1 = v
      rw [Equiv.symm_apply_apply]
    have hpar2a : (par (Fintype.equivFin ι x)).2.1 = c := by
      show (((Fintype.equivFin ι).symm (Fintype.equivFin ι x)).2 :
              {c : Work.Cusp.E3 // c ∈ F ((Fintype.equivFin ι).symm (Fintype.equivFin ι x)).1}).1 = c
      rw [Equiv.symm_apply_apply]
    have hpar2b : (par (Fintype.equivFin ι x)).2.2 = 1/2 := rfl
    have hsrc := Work.RTOwed.cChart_source a D (par (Fintype.equivFin ι x)).1
      (par (Fintype.equivFin ι x)).2.1 (par (Fintype.equivFin ι x)).2.2
      (hδF (Fintype.equivFin ι x)) (hneF (Fintype.equivFin ι x))
    rw [hsrc, hpar1, hpar2a, hpar2b]
    exact incW_mem_cuspCoordMTop_image a D v q.1 q.2 y
      (by linarith) (by linarith) hy c hcc

end Work.RTOwed
