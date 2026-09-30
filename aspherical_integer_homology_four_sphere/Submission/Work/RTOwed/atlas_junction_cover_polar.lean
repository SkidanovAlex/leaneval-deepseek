/-
# The junction charts cover the inner polar layer (source form)

This file proves `Work.RTOwed.atlas_junction_cover_polar`: there is a *finite* family of junction
charts whose **sources** cover the inner polar layer `1/24 < ‖p‖∞ < 1/2` of every filling piece.

It is the *source* form of `Work.RTOwed.jPolar_cover_fin`: that theorem produces a finite family of
junction pins `JPin` such that the coordinate inclusion `jCoordM` of the box of a pin hits the image
of the point `a.incW v q`; here we need the sharper statement that `a.incW v q` lies in the *source*
of the junction chart `jChart a D v P` itself, i.e. that the point of the box pinning it has radial
coordinate below the cut `rCut` of `Work.RTOwed.jBoxR`.

The proof follows `jPolar_cover_fin` line by line; the only difference is that the witness
`q = ThetaPolarS v c pe y0'` produced at a point of layer parameter `‖p‖∞ < 1/2` has radial
coordinate `q 0 = 2 r_J ‖p‖∞ < r_J = 3 < rCut = 61/20`, so it lies in `jBoxR` and hence

  `a.incW v (p,y) ∈ (jChart a D v P).source`

by `Work.RTOwed.jChart_source`.
-/
import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.jPolar_cover_fin

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped RealInnerProductSpace Real

namespace Work.RTOwed

open Work.Cusp

/-! ### The projection of the source of a junction chart -/

/-- **The coordinate inclusion of a radial box point lies in the source of the junction chart.**  If
`q` is a point of the box of the pin `P` whose polar radius `q 0` is below the cut `rCut` (i.e. `q`
lies in `jBoxR a v P`), then `jCoordM` of `q` lies in the source of `jChart a D v P`. -/
theorem mem_jChart_source_of_coordM_rad (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v)
    (q : {q : E4 // q ∈ jBox v P.cU P.k P.W P.kx P.δ})
    (hq : (q : E4) ∈ jBoxR a v P) :
    jCoordM a v (D v) P.cU P.k P.W P.kx P.δ q ∈ (jChart a D v P).source := by
  rw [jChart_source]
  exact ⟨q, hq, rfl⟩

/-! ### The strengthened bundle at a point of the slice -/

/-- The data attached to a point of the slice `{‖p‖∞ = 1/4} × (ℝ/ℤ)²`: the pin, and the two
neighbourhoods (of the direction in the filling square and of the torus coordinate) whose points are
covered by the **source** of the junction chart of the pin.  This is `JBund` with the stronger
`hcov`. -/
structure JBundPolar (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) where
  /-- The pin. -/
  P : JPin a v
  /-- The neighbourhood of the direction `bnd z.1`, inside the wedge of the pin. -/
  Up : Set E2
  /-- The neighbourhood of the torus coordinate `z.2`. -/
  V : Set JTor
  hUp : IsOpen Up
  hbnd : bnd (z.1.1 : E2) ∈ Up
  hV : IsOpen V
  hzV : z.2 ∈ V
  /-- Everything whose direction lies in `Up` and whose torus coordinate lies in `V` is covered, at
  every layer parameter of the inner polar layer, by the **source** of the junction chart of the
  pin. -/
  hcov : ∀ (q : Work.Space.SquarePt × a.Torus v),
    1/24 < nrm (q.1 : E2) → nrm (q.1 : E2) < 1/2 →
    bnd (q.1 : E2) ∈ Up → (D v).tor q.2 ∈ V →
    a.incW v q ∈ (jChart a D v P).source

/-- **The pointwise construction.**  Every point of the slice has a pin and neighbourhoods as in
`JBundPolar`.  This is the proof of `Work.RTOwed.jBund_nonempty` with the radial bound
`q 0 = 2 r_J ‖p‖∞ < r_J < rCut` added, so that the coordinate inclusion lands in `jChart.source` and
not merely in `jCoordM '' univ`. -/
theorem jBundPolar_nonempty (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) : Nonempty (JBundPolar a D v z) := by
  classical
  obtain ⟨p0s, Dv⟩ := z
  set p0e : E2 := (p0s.1 : E2) with hp0e
  have hnrm0 : nrm p0e = jR0 := p0s.2
  have hp0pos : 0 < nrm p0e := by rw [hnrm0]; exact jR0_pos
  have hp0ne : p0e ≠ 0 := by intro h; rw [h] at hp0pos; simp [nrm] at hp0pos
  obtain ⟨c, k, hc, hwk⟩ := jwedge_data hp0pos
  obtain ⟨y0, hy0⟩ := jlift_exists Dv
  obtain ⟨W, hW, hWy0, hsec⟩ := exists_section_box v y0
  set kx : E3 := xOf (polarToUHS v (ThetaPolarS v c p0e y0)) with hkx
  have hd0mem : bnd p0e ∈ wedgeS c k := (jwedgeS_cone c k hp0ne).mpr hwk
  obtain ⟨δ1, hδ1pos, hδ1⟩ := jexists_ball_uS c k hd0mem (jEtaU_pos v)
  set Up : Set E2 := wedgeS c k ∩ Metric.ball (bnd p0e) δ1 with hUp
  set V : Set JTor := {Dv' : JTor | ∃ y0' : E2,
      (∀ i, (y0' i : AddCircle (1:ℝ)) = Dv' i) ∧ wOf v y0' ∈ W ∧ ‖y0' - y0‖ < jEtaY v}
    with hV
  set P : JPin a v := ⟨c, k, W, kx, 1/2, by norm_num, hW, hsec⟩ with hP
  refine ⟨⟨P, Up, V, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hUp]; exact (isOpen_wedgeS c k).inter Metric.isOpen_ball
  · rw [hUp]
    exact ⟨hd0mem, by rw [Metric.mem_ball, dist_self]; exact hδ1pos⟩
  · rw [hV]; exact jisOpen_liftSet v y0 W hW (jEtaY v)
  · rw [hV]
    exact ⟨y0, hy0, hWy0, by rw [sub_self, norm_zero]; exact jEtaY_pos v⟩
  · rintro ⟨p, y⟩ hn1 hn2 hb hVy
    rw [hUp] at hb
    rw [hV] at hVy
    obtain ⟨y0', hy0', hWy0', hdy'⟩ := hVy
    set pe : E2 := (p : E2) with hpe
    have hpe_gt : (1/24 : ℝ) < nrm pe := hn1
    have hpe_lt : nrm pe < 1/2 := hn2
    have hpe_pos : 0 < nrm pe := lt_trans (by norm_num) hpe_gt
    have hpene : pe ≠ 0 := by intro h; rw [h] at hpe_pos; simp [nrm] at hpe_pos
    have hdir : pe ∈ wedgeS c k := (jwedgeS_cone c k hpene).mp hb.1
    set q : E4 := ThetaPolarS v c pe y0' with hq
    have hq0 : q 0 = radial v pe y0' := by rw [hq]; simp [ThetaPolarS]
    have hrad : radial v pe y0' = 2 * rJ * nrm pe := radial_eq_inner v pe y0' (le_of_lt hpe_lt)
    have hq23 : (!₂[q 2, q 3] : E2) = wOf v y0' := by
      rw [hq]; ext i; fin_cases i <;> simp [ThetaPolarS]
    have huq : uqOf v q = uS c pe := by rw [hq]; exact uqOf_ThetaPolarS v c pe y0'
    have hci : cuspInvInner v q = (pe, y0') := by
      rw [hq]; exact cuspInvInner_ThetaPolarS v c pe y0'
    have hqmem : q ∈ jBox v c k W kx (1/2) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq0, hrad, rJ]; linarith
      · rw [hq0, hrad, rJ, rBig]; linarith
      · rw [hq23]; exact hWy0'
      · rw [huq, uS]
        have h1 : c + Int.fract (u pe - c) - c = Int.fract (u pe - c) := by ring
        rw [h1]
        exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      · rw [huq, uS]
        have h1 : c + Int.fract (u pe - c) - c = Int.fract (u pe - c) := by ring
        rw [h1, Int.fract_eq_self.mpr ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩]
        exact hdir.2
      · intro i
        have ha : |uS c pe - uS c p0e| < jEtaU v := by
          have h1 : uS c pe = uS c (bnd pe) := (juS_bnd c hpene).symm
          have h2 : uS c p0e = uS c (bnd p0e) := (juS_bnd c hp0ne).symm
          rw [h1, h2]
          exact hδ1 (bnd pe) hb.1 (by simpa [Metric.mem_ball, dist_eq_norm] using hb.2)
        have hkey := jcuspX_coord_lt v i ha hdy'
        rw [hq, jxOf_polarToUHS_ThetaPolarS v c pe y0', hkx,
          jxOf_polarToUHS_ThetaPolarS v c p0e y0]
        simpa only [PiLp.sub_apply] using hkey
    have hq0le : q 0 ≤ rJ := by rw [hq0, hrad, rJ]; linarith
    -- the new radial bound: `q 0 = 2 r_J ‖p‖∞ < r_J < rCut`
    have hq0lt : (q : E4) ∈ jBoxR a v P := by
      refine ⟨hqmem, ?_⟩
      simp only [Set.mem_ofPred_eq]
      rw [hq0, hrad, rCut, rJ]
      linarith
    have hcoord : jCoordM a v (D v) c k W kx (1/2) ⟨q, hqmem⟩ = a.incW v (p, y) := by
      rw [jCoordM, dif_pos hq0le]
      congr 1
      refine Prod.ext ?_ ?_
      · refine Subtype.ext ?_
        have h1 : (cuspInvInner v q).1 = pe := congrArg Prod.fst hci
        rw [hpe] at h1
        exact h1
      · have h2 : (cuspInvInner v q).2 = y0' := congrArg Prod.snd hci
        rw [h2]
        have hfun : (fun i : Fin 2 => (((y0' i : ℝ)) : AddCircle (1:ℝ))) = (D v).tor y :=
          funext hy0'
        rw [hfun, Homeomorph.symm_apply_apply]
    have hsrc := mem_jChart_source_of_coordM_rad a D v P ⟨q, hqmem⟩ hq0lt
    rwa [hcoord] at hsrc

/-- The chosen bundle at a point of the slice. -/
noncomputable def jbPOf (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) : JBundPolar a D v z :=
  Classical.choice (jBundPolar_nonempty a D v z)

/-- The neighbourhood of a point of the slice, in the slice. -/
def jUzP (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) : Set (JSlice × JTor) :=
  {z' | bnd (z'.1.1 : E2) ∈ (jbPOf a D v z).Up ∧ z'.2 ∈ (jbPOf a D v z).V}

theorem jUzP_isOpen (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) : IsOpen (jUzP a D v z) := by
  have hbndc : Continuous (fun z' : JSlice × JTor => bnd (z'.1.1 : E2)) := by
    have hc : Continuous (fun z' : JSlice × JTor => ((z'.1.1 : E2))) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    have hEq : (fun z' : JSlice × JTor => bnd (z'.1.1 : E2))
        = fun z' => (jR0)⁻¹ • ((z'.1.1 : E2)) := by
      funext z'
      have hn : nrm (z'.1.1 : E2) = jR0 := z'.1.2
      rw [bnd, hn]
    rw [hEq]; exact hc.const_smul ((jR0)⁻¹)
  exact ((jbPOf a D v z).hUp.preimage hbndc).inter ((jbPOf a D v z).hV.preimage continuous_snd)

theorem jUzP_self (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (z : JSlice × JTor) : z ∈ jUzP a D v z :=
  ⟨(jbPOf a D v z).hbnd, (jbPOf a D v z).hzV⟩

/-! ### The finite subcover -/

/-- **The inner polar layer of every cusp is covered by the sources of finitely many junction
charts.** -/
theorem atlas_junction_cover_polar (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v) :
    ∃ (N : ℕ) (par : Fin N → Σ v : Work.Space.Cusp, Work.RTOwed.JPin a v),
      ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
        q ∈ Work.Cusp.polarLayer (a.Torus v) → Work.Cusp.nrm (q.1 : Work.Cusp.E2) < 1/2 →
        ∃ i, (par i).1 = v ∧ a.incW v q ∈
          (Work.RTOwed.jChart a D (par i).1 (par i).2).source := by
  classical
  have hcover : ∀ v : Work.Space.Cusp, ∃ t : Finset (JSlice × JTor),
      (Set.univ : Set (JSlice × JTor)) ⊆ ⋃ z ∈ t, jUzP a D v z := by
    intro v
    exact IsCompact.elim_finite_subcover isCompact_univ (jUzP a D v)
      (fun z => jUzP_isOpen a D v z)
      (fun z _ => Set.mem_iUnion.mpr ⟨z, jUzP_self a D v z⟩)
  choose t ht using hcover
  let S : Finset (Σ v : Work.Space.Cusp, JPin a v) :=
    Finset.univ.biUnion (fun v => (t v).image (fun z => ⟨v, (jbPOf a D v z).P⟩))
  refine ⟨S.card, fun i => (S.equivFin.symm i).1, ?_⟩
  intro v q h1 h2
  set pe : E2 := (q.1 : E2) with hpe
  have hn1 : (1/24 : ℝ) < nrm pe := h1
  have hn2 : nrm pe < 1/2 := h2
  have hpe_pos : 0 < nrm pe := lt_trans (by norm_num) hn1
  have hpene : pe ≠ 0 := by intro h; rw [h] at hpe_pos; simp [nrm] at hpe_pos
  let p0 : JSlice :=
    ⟨⟨jR0 • bnd pe, jmem_Sq_smul_bnd jR0_pos jR0_le_one hpene⟩,
      jnrm_smul_bnd jR0_pos hpene⟩
  let z0 : JSlice × JTor := (p0, (D v).tor q.2)
  have hz0mem : z0 ∈ ⋃ z ∈ t v, jUzP a D v z := ht v (Set.mem_univ z0)
  obtain ⟨zi, hzi_t, hzi⟩ := Set.mem_iUnion₂.mp hz0mem
  have hzi_t' : zi ∈ t v := Finset.mem_coe.mp hzi_t
  have hbndUp : bnd pe ∈ (jbPOf a D v zi).Up := by
    have h := hzi.1
    have hb : bnd (z0.1.1 : E2) = bnd pe := by
      show bnd (jR0 • bnd pe) = bnd pe
      exact jbnd_smul_bnd jR0_pos hpene
    rwa [hb] at h
  have hVy : (D v).tor q.2 ∈ (jbPOf a D v zi).V := hzi.2
  have hcov := (jbPOf a D v zi).hcov q hn1 hn2 hbndUp hVy
  have hmemS : (⟨v, (jbPOf a D v zi).P⟩ : Σ v : Work.Space.Cusp, JPin a v) ∈ S := by
    rw [show S = Finset.univ.biUnion
      (fun v => (t v).image (fun z => ⟨v, (jbPOf a D v z).P⟩)) from rfl]
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v,
      Finset.mem_image.mpr ⟨zi, hzi_t', rfl⟩⟩
  refine ⟨S.equivFin ⟨⟨v, (jbPOf a D v zi).P⟩, hmemS⟩, ?_, ?_⟩
  · show (((S.equivFin.symm (S.equivFin ⟨⟨v, (jbPOf a D v zi).P⟩, hmemS⟩)).1 :
        Σ v : Work.Space.Cusp, JPin a v)).1 = v
    rw [Equiv.symm_apply_apply]
  · simp only []
    rw [Equiv.symm_apply_apply]
    exact hcov

end Work.RTOwed
