/-
# `BridgeSquare/SlabCore.lean` — the chart machinery of the sheared slab

This module contains the *domain calculus* of the slab used by the wall computation of
`Work.BridgeSquare.slabWall_exists`: the affineness of the cube chart `kleinPt`, the ceiling map
`mbarPt_halfopen` on a half-open cube, the chart identity `cSimp_eq_chiRep`/`cSimp_eq_chiRep'`
(a slab triangle that lies in a cube and matches the polytope positions of a flag has chart chain
the characteristic map of that flag), and the translation invariance `slabChain_translate_sub` of
the slab pushforward under cusp-lattice translations.  The target `slabWall_exists` itself lives in
`BridgeSquare/slabWall_exists.lean`, which imports this module and the wall/collar construction of
`BridgeSquare/SlabBuild/`.

It is the *independent* copy of these lemmas: `BridgeSquare/slabWall_exists.lean` re-exports it,
and `WallCollar/Charts*.lean` (which import `slabWall_exists`) get their inputs from here.
-/
import Mathlib
import Submission.Work.BridgeSquare.PlaneSlab
import Submission.Work.BridgeSquare.PlaneSlabBot
import Submission.Work.BridgeSquare.PsiM
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range
import Submission.Work.BridgeSquare.FibreData
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.BridgeSquare.kleinPt_corner
import Submission.Work.BridgeSquare.PlaneAff
import Submission.Work.RTOwed.cubeOf_halfopen
import Submission.Work.RTOwed.cuspCert.cube_quad
import Submission.Work.RTOwed.cuspCert.CuspSupport
import Submission.Work.BridgeSquare.denseSimplex3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BridgeSquare
open Work.RTOwed
open Convexity

noncomputable section

/-! ## §1  The cube chart is affine -/

/-- The linear part of the cube chart `kleinPt a`. -/
def kleinLin (a : Fin 48) : CuspE3 →ₗ[ℝ] CuspE4 where
  toFun x := WithLp.toLp 2 fun i => ∑ j, ((Work.Cusp.cubeXToKlein a) i j : ℝ) * x j
  map_add' x y := by
    apply PiLp.ext
    intro i
    simp only [WithLp.ofLp_toLp, WithLp.ofLp_add, Pi.add_apply]
    rw [show (∑ j : Fin 3, ((Work.Cusp.cubeXToKlein a) i j : ℝ) * (x.ofLp j + y.ofLp j))
        = ∑ j : Fin 3, (((Work.Cusp.cubeXToKlein a) i j : ℝ) * x.ofLp j
            + ((Work.Cusp.cubeXToKlein a) i j : ℝ) * y.ofLp j) from
        Finset.sum_congr rfl (fun j _ => by ring)]
    rw [Finset.sum_add_distrib]
  map_smul' c x := by
    apply PiLp.ext
    intro i
    simp only [WithLp.ofLp_toLp, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (∑ j : Fin 3, ((Work.Cusp.cubeXToKlein a) i j : ℝ) * (c * x.ofLp j))
        = ∑ j : Fin 3, c * (((Work.Cusp.cubeXToKlein a) i j : ℝ) * x.ofLp j) from
        Finset.sum_congr rfl (fun j _ => by ring)]
    rw [Finset.mul_sum]

/-- The constant part of the cube chart `kleinPt a`. -/
def kleinConst (a : Fin 48) : CuspE4 :=
  WithLp.toLp 2 fun i => ((Work.Cusp.cubeXToKleinb a) i : ℝ)

theorem kleinPt_eq (a : Fin 48) (x : CuspE3) :
    kleinPt a x = kleinLin a x + kleinConst a := by
  apply PiLp.ext
  intro i
  simp only [kleinLin, kleinConst, kleinPt, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    WithLp.ofLp_add, Pi.add_apply]

/-- **`kleinPt a` is affine**: it commutes with convex combinations. -/
theorem kleinPt_affine {k : ℕ} (a : Fin 48) (z : Fin (k+1) → CuspE3)
    (w : StdSimplex ℝ (Fin (k+1))) :
    kleinPt a (∑ i, (w.weights i : ℝ) • z i) = ∑ i, (w.weights i : ℝ) • kleinPt a (z i) := by
  rw [kleinPt_eq, map_sum]
  simp only [map_smul]
  have hc : kleinConst a = ∑ i, (w.weights i : ℝ) • kleinConst a := by
    rw [← Finset.sum_smul, StdSimplex.total_of_fintype, one_smul]
  rw [hc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_add, ← kleinPt_eq]

/-! ## §2  The ceiling map on the half-open box -/

/-- **The cube-coordinate chart on the half-open box.**  If `x` lies in the half-open unit box
`[C_a, C_a + 1)³` of the cube `a` of cusp `v`, then the ceiling map is the `mk` of the chart of
`a`: `mbarPt v x = mk (cubeBit a, kleinPt a x)`. -/
theorem mbarPt_halfopen (v : Fin 5) {a : Fin 48} (hca : Work.Cusp.cubeCusp a = v) {x : CuspE3}
    (hx : x ∈ Work.RTOwed.cuspCert.halfopenBox a) :
    mbarPt v x = Work.FoldInst.mk
      (xbarOf a (kleinPt a x) (Work.RTOwed.cuspCert.cube_quad.1 a x
        (Work.RTOwed.cuspCert.halfopenBox_subset_cubeBox a hx))) := by
  have hbox : x ∈ cubeBox a := Work.RTOwed.cuspCert.halfopenBox_subset_cubeBox a hx
  have hfloor : floorV x = Work.Cusp.cubeCorner a := by
    funext i
    have hi := hx i
    simp only [Work.RTOwed.cuspCert.halfopenBox, Set.mem_setOf_eq] at hi
    rw [show floorV x i = ⌊x i⌋ from rfl, Int.floor_eq_iff]
    exact ⟨hi.1, hi.2⟩
  have hfloor' : ∀ i, ⌊x i⌋ = (Work.Cusp.cubeCorner a i : ℤ) := fun i => congrFun hfloor i
  have hcube : cubeOf v x = a := by
    show Work.Cusp.cubeOfMod v (floorV x) = a
    rw [hfloor]
    rw [← hca]
    exact Work.RTOwed.cubeOfMod_cubeCorner a
  have hred : redV v x = x := by
    apply PiLp.ext
    intro i
    simp only [redV, PiLp.toLp_apply]
    rw [hfloor' i]
    show x i - (Work.Cusp.cubeCorner a i : ℝ) + (Work.Cusp.cubeCorner (cubeOf v x) i : ℝ) = x i
    rw [hcube]
    ring
  have hmem : kleinPt (cubeOf v x) (redV v x) ∈ Work.FoldInst.Qbar := by
    rw [hcube, hred]
    exact Work.RTOwed.cuspCert.cube_quad.1 a x hbox
  have hpt : xbarOf (cubeOf v x) (kleinPt (cubeOf v x) (redV v x)) hmem
      = xbarOf a (kleinPt a x)
          (Work.RTOwed.cuspCert.cube_quad.1 a x hbox) := by
    simp only [xbarOf]
    refine Prod.ext ?_ ?_
    · show cubeBit (cubeOf v x) = cubeBit a
      rw [hcube]
    · refine Subtype.ext ?_
      show kleinPt (cubeOf v x) (redV v x) = kleinPt a x
      rw [hcube, hred]
  show Work.FoldInst.mk (cuspPtX v x) = _
  rw [cuspPtX_of_mem v x hmem, hpt]


/-! ## §3  The chart identity of the wall -/

/-- The affine point of the slab vertex family, shifted by `cuspH`: it is the convex combination
of the shifted vertices. -/
theorem cPt_slabV_add_cuspH {k : ℕ} (v : Fin 5) (τ : Fin (k+1) → CuspE3)
    (z : StdSimplex ℝ (Fin (k+1))) :
    cPt (slabV v τ) z + cuspH = ∑ i, (z.weights i : ℝ) • (slabL v (τ i) + cuspH) := by
  rw [cPt_eq_sum]
  rw [show (∑ i : Fin (k+1), (z.weights i : ℝ) • slabV v τ i)
      = ∑ i : Fin (k+1), (z.weights i : ℝ) • slabL v (τ i) from
      Finset.sum_congr rfl (fun i _ => rfl)]
  rw [show (∑ i : Fin (k+1), (z.weights i : ℝ) • (slabL v (τ i) + cuspH))
      = ∑ i : Fin (k+1), ((z.weights i : ℝ) • slabL v (τ i)
          + (z.weights i : ℝ) • cuspH) from
      Finset.sum_congr rfl (fun i _ => smul_add _ _ _)]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, StdSimplex.total_of_fintype, one_smul]

/-- The coordinate of a convex combination of slab points. -/
theorem sum_smul_coord {k : ℕ} (z : StdSimplex ℝ (Fin (k+1))) (y : Fin (k+1) → CuspE3) (j : Fin 3) :
    (∑ i, (z.weights i : ℝ) • y i) j = ∑ i, (z.weights i : ℝ) * y i j := by
  simp only [Finset.sum_apply, PiLp.smul_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The floor of the slab point is the cube corner, when a suitable vertex is interior. -/
theorem floorV_slab {k : ℕ} (v : Fin 5) {a : Fin 48} (τ : Fin (k+1) → CuspE3)
    (z : StdSimplex ℝ (Fin (k+1))) (i₀ : Fin (k+1))
    (hbox : ∀ i, slabL v (τ i) + cuspH ∈ cubeBox a)
    (hfar : ∀ j : Fin 3, (slabL v (τ i₀) + cuspH) j < (Work.Cusp.cubeCorner a j : ℝ) + 1)
    (hz : 0 < z.weights i₀) (j : Fin 3) :
    (Work.Cusp.cubeCorner a j : ℝ) ≤ (∑ i, (z.weights i : ℝ) • (slabL v (τ i) + cuspH)) j
      ∧ (∑ i, (z.weights i : ℝ) • (slabL v (τ i) + cuspH)) j
          < (Work.Cusp.cubeCorner a j : ℝ) + 1 := by
  have hsum : ∑ i, (z.weights i : ℝ) = 1 := StdSimplex.total_of_fintype z
  have hnn : ∀ i, 0 ≤ (z.weights i : ℝ) := fun i => StdSimplex.weights_nonneg i
  have hcoord : ∀ i, (slabL v (τ i) + cuspH) j
      ≤ (Work.Cusp.cubeCorner a j : ℝ) + 1 := fun i => (hbox i j).2
  rw [sum_smul_coord]
  constructor
  · calc (Work.Cusp.cubeCorner a j : ℝ)
        = ∑ i, (z.weights i : ℝ) * (Work.Cusp.cubeCorner a j : ℝ) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ i, (z.weights i : ℝ) * (slabL v (τ i) + cuspH) j :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbox i j).1 (hnn i)
  · calc ∑ i, (z.weights i : ℝ) * (slabL v (τ i) + cuspH) j
        < ∑ i, (z.weights i : ℝ) * ((Work.Cusp.cubeCorner a j : ℝ) + 1) := by
          refine Finset.sum_lt_sum ?_ ?_
          · intro i _
            exact mul_le_mul_of_nonneg_left (hcoord i) (hnn i)
          · exact ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hfar j) hz⟩
      _ = (Work.Cusp.cubeCorner a j : ℝ) + 1 := by
          rw [← Finset.sum_mul, hsum, one_mul]


/-! ## The main generic lemma -/

/-- **The chart identity**: if the three vertices of a slab triangle lie in a cube `a` and match
the polytope positions of a flag `s`, and one of them is strictly inside the cube in every
coordinate, then the chart simplex is the characteristic map `chiRep`. -/
theorem cSimp_eq_chiRep (v : Fin 5) {a : Fin 48} (hca : Work.Cusp.cubeCusp a = v)
    (τ : Fin 3 → CuspE3) (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell 2)
    (c : ZMod 2) (i₀ : Fin 3)
    (hdense : Dense {w : StdSimplex ℝ (Fin 3) | 0 < w.weights i₀})
    (hbox : ∀ i, slabL v (τ i) + cuspH ∈ cubeBox a)
    (hfar : ∀ j : Fin 3, (slabL v (τ i₀) + cuspH) j < (Work.Cusp.cubeCorner a j : ℝ) + 1)
    (hpos : ∀ i, kleinPt a (slabL v (τ i) + cuspH)
        = Work.MbarHomology.QbarPD.posR (Work.MbarHomology.Mbar.flagIdx s i))
    (hbit : cubeBit a = c) :
    cSimp v (slabV v τ) = ⟨fun w => Work.MbarHomology.Mbar.chiRep (c, s) w,
        Work.MbarHomology.Mbar.continuous_chiRep (c, s)⟩ := by
  apply ContinuousMap.ext
  intro z
  refine congrFun (Continuous.ext_on hdense (cSimp v (slabV v τ)).continuous
    (Work.MbarHomology.Mbar.continuous_chiRep (c, s)) ?_) z
  intro w hw
  have hXbox : (∑ i, (w.weights i : ℝ) • (slabL v (τ i) + cuspH))
      ∈ Work.RTOwed.cuspCert.halfopenBox a := by
    intro j
    exact floorV_slab v τ w i₀ hbox hfar hw j
  have hbox' : (∑ i, (w.weights i : ℝ) • (slabL v (τ i) + cuspH)) ∈ cubeBox a :=
    Work.RTOwed.cuspCert.halfopenBox_subset_cubeBox a hXbox
  have hXeq : cPt (slabV v τ) w + cuspH
      = ∑ i, (w.weights i : ℝ) • (slabL v (τ i) + cuspH) := cPt_slabV_add_cuspH v τ w
  have hL : cSimp v (slabV v τ) w = Work.FoldInst.mk
      (xbarOf a (kleinPt a (∑ i, (w.weights i : ℝ) • (slabL v (τ i) + cuspH)))
        (Work.RTOwed.cuspCert.cube_quad.1 a _ hbox')) := by
    show Work.RTOwed.mbarPtC v (cPt (slabV v τ) w) = _
    rw [Work.RTOwed.mbarPtC, hXeq]
    exact mbarPt_halfopen v hca hXbox
  have hpt : Work.MbarHomology.Mbar.ptW s (fun i => w.weights i)
      = kleinPt a (∑ i, (w.weights i : ℝ) • (slabL v (τ i) + cuspH)) := by
    rw [Work.MbarHomology.Mbar.ptW]
    rw [show (∑ i, (w.weights i : ℝ) • Work.MbarHomology.QbarPD.posR
          (Work.MbarHomology.Mbar.flagIdx s i))
        = ∑ i, (w.weights i : ℝ) • kleinPt a (slabL v (τ i) + cuspH) from
        Finset.sum_congr rfl (fun i _ => by rw [hpos i])]
    exact (kleinPt_affine a (fun i => slabL v (τ i) + cuspH) w).symm
  have hR : Work.MbarHomology.Mbar.chiRep (c, s) w = Work.FoldInst.mk
      (c, ⟨kleinPt a (∑ i, (w.weights i : ℝ) • (slabL v (τ i) + cuspH)),
        Work.RTOwed.cuspCert.cube_quad.1 a _ hbox'⟩) := by
    refine congrArg Work.FoldInst.mk (Prod.ext rfl ?_)
    exact Subtype.ext hpt
  rw [hL]
  show Work.FoldInst.mk (xbarOf a (kleinPt a (∑ i, (w.weights i : ℝ) • (slabL v (τ i) + cuspH)))
      (Work.RTOwed.cuspCert.cube_quad.1 a _ hbox')) = Work.MbarHomology.Mbar.chiRep (c, s) w
  rw [hR]
  refine congrArg Work.FoldInst.mk (Prod.ext ?_ ?_)
  · show cubeBit a = c
    exact hbit
  · exact Subtype.ext rfl



/-! ## §3  Translation invariance of the slab pushforward -/

/-- The translation of an affine chain by a vector `δ`. -/
def translateAff (k : ℕ) (δ : CuspE3) : AffC k →ₗ[ℤ] AffC k :=
  Finsupp.lmapDomain ℤ ℤ (fun p : Fin (k+1) → CuspE3 => fun i => p i + δ)

theorem translateAff_single (k : ℕ) (δ : CuspE3) (p : Fin (k+1) → CuspE3) (a : ℤ) :
    translateAff k δ (Finsupp.single p a) = Finsupp.single (fun i => p i + δ) a := by
  rw [translateAff, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem slabV_translate (v : Fin 5) {k : ℕ} (p : Fin (k+1) → CuspE3) (δ : CuspE3) :
    slabV v (fun i => p i + δ) = fun i => slabL v (p i) + slabL v δ := by
  funext i
  simp only [slabV, slabL_add]

/-- **The slab pushforward is invariant under the cusp lattice translations.** -/
theorem slabChain_translate_comp (v : Fin 5) (k : ℕ) (δ : CuspE3)
    (hδ : slabL v δ ∈ Work.Cusp.lattice v) :
    (slabChain v k).comp (translateAff k δ) = slabChain v k := by
  refine Finsupp.lhom_ext fun p a => ?_
  simp only [LinearMap.comp_apply, translateAff_single, slabChain_single]
  congr 1
  rw [slabV_translate v p δ]
  exact cChain_add_lattice v (slabV v p) (slabL v δ) hδ

theorem slabChain_translate (v : Fin 5) (k : ℕ) (δ : CuspE3)
    (hδ : slabL v δ ∈ Work.Cusp.lattice v) (c : AffC k) :
    slabChain v k (translateAff k δ c) = slabChain v k c := by
  rw [← LinearMap.comp_apply, slabChain_translate_comp v k δ hδ]

/-- **The slab pushforward of a translate difference vanishes.** -/
theorem slabChain_translate_sub (v : Fin 5) (k : ℕ) (δ : CuspE3)
    (hδ : slabL v δ ∈ Work.Cusp.lattice v) (c : AffC k) :
    slabChain v k (translateAff k δ c - c) = 0 := by
  rw [map_sub, slabChain_translate v k δ hδ c, sub_self]



/-! ## §4  The chart identity without the density hypothesis, and the assembly -/

/-- **The chart identity of the wall** (without the density hypothesis). -/
theorem cSimp_eq_chiRep' (v : Fin 5) {a : Fin 48} (hca : Work.Cusp.cubeCusp a = v)
    (τ : Fin 3 → CuspE3) (s : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell 2)
    (c : ZMod 2) (i₀ : Fin 3)
    (hbox : ∀ i, slabL v (τ i) + cuspH ∈ cubeBox a)
    (hfar : ∀ j : Fin 3, (slabL v (τ i₀) + cuspH) j < (Work.Cusp.cubeCorner a j : ℝ) + 1)
    (hpos : ∀ i, kleinPt a (slabL v (τ i) + cuspH)
        = Work.MbarHomology.QbarPD.posR (Work.MbarHomology.Mbar.flagIdx s i))
    (hbit : cubeBit a = c) :
    cSimp v (slabV v τ) = ⟨fun w => Work.MbarHomology.Mbar.chiRep (c, s) w,
        Work.MbarHomology.Mbar.continuous_chiRep (c, s)⟩ :=
  cSimp_eq_chiRep v hca τ s c i₀ (denseSimplex3 i₀) hbox hfar hpos hbit

/-- **The assembly**: the wall chain plus the collar give the target, with `s = 1`. -/
theorem slabWall_of_wallCollar (v : Fin 5)
    (h : ∃ (s : ℤ) (W K : AffC 2), (s = 1 ∨ s = -1) ∧
      slabChain v 2 W = s • ((PsiM.f 2) (planeCycleVec v 0)) ∧
      slabChain v 2 K = 0 ∧ dLC 1 K = s • dLC 1 W - dLC 1 slabBot) :
    ∃ (s : ℤ) (c : AffC 2), (s = 1 ∨ s = -1) ∧ dLC 1 c = 0 ∧
      slabChain v 2 c
        = Work.BridgeSquare.singT v
          - s • ((Work.BridgeSquare.PsiM.f 2) (Work.BridgeSquare.planeCycleVec v 0)) := by
  obtain ⟨s, W, K, hs, himg, hKimg, hKbd⟩ := h
  refine ⟨1, slabBot - s • W + K, Or.inl rfl, ?_, ?_⟩
  · have h1 : dLC 1 (slabBot - s • W + K)
        = dLC 1 slabBot - s • (dLC 1 W) + dLC 1 K := by
      rw [map_add, map_sub, map_zsmul]
    rw [h1, hKbd]
    abel
  · have h1 : slabChain v 2 (slabBot - s • W + K)
        = slabChain v 2 slabBot - s • (slabChain v 2 W) + slabChain v 2 K := by
      rw [map_add, map_sub, map_zsmul]
    rw [h1, himg, hKimg, slabChain_bot]
    rcases hs with rfl | rfl <;> simp [smul_smul]



end

end Work.BridgeSquare
