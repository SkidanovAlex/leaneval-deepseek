import Mathlib
import Submission.Work.RTOwed.cuspTorus_homeo_boundary
import Submission.Work.RTOwed.cuspTorus_homeo_circle_torus
import Submission.Work.RTOwed.sqBoundary_homeo_circle
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.slope_lattice
import Submission.Work.Cusp.bndOfU_mem
import Submission.Work.Cusp.bndOfU_uPerim
import Submission.Work.Cusp.bndOfU_add_int
import Submission.Work.Cusp.outerU_cuspX
import Submission.Work.Cusp.frame_orthonormal
import Submission.Work.Cusp.cuspX_injOn
import Submission.Work.Space.Split
import Submission.Work.Space.Assembly
import Submission.Work.Cusp.mbarPt_periodic
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.CuspCollarAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Set Topology Function
open scoped Real InnerProductSpace

noncomputable section

/-! ### The boundary map in cusp coordinates

The boundary homeomorphism `CuspTorus v → ∂[-1,1]² × (ℝ/ℤ)²` is built from the explicit formula
`x ↦ (bndOfU (outerU v x), outerY v x)`, so we first isolate that formula as a map.
-/

/-- The `v`-th gluing boundary: the boundary of the filling square times the phase torus. -/
abbrev CuspBdry (_v : Work.Space.Cusp) : Type :=
  {p : Work.Space.SquarePt × (Fin 2 → AddCircle (1 : ℝ)) // Work.Space.sqNorm p.1 = 1}

/-- **The boundary map in cusp coordinates**: the ceiling point over the cusp coordinate `x` is
sent to the boundary point with perimeter parameter `bndOfU (outerU v x)` and phase coordinates
`outerY v x`. -/
def cuspBdryMap (v : Work.Space.Cusp) (x : Work.Cusp.E3) : CuspBdry v :=
  ⟨(⟨Work.Cusp.bndOfU (Work.Cusp.outerU v x),
      by simpa only [Work.Space.Sq, Work.Cusp.Sq] using
        Work.Cusp.bndOfU_mem (Work.Cusp.outerU v x)⟩,
    fun i => ((Work.Cusp.outerY v x i : ℝ) : AddCircle (1 : ℝ))), by
      show Work.Cusp.nrm (Work.Cusp.bndOfU (Work.Cusp.outerU v x)) = 1
      exact Work.Cusp.nrm_bndOfU (Work.Cusp.outerU v x)⟩

/-- The boundary map is continuous: `outerU`, `outerY` are continuous (`outerU` is an inner
product with a fixed lattice vector, `outerY` is linear), `bndOfU` is continuous, and the
coordinatewise quotient map `ℝ → ℝ/ℤ` is continuous. -/
theorem cuspBdryMap_continuous (v : Work.Space.Cusp) : Continuous (cuspBdryMap v) := by
  have hU : Continuous fun x : Work.Cusp.E3 => Work.Cusp.outerU v x := Work.Cusp.outerU_continuous v
  have hY : Continuous fun x : Work.Cusp.E3 => Work.Cusp.outerY v x := Work.Cusp.continuous_outerY v
  have hbnd : Continuous fun x : Work.Cusp.E3 =>
      (⟨Work.Cusp.bndOfU (Work.Cusp.outerU v x),
        by simpa only [Work.Space.Sq, Work.Cusp.Sq] using
          Work.Cusp.bndOfU_mem (Work.Cusp.outerU v x)⟩ : Work.Space.SquarePt) :=
    (Work.Cusp.continuous_bndOfU.comp hU).subtype_mk _
  have hcoe : Continuous fun y : ℝ => (y : AddCircle (1 : ℝ)) := by fun_prop
  have hT : Continuous fun x : Work.Cusp.E3 =>
      (fun i : Fin 2 => ((Work.Cusp.outerY v x i : ℝ) : AddCircle (1 : ℝ))) := by
    apply continuous_pi
    intro i
    exact hcoe.comp ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i).comp hY)
  have hpair : Continuous fun x : Work.Cusp.E3 =>
      ((⟨Work.Cusp.bndOfU (Work.Cusp.outerU v x),
        by simpa only [Work.Space.Sq, Work.Cusp.Sq] using
          Work.Cusp.bndOfU_mem (Work.Cusp.outerU v x)⟩ : Work.Space.SquarePt),
        fun i => ((Work.Cusp.outerY v x i : ℝ) : AddCircle (1 : ℝ))) := hbnd.prodMk hT
  exact hpair.subtype_mk _

/-! ### The boundary map is invariant under the cusp lattice -/

/-- **The boundary map is invariant under each lattice generator `κ_{v,i}`.**  The `κ_{v,1}`- and
the two other coordinates of `x + κ_{v,i}` differ from those of `x` by the *integers*
`δ_{i,1}` and `δ_{i,2} − b_v δ_{i,1}`, `δ_{i,3}`; the first is invisible to the `1`-periodic
`bndOfU` (`bndOfU_add_int`), the other two are invisible in `AddCircle 1`
(`addCircle_coe_add_int`). -/
theorem cuspBdryMap_add_kv (v : Work.Space.Cusp) (i : Fin 3) (x : Work.Cusp.E3) :
    cuspBdryMap v (x + Work.Cusp.kv v i) = cuspBdryMap v x := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    show Work.Cusp.bndOfU (Work.Cusp.outerU v (x + Work.Cusp.kv v i)) =
      Work.Cusp.bndOfU (Work.Cusp.outerU v x)
    rw [Work.Cusp.outerU_add_kv_int]
    exact Work.Cusp.bndOfU_add_int _ _
  · funext j
    fin_cases j
    · show (((Work.Cusp.outerY v (x + Work.Cusp.kv v i)) 0 : ℝ) : AddCircle (1 : ℝ)) =
        (((Work.Cusp.outerY v x) 0 : ℝ) : AddCircle (1 : ℝ))
      rw [Work.Cusp.outerY_add_kv_fst_int]
      exact Work.Cusp.addCircle_coe_add_int _ _
    · show (((Work.Cusp.outerY v (x + Work.Cusp.kv v i)) 1 : ℝ) : AddCircle (1 : ℝ)) =
        (((Work.Cusp.outerY v x) 1 : ℝ) : AddCircle (1 : ℝ))
      rw [Work.Cusp.outerY_add_kv_snd_int]
      exact Work.Cusp.addCircle_coe_add_int _ _

/-- The periods of the boundary map form an additive subgroup of `E3`. -/
def cuspBdryMapPeriod (v : Work.Space.Cusp) : AddSubgroup Work.Cusp.E3 where
  carrier := {l | ∀ x, cuspBdryMap v (x + l) = cuspBdryMap v x}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro p q hp hq x
    rw [← add_assoc, hq (x + p), hp x]
  neg_mem' := by
    intro p hp x
    have h := hp (x + -p)
    rw [add_assoc, neg_add_cancel, add_zero] at h
    exact h.symm

/-- Every lattice generator `κ_{v,i}` is a period of the boundary map. -/
theorem range_kv_subset_cuspBdryMapPeriod (v : Work.Space.Cusp) :
    Set.range (Work.Cusp.kv v) ⊆ (cuspBdryMapPeriod v : Set Work.Cusp.E3) := by
  rintro d ⟨i, rfl⟩
  exact cuspBdryMap_add_kv v i

/-- **The boundary map is invariant under the cusp lattice** `Λ_v`. -/
theorem cuspBdryMap_periodic (v : Work.Space.Cusp) (x l : Work.Cusp.E3)
    (hl : l ∈ Work.Cusp.lattice v) : cuspBdryMap v (x + l) = cuspBdryMap v x :=
  (AddSubgroup.closure_le (cuspBdryMapPeriod v) |>.mpr (range_kv_subset_cuspBdryMapPeriod v)) hl x

/-! ### The coordinate change `cuspX` is linear in the coordinates

The difference of two cusp coordinates is the cusp coordinate of the difference of the
`(u, y)`-coordinates: this is the linearity of the change of basis
`(u, y) ↦ u σ_v + y₂ λ₂ + y₃ λ₃` used to read off the lattice vector `x - y` from the
coordinate differences. -/
theorem cuspX_sub (v : Fin 5) (u1 u2 : ℝ) (Y1 Y2 : Work.Cusp.E2) :
    Work.Cusp.cuspX v u1 Y1 - Work.Cusp.cuspX v u2 Y2 =
      (u1 - u2) • Work.Cusp.slope v + (Y1 0 - Y2 0) • Work.Cusp.lam2 v
        + (Y1 1 - Y2 1) • Work.Cusp.lam3 v := by
  simp only [Work.Cusp.cuspX, Work.Cusp.cuspY]
  module

/-! ### The boundary map is injective modulo the cusp lattice -/

/-- **The difference of two cusp coordinates with the same image is a lattice vector.**  If
`x` and `y` have the same boundary image, then `outerU v x` and `outerU v y` have the same
fractional part (`uPerim_bndOfU`), and the two `outerY`-coordinates agree modulo `ℤ`; since
`cuspX` is a linear isomorphism with `cuspX v (outerU v x) (outerY v x) = x`, the difference
`x - y` is an integer combination of `σ_v, λ₂, λ₃`, hence lies in `Λ_v`. -/
theorem cuspBdryMap_injective (v : Work.Space.Cusp) {x y : Work.Cusp.E3}
    (h : cuspBdryMap v x = cuspBdryMap v y) : x - y ∈ Work.Cusp.lattice v := by
  -- the boundary and the phase coordinates of the two points
  have hbnd : Work.Cusp.bndOfU (Work.Cusp.outerU v x) = Work.Cusp.bndOfU (Work.Cusp.outerU v y) :=
    congrArg (fun z : CuspBdry v => ((z.1).1 : Work.Cusp.E2)) h
  have htorus : (fun i : Fin 2 => ((Work.Cusp.outerY v x i : ℝ) : AddCircle (1 : ℝ))) =
      (fun i : Fin 2 => ((Work.Cusp.outerY v y i : ℝ) : AddCircle (1 : ℝ))) :=
    congrArg (fun z : CuspBdry v => (z.1).2) h
  -- the *integer* differences of the perimeter parameters
  have hu : ∃ m : ℤ, Work.Cusp.outerU v x - Work.Cusp.outerU v y = (m : ℝ) := by
    refine ⟨⌊Work.Cusp.outerU v x⌋ - ⌊Work.Cusp.outerU v y⌋, ?_⟩
    have hf : Int.fract (Work.Cusp.outerU v x) = Int.fract (Work.Cusp.outerU v y) := by
      rw [← Work.Cusp.uPerim_bndOfU, hbnd, Work.Cusp.uPerim_bndOfU]
    have e1 := Int.floor_add_fract (Work.Cusp.outerU v x)
    have e2 := Int.floor_add_fract (Work.Cusp.outerU v y)
    rw [hf] at e1
    push_cast
    linarith
  -- the *integer* differences of the phase coordinates
  have hn : ∀ i : Fin 2, ∃ n : ℤ, Work.Cusp.outerY v x i - Work.Cusp.outerY v y i = (n : ℝ) := by
    intro i
    have hi : ((Work.Cusp.outerY v x i - Work.Cusp.outerY v y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub (p := (1 : ℝ)), congrFun htorus i, sub_self]
    rw [AddCircle.coe_eq_zero_iff] at hi
    obtain ⟨n, hn⟩ := hi
    rw [zsmul_one] at hn
    exact ⟨n, hn.symm⟩
  obtain ⟨m, hm⟩ := hu
  obtain ⟨n0, hn0⟩ := hn 0
  obtain ⟨n1, hn1⟩ := hn 1
  -- the difference `x - y` in the `(σ_v, λ₂, λ₃)`-coordinates
  have key : x - y = (m : ℝ) • Work.Cusp.slope v + (n0 : ℝ) • Work.Cusp.lam2 v
      + (n1 : ℝ) • Work.Cusp.lam3 v := by
    have h1 := cuspX_sub v (Work.Cusp.outerU v x) (Work.Cusp.outerU v y)
      (Work.Cusp.outerY v x) (Work.Cusp.outerY v y)
    rw [Work.Cusp.cuspX_outerU_outerY v x, Work.Cusp.cuspX_outerU_outerY v y, hm, hn0, hn1] at h1
    exact h1
  rw [key]
  have hslope : Work.Cusp.slope v ∈ Work.Cusp.lattice v := by
    rw [Work.Cusp.slope_eq_kv]
    exact AddSubgroup.add_mem _
      (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (0 : Fin 3))) 1)
      (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (1 : Fin 3)))
        (Work.Cusp.slopeB v))
  have hlam2 : Work.Cusp.lam2 v ∈ Work.Cusp.lattice v :=
    AddSubgroup.subset_closure (Set.mem_range_self (1 : Fin 3))
  have hlam3 : Work.Cusp.lam3 v ∈ Work.Cusp.lattice v :=
    AddSubgroup.subset_closure (Set.mem_range_self (2 : Fin 3))
  refine AddSubgroup.add_mem _ (AddSubgroup.add_mem _ ?_ ?_) ?_
  · rw [Int.cast_smul_eq_zsmul ℝ m (Work.Cusp.slope v)]
    exact AddSubgroup.zsmul_mem _ hslope m
  · rw [Int.cast_smul_eq_zsmul ℝ n0 (Work.Cusp.lam2 v)]
    exact AddSubgroup.zsmul_mem _ hlam2 n0
  · rw [Int.cast_smul_eq_zsmul ℝ n1 (Work.Cusp.lam3 v)]
    exact AddSubgroup.zsmul_mem _ hlam3 n1

/-! ### The boundary map is surjective -/

/-- **Every boundary point is in the image of the boundary map**: pick the real lifts
`u = uPerim p` of the boundary point `p ∈ ∂Sq` (so that `bndOfU u = p`, `bndOfU_uPerim`) and
`y_i = uRep θ_i` of the phase coordinates (`uRep_coe`), and take the cusp coordinate
`cuspX v u y`, whose `outerU` and `outerY` are exactly `u` and `y`. -/
theorem cuspBdryMap_surjective (v : Work.Space.Cusp) : Function.Surjective (cuspBdryMap v) := by
  intro p
  let y : Work.Cusp.E2 := WithLp.toLp 2 (fun i : Fin 2 => Work.Cusp.uRep (p.1.2 i))
  have hy : ∀ i : Fin 2, ((y i : ℝ) : AddCircle (1 : ℝ)) = p.1.2 i :=
    fun i => Work.Cusp.uRep_coe (p.1.2 i)
  refine ⟨Work.Cusp.cuspX v (Work.Cusp.uPerim (p.1.1 : Work.Cusp.E2)) y, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    show Work.Cusp.bndOfU (Work.Cusp.outerU v (Work.Cusp.cuspX v (Work.Cusp.uPerim ↑p.1.1) y))
      = ↑p.1.1
    rw [Work.Cusp.outerU_cuspX, Work.Cusp.bndOfU_uPerim]
    show Work.Cusp.nrm (↑p.1.1 : Work.Cusp.E2) = 1
    simpa only [Work.Space.sqNorm, Work.Space.nrm, Work.Cusp.nrm] using p.2
  · show (fun i : Fin 2 =>
        ((Work.Cusp.outerY v (Work.Cusp.cuspX v (Work.Cusp.uPerim ↑p.1.1) y) i : ℝ) :
          AddCircle (1 : ℝ))) = p.1.2
    rw [Work.Cusp.outerY_cuspX]
    exact funext hy

/-! ### The coordinate form of the boundary homeomorphism -/

/-- **The explicit coordinate form of the cusp torus boundary homeomorphism**: the strengthening of `Work.RTOwed.cuspTorus_homeo_boundary` in which the homeomorphism is computed in the cusp coordinates `(u, y) = (outerU v x, outerY v x)`:

`Ψ (mk x) = (bndOfU (outerU v x), (outerY v x : (ℝ/ℤ)²))`.

This is the coordinate form needed by the gluing `τ_v` of `Work.RTInstance.GlueHomeo` (`CuspGlueData.glue_eq`): the ceiling point over `cuspX v u y` must be sent to the boundary point with perimeter parameter `bndOfU u` and torus coordinates `y`.

Route: the map descends to `E3 ⧸ Λ_v` because `bndOfU` is `1`-periodic (`Work.Cusp.bndOfU_add_int`, `Work.Cusp.bndOfU_u`) and `outerU`, `outerY` change by an *integer* vector under `x ↦ x + κ_{v,i}` (`slopeB v, slopeC v : ℤ`, `Work.Cusp.slope_eq_kv`, `Work.Cusp.kappaCoord`); it is a bijection (injectivity from `Work.Cusp.cuspX_outerU_outerY` and `Work.Cusp.uPerim_bndOfU`/`Work.Cusp.bndOfU_uPerim`, surjectivity by choosing a real lift `u` with `bndOfU u = p`, using `Work.Cusp.uPerim`); `CuspTorus v` is compact (via `Work.RTOwed.cuspTorus_homeo_circle_torus`) and the target is Hausdorff, so `Continuous.homeoOfEquivCompactToT2` turns the continuous bijection into the homeomorphism, and the formula is the definition of the underlying function. -/
theorem cuspTorus_homeo_boundary_explicit (v : Work.Space.Cusp) :
    ∃ Ψ : Work.Cusp.CuspTorus v ≃ₜ
        {p : Work.Space.SquarePt × (Fin 2 → AddCircle (1 : ℝ)) // Work.Space.sqNorm p.1 = 1},
      ∀ x : Work.Cusp.E3,
        Ψ (Quotient.mk'' x) =
          ⟨(⟨Work.Cusp.bndOfU (Work.Cusp.outerU v x),
              by simpa only [Work.Space.Sq, Work.Cusp.Sq] using
                Work.Cusp.bndOfU_mem (Work.Cusp.outerU v x)⟩,
            fun i => ((Work.Cusp.outerY v x i : ℝ) : AddCircle (1 : ℝ))), by
            show Work.Cusp.nrm (Work.Cusp.bndOfU (Work.Cusp.outerU v x)) = 1
            exact Work.Cusp.nrm_bndOfU (Work.Cusp.outerU v x)⟩ := by
  classical
  -- the boundary map descends to the cusp torus
  have hper : ∀ x y : Work.Cusp.E3,
      QuotientAddGroup.leftRel (Work.Cusp.lattice v) x y →
        cuspBdryMap v x = cuspBdryMap v y := by
    intro x y hxy
    have hxy' : -x + y ∈ Work.Cusp.lattice v := QuotientAddGroup.leftRel_apply.mp hxy
    have h := cuspBdryMap_periodic v x (-x + y) hxy'
    rw [show x + (-x + y) = y from by abel] at h
    exact h.symm
  let qm : Work.Cusp.E3 → Work.Cusp.CuspTorus v := fun x => Quotient.mk'' x
  let g : Work.Cusp.CuspTorus v → CuspBdry v := Quotient.lift (cuspBdryMap v) hper
  have hg_mk : ∀ x : Work.Cusp.E3, g (qm x) = cuspBdryMap v x := fun x => rfl
  have hg_cont : Continuous g := by
    refine (isQuotientMap_quotient_mk'
      (s := QuotientAddGroup.leftRel (Work.Cusp.lattice v))).continuous_iff.mpr ?_
    change Continuous (g ∘ qm)
    rw [show g ∘ qm = cuspBdryMap v from funext fun x => hg_mk x]
    exact cuspBdryMap_continuous v
  have hg_inj : Function.Injective g := by
    intro t t' htt'
    revert htt'
    refine Quotient.inductionOn₂ t t' ?_
    intro x y hxy
    rw [hg_mk x, hg_mk y] at hxy
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (cuspBdryMap_injective v hxy)
  have hg_surj : Function.Surjective g := by
    intro p
    obtain ⟨x, hx⟩ := cuspBdryMap_surjective v p
    exact ⟨qm x, by rw [hg_mk x]; exact hx⟩
  have hbij : Function.Bijective g := ⟨hg_inj, hg_surj⟩
  haveI : CompactSpace (Work.Cusp.CuspTorus v) := by
    obtain ⟨h⟩ := cuspTorus_homeo_circle_torus v
    exact h.symm.compactSpace
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hbij) hg_cont, ?_⟩
  intro x
  exact hg_mk x

end

end Work.RTOwed
