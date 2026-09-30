import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.mbarPt_periodic
import Submission.Work.Cusp.mbarPt_continuous
import Submission.Work.Cusp.slope_lattice
import Submission.Work.Cusp.cuspCoordM_continuous
import Submission.Work.Cusp.cuspCoordM_injective
import Submission.Work.Cusp.cuspX_outerU_outerY
import Submission.Work.Cusp.outerU_cuspX
import Submission.Work.Cusp.outerY_cuspX
import Submission.Work.Cusp.bndOfU_add_int
import Submission.Work.Cusp.uPerim_bndOfU

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The ceiling map `mbarPt` realises the cusp torus `ℝ³/Λ_v`

`CuspGlueData.mbarPt : E3 → M̄` is the ceiling of the `v`-th cusp composed with the cusp
coordinate (`D.mbarPt_eq : mbarPt x = mbarLow (ceilingPt x)`, with `ceilingPt x = (x, β x)`), i.e.
the point of the truncation torus `T_v` with cube coordinate `x`.  Since `T_v = ℝ³/Λ_v`, the map
`mbarPt` must descend to a *bijection* `ℝ³/Λ_v → T_v` — the coordinate form of the homeomorphism
`τ_v`.  This file proves exactly that, in the injective form

  `D.mbarPt x = D.mbarPt x' ↔ x - x' ∈ lattice v`.

## The two directions

`←` is `mbarPt_periodic`: `mbarPt` is invariant under the lattice `Λ_v = ⟨κ_{v,1},κ_{v,2},κ_{v,3}⟩`
(the ceiling points over a lattice translate are glued to the same filling boundary point).

`→` is the interesting one.  Both `mbarPt x` and `mbarPt x'` lie on the truncation torus, where
they are glued to filling boundary points of coordinates `(bndOfU (outerU v x), outerY v x)` and
`(bndOfU (outerU v x'), outerY v x')` (`incMbar_mbarPt_eq`).  Since `incMbar` is injective, the
hypothesis says those two filling boundary points agree, and `incW_injective` then says their
coordinates agree:

* `bndOfU (outerU v x) = bndOfU (outerU v x')`, which by `uPerim_bndOfU` gives
  `Int.fract (outerU v x) = Int.fract (outerU v x')`, hence `outerU v x - outerU v x' ∈ ℤ`;
* `(outerY v x) i ≡ (outerY v x') i (mod 1)` in `AddCircle 1`, hence
  `(outerY v x) i - (outerY v x') i ∈ ℤ` for `i = 0,1`.

Writing `c_i = kappaCoord v i (x - x')` for the `κ_{v,i}`-coordinates of `d = x - x'`
(`outerU v x = kappaCoord v 0 x`, `outerY v x = (kappaCoord v 1 x - b_v·outerU v x, kappaCoord v 2 x)`),
these read

* `c_0 ∈ ℤ`,
* `c_1 - b_v c_0 ∈ ℤ`,
* `c_2 ∈ ℤ`,

and since `b_v ∈ ℤ` and the `κ_{v,i}` are an orthogonal basis (`kappaCoord_expansion`), all three
`c_i` are integers, i.e. `d = c_0 κ_{v,1} + c_1 κ_{v,2} + c_2 κ_{v,3} ∈ Λ_v`.
-/

noncomputable section

open Set Topology Function
open scoped Real InnerProductSpace

namespace Work.Cusp

/-! ### Elementary coordinate identities -/

/-- The `κ_{v,i}`-coordinate is additive in its last argument as well. -/
lemma kappaCoord_sub (v : Fin 5) (i : Fin 3) (x y : E3) :
    kappaCoord v i (x - y) = kappaCoord v i x - kappaCoord v i y := by
  simp only [kappaCoord, inner_sub_left, sub_div]

/-- `outerU` is additive: it is the `κ_{v,1}`-coordinate. -/
lemma outerU_sub (v : Fin 5) (x y : E3) :
    outerU v (x - y) = outerU v x - outerU v y := by
  simp only [outerU, kappaCoord, inner_sub_left, sub_div]

/-- The first component of `outerY` in coordinates. -/
lemma outerY_fst (v : Fin 5) (x : E3) :
    (outerY v x) 0 = kappaCoord v 1 x - (slopeB v : ℝ) * outerU v x := by
  simp [outerY]

/-- The second component of `outerY` in coordinates. -/
lemma outerY_snd (v : Fin 5) (x : E3) :
    (outerY v x) 1 = kappaCoord v 2 x := by
  simp [outerY]

/-! ### From equalities of coordinates to integers -/

/-- If two reals have the same point of `∂Sq` under `bndOfU`, then they differ by an integer: the
perimeter parameter `uPerim ∘ bndOfU` is `Int.fract`, which determines the fractional part. -/
lemma bndOfU_sub_int {a b : ℝ} (h : bndOfU a = bndOfU b) : ∃ z : ℤ, a - b = (z : ℝ) := by
  have h1 : Int.fract a = Int.fract b := by
    rw [← uPerim_bndOfU a, ← uPerim_bndOfU b, h]
  refine ⟨⌊a⌋ - ⌊b⌋, ?_⟩
  have ha := Int.floor_add_fract a
  have hb := Int.floor_add_fract b
  push_cast
  linarith

/-- If two reals have the same class in `AddCircle (1 : ℝ)`, then they differ by an integer. -/
lemma addCircle_sub_int {a b : ℝ} (h : (a : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ))) :
    ∃ z : ℤ, a - b = (z : ℝ) := by
  rw [QuotientAddGroup.eq_iff_sub_mem] at h
  rw [AddSubgroup.mem_zmultiples_iff] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by simpa using hk.symm⟩

/-! ### The theorem -/

theorem mbarPt_eq_iff (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (x x' : E3) : D.mbarPt x = D.mbarPt x' ↔ x - x' ∈ lattice v := by
  constructor
  · -- `→`: equality of ceiling points forces the coordinates to agree mod `Λ_v`
    intro h
    -- both ceiling points are glued to filling boundary points
    have hinc : a.incMbar (D.mbarPt x) = a.incMbar (D.mbarPt x') := congrArg _ h
    rw [incMbar_mbarPt_eq a v D x, incMbar_mbarPt_eq a v D x'] at hinc
    -- the filling boundary point determines the coordinates
    have hpq := a.incW_injective v hinc
    have hU : bndOfU (outerU v x) = bndOfU (outerU v x') := by
      have := congrArg
        (fun r : Work.Space.SquarePt × a.Torus v => ((r.1 : Work.Space.SquarePt) : E2)) hpq
      simpa using this
    have hYt : D.tor.symm (fun i => (((outerY v x) i : ℝ) : AddCircle (1 : ℝ)))
        = D.tor.symm (fun i => (((outerY v x') i : ℝ) : AddCircle (1 : ℝ))) := by
      have := congrArg Prod.snd hpq
      simpa using this
    have hY : (fun i => (((outerY v x) i : ℝ) : AddCircle (1 : ℝ)))
        = (fun i => (((outerY v x') i : ℝ) : AddCircle (1 : ℝ))) := D.tor.symm.injective hYt
    -- the three integer conditions on the `κ`-coordinates of `x - x'`
    obtain ⟨z0, hz0⟩ := bndOfU_sub_int hU
    obtain ⟨z1, hz1⟩ := addCircle_sub_int (congrFun hY 0)
    obtain ⟨z2, hz2⟩ := addCircle_sub_int (congrFun hY 1)
    have h0 : kappaCoord v 0 (x - x') = (z0 : ℝ) := by
      show outerU v (x - x') = (z0 : ℝ)
      rw [outerU_sub]
      exact hz0
    have hYsub1 : (outerY v x) 0 - (outerY v x') 0
        = kappaCoord v 1 (x - x') - (slopeB v : ℝ) * (outerU v x - outerU v x') := by
      rw [outerY_fst v x, outerY_fst v x', kappaCoord_sub v 1 x x']
      ring
    have h1 : kappaCoord v 1 (x - x') = ((z1 + slopeB v * z0 : ℤ) : ℝ) := by
      have hc1 : kappaCoord v 1 (x - x')
          - (slopeB v : ℝ) * (outerU v x - outerU v x') = (z1 : ℝ) := by
        rw [← hYsub1]; exact hz1
      rw [hz0] at hc1
      have hc1' : kappaCoord v 1 (x - x')
          = (z1 : ℝ) + (slopeB v : ℝ) * (z0 : ℝ) := by linarith
      rw [hc1']
      push_cast
      ring
    have h2 : kappaCoord v 2 (x - x') = (z2 : ℝ) := by
      rw [outerY_snd v x, outerY_snd v x'] at hz2
      rw [← kappaCoord_sub v 2 x x'] at hz2
      exact hz2
    -- recompose `x - x'` in the `κ`-basis and read off lattice membership
    rw [← kappaCoord_expansion v (x - x'), h0, h1, h2]
    have h0' : kv v 0 ∈ lattice v := AddSubgroup.subset_closure (Set.mem_range_self 0)
    have h1' : kv v 1 ∈ lattice v := AddSubgroup.subset_closure (Set.mem_range_self 1)
    have h2' : kv v 2 ∈ lattice v := AddSubgroup.subset_closure (Set.mem_range_self 2)
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact add_mem (add_mem (zsmul_mem h0' z0) (zsmul_mem h1' (z1 + slopeB v * z0)))
      (zsmul_mem h2' z2)
  · -- `←`: `mbarPt` is invariant under the lattice
    intro h
    have hx : x' + (x - x') = x := by abel
    rw [← hx]
    exact mbarPt_periodic a v D x' (x - x') h

end Work.Cusp
