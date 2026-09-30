/-
# `BridgeSquare/PlaneFrame.lean` — the degree-`2` fibre identity of the `v`-th cusp torus

**Target** (`Work.BridgeSquare.planeIdentT`, the statement below, unchanged):

  `∃ s ∈ {±1}, ∃ y ∈ C_3(M̄), ∂y = singT v - s • Ψ_M(planeCycleVec v 0)`.

## What the statement says, and why it is true

`singT v = Sing(Fn v)(χ_{T₀} - χ_{T₁})` is the image of the fundamental `2`-cycle of the
`Δ`-model of `T²_v` under the section `Fn v = secT v ≫ secMap0 ≫ cuspMap`
(`CuspSection.lean`).  `planeCycleVec v 0` is the *cellular* `κ_{v,2} ∧ κ_{v,3}` cycle of the
cusp cube structure, which is a boundary of `Gen.mbarCx` (`Gen.planeCycle_bd`), hence
`Ψ_M(planeCycleVec v 0) = ∂(Ψ_M(planeWitVec v 0))` is a boundary
(`PsiM_d_planeWit`).  Because the statement has the sign `s ∈ {±1}` free and the second
term is a boundary, the statement is *equivalent* to

  **`[singT v] = 0` in `H_2(M̄; ℤ)`**,

i.e. to the degree-`2` half of `Work.BridgeSquare.SubtorusNull` (statement **(a)** of
`NOTES_LEAD_aspherical_bridge.md` §2.6): the `κ_{v,2}κ_{v,3}` subtorus of the `v`-th cusp is
null-homologous in `M̄`.

## The geometric proof (design; see `NOTES_SESSION3.md` §3/§6)

Write `z = cuspY v y + cuspH` for the *cube coordinate* of the section
(`Fn_apply`: `Fn v (mk y) = mbarPt v (cuspY v (y) + cuspH)`, `cuspH = (1/2,1/2,1/2)`), and let
`m` be the coordinate axis of the meridian `κ_{v,1}` (the cusps' `κ`'s are axis parallel).  Then

* the section's plane is `z_m = 1/2` (the *middle* of the cube layer) with
  `(z_i,z_j)` ranging over a `2×2` (resp. `4×4`) fundamental square of the fibre lattice;
* `planeCycleVec v 0` is the chain of the *bottom faces* (`u_m = 0`) of the cubes
  (`unit_sq_cell` in `scripts/gen_cusp_loops.py`), i.e. the wall `z_m = 0` (identified with
  `z_m = 1`) over the *unit-square* grid of the cube structure.

The two cycles are homologous through the **slab**

  `Φ(y,t) := mbarPt v (cuspY v y + (1-t) • cuspH)`,  `y ∈ [0,1]²`, `t ∈ [0,1]`,

which for `t = 0` is the section (hence the plane chain), for `t = 1` is the *wall*
on the shifted grid `y₀ ∈ (k+1/2)/n₂`, `y₁ ∈ (l+1/2)/n₃` (whose cells are exactly the cube
structure's wall squares), and whose four side faces cancel because
`cuspY v (y + e_i) - cuspY v y = κ_{v,i+1} ∈ Λ_v` and `mbarPt v` is `Λ_v`-periodic.
(NOTE: the shift is `−cuspH`, not `+cuspH`; with `+t•(1,1,1)` both ends are *mid-planes* and the
boundary of the slab vanishes.  See `NOTES_planeIdentT_session5.md` §1.)

Concretely, the proof is assembled from

1. **the affine framework** (below): vertex families `v : Fin (k+1) → E`, their affine simplices
   `affVN v`, the singular chains `singAff G v`, the boundary formula `singAff_d`, the
   face lemma `affVN_faceVN`, and the periodicity lemma `singAff_translate`;
2. **the plane subdivision**: a `3`-chain `W` of the `(y,t)`-box `[0,1]² × [0,1]`, subordinate to
   the sheared cube regions, with `∂(toSing Ψ W) = singT v - (wall chain)` (the `t=0` faces give
   the *fine* plane chain, which differs from `singT v` by the boundary of a further `3`-chain
   obtained by coning the two triangulations of the plane square — `singT v` is the coarse
   two-triangle chain by `singT_eq`);
3. **the wall = the cellular cycle**: at `t = 1` the fine grid's unit squares are the cube
   structure's `2`-cells, and the barycentric subdivision of each such square matches
   `Ψ_M(1_e)` (`PsiM_f_piSingle_eq_sum`): for every vertex of the subdivision the chart value
   `kleinPt a u` of the cube `a` is the polytope position `posR F` of the corresponding face of
   `Q̄` (finite table), and both sides are affine in `w`, so they agree on the whole simplex;
4. **the cellular algebra**: the wall chain is `Ψ_M (planeCycleVec v 0)` up to the explicit
   cellular boundary `Gen.planeCycle_bd`.


## Status of this file (session 3, L854)

Proved here (sorry-free): the affine-chain framework (`faceVN`, `affVN`, `affVN_apply`,
`wts_succAbove`, `wts_zero`, `affVN_faceVN`, `singAff`, `singAff_d`, `transVN`, `affVN_transVN`,
`singAff_transVN`), and the cusp-lattice periodicity of the ceiling map
(`mbarPt_add_kv`, `cuspY_add_zero/one/single`, the latter two via
`Work.RTOwed.cuspCert.mbarPt_latVec` / `kv_latVec` of `cuspCert/lattice_bridge.lean`).

Remaining (the target `planeIdentT` is still open), in the order of the plan above:

1. `singT_eq_aff` (delegated): `singT v` is the two singular `2`-simplices of the plane triangles
   `(0,0),(1,0),(1,1)` and `(0,0),(0,1),(1,1)` under `y ↦ mbarPtC v (cuspX v 0 y)`, i.e. the
   *coarse* plane chain;
2. the *fine* plane chain (the subdivision at the cube walls, in the shifted coordinates), its
   comparison with the coarse one by the cone identity in the plane, and the slab
   `(y,t) ↦ mbarPt v (cuspY v y + (1-t) • cuspH)` with `singAff_d` + `singAff_transVN`
   (`cuspY_add_single` + `mbarPt_add_kv` give the four side cancellations).  The same work is now
   done in the `AffC`/`toSing` calculus of `PlaneAff.lean` / `PlanePush.lean`
   (see `NOTES_planeIdentT_session5.md` §2–§3);
3. the wall end (`t = 1`): the fine unit squares are the cube structure's `2`-cells
   (`gen_cusp_loops.py`: `unit_sq_cell`), and the barycentric subdivision of each such square
   matches `Ψ_M(1_e)` (`PsiM_f_piSingle_eq_sum`): per subdivision vertex, the chart value
   `kleinPt a u` of the cube `a` equals the polytope position `posR F` of the corresponding face
   of `Q̄` (a finite table, generated), and both sides are affine in `w`;
4. the cellular algebra (`Gen.planeCycle_bd`, `PsiM_d_planeWit`) to replace the wall chain by
   `Ψ_M(planeCycleVec v 0)`, with the sign `s` fixed by the orientations.

-/
import Mathlib
import Submission.Work.BridgeSquare.FibreData
import Submission.Work.BridgeSquare.subtorusBoundaries_of_fibreIdent
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range
import Submission.Work.BridgeSquare.Fn_apply
import Submission.Work.RTOwed.cuspCert.lattice_bridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Convexity

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  Affine chains: vertex families, their affine simplices and their singular chains

For a real normed space `E` (in the application `E` is the cube-coordinate space of a cusp or the
`(y,t)`-space `E3 = ℝ³`) and a vertex family `v : Fin (k+1) → E` we write

* `affVN v : C(Δ^k, E)`, `w ↦ ∑ i, wᵢ • vᵢ`, the affine simplex with vertices `v`;
* `singAff G v = singGen (G ∘ affVN v)`, its image under a continuous `G : C(E, X)`, as a
  singular `k`-chain of `X`;
* `transVN d v`, the family translated by `d`, with the periodicity lemma `singAff_transVN`.

The face of a vertex family is `faceVN i v = v ∘ Fin.succAbove i`; the fundamental compatibility
`affVN_faceVN` identifies the `i`-th face of the affine simplex with the affine simplex of the face
family, and `singAff_d` is the resulting boundary formula.  These are the tools that turn every
chain identity below into a presentation-free combinatorial identity of vertex families. -/

/-- The vertices of the `i`-th face of a vertex family. -/
def faceVN {E : Type*} {k : ℕ} (i : Fin (k+2)) (v : Fin (k+2) → E) : Fin (k+1) → E :=
  fun j => v (Fin.succAbove i j)

/-- **The affine simplex with vertex family `v`**: `w ↦ ∑ i, wᵢ • vᵢ`. -/
noncomputable def affVN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (v : Fin (k+1) → E) : C(StdSimplex ℝ (Fin (k+1)), E) where
  toFun w := ∑ i, (w.weights i : ℝ) • v i
  continuous_toFun := by
    apply continuous_finsetSum
    intro i _
    exact (by fun_prop : Continuous fun w : StdSimplex ℝ (Fin (k+1)) => (w.weights i : ℝ)).smul
      continuous_const

@[simp] theorem affVN_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (v : Fin (k+1) → E) (w : StdSimplex ℝ (Fin (k+1))) :
    affVN v w = ∑ i, (w.weights i : ℝ) • v i := rfl

/-- The weight of the `succAbove i`-th vertex of a pushed-forward family. -/
theorem wts_succAbove {k : ℕ} (i : Fin (k+2)) (w : StdSimplex ℝ (Fin (k+1))) (j : Fin (k+1)) :
    (StdSimplex.map (Fin.succAbove i) w).weights (Fin.succAbove i j) = w.weights j := by
  rw [show (StdSimplex.map (Fin.succAbove i) w).weights
      = Finsupp.mapDomain (Fin.succAbove i) w.weights from rfl]
  exact Finsupp.mapDomain_apply_of_injective (Fin.succAbove_right_injective) w.weights j

/-- The weight of the omitted vertex of a pushed-forward family vanishes. -/
theorem wts_zero {k : ℕ} (i : Fin (k+2)) (w : StdSimplex ℝ (Fin (k+1))) :
    (StdSimplex.map (Fin.succAbove i) w).weights i = 0 := by
  rw [show (StdSimplex.map (Fin.succAbove i) w).weights
      = Finsupp.mapDomain (Fin.succAbove i) w.weights from rfl]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨j, hj⟩; exact Fin.succAbove_ne i j hj)

/-- **The face of an affine simplex is the affine simplex of the face family.** -/
theorem affVN_faceVN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (i : Fin (k+2)) (v : Fin (k+2) → E) (w : StdSimplex ℝ (Fin (k+1))) :
    affVN (faceVN i v) w = affVN v (StdSimplex.map (Fin.succAbove i) w) := by
  simp only [affVN_apply, faceVN]
  rw [← Finset.sum_erase_add Finset.univ
        (fun y => ((StdSimplex.map (Fin.succAbove i) w).weights y : ℝ) • v y)
        (Finset.mem_univ i), wts_zero, zero_smul, add_zero]
  refine Finset.sum_bij (fun (j : Fin (k+1)) (_ : j ∈ Finset.univ) => Fin.succAbove i j) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne i j, Finset.mem_univ _⟩
  · intro a _ b _ hab
    exact Fin.succAbove_right_injective hab
  · intro y hy
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (n := k+1) (x := y) (y := i) (Finset.mem_erase.mp hy).1
    exact ⟨j, Finset.mem_univ _, hj⟩
  · intro a _
    rw [wts_succAbove i w a]

/-- **The singular simplex of an affine vertex family**, pushed through `G`. -/
noncomputable def singAff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : TopCat} {k : ℕ}
    (G : C(E, X)) (v : Fin (k+1) → E) : (Work.Homology.singChain Work.Homology.ZMod X).X k :=
  singGen (G.comp (affVN v))

/-- **The boundary of an affine singular simplex**: `∂ (singAff G v)` is the alternating sum of the
affine singular simplices of the faces of `v`. -/
theorem singAff_d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : TopCat} {n : ℕ}
    (G : C(E, X)) (v : Fin (n+2) → E) :
    (Work.Homology.singChain Work.Homology.ZMod X).d (n+1) n (singAff G v)
      = ∑ i : Fin (n+2), (-1 : ℤ)^(i:ℕ) • singAff G (faceVN i v) := by
  have hδ : ∀ i : Fin (n+2),
      (TopCat.toSSet.obj X).δ i
          ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk (n+1)))).symm
            (G.comp (affVN v)))
        = (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).symm
            (G.comp (affVN (faceVN i v))) := by
    intro i
    apply (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).injective
    ext z
    rw [TopCat.toSSetObjEquiv_δ_apply]
    simpa only [Equiv.apply_symm_apply, ContinuousMap.comp_apply] using
      (congrArg G (affVN_faceVN i v z)).symm
  have hkey := SSet.ιChainComplex_d (X := TopCat.toSSet.obj X) (R := Work.Homology.ZMod)
    ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk (n+1)))).symm (G.comp (affVN v)))
  have h2 := CategoryTheory.ConcreteCategory.congr_hom hkey (1 : ℤ)
  simp only [CategoryTheory.ConcreteCategory.comp_apply] at h2
  simp only [singAff, Work.BridgeSquare.singGen]
  refine h2.trans ?_
  simp only [hδ]
  simp

/-! ## §2  Periodicity of an affine chain under a translational symmetry

If `G` is periodic with period `d` then the affine simplex of a family translated by `d` is the same
singular simplex.  This is what makes the four *side* faces of the slab cancel. -/

/-- The vertex family translated by `d`. -/
def transVN {E : Type*} [AddCommMonoid E] {k : ℕ} (d : E) (v : Fin (k+1) → E) : Fin (k+1) → E :=
  fun j => v j + d

theorem affVN_transVN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (d : E) (v : Fin (k+1) → E) (w : StdSimplex ℝ (Fin (k+1))) :
    affVN (transVN d v) w = affVN v w + d := by
  simp only [affVN_apply, transVN, smul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, w.total_of_fintype, one_smul]

/-- **Periodicity**: if `G (x + d) = G x` for all `x`, then translating a vertex family by `d` does
not change the singular chain. -/
theorem singAff_transVN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : TopCat} {k : ℕ}
    {G : C(E, X)} {d : E} (hG : ∀ x, G (x + d) = G x) (v : Fin (k+1) → E) :
    singAff G (transVN d v) = singAff G v := by
  have h : (G.comp (affVN (transVN d v))) = (G.comp (affVN v)) := by
    ext w
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, affVN_transVN, hG]
  rw [singAff, singAff, h]

/-! ## §3  Periodicity of the ceiling map under the cusp lattice

`mbarPt v` is invariant under the cusp lattice `Λ_v` (`Work.RTOwed.cuspCert.mbarPt_latVec`), hence
in particular under the three generators `κ_{v,i}`.  Since the section's plane is parametrised by
`y ↦ cuspY v y + cuspH` and `cuspY v (y + eᵢ) = cuspY v y + κ_{v,i+1}`, the maps
`y ↦ mbarPt v (cuspY v y + cuspH + t • d)` are ℤ²-periodic in `y`; this is what makes the four
*side* faces of the slab cancel (via `singAff_transVN`). -/

theorem mbarPt_add_kv (v : Fin 5) (i : Fin 3) (x : Work.RTOwed.CuspE3) :
    Work.RTOwed.mbarPt v (x + Work.Cusp.kv v i) = Work.RTOwed.mbarPt v x :=
  Work.RTOwed.cuspCert.mbarPt_latVec v x _ (Work.RTOwed.cuspCert.kv_latVec v i)

/-- `cuspY` is shifted by `κ_{v,2}` under the first unit shift of the `y`-plane. -/
theorem cuspY_add_zero (v : Fin 5) (y : Work.Cusp.E2) :
    Work.Cusp.cuspY v (y + Work.Cusp.ofInt2 (Pi.single 0 1))
      = Work.Cusp.cuspY v y + Work.Cusp.kv v 1 := by
  unfold Work.Cusp.cuspY Work.Cusp.ofInt2 Work.Cusp.lam2 Work.Cusp.lam3
  simp only [PiLp.add_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ (0 : Fin 2)),
    Int.cast_one, Int.cast_zero, add_smul, one_smul, zero_smul]
  abel

/-- `cuspY` is shifted by `κ_{v,3}` under the second unit shift of the `y`-plane. -/
theorem cuspY_add_one (v : Fin 5) (y : Work.Cusp.E2) :
    Work.Cusp.cuspY v (y + Work.Cusp.ofInt2 (Pi.single 1 1))
      = Work.Cusp.cuspY v y + Work.Cusp.kv v 2 := by
  unfold Work.Cusp.cuspY Work.Cusp.ofInt2 Work.Cusp.lam2 Work.Cusp.lam3
  simp only [PiLp.add_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ (1 : Fin 2)),
    Int.cast_one, Int.cast_zero, add_smul, one_smul, zero_smul]
  abel

/-- `cuspY` commutes with the unit shifts of the `y`-plane, by `κ_{v,2}` and `κ_{v,3}`. -/
theorem cuspY_add_single (v : Fin 5) (i : Fin 2) (y : Work.Cusp.E2) :
    Work.Cusp.cuspY v (y + Work.Cusp.ofInt2 (Pi.single i 1))
      = Work.Cusp.cuspY v y + (if i = 0 then Work.Cusp.kv v 1 else Work.Cusp.kv v 2) := by
  fin_cases i
  · simpa using cuspY_add_zero v y
  · simpa using cuspY_add_one v y


end

end Work.BridgeSquare
