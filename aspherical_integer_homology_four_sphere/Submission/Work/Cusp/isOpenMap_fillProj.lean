/-
# Openness of the cover projection `fillProj` onto a filling piece

`Work.Cusp.fillProj a v tor` is the map

  `{z : E2 × E2 // ‖z.1‖∞ < 1} → SquarePt × T_v`,  `(p, y) ↦ (p, tor.symm (y mod ℤ²))`

of the cover of the `v`-th filling piece onto the filling piece itself.  It is the product of

* the (open) inclusion `{p : E2 | ‖p‖∞ < 1} → [-1,1]²`, which is an open embedding because
  `‖·‖∞ < 1` is an open condition and `‖p‖∞ < 1` implies `p ∈ [-1,1]²`, and of
* the quotient map `E2 → T_v`, `y ↦ tor.symm (y mod ℤ²)`, which is open as the quotient map of the
  group `ℤ²` acting on `ℝ²` by homeomorphisms (here: a product of two copies of `ℝ → ℝ/ℤ`).

This file proves the openness (`isOpenMap_fillProj`), which is the "covering-map wedge" input of the
polar and core charts on `M̂`.

The auxiliary statements are stated with the sup norm `Work.Cusp.nrm` (which is *definitionally* the
`Work.Space.nrm` of the assembled space) and with `E2 = EuclideanSpace ℝ (Fin 2)`.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.MChartAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-! ### The pieces of `fillProj` -/

/-- **The domain of `fillProj` splits as a product.**  The points of `E2 × E2` whose first
coordinate has sup norm `< 1` are the same as the points of `{p | ‖p‖∞ < 1} × E2`. -/
def fillProj_domHomeo :
    ({z : E2 × E2 // nrm z.1 < 1}) ≃ₜ ({p : E2 // nrm p < 1} × E2) where
  toFun z := (⟨z.1.1, z.2⟩, z.1.2)
  invFun q := ⟨(q.1.1, q.2), q.1.2⟩
  left_inv z := by ext <;> rfl
  right_inv q := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The open inclusion of the layer coordinates into the square.**  The map
`{p : E2 | ‖p‖∞ < 1} → [-1,1]²` is open: it is the restriction of the identity to the open set
`‖·‖∞ < 1`, whose image is the open subset `‖·‖∞ < 1` of the square. -/
theorem fillProj_sqPtOf_isOpenMap :
    IsOpenMap (fun p : {p : E2 // nrm p < 1} =>
      (⟨p.1, mem_sq_of_nrm_lt_one p.2⟩ : Work.Space.SquarePt)) :=
  IsOpenMap.subtype_map IsOpenMap.id (isOpen_lt Work.Space.continuous_nrm continuous_const)
    (fun _ hx => mem_sq_of_nrm_lt_one hx)

/-- **The quotient map to the additive circle is open**: `ℝ → AddCircle 1 = ℝ ⧸ ℤ·1` is the
quotient by the (normal, discrete) subgroup `ℤ·1 ⊆ ℝ`, hence an open map. -/
theorem fillProj_addCircleCoe_isOpenMap :
    IsOpenMap (fun x : ℝ => (x : AddCircle (1 : ℝ))) := by
  simpa using (QuotientAddGroup.isOpenMap_coe (G := ℝ) (N := AddSubgroup.zmultiples (1 : ℝ)))

/-- **The quotient map `E2 → (ℝ/ℤ)²` of the two torus coordinates is open.**  It is the product of
the two open quotient maps `ℝ → AddCircle 1`. -/
theorem fillProj_coord_isOpenMap :
    IsOpenMap (fun y : E2 => fun i : Fin 2 => ((y i : ℝ) : AddCircle (1 : ℝ))) := by
  have hpi : IsOpenMap (Pi.map (fun _ : Fin 2 => fun x : ℝ => (x : AddCircle (1 : ℝ)))) :=
    IsOpenMap.piMap (fun _ => fillProj_addCircleCoe_isOpenMap)
      (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)
  have h2 := hpi.comp (Homeomorph.isOpenMap (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)))
  have heq : (Pi.map (fun _ : Fin 2 => fun x : ℝ => (x : AddCircle (1 : ℝ)))) ∘
      (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ))
      = fun y : E2 => fun i : Fin 2 => ((y i : ℝ) : AddCircle (1 : ℝ)) := by
    funext y i
    rw [Function.comp_apply, Pi.map_apply]
    exact congrArg (fun z : ℝ => (z : AddCircle (1 : ℝ)))
      (show ((PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)) y) i = y.ofLp i from rfl)
  rwa [heq] at h2

/-- **The quotient map to the torus factor `T_v` is open**, in the form in which `fillProj` uses
it: reduce the real torus coordinates modulo `ℤ²` and transport along the homeomorphism `tor`. -/
theorem fillProj_torus_isOpenMap (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) :
    IsOpenMap (fun y : E2 => tor.symm (fun i : Fin 2 => ((y i : ℝ) : AddCircle (1 : ℝ)))) :=
  (Homeomorph.isOpenMap tor.symm).comp fillProj_coord_isOpenMap

/-- **`fillProj` is a composite of open maps**: the domain homeomorphism `fillProj_domHomeo`, the
product of the inclusion of the layer coordinate (`fillProj_sqPtOf_isOpenMap`) with the quotient map
of the torus coordinates (`fillProj_torus_isOpenMap`). -/
theorem fillProj_eq_comp (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) :
    fillProj a v tor =
      Prod.map (fun p : {p : E2 // nrm p < 1} =>
          (⟨p.1, mem_sq_of_nrm_lt_one p.2⟩ : Work.Space.SquarePt)) id ∘
        (Prod.map id
            (fun y : E2 => tor.symm (fun i : Fin 2 => ((y i : ℝ) : AddCircle (1 : ℝ)))) ∘
          fillProj_domHomeo) :=
  rfl

/-- **The projection of the cover of a filling piece onto the filling piece is an open map.** -/
theorem isOpenMap_fillProj (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) :
    IsOpenMap (fillProj a v tor) := by
  rw [fillProj_eq_comp a v tor]
  exact (fillProj_sqPtOf_isOpenMap.prodMap IsOpenMap.id).comp
    ((IsOpenMap.id.prodMap (fillProj_torus_isOpenMap a v tor)).comp
      (Homeomorph.isOpenMap fillProj_domHomeo))

end Work.Cusp
