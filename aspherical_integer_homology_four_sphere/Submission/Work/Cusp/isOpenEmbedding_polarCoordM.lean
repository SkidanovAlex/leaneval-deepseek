/-
# The `(c,k)`-th polar chart of `M̂` is an open embedding

`polarCoordM a v tor c k W` (`Work.Cusp.Assembly`) is the coordinate inclusion of the `(c,k)`-th
polar chart of the `v`-th filling piece into the assembled space `M̂`: it sends a point
`q = (r,θ,w₁,w₂)` of the source `polarBoxSect v c k W` to the point of the `v`-th filling piece
`W_v = SquarePt × T_v` with layer coordinates `cuspInvInner v q` (the inverse of the polar chart) and
torus coordinates `tor.symm (y mod ℤ²)`, included into `M̂` by `incW v`.

`IsOpenEmbedding (polarCoordM a v tor c k W)` is the statement that this chart really is a
homeomorphism onto an open subset of `M̂`.  It factors as

  `polarCoordM a v tor c k W = J ∘ P ∘ S`

where

* `S : polarBoxSect → {z : E2 × E2 // ‖z.1‖∞ < 1}`, `q ↦ ⟨cuspInvInner v q, ·⟩` is the inverse of
  the polar chart on the chart box, an open embedding (`isOpenEmbedding_cuspInvInner_polarBoxSect`),
  whose range is `polarSourceS`;
* `P` is the **cover projection** `fillProj a v tor`, corestricted to the interior of the filling
  piece `fillInterior a v` (`MChartAux`); it is open (`isOpenMap_fillProj`, `IsOpenMap.codRestrict`)
  and continuous (`continuous_fillProj`);
* `J : (fillInterior a v) → M̂` is the inclusion `incW v` of the interior of the filling piece, an
  open embedding (`isOpenEmbedding_incW_interior`).

Composition of open maps is open, and the composite is injective on the chart source by the
hypothesis `hsec`: the section `W` of the cover `ℝ² → (ℝ/ℤ)²` in the `w`-coordinates makes the
`y`-coordinates of the chart injective.  Hence `IsOpenEmbedding` follows from
`IsOpenEmbedding.of_continuous_injective_isOpenMap`.

The injectivity is where `hsec` enters: two points of the source give the same point of `M̂` only if
their `cuspInvInner`-images agree (by `incW_injective`), the `y`-image agreeing in `(ℝ/ℤ)²`; the
`w`-coordinates of these `y` lie in `W` (`wOf_invY`), so `hsec` gives equality of the `y`, and then
the round trip `ThetaPolarS_cuspInvInner` (the `uqOf v q - c ∈ [0,1)` conjunct of `polarBoxSect`
kills the periodic ambiguity) gives equality of the two points of the source.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.MChartAux
import Submission.Work.Cusp.polarBoxSect_aux
import Submission.Work.Cusp.isOpenMap_fillProj
import Submission.Work.Cusp.isOpenEmbedding_incW_interior
import Submission.Work.Cusp.isOpenEmbedding_cuspInvInner_polarBoxSect

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Real InnerProductSpace

namespace Work.Cusp

/-- **The cover projection of a filling piece is continuous** (the domain homeomorphism, the open
inclusion of the layer coordinate into the square, and the quotient map of the torus coordinates). -/
theorem continuous_fillProj (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) :
    Continuous (fillProj a v tor) := by
  unfold fillProj sqPtOf
  fun_prop

theorem isOpenEmbedding_polarCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Topology.IsOpenEmbedding (polarCoordM a v tor c k W) := by
  -- the three factors of the chart
  have hnrm : ∀ q : {q : E4 // q ∈ polarBoxSect v c k W}, nrm (cuspInvInner v q.1).1 < 1 :=
    fun q => nrm_cuspInvInner_lt_one_polarBoxSect v c k W q.1 q.2
  let S : {q : E4 // q ∈ polarBoxSect v c k W} → {z : E2 × E2 // nrm z.1 < 1} :=
    fun q => ⟨cuspInvInner v q.1, hnrm q⟩
  have hmem : ∀ z : {z : E2 × E2 // nrm z.1 < 1}, fillProj a v tor z ∈ fillInterior a v :=
    fun z => by
      have h : nrm z.1.1 < 1 := z.2
      exact h
  let P : {z : E2 × E2 // nrm z.1 < 1} → (fillInterior a v) :=
    Set.codRestrict (fillProj a v tor) (fillInterior a v) hmem
  let J : (fillInterior a v) → a.Mhat := fun p => a.incW v p.1
  let G : {q : E4 // q ∈ polarBoxSect v c k W} → a.Mhat := J ∘ P ∘ S
  have hFG : polarCoordM a v tor c k W = G := rfl
  rw [hFG]
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · -- continuity
    have hJ : Continuous J := (a.continuous_incW v).comp continuous_subtype_val
    have hP : Continuous P := Continuous.codRestrict (continuous_fillProj a v tor) hmem
    have hS : Continuous S :=
      Continuous.subtype_mk ((continuous_cuspInvInner v).comp continuous_subtype_val) hnrm
    exact hJ.comp (hP.comp hS)
  · -- injectivity
    have hinj : Function.Injective (polarCoordM a v tor c k W) := by
      intro q q' h
      have hw := a.incW_injective v h
      have hpq : (cuspInvInner v q.1).1 = (cuspInvInner v q'.1).1 :=
        Subtype.ext_iff.mp (Prod.ext_iff.mp hw).1
      have hcls : ∀ i, (((cuspInvInner v q.1).2 i : ℝ) : AddCircle (1 : ℝ))
          = (((cuspInvInner v q'.1).2 i : ℝ) : AddCircle (1 : ℝ)) := by
        have h2 := (Prod.ext_iff.mp hw).2
        exact funext_iff.mp (tor.symm.injective h2)
      have hWq : wOf v (cuspInvInner v q.1).2 ∈ W := by
        have h : (cuspInvInner v q.1).2 = invY v (!₂[q.1 2, q.1 3] : E2) := rfl
        rw [h, wOf_invY]; exact q.2.2.1
      have hWq' : wOf v (cuspInvInner v q'.1).2 ∈ W := by
        have h : (cuspInvInner v q'.1).2 = invY v (!₂[q'.1 2, q'.1 3] : E2) := rfl
        rw [h, wOf_invY]; exact q'.2.2.1
      have hy : (cuspInvInner v q.1).2 = (cuspInvInner v q'.1).2 := hsec _ _ hWq hWq' hcls
      have hcinv : cuspInvInner v q.1 = cuspInvInner v q'.1 := Prod.ext hpq hy
      have hT : ThetaPolarS v c (cuspInvInner v q.1).1 (cuspInvInner v q.1).2 = q.1 :=
        ThetaPolarS_cuspInvInner v c q.1 q.2.1 q.2.2.2.2.1
      have hT' : ThetaPolarS v c (cuspInvInner v q'.1).1 (cuspInvInner v q'.1).2 = q'.1 :=
        ThetaPolarS_cuspInvInner v c q'.1 q'.2.1 q'.2.2.2.2.1
      exact Subtype.ext (by rw [← hT, ← hT', hcinv])
    intro q q' h
    exact hinj (by rw [hFG]; exact h)
  · -- openness
    have hJ : IsOpenMap J := (isOpenEmbedding_incW_interior a v).isOpenMap
    have hP : IsOpenMap P := IsOpenMap.codRestrict (isOpenMap_fillProj a v tor) hmem
    have hS : IsOpenMap S :=
      IsOpenMap.subtype_mk
        ((isOpenEmbedding_cuspInvInner_polarBoxSect v c k W hW).isOpenMap) hnrm
    exact hJ.comp (hP.comp hS)

end Work.Cusp
