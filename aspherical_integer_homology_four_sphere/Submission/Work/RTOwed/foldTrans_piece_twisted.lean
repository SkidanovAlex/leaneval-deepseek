/-
# The twisted piece formula of a fold transition

`Work.RTOwed.foldTrans_piece` computes the transition of two fold charts at a point `mk y` that
lies in a piece `Dvor i r` of the source class *and* in a piece `Dvor j s` of the target class, with
the **same** lift `y`.  In the atlas of `M̄` the relevant lift of a class is however not always the
same for the two classes: a point of the source of the chart `j` is a class `mk x'` where
`x' = actX γ x` for a group element `γ : Gg` and a lift `x` of the same class in the source of the
chart `i`.  This file proves the corresponding **twisted** formula: for `x ∈ Dvor i r` and
`actX γ x ∈ Dvor j s` (with `mk (actX γ x) = mk x`, i.e. `γ` an identification of the class),

  `foldChart j (mk x) = mobius (transMatG i j r s γ.1) (foldChart i (mk x))`,

where `transMatG i j r s γ.1 = coordPermMat j * (N_F j D_s * diagKR (signVec γ.1)) * (N_F i D_r)⁻¹ *
(coordPermMat i)⁻¹` is the transport matrix of `Work.RTOwed.foldTheta_actTransport`.

The proof is `Work.FoldInst.foldChart_apply` on both sides together with
`Work.RTOwed.foldTheta_actTransport` (the Klein transport `mobiusKlein_act` /
`coordPerm_eq_mobius` computation) — no gluing hypothesis is used.
-/
import Mathlib
import Submission.Work.RTOwed.Defs
import Submission.Work.RTOwed.foldTheta_actTransport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter Matrix
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace Matrix
open Bundle

namespace Work.RTOwed

open Work.FoldInst

/-- The transport matrix of the twisted piece formula: the matrix of
`Work.RTOwed.foldTheta_actTransport`. -/
def transMatG (i j : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (s : Fin (Work.FoldInst.foldCodim j) → Bool) (g : Fin 4 → ZMod 2) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  coordPermMat j
    * ((foldNr j * foldDrR j s * diagKR (signVec g)) * (foldNr i * foldDrR i r)⁻¹)
    * (coordPermMat i)⁻¹

/-- **The twisted piece formula.**  If the class of `x ∈ Dvor i r` has a lift `actX γ x` in the
piece `Dvor j s` of the target class, then the transition of the two fold charts at that class is
the Möbius transformation of `Work.RTOwed.transMatG i j r s γ.1`. -/
theorem foldTrans_piece_twisted (i j : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (s : Fin (Work.FoldInst.foldCodim j) → Bool) (γ : Gg) {x : Xbar}
    (hx : x ∈ Dvor i r) (hxs : actX γ x ∈ Dvor j s) (hrel : mk (actX γ x) = mk x) :
    foldChart j (mk x) = HypModel.mobius (transMatG i j r s γ.1) (foldChart i (mk x)) := by
  have h1 : foldChart j (mk x) = foldTheta j s (actX γ x).2.1 := by
    rw [← hrel, foldChart_apply j s (actX γ x) hxs]
  rw [h1, foldChart_apply i r x hx]
  exact foldTheta_actTransport i j r s γ.1 (Dvor_subset_ball i r hx)

end Work.RTOwed
