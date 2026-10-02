import Mathlib
import Submission.Work.Whitney.TCMProdDefs
import Submission.Work.Whitney.Cutoff
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupLeibniz
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general
import Submission.Work.Thom.Pair
import Submission.Work.Whitney.RankTwo.Cochains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cap map, the clever lift and the cap-pullback lemma (definitions of the rank-one crux)

This module carries the *definitions and point-level inputs* of the "clever lift" route to the
rank-one case of the model product formula:

* `capX Y p : Y × D^p → tcmX Y p 1`, the upper cap (the graph of the upper hemisphere);
* `lastCoord Y p x`, the last coordinate of a point of `tcmX Y p 1`;
* `gammaSharp Y p`, the `0`-cochain that is `1` where `lastCoord >= 0` and `0` elsewhere — the
  "clever lift" of the transgression input of `Mpun 1 Y`, whose cap-pullback is constantly `1`;
* `cap_pullback_cup_gammaSharp`: `capX^*(α ⌣ gammaSharp) = capX^*α`.

They are placed in their own module (rather than in `rankOne_cup_model.lean`) because a number of
files in the assembly — `capCycle`, `capTransferPrep`, `cupSide_eval`, `Signed/CapBasics`, … — need
`capX`/`gammaSharp` but must NOT import the target module, which would create an import cycle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.Whitney

open Work.Thom
open Work.Cohomology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

noncomputable section

variable {R : Type} [CommRing R]


/-- `TopCat.toSSet` acts on simplices by postcomposition (a `rfl` in Mathlib). -/
theorem toSSet_map_apply {X Z : TopCat} (g : X ⟶ Z) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n) :
    (TopCat.toSSetObjEquivOld Z n) ((TopCat.toSSet.map g).app n x) =
      g.hom.comp ((TopCat.toSSetObjEquivOld X n) x) := rfl

/-- The last coordinate of a point of `tcmX Y p 1`, in the coordinates of `tcmSumLin p 1`. -/
def lastCoord (Y : Type) [TopologicalSpace Y] (p : ℕ) (x : tcmX Y p 1) : ℝ :=
  (tcmSumLin p 1 x.2).ofLp (Fin.last p)

/-- The cap map into `tcmX Y p 1`: `(y,u) |-> (y, tcmSumLin.symm (capMap p u))`. -/
def capX (Y : Type) [TopologicalSpace Y] (p : ℕ) : C(Y × MBall p, tcmX Y p 1) where
  toFun q := (q.1, (tcmSumLin p 1).symm (capMap p q.2.1))
  continuous_toFun := by
    refine continuous_fst.prodMk ?_
    exact ((tcmSumLin p 1).symm.continuous.comp
      ((continuous_capMap p).comp (continuous_subtype_val.comp continuous_snd)))

@[simp] theorem capX_apply (Y : Type) [TopologicalSpace Y] (p : ℕ) (q : Y × MBall p) :
    capX Y p q = (q.1, (tcmSumLin p 1).symm (capMap p q.2.1)) := rfl

/-- **The core of the clever lift**: the last coordinate of a cap-image point is
`sqrt (1 - ||u||^2) >= 0`. -/
theorem lastCoord_capX (Y : Type) [TopologicalSpace Y] (p : ℕ) (q : Y × MBall p) :
    lastCoord Y p (capX Y p q) = Real.sqrt (1 - ‖q.2.1‖ ^ 2) := by
  simp only [lastCoord, capX_apply, ContinuousLinearEquiv.apply_symm_apply, capMap_last]

theorem lastCoord_capX_nonneg (Y : Type) [TopologicalSpace Y] (p : ℕ) (q : Y × MBall p) :
    0 ≤ lastCoord Y p (capX Y p q) := by
  rw [lastCoord_capX]; exact Real.sqrt_nonneg _

/-- The **cleverly chosen lift**: the absolute 0-cochain on `tcmX Y p 1` that is `1` where the last
coordinate is `>= 0`, and `0` elsewhere.  Its restriction to the `C = {v != 0}`-part is the
indicator of `{v > 0}`, so it is a legitimate lift of the transgression input of `Mpun 1 Y`. -/
def gammaSharp (Y : Type) [TopologicalSpace Y] (p : ℕ) :
    Cochain ℤ (ssB (tcmX Y p 1)) 0 :=
  RankTwo.cochainOf (ssB (tcmX Y p 1)) 0
    (fun σ => if 0 ≤ lastCoord Y p
        ((TopCat.toSSetObjEquivOld (TopCat.of (tcmX Y p 1)) (Opposite.op (SimplexCategory.mk 0))) σ
          default) then 1 else 0)

@[simp] theorem genEval_gammaSharp (Y : Type) [TopologicalSpace Y] (p : ℕ)
    (σ : (ssB (tcmX Y p 1)) _⦋0⦌) :
    genEval ℤ (ssB (tcmX Y p 1)) (gammaSharp Y p) σ
      = if 0 ≤ lastCoord Y p
          ((TopCat.toSSetObjEquivOld (TopCat.of (tcmX Y p 1))
            (Opposite.op (SimplexCategory.mk 0))) σ default) then 1 else 0 :=
  RankTwo.genEval_cochainOf _ _ _ _

/-- **Piece (1), the key point-level input**: every vertex of the cap image has `gammaSharp = 1`. -/
theorem genEval_gammaSharp_capX (Y : Type) [TopologicalSpace Y] (p : ℕ)
    (q : Y × MBall p) :
    (if 0 ≤ lastCoord Y p (capX Y p q) then (1 : ℤ) else 0) = 1 :=
  if_pos (lastCoord_capX_nonneg Y p q)

/-- **Piece (1)**: the cap-pullback of `gammaSharp` is constantly `1`. -/
theorem genEval_cap_pullback_gammaSharp (Y : Type) [TopologicalSpace Y] (p : ℕ)
    (σ : (ssB (Y × MBall p)) _⦋0⦌) :
    genEval ℤ (ssB (Y × MBall p))
      (((SSet.chainComplexMap
          (TopCat.toSSet.map (TopCat.ofHom (capX Y p))) (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap
        (gammaSharp Y p)) σ = 1 := by
  rw [genEval_dualMap, genEval_gammaSharp]
  rw [toSSet_map_apply]
  exact genEval_gammaSharp_capX Y p
    ((TopCat.toSSetObjEquivOld (TopCat.of (Y × MBall p))
      (Opposite.op (SimplexCategory.mk 0))) σ default)

/-- **Piece (1), final step**: the cap-pullback of `cup alpha gammaSharp` is the cap-pullback of
`alpha`.  This is the whole content of the "clever lift": no orientation comparison occurs.

(The degree `m + 0` on the left is definitionally `m`; it is written out so that the statement of
`cupNatural` matches syntactically.) -/
theorem cap_pullback_cup_gammaSharp (Y : Type) [TopologicalSpace Y] (p : ℕ) {m : ℕ}
    (α : Cochain ℤ (ssB (tcmX Y p 1)) m) :
    ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (capX Y p)))
        (ModuleCat.of ℤ ℤ)).f (m + 0)).hom.dualMap
      (Work.Cohomology.cup ℤ (ssB (tcmX Y p 1)) α (gammaSharp Y p))
    = ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (capX Y p)))
        (ModuleCat.of ℤ ℤ)).f m).hom.dualMap α := by
  rw [← Work.Cohomology.cupNatural ℤ (TopCat.toSSet.map (TopCat.ofHom (capX Y p))) α
    (gammaSharp Y p)]
  exact Work.Cohomology.cup_one_right (R := ℤ) (ssB (Y × MBall p)) _ _
    (genEval_cap_pullback_gammaSharp Y p)





end

end Work.Whitney
