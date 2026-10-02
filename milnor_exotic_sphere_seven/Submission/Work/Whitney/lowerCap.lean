import Mathlib
import Submission.Work.Thom.ModelGeometry
import Submission.Work.Whitney.TCMDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The lower cap map

`Work.Thom.capMap n` is the graph of the **upper** hemisphere,
`w ↦ Fin.snoc w.ofLp (√(1-‖w‖²))`.  Its mirror image (same first `n` coordinates, negated last
coordinate) is the graph of the **lower** hemisphere.  This file provides it, together with the one
property that makes the rank-one model product formula's cycle construction work without any
primitive and without any radial parametrisation
(`Submission/Work/Whitney/NOTES_tcmRankOneSusp.md` §20.3):

* on the boundary sphere `mSph n` the two caps **agree**, because `√(1-‖w‖²) = 0` there,

hence for a chain `B` of the ball whose boundary lies in the sphere the difference
`cap_* B - lcap_* B` is a **cycle** on the sphere.

This file contains nothing else; in particular the consumer-facing identity
`capX Y p q = (q.1, tcmSumLin.symm (capMap p q.2.1))` for the *upper* cap of
`Submission/Work/Whitney/rankOne_cup_model.lean` is definitional, so it need not (and cannot, without
an import cycle) be repeated here.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- The **lower cap map**: the graph of the lower hemisphere of the unit sphere of
`EuclideanSpace ℝ (Fin (n+1))` over the unit ball of `EuclideanSpace ℝ (Fin n)`. -/
def lowerCapMap (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) w.ofLp (-(Real.sqrt (1 - ‖w‖ ^ 2))))

theorem lowerCapMap_ofLp (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    (lowerCapMap n w).ofLp
      = Fin.snoc (α := fun _ => ℝ) w.ofLp (-(Real.sqrt (1 - ‖w‖ ^ 2))) :=
  WithLp.ofLp_toLp _ _

@[simp] theorem lowerCapMap_castSucc (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (lowerCapMap n w).ofLp i.castSucc = w.ofLp i := by
  rw [lowerCapMap_ofLp, Fin.snoc_castSucc]

@[simp] theorem lowerCapMap_last (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    (lowerCapMap n w).ofLp (Fin.last n) = -(Real.sqrt (1 - ‖w‖ ^ 2)) := by
  rw [lowerCapMap_ofLp]
  exact Fin.snoc_last (α := fun _ => ℝ) (x := -(Real.sqrt (1 - ‖w‖ ^ 2))) (p := w.ofLp)

/-- The lower cap map is continuous. -/
theorem continuous_lowerCapMap (n : ℕ) : Continuous (lowerCapMap n) := by
  change Continuous fun w : EuclideanSpace ℝ (Fin n) =>
    WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) w.ofLp (-(Real.sqrt (1 - ‖w‖ ^ 2))))
  fun_prop

/-- The lower cap of the ball lies on the sphere. -/
theorem lowerCapMap_mem_mSph (n : ℕ) {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ mBall n) :
    lowerCapMap n w ∈ mSph (n + 1) := by
  have h1 : ‖w‖ ≤ 1 := hw
  have hnn : (0 : ℝ) ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have h1' : ‖lowerCapMap n w‖ ^ 2 = ∑ i, ‖(lowerCapMap n w).ofLp i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  have h2 : ∑ i, ‖(lowerCapMap n w).ofLp i‖ ^ 2
      = ∑ i : Fin n, ‖w.ofLp i‖ ^ 2 + ‖(lowerCapMap n w).ofLp (Fin.last n)‖ ^ 2 := by
    rw [Fin.sum_univ_castSucc (f := fun i => ‖(lowerCapMap n w).ofLp i‖ ^ 2)]
    simp only [lowerCapMap_castSucc]
  have h3 : ∑ i : Fin n, ‖w.ofLp i‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    exact (Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)).symm
  have h4 : ‖(lowerCapMap n w).ofLp (Fin.last n)‖ ^ 2 = 1 - ‖w‖ ^ 2 := by
    rw [lowerCapMap_last, Real.norm_eq_abs, sq_abs, neg_sq]
    exact Real.sq_sqrt hnn
  have h5 : ‖lowerCapMap n w‖ ^ 2 = 1 := by rw [h1', h2, h3, h4]; ring
  show ‖lowerCapMap n w‖ = 1
  nlinarith [norm_nonneg (lowerCapMap n w)]

/-- **The two caps agree on the boundary sphere.** -/
theorem lowerCapMap_eq_capMap_of_mem_mSph (n : ℕ) {w : EuclideanSpace ℝ (Fin n)}
    (hw : w ∈ mSph n) : lowerCapMap n w = capMap n w := by
  have hs : Real.sqrt (1 - ‖w‖ ^ 2) = 0 := by
    rw [hw]
    norm_num
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [lowerCapMap_last, capMap_last, hs, neg_zero]
  · intro j
    rw [lowerCapMap_castSucc, capMap_castSucc]

/-- The lower cap lies in the lower band `mLower n` (its last coordinate is `≤ 0 ≤ 1/2`). -/
theorem lowerCapMap_mem_mLower (n : ℕ) {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ mBall n) :
    lowerCapMap n w ∈ mLower n := by
  refine ⟨lowerCapMap_mem_mSph n hw, ?_⟩
  rw [lowerCapMap_last]
  have : (0 : ℝ) ≤ Real.sqrt (1 - ‖w‖ ^ 2) := Real.sqrt_nonneg _
  linarith

end

end Work.Thom

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- The **lower cap map into the split model total space** `tcmX Y p 1`: the mirror of
`Work.Whitney.capX`, i.e. `(y,u) ↦ (y, tcmSumLin.symm (lowerCapMap p u))`. -/
def lowerCapX (Y : Type) [TopologicalSpace Y] (p : ℕ) : C(Y × MBall p, tcmX Y p 1) where
  toFun q := (q.1, (tcmSumLin p 1).symm (lowerCapMap p q.2.1))
  continuous_toFun := by
    refine continuous_fst.prodMk ?_
    exact ((tcmSumLin p 1).symm.continuous.comp
      ((continuous_lowerCapMap p).comp (continuous_subtype_val.comp continuous_snd)))

@[simp] theorem lowerCapX_apply (Y : Type) [TopologicalSpace Y] (p : ℕ) (q : Y × MBall p) :
    lowerCapX Y p q = (q.1, (tcmSumLin p 1).symm (lowerCapMap p q.2.1)) := rfl

/-- The lower cap sits over the lower band: applying the coordinate identification `tcmF` gives the
point `(y, lowerCapMap p u)` of `Y × MSph (p+1)`, whose fibre coordinate is in `mLower p`. -/
theorem tcmF_lowerCapX (Y : Type) [TopologicalSpace Y] (p : ℕ) (q : Y × MBall p) :
    tcmF Y p 1 (lowerCapX Y p q) = (q.1, lowerCapMap p q.2.1) := by
  simp only [tcmF, ContinuousMap.coe_mk, lowerCapX_apply, tcmSumLin]
  rw [ContinuousLinearEquiv.apply_symm_apply]

end

end Work.Whitney

/-! ## Axiom check -/

#print axioms Work.Thom.lowerCapMap_eq_capMap_of_mem_mSph
#print axioms Work.Thom.lowerCapMap_mem_mLower
#print axioms Work.Whitney.tcmF_lowerCapX
