import Mathlib
import Submission.Work.BNChart.Chart
import Submission.Work.BNChart.sum_smul_fieldMap_canonBasis_mem_L
import Submission.Work.BNChart.sum_smul_fieldMap_canonBasis_ne_zero
import Submission.Work.Charts.iOf_eq_zero_iff_L_eq_bot
import Submission.Work.Charts.mem_L_sub_sum_ptDiv_iff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.BNChart

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open Work.CurveBasics Work.GCBasics Work.Charts

noncomputable section

set_option maxHeartbeats 800000

/-- **A function of `L (pullK C (rochW C))` is regular at a place where `pullK C (rochW C)`
vanishes.**  If `f ∈ L W` then `div f + W ≥ 0` (as `f ≠ 0`, the other case of `mem_L_iff`), and
`W Q = 0` turns this into `ordAt f Q ≥ 0`. -/
theorem ordAt_nonneg_of_mem_L_pullK_rochW_of_apply_eq_zero {K : Type u} [Field K]
    {C : Curve K} {F : Type u} [Field F] [Algebra K F] {f : (C.baseChange F).functionField}
    (hf : f ∈ (C.baseChange F).L (pullK C (rochW C))) (Q : (C.baseChange F).Place)
    (hQ : pullK C (rochW C) Q = 0) : 0 ≤ (C.baseChange F).ordAt f Q := by
  rcases (Curve.mem_L_iff (C.baseChange F)).mp hf with h0 | heff
  · rw [h0, Curve.ordAt, Scheme.ord_zero]
    simp
  · have := heff Q
    simp only [Finsupp.add_apply, Curve.div_apply] at this
    rw [hQ, add_zero] at this
    exact this

/-- **The converse of the Brill–Noether criterion, for pairwise distinct points.**

Here distinctness is genuinely needed: if two of the places `ptPlace (x m)` coincide, the divisor
`D = ∑ m, ptDiv (x m)` has coefficient at least two there, while the bridge only gives
`ord > 0`.

If `D` is non-special (`iOf = 0`) and the evaluation matrix `(s_j(x m))` were singular, there is a
nonzero coefficient vector `c` with `∑ j, c j * s_j(x m) = 0` for every `m`.  The bridge
`Work.BNChart.EvalSectionBridge C` then gives `ord_{ptPlace (x m)} f > 0` for
`f = ∑ j, c j • fieldMap (h_j)`, and — by distinctness of the places and the vanishing of
`pullK C (rochW C)` at the places of the chart
(`Work.BNChart.pullK_rochW_apply_ptPlace_eq_zero`) — the divisor `div f + pullK C (rochW C) - D`
is effective, i.e. `f ∈ L (pullK C (rochW C) - D)`, contradicting `iOf = 0` (which says that
space is `⊥`); and `f ≠ 0` by `Work.BNChart.linearIndependent_fieldMap_canonBasis`. -/
theorem det_ne_zero_of_iOf_eq_zero {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (h : RiemannRoch.Curve.genus C ≠ 0) {F : Type u} [Field F] [Algebra K F]
    (hbridge : Work.BNChart.EvalSectionBridge C)
    (x : Fin ((RiemannRoch.Curve.genus C - 1) + 1) → Work.SpecLin.CurveFPt C F)
    (hinj : Function.Injective fun m => Work.SpecLin.ptPlace (x m))
    (hxU : ∀ m, (x m).left (IsLocalRing.closedPoint F) ∈ Work.BNChart.chartU C)
    (hi : Work.Charts.iOf C (Work.BNChart.rochW C) (∑ m, Work.SpecLin.ptDiv (x m)) = 0) :
    (Matrix.det (Matrix.of (fun j m => Work.Charts.evalSection (x m).left (hxU m)
      (Work.BNChart.chartSection C h j)))) ≠ 0 := by
  classical
  intro hdet
  -- Step 1: singularity of the evaluation matrix gives a nonzero coefficient vector.
  have hdetT : (Matrix.of (fun j m => Charts.evalSection (x m).left (hxU m)
      (chartSection C h j))).transpose.det = 0 := by
    rw [Matrix.det_transpose]
    exact hdet
  obtain ⟨c, hcne, hcmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have hcM : ∀ m, ∑ j, Charts.evalSection (x m).left (hxU m) (chartSection C h j) * c j = 0 := by
    intro m
    have h1 := congrFun hcmul m
    simpa [Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply, dotProduct] using h1
  have hc' : ∀ m, ∑ j, c j * Charts.evalSection (x m).left (hxU m) (chartSection C h j) = 0 := by
    intro m
    rw [← hcM m]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  -- Step 2: the function `f = ∑ j, c j • fieldMap (h_j)`.
  have hfne_sum : (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom
      ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField)) ≠ 0 :=
    sum_smul_fieldMap_canonBasis_ne_zero h c hcne
  have hfmem_sum : (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom
      ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField))
      ∈ (C.baseChange F).L (pullK C (rochW C)) :=
    sum_smul_fieldMap_canonBasis_mem_L h c
  have hreg_sum : ∀ m, 0 ≤ (C.baseChange F).ordAt
      (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom
        ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField))
      (SpecLin.ptPlace (x m)) := fun m =>
    ordAt_nonneg_of_mem_L_pullK_rochW_of_apply_eq_zero hfmem_sum (SpecLin.ptPlace (x m))
      (pullK_rochW_apply_ptPlace_eq_zero C (x m) (hxU m))
  -- Step 3: the bridge, pointwise: `f` vanishes at every `ptPlace (x m)`.
  have hordpos : ∀ m, 0 < (C.baseChange F).ordAt
      (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom
        ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField))
      (SpecLin.ptPlace (x m)) := by
    intro m
    refine (hbridge (n := (RiemannRoch.Curve.genus C - 1) + 1) (Nat.succ_pos _) (x m)
      (fun j => ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField))
      (chartU C) (fun j => chartU_le_regularOpens C h j) (hxU m) c hfne_sum
      (hreg_sum m)).mp ?_
    simpa only [chartSection] using hc' m
  -- Step 4: `iOf = 0` says `L (pullK C (rochW C) - D) = ⊥`.
  have hLbot : (C.baseChange F).L (pullK C (rochW C) - ∑ m, SpecLin.ptDiv (x m)) = ⊥ := by
    have h0 : Charts.iOf C (rochDataPos C h).W (∑ m, SpecLin.ptDiv (x m)) = 0 := by
      rw [rochDataPos_W]
      exact hi
    have h1 := (Charts.iOf_eq_zero_iff_L_eq_bot (C := C) (R := rochDataPos C h) (F := F)
      (∑ m, SpecLin.ptDiv (x m))).mp h0
    simpa only [rochDataPos_W] using h1
  -- Step 5: `f` lies in that Riemann–Roch space.
  have hfL : (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom
      ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField))
      ∈ (C.baseChange F).L (pullK C (rochW C) - ∑ m, SpecLin.ptDiv (x m)) := by
    rw [Charts.mem_L_sub_sum_ptDiv_iff (A := pullK C (rochW C)) x hinj
      (fun m => pullK_rochW_apply_ptPlace_eq_zero C (x m) (hxU m)) hfne_sum hfmem_sum]
    intro m
    have hm := hordpos m
    omega
  -- Step 6: contradiction with `f ≠ 0`.
  have hfbot : (∑ j, c j • (Curve.bcSquare C F).fieldMap.hom
      ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField))
      ∈ (⊥ : Submodule F (C.baseChange F).functionField) := by
    rw [← hLbot]
    exact hfL
  exact hfne_sum ((Submodule.mem_bot F).mp hfbot)

end

end Work.BNChart
