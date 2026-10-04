import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Set ContinuousMultilinearMap

/-- The `V →L[ℝ] (ℝ [×m]→L[ℝ] V)` map `z ↦ mkPiRing ℝ (Fin m) z`, i.e. the continuous linear
map sending `z` to the `m`-fold product multilinear map with value `z`. -/
private noncomputable def mkPiRingCLM (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (m : ℕ) :
    V →L[ℝ] (ℝ [×m]→L[ℝ] V) :=
  (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) V : V →L[ℝ] (ℝ [×m]→L[ℝ] V))

/-- The currying identity relating `mkPiRing` on `Fin (m+1)` to `mkPiRing` on `Fin m`:
`(z ↦ mkPiRing ℝ (Fin m) z)` composed with `v ↦ v • z` is the left currying of
`mkPiRing ℝ (Fin (m+1)) z`. -/
private lemma mkPiRingCLM_comp_toSpanSingleton {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (z : V) :
    ((mkPiRingCLM V m).comp (ContinuousLinearMap.toSpanSingleton ℝ z))
      = ((ContinuousMultilinearMap.mkPiRing ℝ (Fin (m + 1)) z : ℝ [×(m+1)]→L[ℝ] V)).curryLeft := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousMultilinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousMultilinearMap.curryLeft_apply]
  change (ContinuousMultilinearMap.mkPiRing ℝ (Fin m) (v • z)) w =
    (ContinuousMultilinearMap.mkPiRing ℝ (Fin (m + 1)) z) (Fin.cons v w)
  rw [ContinuousMultilinearMap.mkPiRing_apply, ContinuousMultilinearMap.mkPiRing_apply,
    Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ, smul_smul, mul_comm]

theorem hasFTaylorSeriesUpToOn_tower
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {I : Set ℝ} (hI : Convex ℝ I)
    {c : ℕ → ℝ → V} (h : ∀ j, ∀ t ∈ I, HasDerivWithinAt (c j) (c (j + 1) t) I t) (N : ℕ) :
    HasFTaylorSeriesUpToOn (N : WithTop ℕ∞) (c 0)
      (fun t k => ContinuousMultilinearMap.mkPiRing ℝ (Fin k) (c k t)) I := by
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    simp only [ContinuousMultilinearMap.curry0_apply, ContinuousMultilinearMap.mkPiRing_apply]
    simp
  · intro m _ x hx
    show HasFDerivWithinAt (fun y => ContinuousMultilinearMap.mkPiRing ℝ (Fin m) (c m y))
      ((ContinuousMultilinearMap.mkPiRing ℝ (Fin (m + 1)) (c (m + 1) x) :
        ℝ [×(m+1)]→L[ℝ] V)).curryLeft I x
    rw [← mkPiRingCLM_comp_toSpanSingleton m (c (m + 1) x)]
    exact (ContinuousLinearMap.hasFDerivWithinAt (mkPiRingCLM V m)
        (s := Set.univ) (x := c m x)).comp x ((h m x hx).hasFDerivWithinAt)
      (Set.mapsTo_univ _ _)
  · intro m _
    show ContinuousOn (fun y => ContinuousMultilinearMap.mkPiRing ℝ (Fin m) (c m y)) I
    exact ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) V).continuous.comp_continuousOn
      (fun t ht => (h m t ht).continuousWithinAt))

end Work.Diff.STE.flat
