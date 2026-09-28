import Mathlib
import Submission.Work.HP.BCS.Transport

namespace Work.HP.BCS

-- The volume of the two-cone slice, transported to coordinates: the `k`-dimensional volume of
-- `span_ℝ L ∩ B(1) ∩ 𝒞_v^{(γ)} ∩ 𝒞_w^{(γ)}` equals the Lebesgue volume in `ℝ^k` of the corresponding
-- cone slice, transported by the isometry `isomSpan L b` (with `coneVec L b v` the Riesz vector of
-- the functional `y ↦ ⟪toE v, e.symm y⟫`).
--
-- ROUTE.  `Work.HP.coneSliceVol L v w γ = Work.HP.subVol (Work.HP.spanE L) {t | …}` is the volume
-- of a subset of the subtype `spanE L`; `Work.HP.BCS.isomSpan L b : spanE L ≃ₗᵢ[ℝ] ℝ^k` is an
-- isometry, hence measure preserving (`LinearIsometryEquiv.measurePreserving`, and
-- `MeasurePreserving.measure_preimage` for the inverse direction).  Transport the two cone
-- conditions with `Work.HP.BCS.inner_coneVec` (`inner ℝ (coneVec L b v) y = inner ℝ (toE v) (e.symm y)`)
-- and ‖·‖-preservation, and use `Work.HP.BCS.coeffMap_range`/`Work.HP.BCS.finrank_spanE` to identify
-- `spanE L` with the range of the coefficient map.
theorem coneSliceVol_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) (v w : ι → ℝ) (γ : ℝ) :
    Work.HP.coneSliceVol L v w γ
      = (MeasureTheory.volume {y : EuclideanSpace ℝ (Fin k) | ‖y‖ ≤ 1 ∧
            y ∈ Work.HP.BCS.coneSet (Work.HP.BCS.coneVec L b v) (‖Work.HP.toE v‖ / (2 * γ)) ∧
            y ∈ Work.HP.BCS.coneSet (Work.HP.BCS.coneVec L b w) (‖Work.HP.toE w‖ / (2 * γ))}).toReal := by
  rw [Work.HP.coneSliceVol, Work.HP.subVol]
  simp only [Set.mem_ofPred_eq]
  -- the target set in coordinates of `spanE L`, and the target set in `ℝ^k`
  set T : Set (EuclideanSpace ℝ (Fin k)) :=
    {y | ‖y‖ ≤ 1 ∧
          y ∈ Work.HP.BCS.coneSet (Work.HP.BCS.coneVec L b v) (‖Work.HP.toE v‖ / (2 * γ)) ∧
          y ∈ Work.HP.BCS.coneSet (Work.HP.BCS.coneVec L b w) (‖Work.HP.toE w‖ / (2 * γ))} with hT
  set S : Set (Work.HP.spanE L) :=
    {t | |inner ℝ (Work.HP.toE v) ↑t| ≤ ‖Work.HP.toE v‖ * ‖↑t‖ / (2 * γ) ∧
         |inner ℝ (Work.HP.toE w) ↑t| ≤ ‖Work.HP.toE w‖ * ‖↑t‖ / (2 * γ) ∧ ‖↑t‖ ≤ 1} with hS
  change (MeasureTheory.volume S).toReal = (MeasureTheory.volume T).toReal
  -- the isometry `isomSpan L b` identifies `S` with the preimage of `T`, because it preserves norms
  -- and turns `⟪toE v, ·⟫` into `⟪coneVec L b v, ·⟫`.
  have hpre : S = ⇑(Work.HP.BCS.isomSpan L b) ⁻¹' T := by
    ext t
    rw [hS, hT]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [Work.HP.BCS.coneSet, Work.HP.BCS.coneSet]
    simp only [Set.mem_ofPred_eq]
    rw [Work.HP.BCS.inner_coneVec L b v (Work.HP.BCS.isomSpan L b t),
        Work.HP.BCS.inner_coneVec L b w (Work.HP.BCS.isomSpan L b t)]
    simp only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.norm_map,
      div_mul_eq_mul_div, Submodule.coe_norm]
    tauto
  -- `T` is closed, hence null-measurable
  have hA : MeasurableSet {y : EuclideanSpace ℝ (Fin k) | ‖y‖ ≤ 1} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hB : MeasurableSet
      (Work.HP.BCS.coneSet (Work.HP.BCS.coneVec L b v) (‖Work.HP.toE v‖ / (2 * γ))) := by
    rw [Work.HP.BCS.coneSet]
    exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hC : MeasurableSet
      (Work.HP.BCS.coneSet (Work.HP.BCS.coneVec L b w) (‖Work.HP.toE w‖ / (2 * γ))) := by
    rw [Work.HP.BCS.coneSet]
    exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hTmeas : MeasurableSet T := by
    rw [hT]
    exact hA.inter (hB.inter hC)
  -- measure preservation of the isometry
  have hvol : MeasureTheory.volume S = MeasureTheory.volume T := by
    rw [hpre]
    exact MeasureTheory.MeasurePreserving.measure_preimage
      (LinearIsometryEquiv.measurePreserving (Work.HP.BCS.isomSpan L b)) hTmeas.nullMeasurableSet
  rw [hvol]

end Work.HP.BCS
