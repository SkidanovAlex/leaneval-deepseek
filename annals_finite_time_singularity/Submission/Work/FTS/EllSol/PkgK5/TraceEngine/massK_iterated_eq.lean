import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open MeasureTheory Set Filter
open scoped Real Topology

/- Fubini/monotone-set facts for the joint integrand `G(z,θ) = w z ^ 2 * (∂_θψ z θ) ^ 2 * thEta θ`
on the box `S = [cA k, cB k] × Iθ`, given the integrability hypothesis `hE` of
`Work.FTS.EllSol.PkgK5.TraceEngine.massK_tendsto_zero`.

Route: `Measure.volume_eq_prod ℝ ℝ` + `Measure.prod_restrict` rewrite `hE` into integrability for
the product measure on `s ×ˢ Iθ`; `MeasureTheory.setIntegral_prod` gives the identity of the first
conjunct (with `MeasureTheory.integral_const_mul` to pull `w z ^ 2` out of the inner integral);
`MeasureTheory.setIntegral_nonneg` (using `thEta ≥ 0` on `Iθ`, since `0 ≤ sin(2θ)` there) gives the
second; `MeasureTheory.Integrable.integral_prod_left` gives the third; the fourth and fifth are the
same argument with `IntegrableOn.mono_set` (`Ioo 0 θ ⊆ Iθ`, resp. `Ioo θ (π/2) ⊆ Iθ`). -/
theorem massK_iterated_eq {k : ℕ} {ψ : ℝ → ℝ → ℝ}
    (hE : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 *
        (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
      (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) ×ˢ Work.Spaces.Iθ)) :
    (∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
        (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iθ,
          (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s
      = ∫ p in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
    ∧ 0 ≤ ∫ p in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2
    ∧ MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iθ,
          (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s)
        (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k)))
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ∫ s in Set.Ioo 0 θ,
            (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s)
          (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))))
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ∫ s in Set.Ioo θ (Real.pi / 2),
            (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s)
          (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k)))) := by
  -- Abbreviate the box, the angular interval and the joint integrand.
  set s : Set ℝ := Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) with hs_def
  set I : Set ℝ := Work.Spaces.Iθ with hI_def
  set G : ℝ × ℝ → ℝ := fun p => (Work.Spaces.w p.1) ^ 2 *
    (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2 with hG_def
  -- `hE` is integrability for the product measure `(volume.restrict s).prod (volume.restrict I)`.
  have hE' : MeasureTheory.Integrable G
      ((MeasureTheory.volume.restrict s).prod (MeasureTheory.volume.restrict I)) := by
    rw [Measure.prod_restrict]
    exact hE
  -- The inner `θ`-integral with the constant `(w z)²` pulled out.
  have hinner : ∀ z, ∫ θ, G (z, θ) ∂(MeasureTheory.volume.restrict I) =
      (Work.Spaces.w z) ^ 2 * ∫ θ, ((Work.Spaces.pth ψ z θ) ^ 2 *
        Work.FTS.EllipticEst.thEta θ) ∂(MeasureTheory.volume.restrict I) := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the iterated identity, by Fubini
    rw [show (∫ p in s ×ˢ I, G p) = ∫ p, G p ∂((MeasureTheory.volume.restrict s).prod
        (MeasureTheory.volume.restrict I)) from by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
      rw [← Measure.prod_restrict]]
    rw [MeasureTheory.integral_prod G hE']
    exact (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)).symm
  · -- (2) nonnegativity of the joint integral
    refine MeasureTheory.setIntegral_nonneg ?_ ?_
    · rw [hs_def, hI_def, Work.Spaces.Iθ]
      exact measurableSet_Icc.prod measurableSet_Icc
    · intro p hp
      obtain ⟨hz, hθ⟩ := hp
      have hθnn := Work.FTS.EllipticEst.thEta_nonneg (θ := p.2) hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hθnn
  · -- (3) integrability of the `z`-slice mass over `s`
    have h1 : MeasureTheory.Integrable (fun z => ∫ θ, G (z, θ) ∂(MeasureTheory.volume.restrict I))
        (MeasureTheory.volume.restrict s) := hE'.integral_prod_left
    exact h1.congr (Filter.Eventually.of_forall hinner)
  · -- (4) the same over the sub-interval `Ioo 0 θ ⊆ Iθ`
    intro θ hθ
    have hsub : Set.Ioo 0 θ ⊆ I := by
      rw [hI_def, Work.Spaces.Iθ]
      intro x hx
      exact ⟨hx.1.le, hx.2.le.trans hθ.2.le⟩
    have hmono : MeasureTheory.IntegrableOn G (s ×ˢ Set.Ioo 0 θ) MeasureTheory.volume :=
      hE.mono_set (Set.prod_mono Subset.rfl hsub)
    have h' : MeasureTheory.Integrable G ((MeasureTheory.volume.restrict s).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 θ))) := by
      rw [Measure.prod_restrict]
      exact hmono
    have h2 := h'.integral_prod_left
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    show ∫ y in Set.Ioo 0 θ, G (z, y) = (Work.Spaces.w z) ^ 2 * ∫ s in Set.Ioo 0 θ,
      (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  · -- (5) the same over the sub-interval `Ioo θ (π/2) ⊆ Iθ`
    intro θ hθ
    have hsub : Set.Ioo θ (Real.pi / 2) ⊆ I := by
      rw [hI_def, Work.Spaces.Iθ]
      intro x hx
      exact ⟨hθ.1.le.trans hx.1.le, hx.2.le⟩
    have hmono : MeasureTheory.IntegrableOn G (s ×ˢ Set.Ioo θ (Real.pi / 2)) MeasureTheory.volume :=
      hE.mono_set (Set.prod_mono Subset.rfl hsub)
    have h' : MeasureTheory.Integrable G ((MeasureTheory.volume.restrict s).prod
        (MeasureTheory.volume.restrict (Set.Ioo θ (Real.pi / 2)))) := by
      rw [Measure.prod_restrict]
      exact hmono
    have h2 := h'.integral_prod_left
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    show ∫ y in Set.Ioo θ (Real.pi / 2), G (z, y) = (Work.Spaces.w z) ^ 2 * ∫ s in
      Set.Ioo θ (Real.pi / 2), (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

end Work.FTS.EllSol.PkgK5.TraceEngine
