/-
# `Work.FTS.EllSol.EllPkgAux.MollAux.aesmE2s`

A.e. strong measurability, on every compact interval `[a,b]` with `a > 0`, of the angular slice
energy

`E2s G w = ∫_{Iθ} (∂_θ² G(w,·))² σ_η`

of a datum `G` which is `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)` (`SmoothOpen G`).

The substance is Fubini-measurability of the Bochner integral of a *jointly* a.e. strongly
measurable function:

* `(w,θ) ↦ (∂_θ²G(w,θ))² σ_η(θ)` is continuous on the open quadrant `Q0`, hence a.e. strongly
  measurable for the planar Lebesgue measure restricted to `Q0`;
* the rectangle `Icc a b ×ˢ Iθ` meets the complement of `Q0` only in the two angular boundary
  lines `θ = 0, π/2` (the radial part is safe because `a > 0`), a null set, so the same holds for
  the product measure `(volume.restrict (Icc a b)).prod (volume.restrict Iθ)`;
* `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` then gives the a.e. strong
  measurability in `w` of the angular integral.

Nothing here is a statement of the target.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.EllPkgAux.MollAux

/-- **Measurability of an angular slice energy.**  If `u` is continuous on the open quadrant,
then `w ↦ ∫_{Iθ} (u w θ)² σ_η(θ)` is a.e. strongly measurable on `[a,b]` for every `0 < a`.

(The only use of the open quadrant is joint a.e. strong measurability of `u` on the product
`(volume.restrict (Icc a b)).prod (volume.restrict Iθ)`, whose underlying set differs from
`Icc a b ×ˢ Ioo 0 (π/2) ⊆ Q0` by a null set.) -/
theorem aesm_sliceEnergy_of_continuousOn {u : ℝ → ℝ → ℝ}
    (hu : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.AEStronglyMeasurable
      (fun w : ℝ => ∫ θ in Work.Spaces.Iθ,
        (u w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
  set F : ℝ × ℝ → ℝ := fun p => (u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2 with hF
  -- `σ_η` is continuous on the open quadrant
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      Work.FTS.EllipticEst.Q0 := by
    simp only [Work.FTS.EllipticEst.thEta]
    exact hsin.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  -- hence so is the integrand, and it is a.e. strongly measurable for the planar measure
  have hFcont : ContinuousOn F Work.FTS.EllipticEst.Q0 := (hu.pow 2).mul hcont2
  have hFaesm : AEStronglyMeasurable F (volume.restrict Work.FTS.EllipticEst.Q0) :=
    hFcont.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- `Icc a b ⊆ Ioi 0`, so the rectangle is inside the open quadrant up to the null angular
  -- boundary lines
  have hsub : Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.FTS.EllipticEst.Q0 :=
    fun p hp => Set.mem_prod.mpr ⟨lt_of_lt_of_le ha hp.1.1, hp.2⟩
  have hFaesm' : AEStronglyMeasurable F
      (volume.restrict (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hFaesm.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hae : (Set.Icc a b : Set ℝ) ×ˢ Work.Spaces.Iθ
      =ᵐ[(volume : Measure (ℝ × ℝ))] Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    refine Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) ?_
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc.symm
  have hprod : AEStronglyMeasurable F
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [Measure.prod_restrict]
    change AEStronglyMeasurable F (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    rw [Measure.restrict_congr_set hae]
    exact hFaesm'
  -- Fubini-measurability of the Bochner integral
  have key : AEStronglyMeasurable
      (fun w : ℝ => ∫ θ, F (w, θ) ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict (Set.Icc a b)) :=
    hprod.integral_prod_right' (ν := volume.restrict Work.Spaces.Iθ)
  have hEq : (fun w : ℝ => ∫ θ in Work.Spaces.Iθ,
        (u w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = fun w : ℝ => ∫ θ, F (w, θ) ∂(volume.restrict Work.Spaces.Iθ) := by
    funext w
    simp only [hF]
  rw [hEq]
  exact key

theorem aesmE2s {G : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.AEStronglyMeasurable (Work.FTS.EllSol.EllPkgAux.E2s G)
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
  have hEq : (Work.FTS.EllSol.EllPkgAux.E2s G)
      = fun w : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ := by
    funext w
    simp only [Work.FTS.EllSol.EllPkgAux.E2s]
  rw [hEq]
  exact aesm_sliceEnergy_of_continuousOn (hsm.pth.pth).continuousOn ha

end Work.FTS.EllSol.EllPkgAux.MollAux
