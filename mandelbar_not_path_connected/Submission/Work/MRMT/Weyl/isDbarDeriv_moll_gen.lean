import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Weyl.isDbarDeriv_moll_contDiff
import Submission.Work.MRMT.Sobolev.dzbar_convolution_eq_of_isDbarDerivOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Mollification preserves the weak `∂̄`-equation, with an arbitrary right-hand side

`Work.MRMT.Weyl.moll ρ f` is the convolution of `f` with the (real valued, complexified)
kernel `ρ`, written as a convolution on the left in `ρ`.  The main result of this file is

`isDbarDeriv_moll_gen : IsDbarDeriv u h → IsDbarDeriv (ρ ⋆ u) (ρ ⋆ h)`,

the `∂̄`-analogue of `isDbarDeriv_moll`/`isDbarDeriv_moll_contDiff` (which cover the case
`h = 0`).

The argument is a rearrangement of the two integrations.  Since `moll ρ u` is smooth
(`contDiff_moll`), its distributional `∂̄` is the pointwise Wirtinger derivative `dzbar (moll ρ u)`
(`isDbarDeriv_dzbar`).  One computes, by differentiating the convolution in the smooth factor and
using the reflection chain rule `∂̄(ρ ∘ (z - ·)) = -(∂̄ρ) ∘ (z - ·)`, that

  `dzbar (moll ρ u) z = ∫ t, u t * ∂̄ρ (z - t)`,

and the weak equation for `(u, h)` tested against the test function `t ↦ ρ (z - t)` turns the
right-hand side into `∫ t, h t * ρ (z - t)`, which is `moll ρ h z` after the substitution
`t ↦ z - t`.  This is exactly the statement of
`Work.MRMT.Sobolev.dzbar_convolution_eq_of_isDbarDerivOn`, once the two convolution conventions
are identified by `convolution_mul_eq_moll` below.
-/

namespace Work.MRMT.Weyl

noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

open Work.MRMT

/-- The convolution with the complexified kernel on the right (i.e. `f ⋆[mul ℝ ℂ] ρ`) agrees with
the mollification `moll ρ f`, the convolution with `ρ` on the left: the two integrals differ only
by the measure preserving substitution `t ↦ x - t`. -/
theorem convolution_mul_eq_moll (ρ : ℂ → ℝ) (f : ℂ → ℂ) :
    MeasureTheory.convolution f (fun w => (ρ w : ℂ)) (ContinuousLinearMap.mul ℝ ℂ)
        (volume : Measure ℂ) = moll ρ f := by
  funext x
  rw [MeasureTheory.convolution_def, moll_apply]
  simp only [ContinuousLinearMap.mul_apply']
  rw [← MeasureTheory.integral_sub_left_eq_self
    (fun t => f t * ((ρ (x - t) : ℝ) : ℂ)) volume x]
  apply integral_congr_ae
  filter_upwards with t
  rw [sub_sub_cancel, mul_comm]

theorem isDbarDeriv_moll_gen {u h : ℂ → ℂ} (hu : Work.MRMT.IsDbarDeriv u h) {ρ : ℂ → ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρs : HasCompactSupport ρ) :
    Work.MRMT.IsDbarDeriv (Work.MRMT.Weyl.moll ρ u) (Work.MRMT.Weyl.moll ρ h) := by
  -- the complexified kernel and its smoothness/support
  have hρc : ContDiff ℝ (⊤ : ℕ∞) (fun w => (ρ w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hρ
  have hρcs : HasCompactSupport (fun w => (ρ w : ℂ)) :=
    hρs.comp_left (g := Complex.ofRealCLM) (by simp)
  -- `IsDbarDeriv` is `IsDbarDerivOn` on `Set.univ`
  have hFG : Work.MRMT.IsDbarDerivOn u h Set.univ := by
    obtain ⟨h1, h2, h3⟩ := hu
    exact ⟨MeasureTheory.locallyIntegrableOn_univ.2 h1,
      MeasureTheory.locallyIntegrableOn_univ.2 h2, fun ψ _ => h3 ψ⟩
  -- the pointwise identity `∂̄ (moll ρ u) = moll ρ h`
  have hkey : ∀ z, Work.MRMT.dzbar (moll ρ u) z = moll ρ h z := by
    intro z
    have hconv := Work.MRMT.Sobolev.dzbar_convolution_eq_of_isDbarDerivOn (U := Set.univ)
      (F := u) (G := h) (ρ := fun w => (ρ w : ℂ)) hFG hu.1 hρc hρcs
      (z := z) (fun t _ => trivial)
    rwa [convolution_mul_eq_moll ρ u, convolution_mul_eq_moll ρ h] at hconv
  -- `moll ρ u` is smooth, so its weak `∂̄` is its pointwise `∂̄`
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (moll ρ u) := contDiff_moll hρ hρs hu.1
  have hd : Work.MRMT.IsDbarDeriv (moll ρ u) (Work.MRMT.dzbar (moll ρ u)) :=
    isDbarDeriv_dzbar (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) hsmooth (by simp)
  exact isDbarDeriv_congr hd (fun z => hkey z)

end

end Work.MRMT.Weyl
