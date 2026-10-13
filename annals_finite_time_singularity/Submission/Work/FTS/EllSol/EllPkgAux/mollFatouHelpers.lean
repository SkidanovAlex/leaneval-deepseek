/-
# `Work.FTS.EllSol.EllPkgAux.mollFatou` — the Fatou (lower-semicontinuity) step of the
mollification transfer

The target is the Fatou step of the mollification transfer (see `NOTES_mollTransfer.md`):

for a trace-class datum `G` and `η > 0` there are mollification parameters `δ, ε ∈ Params` with
`∫_z mixIntS G ≤ ∫_z mixIntS (zmoll G δ ε) + η`.

The proof is the standard lower-semicontinuity argument, run along the diagonal sequence
`tseq n = 1/(n+2) → 0`:

* the mixed derivative of the approximant is given by an explicit double convolution
  (`mollDzPth`), whose two derivatives of the mollifying kernel are the kernels `sKerd`;
* a two-dimensional kernel-moment limit (`mollKernelLimit`) shows that the mixed derivative of
  the approximant converges pointwise to `D_z∂_θG` on the open quadrant;
* Fatou's lemma, applied once in `θ` and once in `z`, converts this pointwise convergence into
  `∫ mixIntS G ≤ liminf ∫ mixIntS (zmoll G t t)`;
* a final `ε`-argument produces the index `δ = ε = tseq n` with the `+η` slack.

All analytic inputs are proved in the sibling modules
`mollSliceBound`, `mollKerdMoments`, `mollKernelLimit`, `mollDzPth`, `mollHdom`,
`mollTargetDeriv`, `mollHon`, `mollHconv` and the assembly `mollFatouAssembly`; this file
contains only the wiring.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-- The restricted measures on `Iθ = [0,π/2]` and on the open interval agree (the two endpoints
are null). -/
theorem restrict_Iθ_eq_restrict_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  show Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[MeasureTheory.volume]
    Set.Ioo (0 : ℝ) (Real.pi / 2)
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

/-- `thEta θ = sin(2θ)^{-η}` is continuous on the open interval. -/
theorem continuousOn_thEta_Ioo :
    ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have h := hsin.rpow_const (p := -(Work.Spaces.eta)) (fun θ hθ => Or.inl (hne θ hθ))
  change ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo (0 : ℝ) (Real.pi / 2))
  exact h

/-- The `θ`-slice integrand of the datum is a.e.-strongly measurable: it is continuous on the
open interval, which is conull in `Iθ`. -/
theorem aeStronglyMeasurable_slice_G (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hdiff := (hS.pth.Dz).curry_θ hz
  have hslice : ContinuousOn (fun θ : ℝ => Work.Spaces.Dz (Work.Spaces.pth G) z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hdiff.continuousOn
  have hsq : ContinuousOn (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hslice.pow 2
  have hprod := hsq.mul continuousOn_thEta_Ioo
  rw [restrict_Iθ_eq_restrict_Ioo]
  exact hprod.aestronglyMeasurable measurableSet_Ioo

/-- On the open angular interval the doubly-odd extension `Qext` agrees with `G`, so the
uncurried integrand `Hxyc G` is smooth there. -/
theorem contDiffOn_uncurry_Hxyc (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Hxyc G))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hmap : ContDiffOn ℝ n (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine ContDiffOn.prodMk ?_ ?_
    · exact (Real.contDiff_exp.comp (contDiff_fst)).contDiffOn
    · exact contDiff_snd.contDiffOn
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) Work.FTS.EllipticEst.Q0 := by
    rintro ⟨t, s⟩ ⟨-, hs⟩
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos t, hs.1, hs.2⟩
  have hcomp := (hS.forall n).comp hmap hmaps
  refine hcomp.congr (fun p hp => ?_)
  simp only [Function.uncurry, Function.comp_apply, Hxyc]
  exact Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G (Real.exp p.1) p.2
    (Set.mem_Icc.mpr ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩)

end Work.FTS.EllSol.EllPkgAux
