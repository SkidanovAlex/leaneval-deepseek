/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/XBallIterExistsAux/FstarJepsSmooth.lean`

**The angular moment `F_* (J_ε W)` of the log-coordinate mollifier is `C^∞` on `(0,∞)`**, from
`SmoothOpen W` and the *only* honest-size input `HkMem α 1 W` (no sup and no weighted-`L^∞`
control of `W`).

The proof is the log-coordinate mollification argument:

* in the log variables `s = log z`, the *angular slice* of `J_ε W` is the one-dimensional
  convolution of the kernel `p₁ ↦ Jker ρ ε (p₁, p₂)` with the slice `t ↦ W (e^t) (thShift θ p₂)`,
  so differentiating in `s` hits the *kernel* (`PhiFam.hasDerivAt_Phi`), with no regularity of
  `W` beyond local integrability needed;
* consequently the family `Φ m s (θ,p₂)` (whose `p₁`-integral is that slice) satisfies the three
  hypotheses of the parametric-integral lemma `FstarJepsSmoothAux.ParamIntegral` on the compact
  measure space `Iθ × [-ε,ε]`:
  * a.e. strong measurability (`PhiAEStronglyMeasurable`);
  * `∂_s Φ m = Φ (m+1)` a.e. (`PhiFam.hasDerivAt_Phi`);
  * the domination `|Φ m s x| ≤ C · G (thShift x.1 x.2)` on a slab in `s`
    (`PhiFam.abs_Phi_le`), where `G` is the *uniform in `z`* angular majorant of the slices of
    `W` supplied by `HkMem α 1 W` (`FstarJepsSmoothAux.ZSliceDomination`) and `C` is a constant
    depending only on `ρ, ε, m` (the kernel has compact support);
    the integrability of this majorant is `XBallIterExistsAux.integrable_sinCos2_mul_shift_of_integrableOn`;
* the identification of `F_* (J_ε W) (e^s)` with the `s`-integral of the family is the Fubini
  swap `FstarJepsSmoothAux.FubiniSwap` (the angular weight `sin θ cos²θ` kills the two endpoints
  of `Iθ`, where `W` is only known on the open quadrant);
* finally `z ↦ ∫ x, Φ 0 (log z) x · sinCos2 x.1` is `C^∞` on `(0,∞)` by the chain rule
  (`Real.log` is `C^∞` on `(0,∞)`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.GalBasis.exists_mixed_bound
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ConvDeriv
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ParamIntegral
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ThShiftSubst
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ZSliceDomination
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.PhiAEStronglyMeasurable
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.FubiniSwap
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux.PhiFam
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux.MajorantX

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux

set_option autoImplicit false

theorem FstarJepsSmooth {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} {W : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W))
      (Set.Ioi 0) := by
  intro m
  -- the `s`-smoothness of the parametric integral
  have hsmooth : ContDiff ℝ m (fun s => ∫ x, Phi ρ ε W 0 s x * Work.Elliptic.sinCos2 x.1
      ∂(Jmu ε)) := by
    refine Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ParamIntegral
      (Φ := fun k s x => Phi ρ ε W k s x * Work.Elliptic.sinCos2 x.1) ?_ ?_ ?_ m
    · -- a.e. strong measurability
      intro k s
      have h1 : MeasureTheory.AEStronglyMeasurable (fun x : ℝ × ℝ => Phi ρ ε W k s x)
          (Jmu ε) := by
        change MeasureTheory.AEStronglyMeasurable
          (fun x : ℝ × ℝ => ∫ p₁ : ℝ, Work.Spaces.pzIter k
            (fun a b => Work.FTS.StrongEps.Jker ρ ε (a, b)) p₁ x.2
              * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)) (Jmu ε)
        exact Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.PhiAEStronglyMeasurable
          hρ hε hsm k s
      have h2 : Continuous (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1) := by
        rw [show (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1)
            = (fun x : ℝ × ℝ => Real.sin x.1 * Real.cos x.1 ^ 2) from rfl]
        fun_prop
      exact h1.mul h2.aestronglyMeasurable
    · -- the `s`-derivative
      intro k
      refine Filter.Eventually.mono ae_mem_Ioo_Jmu fun x hx => ?_
      intro s
      exact (hasDerivAt_Phi hρ hε hsm k s hx).mul_const _
    · -- the domination
      intro k s₀
      obtain ⟨G, hGint, hGdom⟩ :=
        Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ZSliceDomination hsm hmem
          (a := Real.exp (s₀ - 1 - ε)) (b := Real.exp (s₀ + 1 + ε))
          (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith))
      have hGnn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ G θ := fun θ hθ =>
        le_trans (abs_nonneg _) (hGdom _ ⟨le_refl _, Real.exp_le_exp.mpr (by linarith)⟩ θ hθ)
      have hinter : MeasureTheory.Integrable (fun x : ℝ × ℝ =>
          Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)) (Jmu ε) :=
        integrable_sinCos2_mul_shift_of_integrableOn hGint
      refine ⟨fun x => (2 * ε * Classical.choose (exists_kernBound hρ hε k))
          * (Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)),
        hinter.const_mul _, ?_⟩
      refine Filter.Eventually.mono ae_mem_Ioo_Jmu fun x hx => ?_
      intro s hs
      have hsrange : ∀ p₁ : ℝ, p₁ ∈ Set.Icc (-ε) ε →
          Real.exp (s - p₁) ∈ Set.Icc (Real.exp (s₀ - 1 - ε)) (Real.exp (s₀ + 1 + ε)) := by
        intro p₁ hp
        refine ⟨Real.exp_le_exp.mpr (by linarith [hs.1, hp.2]),
          Real.exp_le_exp.mpr (by linarith [hs.2, hp.1])⟩
      have h1 := abs_Phi_le hρ hε hsm hGnn hGdom hsrange k hx
      have hsin : 0 ≤ Work.Elliptic.sinCos2 x.1 := by
        rw [Work.Elliptic.sinCos2]
        exact mul_nonneg
          (Real.sin_nonneg_of_mem_Icc ⟨hx.1.le, by linarith [hx.2, Real.pi_pos]⟩)
          (sq_nonneg _)
      have h2 : |Phi ρ ε W k s x * Work.Elliptic.sinCos2 x.1|
          = |Phi ρ ε W k s x| * Work.Elliptic.sinCos2 x.1 := by
        rw [abs_mul, abs_of_nonneg hsin]
      rw [h2]
      calc |Phi ρ ε W k s x| * Work.Elliptic.sinCos2 x.1
          ≤ ((2 * ε * Classical.choose (exists_kernBound hρ hε k))
              * G (Work.FTS.StrongEps.thShift x.1 x.2)) * Work.Elliptic.sinCos2 x.1 :=
            mul_le_mul_of_nonneg_right h1 hsin
        _ = (2 * ε * Classical.choose (exists_kernBound hρ hε k))
              * (Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)) := by
            ring
  -- the identification of the angular moment with the `s`-integral (Fubini swap)
  have hid : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) z
      = ∫ x, Phi ρ ε W 0 (Real.log z) x * Work.Elliptic.sinCos2 x.1 ∂(Jmu ε) := by
    intro z hz
    obtain ⟨G, hGint, hGdom⟩ :=
      Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ZSliceDomination hsm hmem
        (a := Real.exp (Real.log z - ε)) (b := Real.exp (Real.log z + ε))
        (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith))
    have hinter : MeasureTheory.Integrable (fun x : ℝ × ℝ =>
        Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)) (Jmu ε) :=
      integrable_sinCos2_mul_shift_of_integrableOn hGint
    have hsrange : ∀ p₁ : ℝ, p₁ ∈ Set.Icc (-ε) ε →
        Real.exp (Real.log z - p₁)
          ∈ Set.Icc (Real.exp (Real.log z - ε)) (Real.exp (Real.log z + ε)) := by
      intro p₁ hp
      exact ⟨Real.exp_le_exp.mpr (by linarith [hp.2]),
        Real.exp_le_exp.mpr (by linarith [hp.1])⟩
    have hswap := Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.FubiniSwap hρ.moll hε hsm hGdom hinter (Real.log z) hsrange
    rw [Real.exp_log hz] at hswap
    rw [hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Work.Elliptic.sinCos2 x.1 * (∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2)
        * W (Real.exp (Real.log z - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2))
      = Phi ρ ε W 0 (Real.log z) x * Work.Elliptic.sinCos2 x.1
    rw [show Phi ρ ε W 0 (Real.log z) x = (∫ p₁ : ℝ,
        Work.FTS.StrongEps.Jker ρ ε (p₁, x.2)
          * W (Real.exp (Real.log z - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)) from rfl]
    ring
  -- transfer `s`-smoothness back to the variable `z = e^s`
  have hlog : ContDiffOn ℝ m Real.log (Set.Ioi (0 : ℝ)) := fun x hx =>
    (Real.contDiffAt_log.mpr (ne_of_gt hx)).contDiffWithinAt
  exact (hsmooth.comp_contDiffOn hlog).congr (fun z hz => hid z hz)

end Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux
