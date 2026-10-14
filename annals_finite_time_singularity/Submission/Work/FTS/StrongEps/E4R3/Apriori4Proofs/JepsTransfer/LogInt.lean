import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Recur
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.FTS.EllipticEst.AeColl.i1PaperWeakMixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeColl

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- `Vfull u` is the level-`0` `HkSq` of the angular derivative of the radial gradient
(`AeI1Fts.HkSq_pth_grad`), the identification used to read the target's positive term. -/
theorem Vfull_eq_HkSq (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
      = Vfull u := by
  have hinner : ∀ z : ℝ,
      (∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
          * Work.FTS.EllipticEst.AeI1Fts.sigE θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Vz u z θ) ^ 2 := by
    intro z
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [show Work.FTS.EllipticEst.AeI1Fts.sigE θ = sigθ θ from rfl,
      show Work.FTS.EllipticEst.AeI1Fts.V u z θ = Vz u z θ from rfl]
    ring
  rw [Work.FTS.EllipticEst.AeI1Fts.HkSq_pth_grad α u hu]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [hinner z]
  rfl

end


end Work.FTS.EllipticEst.AeColl
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.KernelFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/KernelFacts.lean` — the elementary facts about the kernel `Jker` and the
log pull-back that the transfer estimate consumes

* `jker_even` — an even kernel (`hρs`) gives an even `Jker ρ ε`;
* `jker_momint` — `p ↦ Jker ρ ε p * (|p.1| + |p.2|)` is integrable (continuity + the support
  in the ball of radius `ε`);
* `logPull_continuous` — the log pull-back of a profile smooth on the open quadrant is
  continuous on the plane;
* `jker_conv_integrable` — consequently `p ↦ Jker ρ ε p * logPull g (y - p)` is integrable;
* `logPull_Jeps_eq` — the key identity
  `logPull (J_ε g) y = ∫ p, Jker ρ ε p * logPull g (y - p)`, expressing the mollifier as the
  even convolution on the plane.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- An even admissible kernel gives an even `Jker ρ ε`. -/
theorem jker_even {ρ : ℝ × ℝ → ℝ} (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) (ε : ℝ) (p : ℝ × ℝ) :
    Work.FTS.StrongEps.Jker ρ ε (-p) = Work.FTS.StrongEps.Jker ρ ε p := by
  simp only [Work.FTS.StrongEps.Jker, smul_neg, neg_inj, hρs]

/-- The first moment of the kernel is integrable. -/
theorem jker_momint {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p * (|p.1| + |p.2|)) :=
  ((Work.FTS.StrongEps.Jker_continuous hρ ε).mul
      ((continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd)))
    |>.integrable_of_hasCompactSupport
      ((Work.FTS.StrongEps.Jker_hasCompactSupport hρ hε).mul_right)

/-- The log pull-back of a profile smooth on the open quadrant is continuous. -/
theorem logPull_continuous {g : Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) :=
  Work.FTS.StrongEps.continuous_logPull_of_forall_contDiffOn hg

/-- The kernel against a translate of a continuous profile is integrable. -/
theorem jker_conv_integrable {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {G : ℝ × ℝ → ℝ} (hG : Continuous G) (y : ℝ × ℝ) :
    Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p * G (y - p)) :=
  ((Work.FTS.StrongEps.Jker_continuous hρ ε).mul
      (hG.comp (continuous_const.sub continuous_id)))
    |>.integrable_of_hasCompactSupport
      ((Work.FTS.StrongEps.Jker_hasCompactSupport hρ hε).mul_right)

/-- **The mollifier as an even convolution on the log plane.** -/
theorem logPull_Jeps_eq (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fn) (y : ℝ × ℝ) :
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.FTS.StrongEps.Jeps ρ ε g) y
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g (y - p) := by
  rw [show Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull
        (Work.FTS.StrongEps.Jeps ρ ε g) y
      = Work.FTS.StrongEps.Jeps ρ ε g (Real.exp y.1) (Real.arctan (Real.exp y.2)) from rfl,
    Work.FTS.StrongEps.Jeps_eq_integral ρ ε g (Real.exp_pos y.1)
      ⟨Real.arctan_pos.mpr (Real.exp_pos y.2), Real.arctan_lt_pi_div_two _⟩]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull,
    Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift, Prod.fst_sub, Prod.snd_sub,
    Real.exp_sub, Real.exp_sub, Real.tan_arctan, Real.exp_neg, div_eq_mul_inv]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/LogInt.lean` — log-side integrability from the quadrant

The transfer estimate `logPair_conv_transfer` is stated on the log plane, so it needs the
integrability of `Q y * G y ^ 2` there.  For the weights and profiles of the chapter this is the
quadrant integrability transported by the log-coordinate substitution: for
`Q = logW w` and `G = logPull g` the two integrals

  `∫⁻ y, ofReal (logW w y * logPull g y ^ 2)`   and
  `∫⁻ z ∈ Iz, ∫⁻ θ ∈ Iθ, ofReal (w z θ * g z θ ^ 2)`

are the same (`HkSqAux.lintegral_quad_log_subst`), so a finite quadrant lintegral makes the
log-side function Bochner-integrable.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The log-plane lintegral of a leaf weight times the square of a pulled-back profile is the
quadrant lintegral of the weight times the square of the profile. -/
theorem lintegral_logW_sq_eq (w : ℝ → ℝ → ℝ) (g : Fn)
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hgm : AEMeasurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)) :
    (∫⁻ y : ℝ × ℝ, ENNReal.ofReal
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g y) ^ 2))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (w z θ * g z θ ^ 2) := by
  -- the pointwise identification of the two plane integrands
  have hfun : (fun y : ℝ × ℝ => ENNReal.ofReal
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g y) ^ 2))
      = fun y : ℝ × ℝ => ENNReal.ofReal
          (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
            * ((fun z θ => w z θ * g z θ ^ 2)
                (Real.exp y.1) (Real.arctan (Real.exp y.2)))) := by
    funext y
    congr 1
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  have hae : AEMeasurable (fun y : ℝ × ℝ => ENNReal.ofReal
      (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
        * ((fun z θ => w z θ * g z θ ^ 2)
            (Real.exp y.1) (Real.arctan (Real.exp y.2))))) MeasureTheory.volume := by
    rw [← hfun]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hwm.aemeasurable.mul (hgm.pow_const 2))
  rw [hfun]
  -- the plane integral of the uncurried function is the product integral
  have hprod : (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
        * ((fun z θ => w z θ * g z θ ^ 2) (Real.exp y.1) (Real.arctan (Real.exp y.2)))))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ
        * ((fun z θ => w z θ * g z θ ^ 2) (Real.exp s) (Real.arctan (Real.exp ζ)))) :=
    MeasureTheory.lintegral_prod _ hae
  rw [hprod]
  -- split the Jacobian factor off the `ofReal`
  have hsplit : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ
        * ((fun z θ => w z θ * g z θ ^ 2) (Real.exp s) (Real.arctan (Real.exp ζ)))))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * ENNReal.ofReal ((fun z θ => w z θ * g z θ ^ 2)
              (Real.exp s) (Real.arctan (Real.exp ζ))) := by
    refine MeasureTheory.lintegral_congr (fun s =>
      MeasureTheory.lintegral_congr (fun ζ => ?_))
    exact ENNReal.ofReal_mul (Work.FTS.StrongEps.HkSqAux.logJac_nonneg s ζ)
  rw [hsplit]
  -- undo the log-coordinate substitution
  rw [← Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
    (fun z θ => ENNReal.ofReal (w z θ * g z θ ^ 2))]
  -- the open quadrant carries the same measure as `Iz × Iθ`
  have hIθ : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (w z θ * g z θ ^ 2))
      = fun z : ℝ => ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal (w z θ * g z θ ^ 2) :=
    funext fun z => (MeasureTheory.setLIntegral_congr
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2))).symm
  rw [hIθ]
  exact MeasureTheory.setLIntegral_congr
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))

/-- **Log-side integrability of `logW w · (logPull g)²` from the quadrant lintegral.** -/
theorem integrable_logW_sq_of_lintegral {w : ℝ → ℝ → ℝ} {g : Fn}
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hgm : AEMeasurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g))
    (hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (w z θ * g z θ ^ 2)) ≠ ⊤) :
    Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g y) ^ 2) := by
  have hnn : 0 ≤ᵐ[MeasureTheory.volume] (fun y : ℝ × ℝ =>
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g y) ^ 2) :=
    Eventually.of_forall fun y => mul_nonneg (hw0 y) (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · exact (hwm.aemeasurable.mul (hgm.pow_const 2)).aestronglyMeasurable
  · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn]
    rw [lintegral_logW_sq_eq w g hw0 hwm hgm]
    exact lt_top_iff_ne_top.mpr hfin

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT
end
end
