/-
# `Weil/Assembly` — the two assembly steps of the Weyl route to `SmoothOpen (psiSeries α (RemSource α ψ))`

The smoothness conjunct of `psiSeries_solves_rem` is obtained as follows.

* **Step A (`weakIdentity_of_limits`).**  For every test function `φ` smooth and compactly
  supported in the open quadrant `Q0`, the mode series `R α ψ` satisfies the weak formulation of
  `bslOp α R = RemSource α ψ`:
  `∫_{Q0} R·(bslOp α φ)·w = ∫_{Q0} (RemSource α ψ)·φ·w`,  `w = z^((5-α)/α) cos θ`.
  This is obtained by passing to the limit `N → ∞` in the *truncated* weak identity
  `Work.FTS.H2.ModalSolR.psiTrunc_weak_identity` (which the development proves for every `N`),
  using the two limit theorems supplied as hypotheses here: the left-hand side
  (`tendstoIntegralPsiTrunc`) and the right-hand side (`tendstoIntegralCsrc`).

* **Step B (`smoothOpenR_of_parts`).**  `R α ψ` is continuous on `Q0` and satisfies the weak
  formulation; hence `interiorSmoothQ0_fts` (Weyl's lemma for `bslOp α` on the quadrant, weight
  `(5-α)/α`) produces a `C^∞` function `Φ` on `Q0` with `R =ᵐ Φ`.  Since both are continuous on
  the *open* set `Q0`, the a.e. identity is upgraded to a pointwise one
  (`MeasureTheory.Measure.eqOn_open_of_ae_eq`), so `R α ψ` itself is `C^∞` on `Q0`.

Both statements are stated with the reusable pieces as explicit hypotheses, so that this module
does not depend on the modules that prove them; the instantiation is in `Weil/Main.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Series.Weil.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.ModalSolR.TruncIdent
import Submission.Work.FTS.EllipticEst.Final.InteriorSmoothQ0_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false

/-- **Step A: the weak formulation of the mode series.**  Passing to the limit in the truncated
weak identity. -/
theorem weakIdentity_of_limits (α : ℝ) (ψ : ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.RemSource α ψ))
    (horth : Work.Elliptic.OrthCond (Work.FTS.PhiStar.RemSource α ψ))
    (hL2 : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.RemSource α ψ p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hLHS : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
          Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2
            * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        Filter.atTop
        (nhds (∫ p in Work.FTS.EllipticEst.Q0,
          R α ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))))
    (hRHS : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
          csrc α ψ N p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        Filter.atTop
        (nhds (∫ p in Work.FTS.EllipticEst.Q0,
          Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2)))) :
    ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          R α ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
          Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  intro φ hφ hφc hφs
  -- the truncated weak identity for every `N`
  have htrunc : ∀ N : ℕ,
      (∫ p in Work.FTS.EllipticEst.Q0,
          Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2
            * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
          csrc α ψ N p.1 p.2 * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    fun N => Work.FTS.H2.ModalSolR.psiTrunc_weak_identity α hα hα1 horth hF hL2 hφ hφc hφs N
  -- hence the two sequences of integrals are equal
  have hseq : (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        csrc α ψ N p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
          Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2
            * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) := by
    funext N
    exact (htrunc N).symm
  have hlim := hRHS φ hφ hφc hφs
  rw [hseq] at hlim
  exact tendsto_nhds_unique (hLHS φ hφ hφc hφs) hlim

/-- **Step B: Weyl's lemma plus the a.e.-to-pointwise upgrade.**  A function continuous on the
open quadrant `Q0` which satisfies the weak formulation of `bslOp α R = F` is `C^∞` there. -/
theorem smoothOpenR_of_parts (α : ℝ) (ψ : ℝ → ℝ)
    (hcont : ContinuousOn (Function.uncurry (R α ψ)) Work.FTS.EllipticEst.Q0)
    (hF : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.RemSource α ψ))
    (hα : 0 < α)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          R α ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = (∫ p in Work.FTS.EllipticEst.Q0,
          Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) :
    Work.FTS.EllipticEst.SmoothOpen (R α ψ) := by
  have hQ0 : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have hLI : MeasureTheory.LocallyIntegrableOn (Function.uncurry (R α ψ))
      Work.FTS.EllipticEst.Q0 :=
    hcont.locallyIntegrableOn hQ0
  obtain ⟨Φ, hΦsm, hΦae⟩ :=
    Work.EllipticEst.InteriorRegularity.Q0.interiorSmoothQ0_fts hα hF hLI hweak
  have hΦcont : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hΦsm.continuousOn
  have hEqOn := MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) hΦae
    Work.FTS.EllipticEst.isOpen_Q0 hcont hΦcont
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  refine (hΦsm.forall n).congr (fun p hp => ?_)
  show R α ψ p.1 p.2 = Φ p.1 p.2
  exact hEqOn hp

end Work.FTS.PhiStar.Series.Weil
