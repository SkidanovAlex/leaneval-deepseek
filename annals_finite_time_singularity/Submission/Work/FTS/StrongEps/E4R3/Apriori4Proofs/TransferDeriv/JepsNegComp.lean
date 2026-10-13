import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

set_option autoImplicit false

/-!
# `JepsNegComp` — the negation symmetry of the log-coordinate mollifier

The log-coordinate mollifier `Jeps ρ ε` is the convolution with the rescaled kernel
`Jker ρ ε p = ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)` (`Basic.lean`, `Kernel.lean`), and neither the kernel nor the
shift depends on the *orientation* of the mollifier coordinates.  This module records the two
consequences of that fact:

* if `ρ` is an admissible smooth kernel (`IsSmoothKernel ρ`), so is the reflected kernel
  `p ↦ ρ (-p)` — smoothness is preserved by the linear isometry `p ↦ -p`, and the mass is
  preserved because `volume` on `ℝ × ℝ` is invariant under negation
  (`MeasureTheory.integral_neg_eq_self`);
* for *negative* `ε` the reflected kernel at scale `-ε` reproduces `Jeps ρ ε` exactly:
  `(-ε)⁻¹ = -(ε⁻¹)`, so `-((-ε)⁻¹ • p) = ε⁻¹ • p` and `((-ε)⁻¹) ^ 2 = (ε⁻¹) ^ 2`, i.e. the two
  integrands agree **pointwise** and the integrals are literally equal.

The statement is the `ε < 0` half of the "reflection bookkeeping" of the `Apriori4` transfer: the
`ε`-scheme itself is only run for `ε > 0`, and reflection lets a *negative* scale be re-read as a
positive one applied to the reflected kernel.
-/

/-- **Reflection of an admissible smooth kernel.**  If `ρ` is a smooth admissible mollifier
kernel, so is `p ↦ ρ (-p)`: the linear isometry `p ↦ -p` preserves `C^∞`, continuity, the support
condition and nonnegativity, while the total mass is preserved by the negation invariance of
Lebesgue measure on `ℝ × ℝ`. -/
theorem isSmoothKernel_neg_comp {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    Work.FTS.StrongEps.IsSmoothKernel (fun p : ℝ × ℝ => ρ (-p)) := by
  refine ⟨?_, ?_⟩
  · intro n
    exact (hρ.smooth n).comp (contDiff_neg (𝕜 := ℝ) (F := ℝ × ℝ))
  · refine ⟨hρ.moll.cont.comp continuous_neg, ?_, ?_, ?_⟩
    · intro p hp
      have h := hρ.moll.support (-p) hp
      simpa using h
    · intro p
      exact hρ.moll.nonneg (-p)
    · simpa using (MeasureTheory.integral_neg_eq_self ρ volume).trans hρ.moll.mass

/-- **The reflected kernel at the negated scale is the original mollifier.**  For every `ε` and
every profile `f`, `Jeps ρ ε f = Jeps (p ↦ ρ (-p)) (-ε) f`: the two `p`-integrands agree
pointwise, since `(-ε)⁻¹ = -(ε⁻¹)` entails `-((-ε)⁻¹ • p) = ε⁻¹ • p` and
`((-ε)⁻¹) ^ 2 = (ε⁻¹) ^ 2`. -/
theorem Jeps_neg_comp {ρ : ℝ × ℝ → ℝ} {ε : ℝ} (f : Work.FTS.Galerkin.Fn) :
    Work.FTS.StrongEps.Jeps ρ ε f
      = Work.FTS.StrongEps.Jeps (fun p : ℝ × ℝ => ρ (-p)) (-ε) f := by
  funext z θ
  by_cases hc : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε f hc.1 hc.2,
      Work.FTS.StrongEps.Jeps_eq_integral (fun p : ℝ × ℝ => ρ (-p)) (-ε) f hc.1 hc.2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Work.FTS.StrongEps.Jker]
    have h1 : (-ε)⁻¹ • p = -(ε⁻¹ • p) := by rw [inv_neg, neg_smul]
    rw [h1, neg_neg, inv_neg, neg_sq]
  · rw [Work.FTS.StrongEps.Jeps_eq_zero ρ ε f hc,
      Work.FTS.StrongEps.Jeps_eq_zero (fun p : ℝ × ℝ => ρ (-p)) (-ε) f hc]

theorem JepsNegComp {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : ε < 0) :
    Work.FTS.StrongEps.IsSmoothKernel (fun p : ℝ × ℝ => ρ (-p)) ∧
      ∀ f : Work.FTS.Galerkin.Fn,
        Work.FTS.StrongEps.Jeps ρ ε f
          = Work.FTS.StrongEps.Jeps (fun p : ℝ × ℝ => ρ (-p)) (-ε) f :=
  ⟨isSmoothKernel_neg_comp hρ, fun f => Jeps_neg_comp f⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
