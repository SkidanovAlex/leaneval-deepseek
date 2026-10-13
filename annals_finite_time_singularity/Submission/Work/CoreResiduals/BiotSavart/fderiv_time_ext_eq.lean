import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.continuousOn_farStrip_blocks
import Submission.Work.CoreResiduals.BiotSavart.WindowExtDefs
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds
import Submission.Work.CoreResiduals.BiotSavart.hasFDerivAt_biotSavart_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-- **The second block of `fderiv ℝ (extField ω S)` on the strip.**  For `0 < R`, an `ω` whose
two-sided extension `windowExt ω S` satisfies the window bundle `BSAdmissibleOnWindow` (supplied by
`windowExt_windowBundle`), and a point `(x,t)` with `t ∈ Icc 0 S` at which the field
`extField ω S` (defined in
`Submission/Work/CoreResiduals/BiotSavart/continuousOn_farStrip_blocks.lean` as
`fun p => BS (windowExt ω S · p.2) p.1`) is `C¹`, the time-block of its Fréchet derivative
evaluated at `1` is the Biot–Savart field of the time-derivative slice of the extension:
`BS (∂ₜ(windowExt ω S)(·,t)) x`.

Proof: the chain rule with `hasFDerivAt_prodMk_right` identifies
`(fderiv ℝ (extField ω S) (x,t)).comp (inr ℝ R3 ℝ)` with
`fderiv ℝ (fun s => bsSTField (windowExt ω S) x s) t`; since `t ∈ Icc 0 S ⊆ preWindow (S+1)`, the
local clauses of the bundle around `t` let `hasFDerivAt_bsSTField_time` identify that with
`bsTDeriv (windowExt ω S) x t`, whose value at `1` is
`1 • BS (timeDeriv (windowExt ω S) · t) x = BS (timeDeriv (windowExt ω S) · t) x`
(`bsTDeriv` is `ContinuousLinearMap.toSpanSingleton ℝ _`; use `toSpanSingleton_apply`). -/
theorem fderiv_time_ext_eq {ω : R3 → ℝ → R3} {R S : ℝ} (hR : 0 < R)
    (hbun : Work.CoreResiduals.BSAdmissibleOnWindow (windowExt ω S) R (S + 1))
    {x : R3} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) S)
    (hcd : ContDiffAt ℝ 1 (extField ω S) (x, t)) :
    Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv (windowExt ω S) y t) x
      = ((fderiv ℝ (extField ω S) (x, t)).comp (ContinuousLinearMap.inr ℝ R3 ℝ)) 1 := by
  -- `t` lies in the half-window on which the bundle's local clauses apply
  have htpre : t ∈ Work.ConstructionInstance.preWindow (S + 1) := by
    rw [Work.ConstructionInstance.preWindow, Set.mem_Ioo]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- unpack the window bundle
  obtain ⟨hRpos, hsupp, hbddL, hholdL, haesmL, hdcL, hbddDL, haesmDL⟩ := hbun
  obtain ⟨ε₁, hε₁, M, hMb⟩ := hbddL t htpre
  obtain ⟨ε₃, hε₃, haesm⟩ := haesmL t htpre
  obtain ⟨ε₄, hε₄, hdc⟩ := hdcL t htpre
  obtain ⟨ε₅, hε₅, M₁, hM₁b⟩ := hbddDL t htpre
  -- a single window on which all the local clauses hold simultaneously
  set δ : ℝ := min (min ε₁ ε₃) (min ε₄ ε₅) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (lt_min hε₁ hε₃) (lt_min hε₄ hε₅)
  have hδ1 : δ ≤ ε₁ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ3 : δ ≤ ε₃ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ4 : δ ≤ ε₄ := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ5 : δ ≤ ε₅ := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hsub : ∀ {ε : ℝ}, δ ≤ ε → Set.Ioo (t - δ) (t + δ) ⊆ Set.Ioo (t - ε) (t + ε) := by
    intro ε hε s hs
    exact ⟨by linarith [hs.1, hε], by linarith [hs.2, hε]⟩
  -- the `t`-derivative of the spacetime Biot–Savart field, from the bundle
  have hbsT : HasFDerivAt (fun s : ℝ => bsSTField (windowExt ω S) x s)
      (bsTDeriv (windowExt ω S) x t) t :=
    hasFDerivAt_bsSTField_time (ω := windowExt ω S) (R := R) (M := max M 0) (M₁ := max M₁ 0)
      (ε := δ) hR.le (le_max_right _ _) (le_max_right _ _) hδpos
      (fun s hs y => le_trans (hMb s (hsub hδ1 hs) y) (le_max_left _ _))
      (fun s hs y => le_trans (hM₁b s (hsub hδ5 hs) y) (le_max_left _ _))
      (fun s hs y => hdc s (hsub hδ4 hs) y)
      (fun s hs y hy => hsupp s y hy)
      (fun s hs => haesm s (hsub hδ3 hs))
      x
  -- the chain rule: the derivative of `s ↦ extField ω S (x,s)` is the `t`-block
  have hdf : HasFDerivAt (extField ω S) (fderiv ℝ (extField ω S) (x, t)) (x, t) :=
    (hcd.hasStrictFDerivAt (by simp)).hasFDerivAt
  have hpmk : HasFDerivAt (fun s : ℝ => (x, s)) (ContinuousLinearMap.inr ℝ R3 ℝ) t :=
    hasFDerivAt_prodMk_right x t
  have hcomp : HasFDerivAt (fun s : ℝ => bsSTField (windowExt ω S) x s)
      ((fderiv ℝ (extField ω S) (x, t)).comp (ContinuousLinearMap.inr ℝ R3 ℝ)) t := by
    simpa only [Function.comp_def, extField, bsSTField] using hdf.comp t hpmk
  -- uniqueness of the derivative identifies the `t`-block with `bsTDeriv`
  rw [hcomp.unique hbsT]
  simp [bsTDeriv, ContinuousLinearMap.toSpanSingleton_apply]

end Work.CoreResiduals.BiotSavart
