import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.CoreResiduals.BiotSavart.continuousAt_biotSavart_param
import Submission.Work.StabilityFar.Decay.biotSavart_fderiv
import Submission.Work.StabilityFar.Decay.slicesSupported_timeDeriv_window
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_dtContinuous
import Submission.Work.CoreResiduals.BiotSavart.exists_windowExtension_of_stripBundle
import Submission.Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_of_stripBundle
import Submission.Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_general
import Submission.Work.CoreResiduals.BiotSavart.windowExt_windowBundle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-! ## The two-sided time-extension of the strip vorticity

The strip bundle is *one-sided* in `t`, so the `C¹`-in-`t` inputs at the endpoints `t = 0`, `S` of
the strip (`BSAdmissibleStripFull` gives a two-sided `HasDerivAt` at them, but no information
about the field for `t < 0` or `t > S`) are recovered by gluing `ω` to its affine continuation
beyond the strip — `windowExt ω S` (`Submission/Work/CoreResiduals/BiotSavart/WindowExtDefs.lean`).
That extension satisfies the *two-sided window* bundle `BSAdmissibleOnWindow` and has continuous
`∂ₜ`-slices (`windowExt_windowBundle`, from `exists_windowExtension_of_stripBundle`), so the window
theorem `biotSavartSpacetimeC1_of_dtContinuous` applies to it.  The `hα1 : α < 1` hypothesis of the
original exists-lemma is dead (Lean reports `hα1` unused there); `windowExt_windowBundle` and
`timeDeriv_xHolderOn_general` are the two generalisations that drop it, which is what makes this
file cover the full range `0 < α` of the requested statement. -/

/-- **The spacetime Biot–Savart field of the two-sided time-extension `windowExt ω S`**:
`p ↦ BS (windowExt ω S · p.2) p.1`.  It agrees, on the strip `univ ×ˢ Icc 0 S`, with the
spacetime Biot–Savart field `p ↦ BS (ω · p.2) p.1` of the vorticity itself. -/
noncomputable def extField (ω : R3 → ℝ → R3) (S : ℝ) : R3 × ℝ → R3 :=
  fun p => Work.LWP.biotSavart (fun y => windowExt ω S y p.2) p.1

/-- `extField` is the uncurried form of the spacetime Biot–Savart field of `windowExt ω S`. -/
theorem extField_eq_uncurry (ω : R3 → ℝ → R3) (S : ℝ) :
    extField ω S = Function.uncurry (bsSTField (windowExt ω S)) := rfl

/-! ## The two blocks of `fderiv ℝ (extField ω S)` on the strip

`extField ω S` is `C¹` at every point of the strip (`biotSavartSpacetimeC1_of_dtContinuous` applied
to the extension), so `fderiv ℝ (extField ω S)` is continuous on the strip.  The two blocks of that
derivative — its spatial part (`∘ inl`) and its time part (applied to `1` after `∘ inr`) — are
identified below with the two target blocks of `continuousOn_farStrip_blocks`. -/

/-- **The first block of `fderiv ℝ (extField ω S)` on the strip:** the composition with the
spatial inclusion `ContinuousLinearMap.inl ℝ R3 ℝ` is the spatial derivative of the slice.

This is the chain rule for `extField ω S ∘ (fun y => (y,t))` together with the agreement
`windowExt ω S · t = ω · t` on `Icc 0 S` (`windowExt_of_mem_Icc`). -/
theorem blocks_fderiv_slice_eq {ω : R3 → ℝ → R3} {S : ℝ} {x : R3} {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) S)
    (hcd : ContDiffAt ℝ 1 (extField ω S) (x, t)) :
    fderiv ℝ (Work.LWP.biotSavart (fun y => ω y t)) x
      = (fderiv ℝ (extField ω S) (x, t)).comp (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  have hF : HasFDerivAt (extField ω S) (fderiv ℝ (extField ω S) (x, t)) (x, t) :=
    (hcd.differentiableAt one_ne_zero).hasFDerivAt
  have hcomp : (extField ω S) ∘ (fun e : R3 => (e, t)) = fun x' : R3 => extField ω S (x', t) := by
    funext x'; rfl
  have hchain : fderiv ℝ (fun x' : R3 => extField ω S (x', t)) x
      = (fderiv ℝ (extField ω S) (x, t)).comp (ContinuousLinearMap.inl ℝ R3 ℝ) := by
    rw [← hcomp]
    exact (hF.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)).fderiv
  rw [← hchain]
  have hslice : (fun y : R3 => ω y t) = (fun y : R3 => windowExt ω S y t) := by
    funext y; exact (windowExt_of_mem_Icc ht).symm
  have hfun : (Work.LWP.biotSavart (fun y : R3 => ω y t))
      = (fun x' : R3 => extField ω S (x', t)) := by
    funext x'
    show Work.LWP.biotSavart (fun y => ω y t) x'
      = Work.LWP.biotSavart (fun y => windowExt ω S y t) x'
    rw [hslice]
  rw [hfun]

/-- **The second block of `fderiv ℝ (extField ω S)` on the strip:** the composition with the time
inclusion `ContinuousLinearMap.inr ℝ R3 ℝ`, evaluated at `1`, is the Biot–Savart field of the
time-derivative slice of the extension.

This is the chain rule for `extField ω S (x, ·)` together with `hasFDerivAt_bsSTField_time`
(the differentiation-under-the-integral-symbol identity `∂ₜ BS(ω·t) = BS(∂ₜω·t)`), whose local
hypotheses are taken from the window bundle of `windowExt ω S` at `t ∈ Icc 0 S ⊆ preWindow (S+1)`;
the value at `1` of `bsTDeriv` is the `toSpanSingleton` of `BS(∂ₜ(windowExt ω S)(·,t)) x`. -/
theorem blocks_fderiv_time_eq {ω : R3 → ℝ → R3} {R S : ℝ} (hR : 0 < R)
    (hbun : Work.CoreResiduals.BSAdmissibleOnWindow (windowExt ω S) R (S + 1))
    {x : R3} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) S)
    (hcd : ContDiffAt ℝ 1 (extField ω S) (x, t)) :
    Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv (windowExt ω S) y t) x
      = ((fderiv ℝ (extField ω S) (x, t)).comp (ContinuousLinearMap.inr ℝ R3 ℝ)) 1 := by
  have hF : HasFDerivAt (extField ω S) (fderiv ℝ (extField ω S) (x, t)) (x, t) :=
    (hcd.differentiableAt one_ne_zero).hasFDerivAt
  have hcomp : (extField ω S) ∘ (Prod.mk x) = fun s : ℝ => extField ω S (x, s) := by
    funext s; rfl
  have hchain : fderiv ℝ (fun s : ℝ => extField ω S (x, s)) t
      = (fderiv ℝ (extField ω S) (x, t)).comp (ContinuousLinearMap.inr ℝ R3 ℝ) := by
    rw [← hcomp]
    exact (hF.comp t (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)).fderiv
  rw [← hchain]
  have hpre : t ∈ Work.ConstructionInstance.preWindow (S + 1) := by
    change t ∈ Set.Ioo (-2 : ℝ) (S + 1)
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hR', hsuppG, hbddL, hholdL, haesmL, hdcL, hbddDL, haesmDL⟩ := hbun
  obtain ⟨ε₁, hε₁, M, hMb⟩ := hbddL t hpre
  obtain ⟨ε₂, hε₂, hdc₀⟩ := hdcL t hpre
  obtain ⟨ε₃, hε₃, M₁, hM₁b⟩ := hbddDL t hpre
  obtain ⟨ε₄, hε₄, haesm₀⟩ := haesmL t hpre
  set ε : ℝ := min (min ε₁ ε₂) (min ε₃ ε₄) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄)
  have hle₁ : ε ≤ ε₁ := by rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hle₂ : ε ≤ ε₂ := by rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hle₃ : ε ≤ ε₃ := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hle₄ : ε ≤ ε₄ := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hmem₁ : ∀ s ∈ Set.Ioo (t - ε) (t + ε), s ∈ Set.Ioo (t - ε₁) (t + ε₁) := by
    intro s hs; rw [Set.mem_Ioo] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmem₂ : ∀ s ∈ Set.Ioo (t - ε) (t + ε), s ∈ Set.Ioo (t - ε₂) (t + ε₂) := by
    intro s hs; rw [Set.mem_Ioo] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmem₃ : ∀ s ∈ Set.Ioo (t - ε) (t + ε), s ∈ Set.Ioo (t - ε₃) (t + ε₃) := by
    intro s hs; rw [Set.mem_Ioo] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmem₄ : ∀ s ∈ Set.Ioo (t - ε) (t + ε), s ∈ Set.Ioo (t - ε₄) (t + ε₄) := by
    intro s hs; rw [Set.mem_Ioo] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hderiv : HasFDerivAt (fun s : ℝ => extField ω S (x, s)) (bsTDeriv (windowExt ω S) x t) t :=
    hasFDerivAt_bsSTField_time (R := R) (M := max M 0) (M₁ := max M₁ 0) (ε := ε) (t := t)
      hR.le (le_max_right _ _) (le_max_right _ _) hεpos
      (fun s hs y => le_trans (hMb s (hmem₁ s hs) y) (le_max_left _ _))
      (fun s hs y => le_trans (hM₁b s (hmem₃ s hs) y) (le_max_left _ _))
      (fun s hs y => hdc₀ s (hmem₂ s hs) y)
      (fun s hs y hy => hsuppG s y hy)
      (fun s hs => haesm₀ s (hmem₄ s hs))
      x
  rw [hderiv.fderiv]
  simp only [bsTDeriv, ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-! ## The target statement -/

/-- **Joint continuity of the two far-field blocks on the strip.**

For `0 < α`, `0 < S` and a strip-bundle vorticity `ω`, the two blocks of the derivative of
`q ↦ BS (ω(·,q.2)) q.1` are *jointly continuous* on the far strip
`farRegion (2R+5) × Icc 0 S`:

* `(x,t) ↦ fderiv ℝ (BS (ω·t)) x` — in the far field this is
  `bsDeriv (ω·t) x = (4π)⁻¹ ∫ a, crossL (ω(a,t)) ∘ kDerivCLM (x-a)`, and the integrand is jointly
  continuous in `(x,t)` (for `a ∈ B(0,R)`, `x` far) and dominated by `C·1_{B(0,R)}` (since
  `‖x - a‖ ≥ R`), so dominated convergence gives the joint continuity; the continuity of
  `t ↦ ω(a,t)` comes from the bundle's `HasDerivAt` clause;
* `(x,t) ↦ BS (∂ₜω(·,t)) x` — same, using the bound `M₁` and the support of `∂ₜω(·,t)` on the strip
  (`slicesSupportedStrip_timeDeriv`; the continuity of `t ↦ ∂ₜω(a,t)` comes from the bundle's
  `TimeDerivStripHolder`, which needs `0 < α`).

**Note.**  The hypothesis `0 < α` is not cosmetic: at `α = 0` the bundle's `TimeDerivStripHolder`
clause reads `≤ N₁·|t-τ|^0 = N₁` (pure boundedness), and
`ω(y,t) = ψ(y)·t²·sin(1/t)` satisfies the whole bundle at `α = 0` while
`t ↦ BS(∂ₜω(·,t))(x) = G'(t)·BS ψ (x)` is discontinuous at `t = 0` (the *stated* lemma
`biotSavart_farStrip_holder` carries `hα : 0 < α`).

This is the input of the `ContDiffOn ℝ 1` clause of the far-strip `C^{1,α}` statement: with the
within-derivative on the strip identified with the operator `(D p) ∘ fst + (snd ·).smulRight (E p)`,
the characterisation `contDiffOn_succ_iff_fderivWithin` reduces `ContDiffOn ℝ 1` to
`DifferentiableOn` plus the continuity of that operator field.

**Proof.**  Glue `ω` to its affine continuation outside the strip (`windowExt ω S`), which satisfies
the two-sided window bundle (`windowExt_windowBundle`, using the `x`-Hölder regularity of `∂ₜω`
from `timeDeriv_xHolderOn_general`); the window theorem
`biotSavartSpacetimeC1_of_dtContinuous` then gives `ContDiffAt ℝ 1 (extField ω S) q` at every
`q` of the strip, hence `ContinuousAt (fderiv ℝ (extField ω S)) q`.  The two blocks of that
derivative, read off through `blocks_fderiv_slice_eq` / `blocks_fderiv_time_eq`, are the two target
fields on the strip; `ContinuousWithinAt.congr` transfers the continuity. -/
theorem continuousOn_farStrip_blocks {α : NNReal} (hα : 0 < (α : ℝ))
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ}
    (hS : 0 < S) (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ContinuousOn (fun p : Work.LWP.R3 × ℝ =>
        fderiv ℝ (Work.LWP.biotSavart (fun y => ω y p.2)) p.1)
      (Work.StabilityFar.farRegion (2 * R + 5) ×ˢ Set.Icc (0:ℝ) S) ∧
      ContinuousOn (fun p : Work.LWP.R3 × ℝ =>
        Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1)
      (Work.StabilityFar.farRegion (2 * R + 5) ×ˢ Set.Icc (0:ℝ) S) := by
  -- the strip bundle's differentiability clause and the positivity of `R`
  have hdiff := hbun.2.1.1
  have hRpos : 0 < R := hbun.1.1
  -- the two inputs coming from the generalised (no `hα1`) extension lemmas
  obtain ⟨hadmw, hdtc⟩ := windowExt_windowBundle hα hS hbun
    (timeDeriv_xHolderOn_general hα hS hbun)
  -- the `C¹` statement of the extension at every point of the strip
  have hpre : ∀ t ∈ Set.Icc (0:ℝ) S, t ∈ Work.ConstructionInstance.preWindow (S + 1) := by
    intro t ht
    change t ∈ Set.Ioo (-2 : ℝ) (S + 1)
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcd : ∀ q : R3 × ℝ, q.2 ∈ Set.Icc (0:ℝ) S → ContDiffAt ℝ 1 (extField ω S) q := by
    intro q hq
    exact biotSavartSpacetimeC1_of_dtContinuous (ω := windowExt ω S) (R := R) (T := S + 1)
      hadmw hdtc q.1 q.2 (hpre q.2 hq)
  -- continuity of the two assembled blocks
  have hcont1 : ∀ q : R3 × ℝ, q.2 ∈ Set.Icc (0:ℝ) S →
      ContinuousAt (fun p : R3 × ℝ =>
        (fderiv ℝ (extField ω S) p).comp (ContinuousLinearMap.inl ℝ R3 ℝ)) q := by
    intro q hq
    have h₁ : ContinuousAt (fderiv ℝ (extField ω S)) q :=
      (hcd q hq).continuousAt_fderiv one_ne_zero
    have h₂ : ContinuousAt (fun p : R3 × ℝ =>
        (ContinuousLinearMap.compL ℝ R3 (R3 × ℝ) R3) (fderiv ℝ (extField ω S) p)) q :=
      (ContinuousLinearMap.compL ℝ R3 (R3 × ℝ) R3).continuous.continuousAt.comp h₁
    have h₃ := h₂.clm_apply (continuousAt_const : ContinuousAt
      (fun _ : R3 × ℝ => (ContinuousLinearMap.inl ℝ R3 ℝ)) q)
    simpa only [ContinuousLinearMap.compL_apply] using h₃
  have hcont2 : ∀ q : R3 × ℝ, q.2 ∈ Set.Icc (0:ℝ) S →
      ContinuousAt (fun p : R3 × ℝ =>
        ((fderiv ℝ (extField ω S) p).comp (ContinuousLinearMap.inr ℝ R3 ℝ)) 1) q := by
    intro q hq
    have h₁ : ContinuousAt (fderiv ℝ (extField ω S)) q :=
      (hcd q hq).continuousAt_fderiv one_ne_zero
    have h₂ : ContinuousAt (fun p : R3 × ℝ =>
        (ContinuousLinearMap.compL ℝ ℝ (R3 × ℝ) R3) (fderiv ℝ (extField ω S) p)) q :=
      (ContinuousLinearMap.compL ℝ ℝ (R3 × ℝ) R3).continuous.continuousAt.comp h₁
    have h₃ := h₂.clm_apply (continuousAt_const : ContinuousAt
      (fun _ : R3 × ℝ => (ContinuousLinearMap.inr ℝ R3 ℝ)) q)
    have h₄ := h₃.clm_apply (continuousAt_const : ContinuousAt (fun _ : R3 × ℝ => (1:ℝ)) q)
    simpa only [ContinuousLinearMap.compL_apply] using h₄
  -- agreement of the `∂ₜ`-slices on the strip
  have hdt_agree : ∀ t ∈ Set.Icc (0:ℝ) S,
      (fun y => FiniteTimeSingularity.timeDeriv ω y t)
        = (fun y => FiniteTimeSingularity.timeDeriv (windowExt ω S) y t) := by
    intro t ht
    funext y
    rw [timeDeriv_windowExt hS hdiff y t, dtExt_of_mem_Icc ht]
  constructor
  · intro q hq
    refine (hcont1 q hq.2).continuousWithinAt.congr (fun p hp => ?_)
      (blocks_fderiv_slice_eq hq.2 (hcd q hq.2))
    exact blocks_fderiv_slice_eq hp.2 (hcd p hp.2)
  · intro q hq
    refine (hcont2 q hq.2).continuousWithinAt.congr (fun p hp => ?_)
      (by rw [hdt_agree q.2 hq.2]
          exact blocks_fderiv_time_eq hRpos hadmw hq.2 (hcd q hq.2))
    rw [hdt_agree p.2 hp.2]
    exact blocks_fderiv_time_eq hRpos hadmw hp.2 (hcd p hp.2)

end Work.CoreResiduals.BiotSavart
