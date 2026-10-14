import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_contDiffOn
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row3GGopen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.biotSavart_fderiv
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.continuousOn_farStrip_blocks =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.radPsi_zero_bound_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped ContDiff Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptQSmooth

open Work.FTS.PhiStar.RadialWAux (radPsi radP radPsi_zero_eq contDiffOn_tailIntegral)

/-!
# The `m = 0` (borderline) case of the outer rescaled Green piece `Ψ`

For a source `c` of class `C^{a+1}` on `(0,∞)` with `|c^{(k)}| ≤ K` there (`k ≤ a+1`) which
vanishes off `[a₀,b]` with `a₀ > 0`, the borderline piece

  `radPsi α 0 c z = ∫_{u > 1} c (z u) u^{-1} du`

is controlled uniformly: its first `a` derivatives are bounded by `C K` on `[z₀,∞)`, and it is
differentiable to order `a + 1` on `(0,∞)`.

The two ingredients are (i) the change of variables `t = z u`, which exhibits `radPsi α 0 c` as
the *tail integral* of `k t = c t / t` on `(0,∞)` (`radPsi_zero_eq`) — smoothness then follows
from `contDiffOn_tailIntegral` — and (ii) the observation that, because `c` is supported in
`[a₀,b]`, the outer integral may be truncated at the fixed `U = max 1 (2b/z₁)`, whereupon the
derivatives and their bounds are those of the truncated kernel
(`Deleg.truncated_kernel_facts`).
-/

/-- If the source vanishes off `[a₀,b]` then the rescaled outer integrand of `radPsi` vanishes
for `u` beyond `U = max 1 (2b/z₁)`, uniformly for `z ≥ z₁ > 0`. -/
lemma trunc_vanishing {c : ℝ → ℝ} {a₀ b z₁ : ℝ} (ha₀ : 0 < a₀) (hz₁ : 0 < z₁)
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) :
    ∀ z : ℝ, z₁ ≤ z → ∀ u : ℝ, max 1 (2 * b / z₁) < u → c (z * u) = 0 := by
  intro z hz u hu
  by_contra hne
  have hmem : z * u ∈ Set.Icc a₀ b := by
    by_contra h
    exact hne (hsupp (z * u) h)
  rw [Set.mem_Icc] at hmem
  have hU2 : 2 * b / z₁ < u := lt_of_le_of_lt (le_max_right (1 : ℝ) (2 * b / z₁)) hu
  have h1u : (1 : ℝ) < u := lt_of_le_of_lt (le_max_left (1 : ℝ) (2 * b / z₁)) hu
  have hzu : b < z * u := by
    have h1 : z₁ * (2 * b / z₁) < z₁ * u := mul_lt_mul_of_pos_left hU2 hz₁
    have h2 : z₁ * (2 * b / z₁) = 2 * b := by field_simp
    have h3 : z₁ * u ≤ z * u :=
      mul_le_mul_of_nonneg_right hz (le_of_lt (lt_trans zero_lt_one h1u))
    rw [h2] at h1
    linarith
  linarith [hmem.2]

/-- The rescaled outer piece, truncated at `U = max 1 (2b/z₁)`: if the source is supported in
`[a₀,b]` then for `z ≥ z₁ > 0` the outer integral may be taken over the fixed interval `(1,U)`. -/
lemma radPsi_zero_eq_trunc {α : ℝ} {c : ℝ → ℝ} {a₀ b z₁ z : ℝ} (ha₀ : 0 < a₀) (hz₁ : 0 < z₁)
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) (hz : z₁ ≤ z) :
    radPsi α 0 c z
      = ∫ u in (1 : ℝ)..(max 1 (2 * b / z₁)), c (z * u) * u ^ (-(radP α 0) - 1) := by
  set U : ℝ := max 1 (2 * b / z₁) with hUdef
  have hU1 : (1 : ℝ) ≤ U := le_max_left _ _
  rw [radPsi]
  have hsub : Set.Ioc (1 : ℝ) U ⊆ Set.Ioi (1 : ℝ) := fun x hx => hx.1
  have hvan : ∀ u ∈ Set.Ioi (1 : ℝ) \ Set.Ioc (1 : ℝ) U,
      c (z * u) * u ^ (-(radP α 0) - 1) = 0 := by
    intro u hu
    have hnu : ¬ (u ≤ U) := fun hle => hu.2 ⟨hu.1, hle⟩
    have huU : U < u := not_le.mp hnu
    rw [hUdef] at huU
    rw [trunc_vanishing ha₀ hz₁ hsupp z hz u huU, zero_mul]
  rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hvan]
  exact (intervalIntegral.integral_of_le hU1).symm

/-- Integrability of `t ↦ c t / t` on a tail, for a source which is continuous on `(0,∞)`,
bounded by `K` and supported in `[a₀,b]`, `a₀ > 0`. -/
lemma integrableOn_mul_inv_Ioi {c : ℝ → ℝ} {a₀ b K : ℝ} (ha₀ : 0 < a₀) (hK : 0 ≤ K)
    (hcont : ContinuousOn c (Set.Ioi 0)) (hb : ∀ t : ℝ, 0 < t → |c t| ≤ K)
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => c t * t⁻¹) (Set.Ioi a) volume := by
  have hkc : ContinuousOn (fun t : ℝ => c t * t⁻¹) (Set.Ioi 0) :=
    hcont.mul (continuousOn_id.inv₀ fun t ht => ne_of_gt ht)
  have hbound : ∀ t ∈ Set.Icc a₀ b, ‖c t * t⁻¹‖ ≤ K / a₀ := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha₀ ht.1
    have h2 : |t⁻¹| ≤ a₀⁻¹ := by
      rw [abs_inv, abs_of_pos ht0]
      exact inv_anti₀ ha₀ ht.1
    rw [Real.norm_eq_abs, abs_mul, div_eq_mul_inv]
    exact mul_le_mul (hb t ht0) h2 (abs_nonneg _)
      (le_trans (abs_nonneg _) (hb t ht0))
  have hmeas : AEStronglyMeasurable (fun t : ℝ => c t * t⁻¹)
      (volume.restrict (Set.Icc a₀ b)) :=
    ((hkc.mono fun t ht => lt_of_lt_of_le ha₀ ht.1).aestronglyMeasurable measurableSet_Icc)
  have hint : IntegrableOn (fun t : ℝ => c t * t⁻¹) (Set.Icc a₀ b) volume :=
    IntegrableOn.of_bound measure_Icc_lt_top hmeas (K / a₀)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hbound t ht)
  have hvan : (fun t : ℝ => c t * t⁻¹)
      = (Set.Icc a₀ b).indicator (fun t : ℝ => c t * t⁻¹) := by
    funext t
    by_cases ht : t ∈ Set.Icc a₀ b
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, hsupp t ht, zero_mul]
  have hkint : Integrable (fun t : ℝ => c t * t⁻¹) volume :=
    ((integrable_indicator_iff measurableSet_Icc).2 hint).congr
      (Eventually.of_forall (fun t => (congrFun hvan t).symm))
  exact hkint.mono_measure Measure.restrict_le_self

/-- Smoothness of the borderline outer piece `radPsi α 0 c`: on `(0,∞)` it is as smooth as the
source, no matter how small `α` is (the exponent `radP α 0 = 0` is critical, but the tail
integral `∫_{Ioi z} c t t^{-1} dt` is still differentiable, its integrand being continuous and
supported in `[a₀,b]`). -/
lemma radPsi_zero_contDiffOn {α : ℝ} {n : ℕ} {c : ℝ → ℝ} {a₀ b K : ℝ}
    (ha₀ : 0 < a₀) (hc : ContDiffOn ℝ (↑n) c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv n c K)
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) :
    ContDiffOn ℝ (↑n) (radPsi α 0 c) (Set.Ioi 0) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hb 0 (Nat.zero_le n) 1 one_pos)
  have hbdd : ∀ t : ℝ, 0 < t → |c t| ≤ K := fun t ht => hb 0 (Nat.zero_le n) t ht
  have hk : ContDiffOn ℝ (↑n) (fun t : ℝ => c t * t⁻¹) (Set.Ioi 0) := by
    refine hc.mul ?_
    have h : ContDiffOn ℝ (↑n) (fun y : ℝ => y ^ (-1 : ℝ)) (Set.Ioi 0) :=
      contDiffOn_id.rpow_const_of_ne (p := (-1 : ℝ)) (fun x hx => ne_of_gt hx)
    exact h.congr (fun y _ => by rw [Real.rpow_neg_one])
  have hint : ∀ a ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun t : ℝ => c t * t⁻¹) (Set.Ioi a) volume :=
    fun a ha => integrableOn_mul_inv_Ioi ha₀ hK hc.continuousOn hbdd hsupp ha
  have hT : ContDiffOn ℝ (↑(n + 1)) (fun z => ∫ t in Set.Ioi z, c t * t⁻¹) (Set.Ioi 0) :=
    contDiffOn_tailIntegral (n := n) hk hint
  refine (hT.of_le (by exact_mod_cast Nat.le_succ n)).congr (fun z hz => ?_)
  exact radPsi_zero_eq hz

theorem radPsi_zero_bound_hasDerivAt {α : ℝ} {a : ℕ} {a₀ b z₀ : ℝ}
    (ha₀ : 0 < a₀) (hz₀ : 0 < z₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ → ℝ} {K : ℝ}, 0 ≤ K →
      ContDiffOn ℝ (↑(a + 1)) c (Set.Ioi 0) → Work.FTS.PhiStar.BddDeriv (a + 1) c K →
      (∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) →
      (∀ j : ℕ, j ≤ a → ∀ z : ℝ, z₀ ≤ z →
          |iteratedDeriv j (fun z' => Work.FTS.PhiStar.RadialWAux.radPsi α 0 c z') z| ≤ C * K)
      ∧ (∀ j : ℕ, j + 1 ≤ a + 1 → ∀ z : ℝ, 0 < z →
          HasDerivAt (iteratedDeriv j (fun z' => Work.FTS.PhiStar.RadialWAux.radPsi α 0 c z'))
            (iteratedDeriv (j + 1) (fun z' => Work.FTS.PhiStar.RadialWAux.radPsi α 0 c z') z) z) := by
  set z₁ : ℝ := z₀ / 2 with hz₁def
  have hz₁ : 0 < z₁ := by rw [hz₁def]; linarith
  set U : ℝ := max 1 (2 * b / z₁) with hUdef
  have hU1 : (1 : ℝ) ≤ U := by rw [hUdef]; exact le_max_left _ _
  have hU0 : (0 : ℝ) < U := lt_of_lt_of_le zero_lt_one hU1
  refine ⟨U ^ (a + 2), pow_nonneg hU0.le _, ?_⟩
  intro c K hK hc hb hsupp
  have hsneg : -(radP α 0) - 1 ≤ (0 : ℝ) := by
    have h0 : radP α 0 = 0 := by simp [radP]
    rw [h0]; norm_num
  constructor
  · intro j hj z hz
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
    have hz1lt : z₁ < z := by rw [hz₁def]; linarith
    have hev : (fun z' => radPsi α 0 c z') =ᶠ[𝓝 z]
        fun x => ∫ u in (1 : ℝ)..U, c (x * u) * u ^ (-(radP α 0) - 1) := by
      have hmem : Set.Ici z₁ ∈ 𝓝 z :=
        mem_of_superset (isOpen_Ioi.mem_nhds hz1lt) (fun x hx => le_of_lt (show z₁ < x from hx))
      filter_upwards [hmem] with x hx
      rw [hUdef]
      exact radPsi_zero_eq_trunc ha₀ hz₁ hsupp hx
    have hbnd := (Work.FTS.PhiStar.Honesty.CptQSmooth.Deleg.truncated_kernel_facts
      (N := a + 1) (c := c) (K := K) (U := U) (s := -(radP α 0) - 1)
      hK hU1 hsneg hc hb j (by omega) z hzpos).2
    rw [max_eq_right hU1] at hbnd
    rw [hev.iteratedDeriv_eq j]
    exact hbnd.trans (by rw [mul_comm])
  · intro j hj z hz
    have hcd : ContDiffOn ℝ (↑(a + 1))
        (fun z' => radPsi α 0 c z') (Set.Ioi 0) :=
      radPsi_zero_contDiffOn ha₀ hc hb hsupp
    have hcAt : ContDiffAt ℝ (↑(a + 1)) (fun z' => radPsi α 0 c z') z :=
      hcd.contDiffAt (isOpen_Ioi.mem_nhds hz)
    exact Work.FTS.PhiStar.Series.SmoothAux.Deleg.rpr_hasDerivAt_iteratedDeriv hcAt (by omega)

end Work.FTS.PhiStar.Honesty.CptQSmooth
end
end
-- ===== merged: Submission.Work.FTS_MuLamOK.Rows.GgRowsEnv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-! ## The arithmetic of the row constants -/

/-- `√(C_A/(γ-1)) = √(10·C_A)·α^{-1/2}` (`γ - 1 = α/10`). -/
private theorem sqrt_div_gam_gg {CA α : ℝ} (hCA : 0 ≤ CA) (hα : 0 < α) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) = Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ)) := by
  have hγ : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have h10 : (0 : ℝ) ≤ 10 * CA := by linarith
  have hsq : (Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ))) ^ 2 = CA / (Work.Spaces.gam α - 1) := by
    rw [mul_pow, Real.sq_sqrt h10, ← Real.rpow_two, ← Real.rpow_mul hα.le,
      show -(1 / 2 : ℝ) * 2 = -1 by norm_num, Real.rpow_neg_one, hγ]
    field_simp
  rw [← hsq, Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hα.le _))]

/-- **The row constant is dominated by `Env`.**  For `0 < α ≤ 1`, `C_A, B ≥ 0` and `0 ≤ c ≤ 2`,
the row expression `√(C_A/(γ-1))·3√(π/2)·c·B·|g|²_{ℋ⁴}` is at most
`(6·√(π/2)·√(10·C_A)·B + 1)·Env α g` (because `α^{-1/2}·c ≤ 2·α^{-3/2}` and
`α^{-3/2}·|g|²_{ℋ⁴} ≤ Env α g`). -/
private theorem rowConstLe_gg {α CA B c : ℝ} {g : Fn} (hCA : 0 ≤ CA) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hc2 : c ≤ 2) (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * c * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2
      ≤ (6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B + 1)
        * Work.FTS.NonlinRows.Rl1.Env α g := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hX2 : 0 ≤ (Work.FTS.Nonlin.Xn α g) ^ 2 := sq_nonneg _
  have hEnv : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α g :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg g hα.le
  have hp3 : 0 ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- `α^{-1/2} ≤ α^{-3/2}`
  have hpow : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) := by
    have h1 : α ^ (-(3 / 2 : ℝ)) = α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hα]
      congr 1
      norm_num
    rw [h1]
    have h2 : 1 ≤ α ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]
      simpa only [one_div] using one_le_one_div hα hα1
    have h3 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    nlinarith
  have h0 : 0 ≤ 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) hB
  have hpos : 0 ≤ Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
      * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))) hB) hX2
  have hstep1 : α ^ (-(1 / 2 : ℝ)) * c ≤ 2 * α ^ (-(3 / 2 : ℝ)) := by
    have h := mul_le_mul hpow hc2 hc hp3
    linarith [h]
  -- `α^{-3/2}·|g|² ≤ Env`
  have hEnvge : α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2
      ≤ Work.FTS.NonlinRows.Rl1.Env α g := by
    rw [Work.FTS.NonlinRows.Rl1.Env]
    have h1 : 0 ≤ α ^ 2 := sq_nonneg α
    have h2 : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hX
    linarith
  rw [sqrt_div_gam_gg hCA hα]
  have h1 : Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ)) * (3 * Real.sqrt (Real.pi / 2)) * c * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2
      = (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
          * (Work.FTS.Nonlin.Xn α g) ^ 2) * (α ^ (-(1 / 2 : ℝ)) * c) := by ring
  rw [h1]
  have h2 : (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2) * (α ^ (-(1 / 2 : ℝ)) * c)
      ≤ (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2) * (2 * α ^ (-(3 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hstep1 hpos
  have h3 : (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2) * (2 * α ^ (-(3 / 2 : ℝ)))
      = 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2) := by ring
  have h4 : 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2)
      ≤ 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * Work.FTS.NonlinRows.Rl1.Env α g :=
    mul_le_mul_of_nonneg_left hEnvge h0
  have h5 : 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * Work.FTS.NonlinRows.Rl1.Env α g
      ≤ (6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B + 1)
        * Work.FTS.NonlinRows.Rl1.Env α g := by
    nlinarith [hEnv]
  exact le_trans h2 (le_trans (le_of_eq h3) (le_trans h4 h5))

/-! ## The three rows against `Env` -/

theorem GgRowsEnv (Ce : ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f Ξg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.VocabO.EllPkgGo α Ce f Ξg →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1gg α f Ξg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2gg α f Ξg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3gg α f Ξg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  obtain ⟨CA, hCA, hang⟩ := Work.FTS.NonlinRows.Rl1.angSup_le
  refine ⟨6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * max Ce 0 + 1, ?_, ?_⟩
  · have h : 0 ≤ 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * max Ce 0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (le_max_right Ce 0)
    linarith
  intro α f Ξg hα hα1 hso hmem hEll
  have hB0 : 0 ≤ max Ce 0 := le_max_right Ce 0
  -- the two row constants, dominated by `Env`
  have hrc12 := rowConstLe_gg (α := α) (CA := CA) (B := max Ce 0) (c := 2) (g := f)
    hCA.le hB0 (by norm_num) (by norm_num) hα hα1
  have hrc3 := rowConstLe_gg (α := α) (CA := CA) (B := max Ce 0) (c := 2 * α) (g := f)
    hCA.le hB0 (by positivity) (by linarith) hα hα1
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row1GGopen (CA := CA) hCA
      (α := α) (Ce := Ce) hα hso hmem hEll
      (fun z θ hz hθ0 hθ1 =>
        hang α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg)) hα hα1
          hEll.R.1.1 hEll.R.1.2 z θ hz hθ0 hθ1)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have heq : Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * 2
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2
        = Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * 6
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2 := by ring
    rw [← heq]
    exact hrc12
  · have h2 := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row2GGopen (CA := CA) hCA
      (α := α) (Ce := Ce) hα hso hmem hEll
      (fun z θ hz hθ0 hθ1 =>
        hang α (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) z θ
            / Work.Construction.s2 θ) hα hα1 hEll.U.1.1 hEll.U.1.2 z θ hz hθ0 hθ1)
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    have heq : Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * 2
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2
        = Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * 6
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2 := by ring
    rw [← heq]
    exact hrc12
  · have h3 := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row3GGopen (CA := CA) hCA
      (α := α) (Ce := Ce) hα hso hmem hEll
      (fun z θ hz hθ0 hθ1 =>
        hang α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg)) hα hα1
          hEll.V.1.1 hEll.V.1.2 z θ hz hθ0 hθ1)
    refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
    have heq : Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * (2 * α)
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2
        = Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * (6 * α)
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2 := by ring
    rw [← heq]
    exact hrc3

end

end Work.FTS_MuLamOK.Rows
end
-- ===== merged: Submission.Work.FTS_RegExport.RX0.hzmodp_ext_c4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RX0

theorem hzmodp_ext_c4 {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hc4 : ∀ τ ∈ Set.Icc 0 S, ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Regularity.gSlice g τ)) Work.FTS.EllipticEst.Q0)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    (hsup : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ| ≤ M)
    (hsup2 : ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ| ≤ M₂) :
    ∃ Nz : ℝ, 0 ≤ Nz ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
          - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ|
          ≤ Nz * |z - z'| ^ α := by
  obtain ⟨M, hM0, hM⟩ := hsup
  obtain ⟨M₂, hM₂0, hM₂⟩ := hsup2
  have hN0 : 0 ≤ max M₂ (2 * M) := le_trans hM₂0 (le_max_left _ _)
  refine ⟨max M₂ (2 * M), hN0, ?_⟩
  intro τ hτ z z' hz hz' θ hθ
  set F : ℝ → ℝ → ℝ := fun z θ => Work.FTS.RegPkgGal.extG g z θ τ with hF
  by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
  · -- the angular interior: everything happens at `θ ∈ (0,π/2)`
    set f : ℝ → ℝ := fun z => Work.Spaces.pz F z θ with hf
    change |f z - f z'| ≤ max M₂ (2 * M) * |z - z'| ^ α
    -- `f` is continuous at `0`, because `g̃` is `C¹` jointly near `(0,τ)` and vanishes for `z ≤ 0`
    have hcont_f : ContinuousAt f 0 := by
      have hslice1 : ContDiffOn ℝ 1 (fun z : ℝ => Work.FTS.RegPkgGal.extG g z θ τ)
          (Set.Ioi (-1)) := by
        have hcomp := (hcont θ hθ).comp (f := fun z : ℝ => (z, τ)) (by fun_prop)
          (fun z hz => ⟨hz, ⟨by linarith [hτ.1], by linarith [hτ.2, hS]⟩⟩)
        simpa [Function.comp_def] using hcomp
      have hcd : ContinuousOn (deriv (fun z : ℝ => Work.FTS.RegPkgGal.extG g z θ τ))
          (Set.Ioi (-1)) :=
        hslice1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
      have h0 : (0 : ℝ) ∈ Set.Ioi (-1) := by norm_num
      have hca : ContinuousAt (deriv (fun z : ℝ => Work.FTS.RegPkgGal.extG g z θ τ)) 0 :=
        hcd.continuousAt (isOpen_Ioi.mem_nhds h0)
      have hfeq : f = deriv (fun z : ℝ => Work.FTS.RegPkgGal.extG g z θ τ) := by
        funext x
        simp only [hf, hF, Work.Spaces.pz]
      rwa [hfeq]
    -- on `(0,∞)` the function `f` is the `z`-derivative of the smooth slice `g(·,θ,τ)`
    have hEqOn : Set.EqOn f (deriv (fun z : ℝ => g z θ τ)) (Set.Ioi 0) := by
      intro x hx
      have hev : (fun z' => F z' θ) =ᶠ[𝓝 x] (fun z' => g z' θ τ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
        rw [hF]
        exact Work.FTS.RegPkgGal.extG_of_pos hu hτ.1
      have h1 : f x = deriv (fun z' => F z' θ) x := by rw [hf]; rfl
      rw [h1]
      exact hev.deriv_eq
    -- the slice `z ↦ g z θ τ` is `C²` on `(0,∞)`: this is the only use of `hc4`
    have hcomp4 : ContDiffOn ℝ 4 (fun z : ℝ => g z θ τ) (Set.Ioi 0) := by
      have hs : ContDiffOn ℝ 4 (fun z : ℝ => (z, θ)) (Set.Ioi 0) :=
        (contDiffOn_id : ContDiffOn ℝ 4 (fun z : ℝ => z) (Set.Ioi 0)).prodMk contDiffOn_const
      have h := (hc4 τ hτ).comp hs (fun z hz => by
        rw [Work.FTS.EllipticEst.mem_Q0]
        exact ⟨hz, hθi.1, hθi.2⟩)
      simpa [Function.uncurry, Function.comp_def, Work.FTS.Regularity.gSlice] using h
    have hsl : ContDiffOn ℝ 2 (fun z : ℝ => g z θ τ) (Set.Ioi 0) :=
      hcomp4.of_le (by norm_num)
    have hd1 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => g z θ τ)) (Set.Ioi 0) :=
      hsl.deriv_of_isOpen isOpen_Ioi (by norm_num)
    have hdiff_deriv : DifferentiableOn ℝ (deriv (fun z : ℝ => g z θ τ)) (Set.Ioi 0) :=
      hd1.differentiableOn_one
    have hdiff_f : DifferentiableOn ℝ f (Set.Ioi (0 : ℝ)) := hdiff_deriv.congr hEqOn
    have hdiff : ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ f x := by
      intro x hx
      exact (hdiff_f x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
    have hbd : ∀ x ∈ Set.Ioi (0 : ℝ), |deriv f x| ≤ M₂ := by
      intro x hx
      have h1 : deriv f x = Work.Spaces.pz (Work.Spaces.pz F) x θ := by rw [hf]; rfl
      rw [h1, hF]
      exact hM₂ τ hτ x θ hx hθ
    have hbdd : ∀ x : ℝ, 0 ≤ x → |f x| ≤ M := by
      intro x hx
      have h1 : f x = Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) x θ := by
        rw [hf, hF]
      rw [h1]
      exact hM τ hτ x θ hx hθ
    have hlip : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |f z - f z'| ≤ M₂ * |z - z'| :=
      Work.FTS.RegPkgGal.Der.Lib.lip_of_bounded_deriv hM₂0 hdiff hbd hcont_f
    exact Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded hα hα1 hM₂0 hM0 hlip hbdd
      z z' hz hz'
  · -- the two angular endpoints: the whole slice vanishes
    have hθ0 : θ = 0 ∨ θ = π / 2 := by
      by_cases h1 : θ = 0
      · exact Or.inl h1
      · refine Or.inr ?_
        by_contra h2
        exact hθi ⟨lt_of_le_of_ne hθ.1 (Ne.symm h1), lt_of_le_of_ne hθ.2 h2⟩
    have hgz : ∀ w : ℝ, Work.FTS.RegPkgGal.extG g w θ τ = 0 := by
      intro w
      by_cases hw : w ≤ 0
      · exact Work.FTS.RegPkgGal.extG_of_nonpos hw
      · rw [Work.FTS.RegPkgGal.extG_of_pos (not_le.mp hw) hτ.1]
        rcases hθ0 with rfl | rfl
        · exact (hvan τ hτ w (le_of_lt (not_le.mp hw))).1
        · exact (hvan τ hτ w (le_of_lt (not_le.mp hw))).2
    have hFz : ∀ w : ℝ, F w θ = 0 := by
      intro w
      rw [hF]
      exact hgz w
    have hfz : ∀ w : ℝ, Work.Spaces.pz F w θ = 0 := by
      intro w
      have hz : (fun w' => F w' θ) = fun _ => (0 : ℝ) := funext hFz
      change deriv (fun w' => F w' θ) w = 0
      rw [hz]; simp
    change |Work.Spaces.pz F z θ - Work.Spaces.pz F z' θ| ≤ max M₂ (2 * M) * |z - z'| ^ α
    rw [hfz z, hfz z']
    simp only [sub_self, abs_zero]
    exact mul_nonneg hN0 (Real.rpow_nonneg (abs_nonneg _) α)

end Work.FTS_RegExport.RX0
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.st1_fb_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Set Filter MeasureTheory
open scoped Real Topology

namespace Work.FTS_RegExport.RXT

/-- `Γ(θ) ≤ θ^α` on `Iθ`. -/
theorem fb_Gamma_le_self {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.Regularity.Gamma α θ ≤ θ ^ α := by
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hnn : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hsin0 (sq_nonneg _)
  have hle : Real.sin θ * Real.cos θ ^ 2 ≤ θ := by
    have h1 : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * 1 :=
      mul_le_mul_of_nonneg_left hcos2 hsin0
    have h2 : Real.sin θ ≤ θ := Real.sin_le hθ.1
    linarith
  have hG : Work.FTS.Regularity.Gamma α θ = (Real.sin θ * Real.cos θ ^ 2) ^ α := rfl
  rw [hG]
  exact Real.rpow_le_rpow hnn hle hα.le

/-- `Γ(θ) ≤ (π/2)^α·(π/2-θ)^α` on `Iθ`. -/
theorem fb_Gamma_le_endpoint {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.Regularity.Gamma α θ ≤ (Real.pi / 2) ^ α * (Real.pi / 2 - θ) ^ α := by
  set y : ℝ := Real.pi / 2 - θ with hy
  have hy0 : 0 ≤ y := by rw [hy]; linarith [hθ.2, Real.pi_pos]
  have hyhalf : y ≤ Real.pi / 2 := by rw [hy]; linarith [hθ.1]
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hcos0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hcosy : Real.cos θ = Real.sin y := by
    rw [hy]; exact (Real.sin_pi_div_two_sub θ).symm
  have h1 : Work.FTS.Regularity.Gamma α θ ≤ (Real.cos θ ^ 2) ^ α := by
    have hG : Work.FTS.Regularity.Gamma α θ = (Real.sin θ * Real.cos θ ^ 2) ^ α := rfl
    rw [hG]
    refine Real.rpow_le_rpow (mul_nonneg hsin0 (sq_nonneg _)) ?_ hα.le
    have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    nlinarith [sq_nonneg (Real.cos θ), hsin0]
  have h2 : (Real.cos θ ^ 2) ^ α = Real.sin y ^ (2 * α) := by
    have ha : (Real.cos θ ^ 2) ^ α = Real.cos θ ^ (((2:ℕ):ℝ) * α) := by
      rw [← Real.rpow_natCast (Real.cos θ) 2, ← Real.rpow_mul hcos0]
    rw [ha, show ((2:ℕ):ℝ) * α = 2 * α by norm_num, hcosy]
  have h3 : Real.sin y ^ (2 * α) ≤ y ^ (2 * α) :=
    Real.rpow_le_rpow (Real.sin_nonneg_of_mem_Icc ⟨hy0, by linarith [Real.pi_pos]⟩)
      (Real.sin_le hy0) (by positivity)
  have h4 : y ^ (2 * α) = (y * y) ^ α := by
    have ha : y ^ (2 * α) = (y ^ (2:ℝ)) ^ α := Real.rpow_mul hy0 2 α
    rw [ha, show y ^ (2:ℝ) = y * y by rw [Real.rpow_two]; ring]
  have h5 : (y * y) ^ α ≤ (y * (Real.pi / 2)) ^ α := by
    refine Real.rpow_le_rpow (mul_nonneg hy0 hy0) ?_ hα.le
    nlinarith [hy0, hyhalf]
  have h6 : (y * (Real.pi / 2)) ^ α = y ^ α * (Real.pi / 2) ^ α :=
    Real.mul_rpow hy0 (by linarith [Real.pi_pos])
  calc Work.FTS.Regularity.Gamma α θ ≤ (Real.cos θ ^ 2) ^ α := h1
    _ = Real.sin y ^ (2 * α) := h2
    _ ≤ y ^ (2 * α) := h3
    _ = (y * y) ^ α := h4
    _ ≤ (y * (Real.pi / 2)) ^ α := h5
    _ = y ^ α * (Real.pi / 2) ^ α := h6
    _ = (Real.pi / 2) ^ α * (Real.pi / 2 - θ) ^ α := by rw [hy]; ring

/-- `Γ(θ)/sin 2θ ≤ M·θ^{α-1} + N·(π/2-θ)^{2α-1}` on `(0,π/2)`, with the two rates of `R4b`. -/
theorem fb_density_le {α M N : ℝ} (hM0 : 0 ≤ M) (hN0 : 0 ≤ N)
    (hM : ∀ t : ℝ, 0 < t → t ≤ Real.pi / 4 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ M * t ^ (α - 1))
    (hN : ∀ t : ℝ, Real.pi / 4 ≤ t → t < Real.pi / 2 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ N * (Real.pi / 2 - t) ^ (2 * α - 1))
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < Real.pi / 2) :
    Work.FTS.Regularity.Gamma α x / Real.sin (2 * x)
      ≤ M * x ^ (α - 1) + N * (Real.pi / 2 - x) ^ (2 * α - 1) := by
  rcases le_or_gt x (Real.pi / 4) with hxle | hxgt
  · have h1 := hM x hx0 hxle
    have h2 : 0 ≤ N * (Real.pi / 2 - x) ^ (2 * α - 1) :=
      mul_nonneg hN0 (Real.rpow_nonneg (by linarith) _)
    linarith
  · have h1 := hN x (le_of_lt hxgt) hx1
    have h2 : 0 ≤ M * x ^ (α - 1) := mul_nonneg hM0 (Real.rpow_nonneg hx0.le _)
    linarith

theorem theta_modulus_uniform_fb {α C K : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hC : 0 ≤ C)
    (hK : 0 ≤ K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ⦃u u' : ℝ → ℝ⦄,
      (∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2), HasDerivAt u (u' x) x) →
      (∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |u' x| ≤ C * (Work.FTS.Regularity.Gamma α x / Real.sin (2 * x))) →
      (∀ x ∈ Work.Spaces.Iθ, |u x| ≤ K * Work.FTS.Regularity.Gamma α x) →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ, |u θ - u θ'| ≤ L * |θ - θ'| ^ α := by
  have hα1 : α ≤ 1 := by linarith
  have hα2 : 2 * α ≤ 1 := by linarith
  obtain ⟨M, hM0, hM⟩ := Work.FTS.RegPkgGal.R4b.primBoundLeft hα
  obtain ⟨N, hN0, hN⟩ := Work.FTS.RegPkgGal.R4b.primBoundRight hα
  set P : ℝ := (Real.pi / 2) ^ α with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hD0 : 0 ≤ (C * M + C * N * P) / α :=
    div_nonneg (add_nonneg (mul_nonneg hC hM0) (mul_nonneg (mul_nonneg hC hN0) hP0)) hα.le
  have hKP0 : 0 ≤ K * P := mul_nonneg hK hP0
  set L : ℝ := K + K * P + (C * M + C * N * P) / α with hL
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  refine ⟨L, hL0, ?_⟩
  intro u u' hderiv hbd hval
  have hKL : K ≤ L := by rw [hL]; linarith
  have hKP : K * P ≤ L := by rw [hL]; linarith
  have hCD : ∀ T : ℝ, 0 ≤ T → C * (M * (T / α) + N * (P * T / (2 * α))) ≤ L * T := by
    intro T hT
    have hstep : C * (M * (T / α) + N * (P * T / (2 * α)))
        = (C * M * T + C * N * P * T / 2) / α := by
      field_simp
    have hLα : L * α = (K + K * P) * α + (C * M + C * N * P) := by
      rw [hL]; field_simp
    have hCNPT : 0 ≤ C * N * P * T := mul_nonneg (mul_nonneg (mul_nonneg hC hN0) hP0) hT
    have h1 : C * M * T + C * N * P * T / 2 ≤ (C * M + C * N * P) * T := by
      nlinarith [hCNPT]
    have h3 : 0 ≤ (K + K * P) * α := mul_nonneg (by linarith) hα.le
    have h4 : (C * M + C * N * P) * T
        ≤ ((K + K * P) * α + (C * M + C * N * P)) * T :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h3) hT
    have h5 : ((K + K * P) * α + (C * M + C * N * P)) * T = (L * T) * α := by
      rw [← hLα]; ring
    rw [hstep, div_le_iff₀ hα, ← h5]
    linarith
  have key : ∀ a b : ℝ, a ∈ Work.Spaces.Iθ → b ∈ Work.Spaces.Iθ → a ≤ b →
      |u b - u a| ≤ L * (b - a) ^ α := by
    intro a b ha hb hab
    have hba0 : 0 ≤ b - a := sub_nonneg.mpr hab
    rcases eq_or_lt_of_le ha.1 with ha0 | hapos
    · have hz : u 0 = 0 := by
        have h := hval 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
        have hΓ0 : Work.FTS.Regularity.Gamma α 0 = 0 := by
          have hs : Real.sin (0:ℝ) * Real.cos (0:ℝ) ^ 2 = 0 := by
            rw [Real.sin_zero, Real.cos_zero]; ring
          rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, hs,
            Real.zero_rpow (ne_of_gt hα)]
        rw [hΓ0, mul_zero] at h
        exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      rw [← ha0, hz, sub_zero, sub_zero]
      have h1 : Work.FTS.Regularity.Gamma α b ≤ b ^ α := fb_Gamma_le_self hα hb
      calc |u b| ≤ K * Work.FTS.Regularity.Gamma α b := hval b hb
        _ ≤ K * b ^ α := mul_le_mul_of_nonneg_left h1 hK
        _ ≤ L * b ^ α := mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg hb.1 α)
    · rcases eq_or_lt_of_le hb.2 with hbπ | hblt
      · have hz : u (Real.pi / 2) = 0 := by
          have h := hval (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩
          have hΓπ : Work.FTS.Regularity.Gamma α (Real.pi / 2) = 0 := by
            have hs : Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2 = 0 := by
              rw [Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
            rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, hs,
              Real.zero_rpow (ne_of_gt hα)]
          rw [hΓπ, mul_zero] at h
          exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
        rw [hbπ, hz, zero_sub, abs_neg]
        have h1 : Work.FTS.Regularity.Gamma α a ≤ P * (Real.pi / 2 - a) ^ α :=
          fb_Gamma_le_endpoint hα ha
        have h2 : 0 ≤ (Real.pi / 2 - a) ^ α := Real.rpow_nonneg (by linarith [ha.2]) α
        calc |u a| ≤ K * Work.FTS.Regularity.Gamma α a := hval a ha
          _ ≤ K * (P * (Real.pi / 2 - a) ^ α) := mul_le_mul_of_nonneg_left h1 hK
          _ = (K * P) * (Real.pi / 2 - a) ^ α := by ring
          _ ≤ L * (Real.pi / 2 - a) ^ α := mul_le_mul_of_nonneg_right hKP h2
      · have hcont : ContinuousOn u (Set.Icc a b) := by
          have hd : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) :=
            fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
          exact hd.continuousOn.mono
            (fun x hx => ⟨lt_of_lt_of_le hapos hx.1, lt_of_le_of_lt hx.2 hblt⟩)
        have hmaj : ∀ x ∈ Set.Ioo a b,
            ‖u' x‖ ≤ C * (M * x ^ (α - 1) + N * (Real.pi / 2 - x) ^ (2 * α - 1)) := by
          intro x hx
          rw [Real.norm_eq_abs]
          have hx0 : 0 < x := lt_trans hapos hx.1
          have hx1 : x < Real.pi / 2 := lt_trans hx.2 hblt
          calc |u' x| ≤ C * (Work.FTS.Regularity.Gamma α x / Real.sin (2 * x)) :=
                hbd x ⟨hx0, hx1⟩
            _ ≤ C * (M * x ^ (α - 1) + N * (Real.pi / 2 - x) ^ (2 * α - 1)) :=
                mul_le_mul_of_nonneg_left (fb_density_le hM0 hN0 hM hN hx0 hx1) hC
        have hMint : IntervalIntegrable (fun x : ℝ => M * x ^ (α - 1)) volume a b :=
          (intervalIntegral.intervalIntegrable_rpow'
            (show (-1:ℝ) < α - 1 by linarith)).const_mul M
        have hNint : IntervalIntegrable
            (fun x : ℝ => N * (Real.pi / 2 - x) ^ (2 * α - 1)) volume a b := by
          have hbase : IntervalIntegrable (fun x : ℝ => x ^ (2 * α - 1)) volume
              (Real.pi / 2 - b) (Real.pi / 2 - a) :=
            intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < 2 * α - 1 by linarith)
          have hcomp := hbase.comp_sub_left (Real.pi / 2)
          rw [show Real.pi / 2 - (Real.pi / 2 - b) = b by ring,
            show Real.pi / 2 - (Real.pi / 2 - a) = a by ring] at hcomp
          exact hcomp.symm.const_mul N
        have hmaj_int : IntervalIntegrable
            (fun x : ℝ => C * (M * x ^ (α - 1) + N * (Real.pi / 2 - x) ^ (2 * α - 1)))
            volume a b := (hMint.add hNint).const_mul C
        have hftc := Work.FTS.RegPkgGal.R4d.abs_sub_le_integral_of_continuousOn hab hcont
          (fun x hx => hderiv x ⟨lt_trans hapos hx.1, lt_trans hx.2 hblt⟩)
          hmaj_int hmaj
        have hint1 : ∫ x in a..b, M * x ^ (α - 1) = M * ((b ^ α - a ^ α) / α) := by
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (show (-1:ℝ) < α - 1 by linarith)),
            show α - 1 + 1 = α by ring]
        have hint2 : ∫ x in a..b, N * (Real.pi / 2 - x) ^ (2 * α - 1)
            = N * (((Real.pi / 2 - a) ^ (2 * α) - (Real.pi / 2 - b) ^ (2 * α)) / (2 * α)) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (2 * α - 1)) (Real.pi / 2),
            integral_rpow (Or.inl (show (-1:ℝ) < 2 * α - 1 by linarith)),
            show 2 * α - 1 + 1 = 2 * α by ring]
        have hInt : ∫ x in a..b, C * (M * x ^ (α - 1) + N * (Real.pi / 2 - x) ^ (2 * α - 1))
            = C * (M * ((b ^ α - a ^ α) / α)
              + N * (((Real.pi / 2 - a) ^ (2 * α) - (Real.pi / 2 - b) ^ (2 * α)) / (2 * α))) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add hMint hNint, hint1, hint2]
        have hb1 : b ^ α - a ^ α ≤ (b - a) ^ α := by
          have h := Real.rpow_add_le_add_rpow ha.1 hba0 hα.le hα1
          rw [show a + (b - a) = b by ring] at h
          linarith
        have hb2 : (Real.pi / 2 - a) ^ (2 * α) - (Real.pi / 2 - b) ^ (2 * α)
            ≤ P * (b - a) ^ α := by
          have hx0 : 0 ≤ Real.pi / 2 - b := by linarith [hb.2, Real.pi_pos]
          have hsub := Real.rpow_add_le_add_rpow hx0 hba0 (by linarith : (0:ℝ) ≤ 2 * α) hα2
          have hid : Real.pi / 2 - a = (Real.pi / 2 - b) + (b - a) := by ring
          have hmain : (Real.pi / 2 - a) ^ (2 * α)
              ≤ (Real.pi / 2 - b) ^ (2 * α) + (b - a) ^ (2 * α) := by
            rw [hid]; exact hsub
          have hy : (b - a) ^ (2 * α) ≤ (b - a) ^ α * P := by
            have h1 : (b - a) ^ (2 * α) = ((b - a) * (b - a)) ^ α := by
              have ha' : (b - a) ^ (2 * α) = ((b - a) ^ (2:ℝ)) ^ α := Real.rpow_mul hba0 2 α
              rw [ha', show (b - a) ^ (2:ℝ) = (b - a) * (b - a) by rw [Real.rpow_two]; ring]
            rw [h1]
            have h2 : (b - a) * (b - a) ≤ (b - a) * (Real.pi / 2) :=
              mul_le_mul_of_nonneg_left (by linarith [ha.1, hb.2, Real.pi_pos]) hba0
            calc ((b - a) * (b - a)) ^ α ≤ ((b - a) * (Real.pi / 2)) ^ α :=
                  Real.rpow_le_rpow (mul_nonneg hba0 hba0) h2 hα.le
              _ = (b - a) ^ α * P := by
                  rw [Real.mul_rpow hba0 (by linarith [Real.pi_pos]), hP]
          have hT0 : 0 ≤ (b - a) ^ α := Real.rpow_nonneg hba0 α
          linarith
        refine le_trans hftc ?_
        rw [hInt]
        have hstep : C * (M * ((b ^ α - a ^ α) / α)
              + N * (((Real.pi / 2 - a) ^ (2 * α) - (Real.pi / 2 - b) ^ (2 * α)) / (2 * α)))
            ≤ C * (M * ((b - a) ^ α / α) + N * (P * (b - a) ^ α / (2 * α))) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          have h1 : M * ((b ^ α - a ^ α) / α) ≤ M * ((b - a) ^ α / α) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb1 hα.le) hM0
          have h2 : N * (((Real.pi / 2 - a) ^ (2 * α) - (Real.pi / 2 - b) ^ (2 * α)) / (2 * α))
              ≤ N * (P * (b - a) ^ α / (2 * α)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb2 (by linarith)) hN0
          linarith
        exact le_trans hstep (hCD ((b - a) ^ α) (Real.rpow_nonneg hba0 α))
  intro θ hθ θ' hθ'
  rcases le_total θ θ' with hle | hle
  · have h := key θ θ' hθ hθ' hle
    have h1 : |θ - θ'| = θ' - θ := by
      rw [abs_sub_comm θ θ', abs_of_nonneg (sub_nonneg.mpr hle)]
    have h2 : |u θ - u θ'| = |u θ' - u θ| := abs_sub_comm _ _
    rw [h1, h2]
    exact h
  · have h := key θ' θ hθ' hθ hle
    have h1 : |θ - θ'| = θ - θ' := abs_of_nonneg (sub_nonneg.mpr hle)
    rw [h1]
    exact h

end Work.FTS_RegExport.RXT
end
end
