import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLCompLeaf.exists_compact_continuous_of_U6

/-!
# C8/Leaf — `luzin_riesz` **with the local-finiteness hypothesis** (the correct statement)

`Submission/Work/EKLCompLeaf/luzin_riesz.lean` requests

`U6clause μ ν X'` ⟹ (compact `X₁ ⊆ X'`, `μ X₁ > 1 - η`, every `f ↦ ∫ f dν ·` continuous on `X₁`,
and: two `ν`-equal sequences in `X₁` converging in `X₃` have `ν`-equal limits).

That statement is **false**: `U6clause` alone says only that `x ↦ ∫ f dν x` is continuous, which
after taking limits gives `∫ f dν y = ∫ f dν y'` for all `f : C_c(SL₃(ℝ), ℝ)`.  Passing from
this to `ν y = ν y'` is *Riesz uniqueness*, which requires the two measures to be finite on
compacts (`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`,
`RealRMK.measure_le_of_isCompact_of_integral` — Mathlib warns there that `IsFiniteMeasureOnCompacts`
cannot be dropped).  Without it one can take `ν x ∈ {⊤ • δ_p, ⊤ • δ_q}` (`p ≠ q`): both have every
`C_c`-integral equal to `0` (see `Work.EKLCompLeaf.exists_cc_invisible_measures`), so `U6clause`
holds trivially, while the last clause can be violated on a "double Bernstein" partition of `X₃`.

The statement proved here adds exactly that hypothesis, which the source lemma
(`Work.EKLComp.prove_LowEntropyCore.luzin_riesz`, via `Work.EKLContract.IsLeafwise.radon`, or via
`Work.EKLCompLeaf.fixRadon`) supplies in the application.  Proof = the two halves:

* `Work.EKLCompLeaf.exists_compact_continuous_of_U6` : `U6clause` ⟹ a compact `X₁ ⊆ X'` with
  `μ X₁ > 1 - η` and continuity of all the test-function integrals on `X₁`;
* `eq_of_tendsto_of_cc_integrals` (below) : continuity on compact `X₁` + local finiteness of `ν x`
  on `X₁` ⟹ `ν y = ν y'` for `ν`-equal sequences with limits `y`, `y'`.
-/

set_option linter.style.haveILetI false

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLCompLeaf

open Work.EKLContract

/-- **Riesz half of the corrected `luzin_riesz`.**  On a compact set `X₁` on which all the
test-function integrals are continuous, and where every `ν x` is finite on compact sets, two
`ν`-equal sequences with limits in `X₁` have `ν`-equal limits. -/
theorem eq_of_tendsto_of_cc_integrals [T2Space X3]
    {ν : X3 → Measure SL3} {X₁ : Set X3}
    (hK : IsCompact X₁)
    (hcont : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ContinuousOn (fun x => ∫ g, f g ∂(ν x)) X₁)
    (hν : ∀ x ∈ X₁, IsFiniteMeasureOnCompacts (ν x)) :
    ∀ (y y' : X3) (ys ys' : ℕ → X3),
      (∀ n, ys n ∈ X₁) → (∀ n, ys' n ∈ X₁) →
      Tendsto ys atTop (𝓝 y) → Tendsto ys' atTop (𝓝 y') →
      (∀ n, ν (ys n) = ν (ys' n)) → ν y = ν y' := by
  intro y y' ys ys' hy hy' hys hys' heq
  have hcl : IsClosed X₁ := hK.isClosed
  have hyK : y ∈ X₁ := hcl.mem_of_tendsto hys (Eventually.of_forall hy)
  have hyK' : y' ∈ X₁ := hcl.mem_of_tendsto hys' (Eventually.of_forall hy')
  have hint : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂(ν y) = ∫ g, f g ∂(ν y') := by
    intro f
    have hc := hcont f
    have hcy : Tendsto (fun x => ∫ g, f g ∂(ν x)) (𝓝[X₁] y) (𝓝 (∫ g, f g ∂(ν y))) :=
      hc.continuousWithinAt hyK
    have hcy' : Tendsto (fun x => ∫ g, f g ∂(ν x)) (𝓝[X₁] y') (𝓝 (∫ g, f g ∂(ν y'))) :=
      hc.continuousWithinAt hyK'
    have hysw : Tendsto ys atTop (𝓝[X₁] y) :=
      tendsto_nhdsWithin_iff.mpr ⟨hys, Eventually.of_forall hy⟩
    have hysw' : Tendsto ys' atTop (𝓝[X₁] y') :=
      tendsto_nhdsWithin_iff.mpr ⟨hys', Eventually.of_forall hy'⟩
    have t1 : Tendsto (fun n => ∫ g, f g ∂(ν (ys n))) atTop (𝓝 (∫ g, f g ∂(ν y))) :=
      hcy.comp hysw
    have t2 : Tendsto (fun n => ∫ g, f g ∂(ν (ys' n))) atTop (𝓝 (∫ g, f g ∂(ν y'))) :=
      hcy'.comp hysw'
    have hfun : (fun n => ∫ g, f g ∂(ν (ys n))) = fun n => ∫ g, f g ∂(ν (ys' n)) := by
      funext n; rw [heq n]
    rw [hfun] at t1
    exact tendsto_nhds_unique t1 t2
  haveI : IsFiniteMeasureOnCompacts (ν y) := hν y hyK
  haveI : IsFiniteMeasureOnCompacts (ν y') := hν y' hyK'
  exact Measure.ext_of_integral_eq_on_compactlySupported hint

/-- **`luzin_riesz` with the local-finiteness hypothesis on `X'`** (the corrected statement). -/
theorem luzin_riesz_of_radon {μ : Measure X3}
    [IsProbabilityMeasure μ] [T2Space X3]
    {ν : X3 → Measure SL3} {X' : Set X3}
    (hU6 : Work.EKLComp.U6clause μ ν X')
    (hν : ∀ x ∈ X', IsFiniteMeasureOnCompacts (ν x))
    (η : ℝ) (hη : 0 < η) :
    ∃ X₁ : Set X3, IsCompact X₁ ∧ X₁ ⊆ X' ∧ 1 - η < (μ X₁).toReal ∧
      (∀ f : CompactlySupportedContinuousMap SL3 ℝ,
        ContinuousOn (fun x => ∫ g, f g ∂(ν x)) X₁) ∧
      (∀ (y y' : X3) (ys ys' : ℕ → X3),
        (∀ n, ys n ∈ X₁) → (∀ n, ys' n ∈ X₁) →
        Tendsto ys atTop (𝓝 y) → Tendsto ys' atTop (𝓝 y') →
        (∀ n, ν (ys n) = ν (ys' n)) → ν y = ν y') := by
  obtain ⟨X₁, hK, hsub, hmeas, hcont⟩ := exists_compact_continuous_of_U6 hU6 η hη
  exact ⟨X₁, hK, hsub, hmeas, hcont,
    eq_of_tendsto_of_cc_integrals hK hcont fun x hx => hν x (hsub hx)⟩

/-- **`luzin_riesz` for a leafwise system** — the statement of
`Work.EKLComp.prove_LowEntropyCore.luzin_riesz`, with the Luzin clause `U6clause` supplied
separately (it is the `(U6)` component of the frozen `Work.EKLContract.P_Leafwise`). -/
theorem luzin_riesz_of_leafwise {μ : Measure X3}
    [IsProbabilityMeasure μ] [T2Space X3]
    {ν : X3 → Measure SL3} {X' : Set X3}
    (hL : IsLeafwise μ (Uij Work.EKLComp.h01) ν X')
    (hU6 : Work.EKLComp.U6clause μ ν X')
    (η : ℝ) (hη : 0 < η) :
    ∃ X₁ : Set X3, IsCompact X₁ ∧ X₁ ⊆ X' ∧ 1 - η < (μ X₁).toReal ∧
      (∀ f : CompactlySupportedContinuousMap SL3 ℝ,
        ContinuousOn (fun x => ∫ g, f g ∂(ν x)) X₁) ∧
      (∀ (y y' : X3) (ys ys' : ℕ → X3),
        (∀ n, ys n ∈ X₁) → (∀ n, ys' n ∈ X₁) →
        Tendsto ys atTop (𝓝 y) → Tendsto ys' atTop (𝓝 y') →
        (∀ n, ν (ys n) = ν (ys' n)) → ν y = ν y') :=
  luzin_riesz_of_radon hU6 hL.radon η hη

end Work.EKLCompLeaf
