/-
# `hxycSliceLocIntHonest` — local integrability of the sliced angular mollification

For a **trace-class** datum `G` (`TraceClass G`) this file proves the *honest* version of the
slice local-integrability statement of the angular mollification of `Hxyc G t s = Qext G (eᵗ) s`:

  `t ↦ ∫ s, k (θ - s) · Hxyc G t s`   is locally integrable on `ℝ`

for a continuous kernel `k` supported in `(-ε, ε)`, bounded by `M`, with `0 < ε ≤ 1/2` and
`θ ∈ (-1/4, π/2 + 1/4)`.

The (false) sibling `hxycSliceLocInt` used only `SmoothOpen G`: with that hypothesis the angular
slice can blow up at the endpoint `s = π/2` (the counterexample `ceG` of
`hxycSliceLocInt.lean`), so the slice integral `∫_{Iθ} |Hxyc G t s|` is a Bochner integral of a
non-integrable function — identically `0` — and the hypothesis `hdom` is vacuous.  Under
`TraceClass G` the slices are honest (`hT` controls the endpoint *values* and traces), the
domination of `kernelSliceBound` is a bounded multiple of the slice norm, and `hdom` gives the
local integrability.

Two independent ingredients:

* **domination** — `Work.FTS.ClassC.RopGen.Trace.ZmollAux.kernelSliceBound`, applied at
  `w = exp t`, gives `|∫ s, k (θ-s) · Hxyc G t s| ≤ 3 M ∫_{Iθ} |Hxyc G t s|` (its continuity
  hypothesis is `qext_continuousOn`, which is where `TraceClass` enters);
* **measurability** — `t ↦ ∫ s, k (θ-s) · Hxyc G t s` is a.e. strongly measurable.  Since
  `G` is only smooth on the *open* quadrant, the doubly odd extension `Qext G (eᵗ) ·` is
  replaced by the *globally measurable* branch function `Hm G` of `mollHon`
  (`measurable_Hm`): off the null set `{0, π/2}` the two integrands agree as soon as
  `k (θ - s) ≠ 0`, because then `|θ - s| ≤ ε ≤ 1/2` confines every argument of `G` to the open
  quadrant.  Fubini's measurability theorem
  (`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) then gives the a.e. strong
  measurability of the sliced integral.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.kernelSliceBound
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn
import Submission.Work.FTS.EllSol.EllPkgAux.mollHon

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.RopGen.Trace.ZmollAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.EllSol.EllPkgAux

/-! ## The kernel slice against the globally measurable branch function -/

/-- **Branch agreement of the two integrands.**  For a kernel `k` supported in `(-ε, ε)` with
`ε ≤ 1/2`, a modulus `θ ∈ (-1/4, π/2 + 1/4)` and any `t'`, the integrands
`s ↦ k (θ - s) · Hxyc G t' s` and `s ↦ k (θ - s) · Hm G (t', s)` agree off the null set
`{0, π/2}`: whenever `k (θ - s) ≠ 0` the argument `θ - s` lies in `(-ε, ε)`, which forces every
argument at which `Kq G` is evaluated (namely `s`, `-s` for `s < 0` and `π - s` for
`s > π/2`) into the open quadrant, where `Kq G` is the datum and the branches of `Qext`
reproduce the three cases of `Hm G`. -/
theorem kernel_mul_Hxyc_eq_Hm (G : ℝ → ℝ → ℝ) {k : ℝ → ℝ} {ε θ : ℝ}
    (hε1 : ε ≤ 1 / 2) (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) (t' : ℝ) :
    (fun s : ℝ => k (θ - s) * Hxyc G t' s)
      =ᵐ[volume] (fun s : ℝ => k (θ - s) * Hm G (t', s)) := by
  have key : ∀ s : ℝ, s ≠ 0 → s ≠ Real.pi / 2 →
      k (θ - s) * Hxyc G t' s = k (θ - s) * Hm G (t', s) := by
    intro s hs0 hspi
    by_cases hk : k (θ - s) = 0
    · rw [hk, zero_mul, zero_mul]
    · have hwin : |θ - s| ≤ ε := by
        by_contra hlt
        exact hk (hvan _ (lt_of_not_ge hlt))
      have hb : -ε ≤ θ - s ∧ θ - s ≤ ε := abs_le.mp hwin
      have hpt : Hxyc G t' s = Hm G (t', s) := by
        rcases lt_trichotomy s 0 with hs | hs | hs
        · -- `s < 0`: the reflected argument `-s` is in `(0, π/2)`
          have hmem : 0 < -s ∧ -s < Real.pi / 2 :=
            ⟨by linarith, by linarith [hb.2, hε1, hθ.1, Real.pi_gt_three]⟩
          have hKq : Kq G (Real.exp t', -s) = G (Real.exp t') (-s) := by
            unfold Kq
            rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
          unfold Hxyc Hm
          rw [if_pos hs, Qext_of_neg G (Real.exp t') s hs, hKq]
        · exact absurd hs hs0
        · by_cases hsle : s ≤ Real.pi / 2
          · -- the middle branch: `0 < s < π/2`
            have hmem : 0 < s ∧ s < Real.pi / 2 := ⟨hs, lt_of_le_of_ne hsle hspi⟩
            have hKq : Kq G (Real.exp t', s) = G (Real.exp t') s := by
              unfold Kq
              rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
            unfold Hxyc Hm
            rw [if_neg (not_lt.mpr (le_of_lt hs)), if_pos hsle,
              Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G (Real.exp t') s ⟨le_of_lt hs, hsle⟩, hKq]
          · -- `s > π/2`: the reflected argument `π - s` is in `(0, π/2)`
            have hmem : 0 < Real.pi - s ∧ Real.pi - s < Real.pi / 2 :=
              ⟨by linarith [hb.1, hθ.2, hε1, Real.pi_gt_three], by linarith⟩
            have hKq : Kq G (Real.exp t', Real.pi - s) = G (Real.exp t') (Real.pi - s) := by
              unfold Kq
              rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
            unfold Hxyc Hm
            rw [if_neg (not_lt.mpr (le_of_lt hs)), if_neg hsle,
              Qext_of_pihalf_lt G (Real.exp t') s (not_le.mp hsle), hKq]
      rw [hpt]
  refine MeasureTheory.ae_iff.mpr ?_
  refine measure_mono_null ?_ (Set.Finite.measure_zero
    ((Set.finite_singleton (Real.pi / 2)).insert 0) volume)
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra hcon
  push_neg at hcon
  exact hs (key s hcon.1 hcon.2)

/-! ## A.e. strong measurability of the sliced integral -/

/-- **A.e. strong measurability of the sliced angular mollification.**  The `s`-integrand with the
doubly odd extension is replaced by the globally measurable branch function `Hm G`
(`measurable_Hm`), the parameter integral is measurable by Fubini
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`), and the two parameter integrals are
identified pointwise through `kernel_mul_Hxyc_eq_Hm`. -/
theorem aesm_slice_kernel (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {k : ℝ → ℝ} (hk : Continuous k) {ε θ : ℝ} (hε1 : ε ≤ 1 / 2)
    (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => ∫ s : ℝ, k (θ - s) *
      Work.FTS.EllSol.EllPkgAux.Hxyc G t s) MeasureTheory.volume := by
  have hjoint : Measurable (fun p : ℝ × ℝ => k (θ - p.2) * Hm G p) :=
    (hk.measurable.comp (continuous_const.sub continuous_snd).measurable).mul
      (measurable_Hm G hS)
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => ∫ s : ℝ, k (θ - s) * Hm G (t, s))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      hjoint.aestronglyMeasurable
  refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
  exact (integral_congr_ae (kernel_mul_Hxyc_eq_Hm G hε1 hvan hθ t)).symm

/-! ## The target -/

theorem hxycSliceLocIntHonest (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hdom : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
      |Work.FTS.EllSol.EllPkgAux.Hxyc G t s|) MeasureTheory.volume)
    {k : ℝ → ℝ} (hk : Continuous k) {ε M θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hM0 : 0 ≤ M) (hM : ∀ x : ℝ, |k x| ≤ M) (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s : ℝ, k (θ - s) *
      Work.FTS.EllSol.EllPkgAux.Hxyc G t s) MeasureTheory.volume := by
  have hS : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  -- ## Measurability of the sliced integral
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => ∫ s : ℝ, k (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    aesm_slice_kernel G hS hk hε1 hvan hθ
  -- ## The pointwise domination by the honest slice norm
  have hbound : ∀ t : ℝ, |∫ s : ℝ, k (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s|
      ≤ 3 * M * ∫ s in Work.Spaces.Iθ, |Work.FTS.EllSol.EllPkgAux.Hxyc G t s| := by
    intro t
    have h := kernelSliceBound G (Real.exp t)
      (Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn G hT (Real.exp_pos t))
      hk hε0 hε1 hM0 hM hvan hθ
    simpa only [Work.FTS.EllSol.EllPkgAux.Hxyc] using h
  -- ## Local integrability of the dominating function (a constant multiple of the slice norm)
  refine (hdom.smul (3 * M)).mono hmeas (Filter.Eventually.of_forall fun t => ?_)
  have hnn : (0 : ℝ) ≤ 3 * M * ∫ s in Work.Spaces.Iθ,
      |Work.FTS.EllSol.EllPkgAux.Hxyc G t s| :=
    mul_nonneg (by linarith [hM0]) (integral_nonneg (fun s => abs_nonneg _))
  change ‖∫ s : ℝ, k (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s‖
    ≤ ‖(3 * M) • (∫ s in Work.Spaces.Iθ, |Work.FTS.EllSol.EllPkgAux.Hxyc G t s|)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg hnn]
  exact hbound t

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
