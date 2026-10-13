/-
Copyright: work module for the Elgindi finite-time singularity project.

# Measurability in the time variable of the mixed derivatives of a family

The "strong `ε`-scheme" of `Submission/Work/FTS/StrongEps` is a Friedrichs-mollified
approximation scheme for the family `g(τ) = g(·,·,τ)`.  Its convergence arguments
(`HkSq_Jeps_le`, `EpsLimit`, …) need that for a family `H : ℝ → ℝ → ℝ → ℝ`,
`s ↦ mixed j i (H s) z θ` is (a.e.) strongly measurable as soon as

* every slice `H s` (`s ∈ [0,T]`) is `C^∞` on the *open* quadrant
  (`Work.FTS.EllipticEst.SmoothOpen`), and
* every value `s ↦ H s z θ` is continuous on `[0,T]` for each *fixed* point `(z,θ)`
  of the open quadrant.

Only measurability — not continuity — is claimed: the (iterated) derivatives in
`(z,θ)` are limits of difference quotients, and a pointwise limit of measurable
functions is measurable, whereas a limit of continuous functions need not be
continuous.

The proof is the natural double induction: `mixed j i = D_z^j ∘ D_θ^i`, the `D_θ`-step
differentiates the `θ`-slice of a family whose `θ`-slices are measurable for nearby
angles (which is exactly the induction hypothesis at the neighbouring point), and the
`D_z`-step differentiates the `z`-slice similarly.  The core analytic ingredient is
`aesm_of_hasDerivAt_family` below: the slope quotients along `t = r/(n+2)` of a
pointwise-differentiable family of measurable functions are measurable, so their
pointwise limit — the derivative — is too.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Derivative of a measurable family.**  If the slices `y ↦ g s y` are differentiable
at `x` for almost every `s`, with derivative `g' s`, and if the slices
`s ↦ g s y` are a.e. strongly measurable for all `y` in a neighbourhood of `x`, then
`s ↦ g' s` is a.e. strongly measurable.  (The derivative is the pointwise limit of the
slope quotients along `y = x + r/(n+2)`.) -/
private lemma aesm_of_hasDerivAt_family {μ : Measure ℝ} {g : ℝ → ℝ → ℝ} {g' : ℝ → ℝ}
    {x r : ℝ} (hr : 0 < r)
    (hmeas : ∀ y ∈ Set.Ioo (x - r) (x + r), AEStronglyMeasurable (fun s => g s y) μ)
    (hder : ∀ᵐ s ∂μ, HasDerivAt (fun y => g s y) (g' s) x) :
    AEStronglyMeasurable g' μ := by
  have hmem : ∀ n : ℕ, x + r / ((n : ℝ) + 2) ∈ Set.Ioo (x - r) (x + r) := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hp : 0 < r / ((n : ℝ) + 2) := div_pos hr h2
    have hl : r / ((n : ℝ) + 2) < r := by
      rw [div_lt_iff₀ h2]; nlinarith
    exact ⟨by linarith, by linarith⟩
  have hxn : x ∈ Set.Ioo (x - r) (x + r) := ⟨by linarith, by linarith⟩
  have hu : ∀ n : ℕ, AEStronglyMeasurable
      (fun s => (r / ((n : ℝ) + 2))⁻¹ * (g s (x + r / ((n : ℝ) + 2)) - g s x)) μ := by
    intro n
    exact ((hmeas _ (hmem n)).sub (hmeas _ hxn)).const_mul _
  have htend : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hg : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop hg
    · exact Eventually.of_forall (fun n => ne_of_gt (div_pos hr (by positivity)))
  have hlim : ∀ᵐ s ∂μ, Tendsto (fun n : ℕ =>
      (r / ((n : ℝ) + 2))⁻¹ * (g s (x + r / ((n : ℝ) + 2)) - g s x)) atTop (𝓝 (g' s)) :=
    hder.mono (fun s hs => by
      have h := hs.tendsto_slope_zero.comp htend
      simpa only [Function.comp_def, smul_eq_mul] using h)
  exact aestronglyMeasurable_of_tendsto_ae atTop hu hlim

/-- The `θ`-derivative of the `θ`-slice of a function `C^∞` on the open quadrant
(the `θ`-analogue of `Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice`). -/
private lemma SmoothOpen_hasDerivAt_slice_θ {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ := by
  have h : DifferentiableOn ℝ (fun θ' : ℝ => F z θ') (Set.Ioo 0 (π / 2)) :=
    (hF.curry_θ hz).differentiableOn (by norm_num)
  have h2 := (h.differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  simpa only [Work.Spaces.pth] using h2

/-- **The `D_z`-iterates of a family with measurable values.**  If every slice `G s` is
`C^∞` on the open quadrant (a.e. in `s`) and the values `s ↦ G s z θ` are a.e. strongly
measurable for every point of the open quadrant, then so are the values of all the
`D_z`-iterates. -/
private lemma aesm_DzIter_family {μ : Measure ℝ} {G : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ᵐ s ∂μ, Work.FTS.EllipticEst.SmoothOpen (G s))
    (hbase : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s => G s z θ) μ) :
    ∀ (j : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s => Work.Spaces.DzIter j (G s) z θ) μ := by
  intro j
  induction j with
  | zero => intro z θ hzθ; simpa using hbase z θ hzθ
  | succ j ih =>
      intro z θ hzθ
      obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
      have hfull : AEStronglyMeasurable
          (fun s => Work.Spaces.pz (Work.Spaces.DzIter j (G s)) z θ) μ := by
        refine aesm_of_hasDerivAt_family
          (g := fun s y => Work.Spaces.DzIter j (G s) y θ)
          (g' := fun s => Work.Spaces.pz (Work.Spaces.DzIter j (G s)) z θ)
          (x := z) (r := z / 2) (by linarith) ?_ ?_
        · intro y hy
          exact ih y θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨by linarith [hy.1], hθ0, hθ1⟩)
        · filter_upwards [hsm] with s hs
          exact (hs.DzIter j).hasDerivAt_slice ⟨hθ0, hθ1⟩ hz0
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.Dz] using hfull.const_mul z

/-- **The `D_θ`-iterates of a family with measurable values** (the companion of
`aesm_DzIter_family`). -/
private lemma aesm_DthIter_family {μ : Measure ℝ} {G : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ᵐ s ∂μ, Work.FTS.EllipticEst.SmoothOpen (G s))
    (hbase : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s => G s z θ) μ) :
    ∀ (i : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s => Work.Spaces.DthIter i (G s) z θ) μ := by
  intro i
  induction i with
  | zero => intro z θ hzθ; simpa using hbase z θ hzθ
  | succ i ih =>
      intro z θ hzθ
      obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
      have hfull : AEStronglyMeasurable
          (fun s => Work.Spaces.pth (Work.Spaces.DthIter i (G s)) z θ) μ := by
        refine aesm_of_hasDerivAt_family
          (g := fun s y => Work.Spaces.DthIter i (G s) z y)
          (g' := fun s => Work.Spaces.pth (Work.Spaces.DthIter i (G s)) z θ)
          (x := θ) (r := min θ (π / 2 - θ) / 2) ?_ ?_ ?_
        · have h1 : 0 < θ := hθ0
          have h2 : 0 < π / 2 - θ := by linarith
          exact div_pos (lt_min h1 h2) two_pos
        · intro y hy
          have hy0 : 0 < y := by
            have := min_le_left θ (π / 2 - θ)
            linarith [hy.1]
          have hy1 : y < π / 2 := by
            have := min_le_right θ (π / 2 - θ)
            linarith [hy.2]
          exact ih z y (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hy0, hy1⟩)
        · filter_upwards [hsm] with s hs
          exact SmoothOpen_hasDerivAt_slice_θ (hs.DthIter i) hz0 ⟨hθ0, hθ1⟩
      simpa only [Work.Spaces.DthIter_succ, Work.Spaces.Dth] using
        hfull.const_mul (Real.sin (2 * θ))

/-- A property holding at every point of `[0,T]` holds a.e. for the restricted measure. -/
private lemma ae_restrict_Icc_of_forall {T : ℝ} {p : ℝ → Prop}
    (h : ∀ s ∈ Set.Icc (0 : ℝ) T, p s) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), p s := by
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall (fun s hs => h s hs)

theorem aemeasurable_mixed_family {T : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => H s z θ) (Set.Icc (0 : ℝ) T)) :
    ∀ (j i : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := by
  intro j i z θ hzθ
  have hsm_ae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Work.FTS.EllipticEst.SmoothOpen (H s) :=
    ae_restrict_Icc_of_forall (fun s hs => hsm s hs)
  have hbaseH : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => H s z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun z θ hzθ => (hcont z θ hzθ).aestronglyMeasurable measurableSet_Icc
  have hDth := aesm_DthIter_family (G := H) hsm_ae hbaseH i
  have hsmG : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Spaces.DthIter i (H s) z θ) :=
    hsm_ae.mono (fun s hs => hs.DthIter i)
  have hbaseG : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.DthIter i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := fun z θ hzθ => hDth z θ hzθ
  have h := aesm_DzIter_family (G := fun s => Work.Spaces.DthIter i (H s))
    hsmG hbaseG j z θ hzθ
  simpa only [Work.Spaces.mixed] using h

end Work.FTS.StrongEps
