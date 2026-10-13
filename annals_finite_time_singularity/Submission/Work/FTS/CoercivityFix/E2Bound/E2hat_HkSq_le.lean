import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.QuadAux
import Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkIntegrand_le_uniform
import Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_slice_le
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.Coercivity.setIntegral_iterated_le_of_pointwise
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.EllipticEst.Honest.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.E2Bound

set_option autoImplicit false

/-- **The honest route.**  If both right-hand sides of

`|Ê₂ f|²_{ℋⁿ} ≤ C (|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ})`

are honest, the estimate follows from the *slice* inequality `E2hat_slice_le`
(`Ê₂ f = (z/(1+z)²)(2f + 3D_θf)` is a bounded `z`-multiplier combination of `f` and `D_θ f`,
so the slices of the integrand of `Ê₂ f` are dominated by the sum of the slices of the two
right-hand integrands) by monotonicity of the outer integral. -/
theorem E2hat_HkSq_le_of_honest (α : ℝ) (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ f : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad f →
      Work.Spaces.HkMem α n f → Work.Spaces.HkMem α n (Work.Spaces.Dth f) →
      Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ Cn * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨C, hC, hsl⟩ := E2hat_slice_le α n
  refine ⟨C, hC, fun f hsm hmf hmh => ?_⟩
  have hsl0 : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n
          (Work.FTS.CoercivityFix.E2hat f) z θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n
              (Work.Spaces.Dth f) z θ)) := fun z hz => hsl f hsm hmf z hz
  have hint : MeasureTheory.Integrable (fun z => C *
      ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n
            (Work.Spaces.Dth f) z θ))) (volume.restrict Work.Spaces.Iz) :=
    (hmf.2.add hmh.2).const_mul C
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg
      (fun θ => Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.E2hat f) z θ))
    hint (MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)
      (fun z hz => hsl0 z hz))
  have hadd : (∫ z in Work.Spaces.Iz, C *
      ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n
            (Work.Spaces.Dth f) z θ)))
      = C * ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n f z θ)
          + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)) := by
    rw [integral_const_mul, integral_add hmf.2 hmh.2]
  simp only [Work.Spaces.HkSq]
  rw [hadd] at hmono
  exact hmono

/-- **The `Ê₂`-defect estimate in the regime `α ≥ -1/10`.**

For `f ∈ RegQ α (n+1)` with `α ≥ -1/10` — in particular for every `α > 0`, the range in which
the paper and `CoercivityFix.StepCoer.step_coer` consume it — the `ℋⁿ`-norm of the
`D_z`-commutator defect `Ê₂ f = (2zf + 3z·D_θf)/(1+z)²` of `Lhat = 𝓛 − Transport` is controlled
by the `ℋⁿ`-norms of `f` and `D_θ f`, with a constant depending only on `α` and `n`.

Indeed `γ = 1 + α/10 ≥ η = 99/100`, so the mixed weight `Wt α = w·sin(2θ)^{-γ/2}` dominates the
pure weight `w/sin(2θ)^{η/2}`: `RegQ α (n+1) f` gives `HkMem α n (D_θ f)` via
`HkMem_dth_of_RegQ_ge`, and the honest route (`E2hat_HkSq_le_of_honest`) applies.  The
hypothesis `α ≥ -1/10` cannot be dropped: the unrestricted statement `E2hat_HkSq_le` is
**false** for `α < -1/10` (see the counterexample at the end of this file). -/
theorem E2hat_HkSq_le_of_ge (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ f : ℝ → ℝ → ℝ, Work.FTS.Nonlin.RegQ α (n + 1) f →
      Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ Cn * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨C, hC, hb⟩ := E2hat_HkSq_le_of_honest α n
  refine ⟨C, hC, fun f hf => ?_⟩
  have hmh : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    HkMem_dth_of_RegQ_ge α n hα hf
  obtain ⟨hsm, hmem, _hbd⟩ := hf
  have hmf : Work.Spaces.HkMem α n f :=
    Work.FTS.LocDataExt.HkMem_mono (Nat.le_succ n) hsm hmem
  exact hb f hsm hmf hmh

/- **The requested unrestricted statement is FALSE for `α < -1/10`** — it is true for `α ≥ -1/10`
(`E2hat_HkSq_le_of_ge`), and it fails for `α < -1/10` already at `n = 0`.  The statement is
kept here, unchanged, for the record, but no proof is given; the counterexample:

Let `γ = 1 + α/10 < η = 99/100`, `θ_c(z) := (log z)^{-s}` with `s > 0` (so `θ_c(z) → 0` as
`z → ∞`), `δ_N(z) := θ_c(z)·z^{-N}`, and let `g` be a smooth bump supported in `(-1/2, 1/2)`.
For `Φ(z) := z^{-1}(log z)^{-a}` with `a ∈ (1 - s(η-γ), 1]` put
`A_N(z)² := Φ(z)·δ_N(z)·θ_c(z)^{η-2}` and
`f_N(z,θ) := A_N(z)·g((θ - θ_c(z))/δ_N(z))` (times a smooth cut-off supported in `z ≥ 3`).

* `f_N ∈ RegQ α 1`: the three `ℋ¹`-conditions of `HkMem α 1 f_N` become
  `∫_z z^{-1-2N}(log z)^{-a}`, `c∫_z z^{-1}(log z)^{-a-2}` and
  `c∫_z z^{-1}(log z)^{-a-s(η-γ)}`, all finite, while `SmoothQuad` and `BdryTraces` are
  immediate from the cut-offs (the bump's support stays inside `(0, π/2)` and leaves every
  fixed angle as `z → ∞`).
* The `θ`-slice of the `ℋ⁰`-integrand of `Ê₂ f_N` is `≍ 36Φ(z)`: a derivative of a bump of
  width `δ_N` costs `δ_N^{-1}`, and the factors `θ_c^{η-2}` (from `A_N²`) and `θ^{-η}` cancel.
  Since `φ(z)²w(z)² = 1/z²`, this gives `HkSq α 0 (Ê₂ f_N) = 36m∫_3^∞ z^{-3}(log z)^{-a} dz > 0`,
  a positive constant *independent of `N`*.
* The `θ`-slice of the `ℋ⁰`-integrand of `D_θ f_N` is `≍ 4mΦ(z)`, whose `z`-integral
  `∫_z w²Φ = ∫_z (1+z)^4z^{-4}·z^{-1}(log z)^{-a}` diverges (as `a ≤ 1`), so
  `HkSq α 0 (D_θ f_N) = 0` by the junk-value convention of the Bochner integral.
* `HkSq α 0 f_N = ∫_z z^{-1-2N}(log z)^{-a} → 0` as `N → ∞` (the narrowness factor
  `δ_N² = θ_c²z^{-2N}`).

Hence for every `Cn` there is `N` violating the inequality, so the statement is false as soon
as the hypothesis `α ≥ -1/10` is dropped.  The mechanism is exactly the weight mismatch
`η > γ`: the right-hand side only sees `D_θ f` through `η`-weighted pure slots whose mass is
suppressed by `δ_N²`, while the defect `Ê₂ f` carries the extra factor `φ(z)² = z²/(1+z)^4`
that compensates the radial weight `w²` and leaves `1/z²`.  The correct form of the lemma is
`E2hat_HkSq_le_of_ge`, whose range contains the paper's `α ∈ (0, α₂]`. -/
/- The unrestricted form (all `α`) is **false**: see the counterexample documented above —
   the hypothesis `α ≥ -1/10` cannot be dropped.  The usable form is `E2hat_HkSq_le_of_ge`,
   whose range contains the paper's `α ∈ (0, α₂]`.  (The false statement is deliberately not
   retained here.) -/
