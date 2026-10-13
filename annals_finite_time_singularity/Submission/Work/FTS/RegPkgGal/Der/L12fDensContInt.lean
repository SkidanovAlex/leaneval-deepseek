/-
# `Work.FTS.RegPkgGal.Der.L12fDensContInt` — continuity and integrability of the density

The angular density of the fundamental model is

  `L12dens K f s = ∫_0^{π/2} K(θ)·f(s,θ)/s dθ`   (`K(θ) = 3 sin θ cos²θ`),

and this module proves that, for a profile family `F` whose `τ`-slice `gSlice F τ` is a `Jet`
(bounded and jointly `α`-Hölder), linear at `z = 0` (`hlin`) and compactly supported in `z`
(`hsupp`), the density of the slice is

* **continuous on `(0,∞)`**, and
* **`L¹` on `(0,∞)`**,

as a function of the radial variable `s`.  This is what turns `L₁₂^K(gSlice F τ)` into a genuine
function of `ρ` (the module `Der/jet_L12f`).

## The two halves

*Continuity.*  Writing `T(s) = ∫_θ K(θ)·F(s,θ,τ) dθ`, the joint Hölder clause of `Jet` gives, for
`s, s' > 0`, the pointwise bound `|F(s,θ,τ) − F(s',θ,τ)| ≤ N·|s−s'|^α`; integrating this against
the sharp angular weight `|K|` gives `|T(s) − T(s')| ≤ (N·∫_θ|K θ|)·|s−s'|^α`, i.e. `T` is
`α`-Hölder on `(0,∞)` (this is the sibling lemma `L12densAngIntegralHolder`), hence continuous
(`continuousOn_of_holder`).  Since `L12dens K (gSlice F τ) s = T(s)/s` for `s ≠ 0`
(`L12dens_eq`), the density is continuous on `(0,∞)` by `ContinuousOn.div`.

*Integrability.*  The density vanishes for `s ≥ Lf` (`L12fDensBound.2`) and is bounded by
`6·max Kl N` on `(0,∞)` (`L12fDensBound.1`, whose two branches are `|F| ≤ Kl·s` near `0` and
`|F| ≤ N` on `[1,∞)`); these two facts are exactly the hypotheses of the general support lemma
`integrableOn_Ioi_of_bound_of_eventually_zero`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegPkgGal.Der.L12fBasic
import Submission.Work.FTS.RegPkgGal.Der.L12fDensBound
import Submission.Work.FTS.RegPkgGal.Der.L12densAngIntegralHolder
import Submission.Work.FTS.RegPkgGal.Der.integrableOn_Ioi_of_bound_of_eventually_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

/-- **Continuity of the density in the radial variable.** -/
theorem continuousOn_L12dens_gSlice {α S N : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hJ : Work.FTS.Regularity.Jet α S N F) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ContinuousOn (fun s : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.Regularity.gSlice F τ) s) (Set.Ioi 0) := by
  -- the numerator is `α`-Hölder (with the sharp constant `N·∫|K|`), hence continuous
  have hNc : (0 : ℝ) ≤ N * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ|) :=
    mul_nonneg hJ.nonneg
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ _ => abs_nonneg _)
  have hT : ContinuousOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.K θ * F s θ τ) (Set.Ioi 0) :=
    continuousOn_of_holder hNc hα ((L12densAngIntegralHolder hα hJ.nonneg hJ) τ hτ)
  -- and the density is the numerator divided by `s ≠ 0`
  have hdiv : ContinuousOn (fun s : ℝ => (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.K θ * F s θ τ) / s) (Set.Ioi 0) :=
    hT.div continuousOn_id fun s hs => ne_of_gt hs
  refine hdiv.congr fun s hs => ?_
  rw [Work.FM.L12dens_eq (ne_of_gt hs)]
  simp only [Work.Spaces.Iθ, Work.FTS.Regularity.gSlice_apply]

theorem L12fDensContInt {α S N Kl Lf : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α)
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      |F z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → F z θ τ = 0) :
    ∀ τ ∈ Set.Icc 0 S,
      ContinuousOn (fun s : ℝ => Work.FM.L12dens Work.Spaces.K
          (Work.FTS.Regularity.gSlice F τ) s) (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (fun s : ℝ => Work.FM.L12dens Work.Spaces.K
          (Work.FTS.Regularity.gSlice F τ) s) (Set.Ioi 0) := by
  intro τ hτ
  refine ⟨continuousOn_L12dens_gSlice hα hJ hτ, ?_⟩
  -- the two facts supplied by the sibling module `L12fDensBound`
  have hbd : ∀ s : ℝ, 0 < s → |Work.FM.L12dens Work.Spaces.K
      (Work.FTS.Regularity.gSlice F τ) s| ≤ 6 * max Kl N :=
    (L12fDensBound hJ hlin hsupp).1 τ hτ
  have hzv : ∀ s : ℝ, Lf ≤ s → Work.FM.L12dens Work.Spaces.K
      (Work.FTS.Regularity.gSlice F τ) s = 0 :=
    (L12fDensBound hJ hlin hsupp).2 τ hτ
  -- a continuous function on `(0,∞)` which is bounded there and vanishes past `Lf > 0` is `L¹`
  exact integrableOn_Ioi_of_bound_of_eventually_zero hsupp.1
    (continuousOn_L12dens_gSlice hα hJ hτ) hbd hzv

end Work.FTS.RegPkgGal.Der
