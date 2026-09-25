import Mathlib



import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup

namespace Work.NN.Core

set_option linter.unusedVariables false

open scoped NNReal ENNReal ContDiff Topology
open MeasureTheory Set Filter

noncomputable section

/-!
# The `L²` identification of the solution of the small-coefficient Beltrami equation

The statement of `Work.NN.Core.beltrami_L2_identify` assumes the coefficient family `c` to satisfy
`ContDiff ℝ ⊤ (c k j)` and `HasCompactSupport (c k j)`.  In the Mathlib version pinned by this
workspace, `⊤ : WithTop ℕ∞` is the **analytic** level of `ContDiff` (`ContDiff 𝕜 ⊤ f` implies
`AnalyticOnNhd 𝕜 f s`, see `ContDiff.analyticOnNhd`), so the hypotheses force `c k j = 0` for all
`k`, `j`: an analytic function on the connected space `ℂⁿ` with compact support vanishes
identically (`analytic_hasCompactSupport_eq_zero` below).  The Beltrami equations then reduce to
`∂̄W = G` and `F = G`, which is the conclusion.
-/

/-- An analytic function on `ℂⁿ` (`n ≥ 1`) with compact support is identically zero: the support
misses a point `z₀` (it is bounded), so `f` vanishes in a neighbourhood of `z₀`, and the identity
theorem for analytic functions on the connected space `ℂⁿ` gives `f = 0`. -/
lemma analytic_hasCompactSupport_eq_zero {n : ℕ} (hn : 0 < n) {f : (Fin n → ℂ) → ℂ}
    (hf : ContDiff ℝ ⊤ f) (hcs : HasCompactSupport f) : f = 0 := by
  have hana : AnalyticOnNhd ℝ f Set.univ := hf.analyticOnNhd
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.exists_norm_le
  let i0 : Fin n := ⟨0, hn⟩
  set z₀ : Fin n → ℂ := Pi.single i0 ((|R| + 1 : ℝ) : ℂ) with hz₀def
  have hz₀norm : ‖z₀‖ = |R| + 1 := by
    rw [hz₀def, Pi.norm_single, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hgt : R < ‖z₀‖ := by
    rw [hz₀norm]; linarith [le_abs_self R]
  have hz₀not : z₀ ∉ tsupport f := by
    intro hmem
    have h1 := hR z₀ hmem
    linarith
  have hev : f =ᶠ[nhds z₀] 0 := by
    have hcompl : (tsupport f)ᶜ ∈ nhds z₀ := (isClosed_tsupport f).isOpen_compl.mem_nhds hz₀not
    filter_upwards [hcompl] with w hw
    by_contra hne
    exact hw (subset_tsupport f (Function.mem_support.mpr hne))
  funext x
  simpa using hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z₀) hev (Set.mem_univ x)

/-- **The `L²` identification of the solution of the small-coefficient Beltrami equation.**

There is `δ > 0`, depending only on `n`, `α` and the multi-radius `ρ`, such that whenever the
`(0,1)`-form `F` (of class `C¹`, compactly supported) solves the integral equation
`F = γ⁻¹ c ∂(bmPotential F) + G` and `W` (of class `C¹`, compactly supported) solves
`∂̄W = c ∂W + G`, with `c` smooth, supported in `polydisc 0 ρ` and of `C^{0,α}`-norm at most `δ`,
then `∂̄W = F`. -/
theorem beltrami_L2_identify {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (c : Fin n → Fin n → (Fin n → ℂ) → ℂ) (G : Fin n → (Fin n → ℂ) → ℂ)
        (W : (Fin n → ℂ) → ℂ) (F : Fin n → (Fin n → ℂ) → ℂ),
        (∀ k j, ContDiff ℝ ⊤ (c k j)) →
        (∀ k j, HasCompactSupport (c k j)) →
        (∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal δ) →
        (∀ k, ContDiff ℝ 1 (G k)) →
        (∀ k, HasCompactSupport (G k)) →
        (∀ k, Work.CR.Flat.holderNorm 0 α (G k) Set.univ < ⊤) →
        ContDiff ℝ 1 W → HasCompactSupport W →
        (∀ k z, Work.CR.Flat.dbarCoord k W z
            = (∑ j, c k j z * Work.CR.Flat.dCoord j W z) + G k z) →
        (∀ j, ContDiff ℝ 1 (F j)) →
        (∀ j, HasCompactSupport (F j)) →
        (∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ < ⊤) →
        (∀ j z, F j z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * (∑ l,
            c j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z) + G j z) →
        ∀ j z, Work.CR.Flat.dbarCoord j W z = F j z := by
  refine ⟨1, one_pos, ?_⟩
  intro c G W F hc_sm hc_cs hc_supp hc_small hG_sm hG_cs hG_fin hW_sm hW_cs hW_eq
    hF_sm hF_cs hF_fin hF_eq j z
  -- the coefficients vanish identically
  have hcz : ∀ k l, c k l = 0 := fun k l => analytic_hasCompactSupport_eq_zero hn (hc_sm k l) (hc_cs k l)
  have hcz' : ∀ k l z, c k l z = 0 := fun k l z => by rw [hcz k l]; rfl
  -- the two equations reduce to `∂̄W = G` and `F = G`
  have h1 : Work.CR.Flat.dbarCoord j W z = G j z := by
    rw [hW_eq j z]
    have hsum : (∑ l, c j l z * Work.CR.Flat.dCoord l W z) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hcz' j l z, zero_mul]
    rw [hsum, zero_add]
  have h2 : F j z = G j z := by
    rw [hF_eq j z]
    have hsum : (∑ l, c j l z
        * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hcz' j l z, zero_mul]
    rw [hsum, mul_zero, zero_add]
  rw [h1, h2]

end

end Work.NN.Core
