import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The fundamental lemma of the calculus of variations on an open set of `ℝ × ℝ`

`Work.EllipticEst.Assembly.eq_zero_of_test_integral_zero`:

If `G` is continuous on an open set `U ⊆ ℝ × ℝ` and the integral `∫_U G φ` vanishes for every
`C^∞` compactly supported test function `φ` whose (topological) support lies in `U`, then `G`
vanishes at every point of `U`.

Proof.  Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`
(`Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`) gives the a.e. statement
`∀ᵐ x ∂volume, x ∈ U → G x = 0`; the test-function hypothesis of that theorem is exactly ours,
the only difference being that its integral is taken over the whole space, which is harmless
because `φ` vanishes off `tsupport φ ⊆ U`
(`MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero`).  Finally the a.e. statement is
upgraded to a pointwise one: `{x ∈ U | G x ≠ 0}` is open (continuity at every point of the open
set `U`), so if it were nonempty it would have positive measure, contradicting the a.e. vanishing.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Work.EllipticEst.Assembly

theorem eq_zero_of_test_integral_zero {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {G : ℝ × ℝ → ℝ} (hG : ContinuousOn G U)
    (h : ∀ φ : (ℝ × ℝ) → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      tsupport φ ⊆ U → ∫ x in U, G x * φ x = 0) :
    ∀ x ∈ U, G x = 0 := by
  -- Step 1: `G` vanishes a.e. on `U`.
  have hae : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), x ∈ U → G x = 0 := by
    refine IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hU ?_ ?_
    · -- continuity on the open set `U` gives local integrability there
      exact hG.locallyIntegrableOn hU.measurableSet
    · intro g hg hgsupp htsupp
      -- `g x • G x = G x * g x` for real-valued `G`
      have hfun : (fun x : ℝ × ℝ => g x • G x) = fun x => G x * g x := by
        funext x; rw [smul_eq_mul, mul_comm]
      rw [hfun]
      -- the integral over `U` of `G * g` is the integral over the whole space, as `g` vanishes
      -- off `U`
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun x hx => ?_)]
      · exact h g (fun n => hg.of_le (WithTop.coe_le_coe.mpr le_top)) hgsupp htsupp
      · have : g x = 0 := by
          by_contra hgx
          exact hx (htsupp (subset_closure (Function.mem_support.mpr hgx)))
        rw [this, mul_zero]
  -- Step 2: the (relatively) open set `{x ∈ U | G x ≠ 0}` is null, hence empty.
  intro x hx
  by_contra hne
  have hSopen : IsOpen {y : ℝ × ℝ | y ∈ U ∧ G y ≠ 0} := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyU, hyG⟩
    have hcont : ContinuousAt G y := hG.continuousAt (hU.mem_nhds hyU)
    have h1 : ∀ᶠ z in 𝓝 y, G z ≠ 0 := hcont.eventually_ne hyG
    filter_upwards [h1, hU.mem_nhds hyU] with z hz1 hz2
    exact ⟨hz2, hz1⟩
  have hSnull : volume {y : ℝ × ℝ | y ∈ U ∧ G y ≠ 0} = 0 := by
    have h0 := MeasureTheory.ae_iff.mp hae
    rwa [show {x : ℝ × ℝ | ¬ (x ∈ U → G x = 0)} = {y : ℝ × ℝ | y ∈ U ∧ G y ≠ 0} from by
          ext y; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, not_imp]] at h0
  have hSne : ({y : ℝ × ℝ | y ∈ U ∧ G y ≠ 0} : Set _).Nonempty := ⟨x, hx, hne⟩
  have hpos : 0 < volume {y : ℝ × ℝ | y ∈ U ∧ G y ≠ 0} := hSopen.measure_pos volume hSne
  rw [hSnull] at hpos
  exact lt_irrefl 0 hpos

end Work.EllipticEst.Assembly
