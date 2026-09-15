/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.BilinearReduction
import Submission.Vinogradov.Extension

/-!
# The extension operator lies in the class `𝒞(U)`

This module connects the two formalizations of "Fourier support in a plate":

* the repository's extension operator `extOp k g a b` (`Extension.lean`, the operator that
  appears in `bdg_thm_ntmain`);
* the class `IsFourierRep k U f` of `DecouplingClass.lean` (the GLYZK formalization of
  "`supp f̂ ⊆ U`").

The main result `extOp_isFourierRep` says that for `a < b` and `g ∈ L¹([a,b])` the function
`E_{[a,b]}g(x) = ∫_a^b g(t) e(x·γ(t)) dt` belongs to the class over the plate
`𝒰_{[a,b]} = plate k ((b-a)/2) ((a+b)/2)`: it is the Fourier transform of the finite measure
`g(t)·1_{[a,b]}(t) dt` pushed forward by the moment curve, and `γ([a,b]) ⊆ 𝒰_{[a,b]}`
(`Plate.gammaVec_mem_plate`).  Consequently the GLYZK decoupling inequality `DecLin` applies
to the family `(E_{J_i}g)_i` of the `m`-fold partition of `[0,1]`, which is the first step of
the passage from GLYZK Theorem 1.1 to `bdg_thm_ntmain` (see `ROADMAP.lean`, session 31 (D)).
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal Interval

set_option autoImplicit false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-- The moment curve is measurable. -/
lemma measurable_gammaVec (k : ℕ) : Measurable (gammaVec k) := by
  have h : Measurable (fun t : ℝ => fun j : Fin k => t ^ (j.val + 1)) :=
    measurable_pi_iff.mpr fun j => by fun_prop
  have h2 := (WithLp.measurable_toLp (2) (Fin k → ℝ)).comp h
  convert h2 using 1
  ext t j
  simp only [Function.comp_apply, WithLp.ofLp_toLp, gammaVec_apply]

/-- **The extension operator lies in the class over its plate.** -/
theorem extOp_isFourierRep (k : ℕ) {g : ℝ → ℂ} (hg : Measurable g) {a b : ℝ} (hab : a < b)
    (hgi : IntegrableOn g (Set.Icc a b) volume) :
    IsFourierRep k (plate k ((b - a) / 2) ((a + b) / 2)) (extOp k g a b) := by
  have hδ : 0 < (b - a) / 2 := by linarith
  have hIcc : Set.Icc a b =ᵐ[volume] Set.Ioc a b := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null ?_ (measure_singleton a), ?_⟩
    · intro x hx
      simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc] at hx
      exact le_antisymm (not_lt.mp fun h => hx.2 ⟨h, hx.1.2⟩) hx.1.1
    · have hempty : Set.Ioc a b \ Set.Icc a b = ∅ := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨h1, h2⟩, h3⟩
        exact h3 ⟨le_of_lt h1, h2⟩
      rw [hempty, measure_empty]
  refine IsFourierRep.mk' (ι := ℝ) (Γ := gammaVec k) (ν := volume.restrict (Set.Icc a b))
    (φ := fun u => if u ∈ Set.Icc a b then g u else 0) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [isFiniteMeasure_restrict]
    exact measure_Icc_lt_top.ne
  · refine (show Integrable g (volume.restrict (Set.Icc a b)) from hgi).congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards with u hu
    rw [if_pos hu]
  · exact measurable_gammaVec k
  · exact hg.piecewise measurableSet_Icc measurable_const
  · intro u hu
    have huI : u ∈ Set.Icc a b := by
      by_contra hcon
      exact hu (if_neg hcon)
    exact gammaVec_mem_plate k hδ (by rw [abs_le]; exact ⟨by linarith [huI.1], by linarith [huI.2]⟩)
  · intro x
    rw [extOp, intervalIntegral.integral_of_le hab.le, ← setIntegral_congr_set hIcc]
    refine integral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards with u hu
    rw [chat_gammaVec, if_pos hu]
    ring

end Submission.Vinogradov
