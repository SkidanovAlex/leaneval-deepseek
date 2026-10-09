import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Filter

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

-- Module `Submission.NK.GlobalCFTdeep.SecondInequality.sum_log_norm_eulerProduct_nontrivial_le`,
-- namespace `NK.GlobalCFTdeep.SecondInequality`, importing
-- `Submission.NK.GlobalCFTdeep.SecondInequality.Defs`.
-- (Note: the module preamble must `open Filter` or write `Filter.Tendsto`.)
--
-- Hypothesis `hreg` is the (Hecke) regularity of the `L`-series of every non-trivial character at
-- `s = 1`.  It implies that the *finite* product `∏_{χ ≠ 1} eulerProduct b S χ s` of the norms is
-- bounded above near `s = 1`, since it converges to the finite product `∏_{χ ≠ 1} v(χ)` (each
-- factor is a convergent sequence in `ℂ`, and the product over the finitely many `χ ≠ 1` of the
-- limits is its limit); hence the sum of the logarithms of the norms is bounded above.
-- Make sure the module is in a `noncomputable section` (the `Fintype (B →* ℂˣ)` instance is
-- noncomputable).

/-- If `f : ℝ → ℂ` has a limit `v` along `𝓝[>] 1`, then `s ↦ log ‖f s‖` is bounded above near
`1` from the right.

If `v ≠ 0` this is continuity of `z ↦ log ‖z‖` at `v`; if `v = 0` then eventually `‖f s‖ ≤ 1`,
and `log x ≤ 0` for `0 ≤ x ≤ 1` (the value `log 0 = 0` is harmless). -/
lemma log_norm_le_of_tendsto {f : ℝ → ℂ} {v : ℂ}
    (h : Filter.Tendsto f (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds v)) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1), Real.log ‖f s‖ ≤ C := by
  by_cases hv : v = 0
  · refine ⟨0, ?_⟩
    have hnorm : Filter.Tendsto (fun s => ‖f s‖) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds 0) := by
      simpa [hv] using h.norm
    filter_upwards [hnorm.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with s hs
    exact Real.log_nonpos (norm_nonneg _) hs.le
  · refine ⟨Real.log ‖v‖ + 1, ?_⟩
    have hv' : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
    have hcont : Filter.Tendsto (fun z : ℂ => Real.log ‖z‖) (nhds v) (nhds (Real.log ‖v‖)) :=
      ((Real.continuousAt_log (ne_of_gt hv')).tendsto).comp continuous_norm.continuousAt
    filter_upwards [(hcont.comp h).eventually
      (isOpen_Iio.mem_nhds (by linarith : Real.log ‖v‖ < Real.log ‖v‖ + 1))] with s hs
    exact hs.le

theorem sum_log_norm_eulerProduct_nontrivial_le {K : Type*} [Field K] [NumberField K] {B : Type*}
    [CommGroup B] [Fintype B] (b : PrimeIdeal K → B) (S : Finset (PrimeIdeal K))
    (hreg : ∀ χ : B →* ℂˣ, χ ≠ 1 → ∃ v : ℂ,
      Filter.Tendsto (eulerProduct b S χ) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds v)) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      ∑ χ ∈ (Finset.univ.erase (1 : B →* ℂˣ)), Real.log ‖eulerProduct b S χ s‖ ≤ C := by
  classical
  -- each non-trivial `χ` contributes a bounded-above term near `1⁺`
  have hbound : ∀ χ : B →* ℂˣ, χ ≠ 1 → ∃ C : ℝ,
      ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
        Real.log ‖eulerProduct b S χ s‖ ≤ C := by
    intro χ hχ
    obtain ⟨v, hv⟩ := hreg χ hχ
    exact log_norm_le_of_tendsto hv
  choose C hC using hbound
  -- extend the bound to the trivial character (whose value is irrelevant for the sum)
  let C' : (B →* ℂˣ) → ℝ := fun χ => if h : χ = 1 then 0 else C χ h
  refine ⟨∑ χ ∈ Finset.univ.erase (1 : B →* ℂˣ), C' χ, ?_⟩
  have hC' : ∀ χ ∈ Finset.univ.erase (1 : B →* ℂˣ),
      ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
        Real.log ‖eulerProduct b S χ s‖ ≤ C' χ := by
    intro χ hχ
    have hne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    have := hC χ hne
    simpa [C', dif_neg hne] using this
  -- finitely many eventual statements can be combined
  have hall : ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      ∀ χ ∈ Finset.univ.erase (1 : B →* ℂˣ), Real.log ‖eulerProduct b S χ s‖ ≤ C' χ :=
    (eventually_all_finset _).mpr hC'
  filter_upwards [hall] with s hs
  exact Finset.sum_le_sum hs

end NK.GlobalCFTdeep.SecondInequality
