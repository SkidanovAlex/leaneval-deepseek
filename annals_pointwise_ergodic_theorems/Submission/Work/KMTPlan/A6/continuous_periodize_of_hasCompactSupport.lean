import Mathlib
import Submission.Work.KMTContract.summableShiftRestrict
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

/-!
# Continuity of the periodisation of a compactly supported continuous function

For `ψ : ℝ → ℂ` the *periodisation* (see `Work.Analysis.IonescuWainger.periodize`) is

`periodize ψ ξ = ∑' k : ℤ, ψ (x + k)`,   `x = (AddCircle.equivIco 1 0 ξ).val ∈ [0,1)`.

This file proves that if `ψ` is continuous with compact support then `periodize ψ` is continuous
on the circle `ℝ/ℤ`.

The argument is short and geometric.  By compactness there is `R ≥ 0` with `ψ x = 0` for `|x| > R`.
Hence the periodic sum

`G x = ∑' k : ℤ, ψ (x + k)`

is locally a *finite* sum of translates of `ψ` (around a point `x₀` only the integers in
`[⌈-M⌉, ⌊M⌋]`, `M = R + 1 + |x₀|`, can contribute, because `|x + k| ≤ R` forces
`-M ≤ k ≤ M`), so `G` is continuous on `ℝ` — this is `continuous_tsum_add_of_hasCompactSupport`.
Moreover `G (x + 1) = G x` by reindexing the sum over `ℤ`, i.e. `G 0 = G 1`.  Since `periodize ψ` is
by definition the lift `AddCircle.liftIco 1 0 G` of `G` to `ℝ/ℤ`, the matching condition
`G 0 = G 1` and the continuity of `G` are exactly the hypotheses of
`AddCircle.liftIco_zero_continuous`, which gives the result.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory

/-- A continuous function on `ℝ` with compact support vanishes outside a symmetric interval:
there is `R ≥ 0` with `ψ x = 0` whenever `R < |x|`. -/
private lemma exists_abs_bound_of_hasCompactSupport {ψ : ℝ → ℂ}
    (hs : HasCompactSupport ψ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R < |x| → ψ x = 0 := by
  obtain ⟨r, hr⟩ := hs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max r 0, le_max_right _ _, fun x hx => ?_⟩
  by_contra hne
  have hmem : x ∈ tsupport ψ := subset_tsupport ψ hne
  have h1 := hr hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  linarith [le_max_left r 0]

/-- The periodisation is the lift to the circle of the periodic sum `x ↦ ∑' k, ψ (x + k)`
(definitional identity). -/
private lemma periodize_eq_liftIco (ψ : ℝ → ℂ) :
    Work.Analysis.IonescuWainger.periodize ψ
      = AddCircle.liftIco 1 0 (fun x : ℝ => ∑' k : ℤ, ψ (x + k)) := rfl

/-- The periodic sum `x ↦ ∑' k : ℤ, ψ (x + k)` of a continuous compactly supported `ψ` is
continuous on `ℝ`.  Locally it is a finite sum of translates of `ψ`. -/
theorem continuous_tsum_add_of_hasCompactSupport (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hs : HasCompactSupport ψ) :
    Continuous (fun x : ℝ => ∑' k : ℤ, ψ (x + k)) := by
  obtain ⟨R, hR0, hR⟩ := exists_abs_bound_of_hasCompactSupport hs
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨hxa, hxb⟩ := abs_le.mp (le_refl |x₀|)
  set M : ℝ := R + 1 + |x₀| with hM
  set s : Finset ℤ := Finset.Icc ⌈-M⌉ ⌊M⌋ with hs'
  -- on `[x₀ - 1, x₀ + 1]` only the integers in `s` contribute
  have hfin : ∀ x ∈ Set.Icc (x₀ - 1) (x₀ + 1),
      (∑' k : ℤ, ψ (x + k)) = ∑ k ∈ s, ψ (x + k) := by
    intro x hx
    refine tsum_eq_sum (fun k hk => ?_)
    by_contra hne
    have hb : |x + (k : ℝ)| ≤ R := by
      by_contra h
      exact hne (hR _ (lt_of_not_ge h))
    rw [abs_le] at hb
    have hk_le : k ≤ ⌊M⌋ := Int.le_floor.mpr (by linarith [hb.2, hx.1, hxa])
    have hk_ge : ⌈-M⌉ ≤ k := Int.ceil_le.mpr (by linarith [hb.1, hx.2, hxb])
    exact hk (by rw [hs']; exact Finset.mem_Icc.mpr ⟨hk_ge, hk_le⟩)
  have hcont : Continuous (fun x : ℝ => ∑ k ∈ s, ψ (x + k)) :=
    continuous_finsetSum _ (fun k _ => hψ.comp (continuous_id.add continuous_const))
  refine hcont.continuousAt.congr ?_
  exact Filter.eventually_of_mem (Icc_mem_nhds (by linarith) (by linarith))
    (fun x hx => (hfin x hx).symm)

theorem continuous_periodize_of_hasCompactSupport (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hs : HasCompactSupport ψ) :
    Continuous (Work.Analysis.IonescuWainger.periodize ψ) := by
  rw [periodize_eq_liftIco ψ]
  refine AddCircle.liftIco_zero_continuous (p := (1 : ℝ)) ?h0 ?hc
  · -- `1`-periodicity of the periodic sum: `G 0 = G 1`
    show (∑' k : ℤ, ψ ((0 : ℝ) + (k : ℝ))) = ∑' k : ℤ, ψ ((1 : ℝ) + (k : ℝ))
    trans ∑' k : ℤ, ψ ((k : ℝ))
    · exact tsum_congr (fun k => by simp)
    · rw [show (∑' k : ℤ, ψ ((1 : ℝ) + (k : ℝ)))
          = ∑' k : ℤ, ψ (((k + 1 : ℤ) : ℝ)) from
        tsum_congr (fun k => by congr 1; push_cast; ring)]
      exact (Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun j : ℤ => ψ ((j : ℝ)))).symm
  · exact (continuous_tsum_add_of_hasCompactSupport ψ hψ hs).continuousOn

end Work.KMTPlan.A6
