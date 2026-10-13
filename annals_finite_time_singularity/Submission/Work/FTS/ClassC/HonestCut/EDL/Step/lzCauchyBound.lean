import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.HonestCut.EDL.Step

open Filter Set

/-- Cauchy criterion with an explicit rate: if the increments of `F` on `(0, δ)` are bounded by
the value of the (positive, `0`-vanishing) function `b ↦ K b^p W b` at the *upper* endpoint, then
`F` has a limit at `0⁺` and that limit is reached at the same rate. -/
theorem lzCauchyBound {F W : ℝ → ℝ} {δ K p : ℝ} (hδ : 0 < δ)
    (hlim : Filter.Tendsto (fun b : ℝ => K * b ^ p * W b)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hbound : ∀ a b : ℝ, 0 < a → a ≤ b → b < δ → |F b - F a| ≤ K * b ^ p * W b) :
    ∃ L : ℝ, Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
      ∀ θ ∈ Set.Ioo 0 δ, |F θ - L| ≤ K * θ ^ p * W θ := by
  have hne : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsGT_neBot 0
  -- `F` is Cauchy near `0⁺`, because its increments are bounded by a quantity tending to `0`.
  have hcauchy : Cauchy (Filter.map F (nhdsWithin (0 : ℝ) (Set.Ioi 0))) := by
    rw [Metric.cauchy_iff]
    refine ⟨hne.map F, ?_⟩
    intro ε hε
    have hev : ∀ᶠ b in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), |K * b ^ p * W b| < ε := by
      have h := (Metric.tendsto_nhds.mp hlim) ε hε
      simpa only [Real.dist_eq, sub_zero] using h
    rw [Filter.eventually_iff_exists_mem] at hev
    obtain ⟨s, hs, hsb⟩ := hev
    refine ⟨F '' (s ∩ Set.Ioi (0 : ℝ) ∩ Set.Iio δ), ?_, ?_⟩
    · refine Filter.mem_map.mpr (Filter.mem_of_superset ?_ (Set.subset_preimage_image F _))
      exact Filter.inter_mem (Filter.inter_mem hs self_mem_nhdsWithin)
        (nhdsWithin_le_nhds (Iio_mem_nhds hδ))
    · rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
      rw [Real.dist_eq]
      rcases le_or_gt a b with hab | hab
      · rw [abs_sub_comm]
        exact lt_of_le_of_lt (hbound a b ha.1.2 hab hb.2)
          (lt_of_le_of_lt (le_abs_self _) (hsb b hb.1.1))
      · exact lt_of_le_of_lt (hbound b a hb.1.2 (le_of_lt hab) ha.2)
          (lt_of_le_of_lt (le_abs_self _) (hsb a ha.1.1))
  obtain ⟨L, hL⟩ :=
    (@cauchy_map_iff_exists_tendsto ℝ ℝ _ _ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) F hne).mp hcauchy
  refine ⟨L, hL, ?_⟩
  -- The rate: pass to the limit in `|F θ - F a| ≤ K θ^p W θ` along `a → 0⁺`.
  intro θ hθ
  have hC : Filter.Tendsto (fun a : ℝ => |F θ - F a|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds |F θ - L|) :=
    (tendsto_const_nhds.sub hL).abs
  refine le_of_tendsto (hx := hne) hC ?_
  have h1 : ∀ᶠ a in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), (0 : ℝ) < a := self_mem_nhdsWithin
  have h2 : ∀ᶠ a in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), a < θ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hθ.1)
  filter_upwards [h1, h2] with a ha0 haθ
  exact hbound a θ ha0 (le_of_lt haθ) hθ.2

end Work.FTS.ClassC.HonestCut.EDL.Step
