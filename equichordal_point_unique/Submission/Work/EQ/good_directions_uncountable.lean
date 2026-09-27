import Mathlib
import Submission.Work.EQ.good_directions

/-!
# The set of good radial-limit values is uncountable

Rychlik's Theorem 11 needs, besides the a.e. existence of good radial limits (Fatou–Riesz,
`Work.EQ.ae_radial_limit_ne_zero_notMem_countable`), the *uncountability* of the set of values
attained as such limits.  Since every level set `{θ | radial limit = c}` is null (Riesz uniqueness)
and the union of countably many null sets is null, whereas the good directions have full measure,
the set of good values must be uncountable.

This is the "step 3" countability statement of `PAPER_PROOFS.md` §6.
-/

noncomputable section

open MeasureTheory Filter Complex Metric _root_.Topology

namespace Work.EQ

/-- **The set of good radial-limit values is uncountable.**  For a bounded holomorphic `g` on the
unit disc which is not constant, and a countable set `L` of values not attained identically, the
set of values `c ≠ 0`, `c ∉ L` which occur as radial limits of `g` is uncountable. -/
theorem not_countable_good_values (hfatou : FatouRiesz) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖g z‖ ≤ M)
    (hne0 : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0)
    (hnc : ∃ z₁ ∈ Metric.ball (0 : ℂ) 1, ∃ z₂ ∈ Metric.ball (0 : ℂ) 1, g z₁ ≠ g z₂)
    (L : Set ℂ) (hL : L.Countable) (hLc : ∀ c ∈ L, ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ c) :
    ¬ Set.Countable {c : ℂ | ∃ θ : ℝ, c ≠ 0 ∧ c ∉ L ∧
      Tendsto (fun t : ℝ => g (t * Complex.exp ((θ : ℂ) * Complex.I)))
        (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds c)} := by
  intro hcount
  obtain ⟨-, hnull⟩ := hfatou g hg M hM
  have hae := ae_radial_limit_ne_zero_notMem_countable hfatou hg hM hne0 L hL hLc
  set rad : ℝ → ℂ → Prop := fun θ c =>
    Tendsto (fun t : ℝ => g (t * Complex.exp ((θ : ℂ) * Complex.I)))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds c) with hrad
  set GV : Set ℂ := {c : ℂ | ∃ θ : ℝ, c ≠ 0 ∧ c ∉ L ∧ rad θ c} with hGV
  set A : ℂ → Set ℝ := fun c => {θ : ℝ | rad θ c} with hA
  have hnc' : ∀ c : ℂ, ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ c := by
    intro c
    obtain ⟨z₁, h1, z₂, h2, hne⟩ := hnc
    by_cases h : g z₁ = c
    · exact ⟨z₂, h2, fun hc => hne (h.trans hc.symm)⟩
    · exact ⟨z₁, h1, h⟩
  have hcountGV : GV.Countable := by rw [hGV]; exact hcount
  haveI : Countable GV := hcountGV.to_subtype
  set U : Set ℝ := ⋃ c : GV, A (c : ℂ) with hU
  have hsub : ∀ᵐ θ : ℝ, θ ∈ U := by
    rw [hU]
    filter_upwards [hae] with θ hθ
    obtain ⟨c, hc0, hcL, hclim⟩ := hθ
    refine Set.mem_iUnion.mpr ⟨⟨c, ?_⟩, ?_⟩
    · rw [hGV]
      exact ⟨θ, hc0, hcL, by simpa only [hrad] using hclim⟩
    · show rad θ c
      simpa only [hrad] using hclim
  have hzero : volume U = 0 := by
    rw [hU]
    exact measure_iUnion_null fun c => by
      show volume (A (c : ℂ)) = 0
      simpa only [hA, hrad] using hnull (c : ℂ) (hnc' (c : ℂ))
  have hcompl : volume Uᶜ = 0 := by
    have h := (ae_iff (μ := volume) (p := fun θ : ℝ => θ ∈ U)).mp hsub
    exact h
  have htop : (⊤ : ENNReal) ≤ 0 := by
    have h1 : volume (Set.univ : Set ℝ) ≤ volume U + volume Uᶜ := by
      rw [← Set.union_compl_self U]
      exact measure_union_le _ _
    rw [Real.volume_univ, hzero, hcompl, add_zero] at h1
    exact h1
  exact ENNReal.top_ne_zero (le_antisymm htop bot_le)

end Work.EQ
