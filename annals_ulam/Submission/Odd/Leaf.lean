import Mathlib
import Submission.Commons.Geometry.Ulam.strictConvex_body_of_revolution
import Submission.Commons.Geometry.Ulam.isCompact_body_of_revolution
import Submission.Commons.Geometry.Ulam.interior_nonempty_body_of_revolution
import Submission.Commons.Geometry.Ulam.odd_floating_of_family
import Submission.Odd.FamilyData

namespace Submission.Odd

open MeasureTheory
open Commons.Geometry.Ulam
open scoped BigOperators ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

lemma odd_floating_body_exists_leaf (hd : 3 ≤ d) (hdodd : Odd d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ R₁ R₂ : ℝ, ∃ f : ℝ → ℝ,
      f.support ⊆ Set.Icc (-R₁) R₂ ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-R₁) R₂) ∧
      ConcaveOn ℝ (Set.Icc (-R₁) R₂) f ∧
      let K : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      StrictConvex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
      (¬ ∃ p : ℝᵈ, K - {p} = -(K - {p})) ∧
      ∀ ξ : Metric.sphere (0 : ℝᵈ) 1, ∀ t : ℝ,
        volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
        (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈ ℝ ∙ (ξ : ℝᵈ) := by
  classical
  letI : NeZero d := ⟨by omega⟩
  have hdodd0 : Odd d := hdodd
  obtain ⟨n, hdn⟩ := hdodd
  have hn : 1 ≤ n := by omega
  obtain ⟨R₁, R₂, f, h, hRlt, hf_supp, hf_sm, hf_strict, hf_cont, hf_left, hf_right,
    hf_pos, hh_sm, hh0, hhne, hvol_family, hcent_family, hnoncentral⟩ :=
    Submission.Odd.odd_floating_family_data (d := d) hd hdodd0
  refine ⟨R₁, R₂, f, hf_supp, hf_sm, hf_strict.concaveOn, ?_⟩
  let K : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
  have hf_conc : ConcaveOn ℝ (Set.Icc (-R₁) R₂) f := hf_strict.concaveOn
  have hf_nonneg : ∀ t ∈ Set.Icc (-R₁) R₂, 0 ≤ f t := by
    intro t ht
    by_cases htneg : t = -R₁
    · subst t; simp [hf_left]
    by_cases htpos : t = R₂
    · subst t; simp [hf_right]
    have htIoo : t ∈ Set.Ioo (-R₁) R₂ := by
      constructor
      · exact lt_of_le_of_ne ht.1 (Ne.symm htneg)
      · exact lt_of_le_of_ne ht.2 htpos
    exact le_of_lt (hf_pos t htIoo)
  have hstrict : StrictConvex ℝ K := by
    exact strictConvex_body_of_revolution (d := d) (R₁ := R₁) (R₂ := R₂) (f := f)
      hf_nonneg hf_strict hf_cont hf_left hf_right hf_pos
  have hcomp : IsCompact K := by
    exact isCompact_body_of_revolution (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) hf_cont
  have hinter : (interior K).Nonempty := by
    exact interior_nonempty_body_of_revolution (d := d) (R₁ := R₁) (R₂ := R₂) (f := f)
      hRlt hf_sm.continuousOn hf_pos
  have hnoncentral' : ¬ ∃ p : ℝᵈ, K - {p} = -(K - {p}) := by
    simpa [K] using hnoncentral
  have hfloat : ∀ ξ : Metric.sphere (0 : ℝᵈ) 1, ∀ t : ℝ,
      volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈ ℝ ∙ (ξ : ℝᵈ) := by
    intro ξ t ht
    have hfloat' := odd_floating_of_family (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) (h := h)
      n hdn hn hf_supp hf_sm hf_conc hf_left hf_right hf_pos hh_sm hh0 hvol_family hcent_family
    exact hfloat' ξ t ht
  change StrictConvex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
    (¬ ∃ p : ℝᵈ, K - {p} = -(K - {p})) ∧
    ∀ ξ : Metric.sphere (0 : ℝᵈ) 1, ∀ t : ℝ,
      volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈ ℝ ∙ (ξ : ℝᵈ)
  exact ⟨hstrict, hcomp, hinter, hnoncentral', hfloat⟩

end Submission.Odd
