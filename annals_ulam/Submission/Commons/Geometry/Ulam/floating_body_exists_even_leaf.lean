import Mathlib
import Submission.Commons.Geometry.Ulam.strictConvex_body_of_revolution
import Submission.Commons.Geometry.Ulam.isCompact_body_of_revolution
import Submission.Commons.Geometry.Ulam.interior_nonempty_body_of_revolution
import Submission.Commons.Geometry.Ulam.not_centrally_symmetric_body_of_revolution_of_not_even_v4
import Submission.Commons.Geometry.Ulam.floating_from_even_profile_moment_equations_tau
import Submission.Commons.Geometry.Ulam.exists_even_floating_profile_data_strict_v4

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

variable {d : ℕ}

lemma floating_body_exists_even_leaf (hd : 3 ≤ d) (heven : Even d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ R₁ R₂ : ℝ, ∃ f : ℝ → ℝ,
      f.support ⊆ Set.Icc (-R₁) R₂ ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-R₁) R₂) ∧
      ConcaveOn ℝ (Set.Icc (-R₁) R₂) f ∧
      let K : Set (EuclideanSpace ℝ (Fin d)) := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      StrictConvex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
      (¬ ∃ p : EuclideanSpace ℝ (Fin d), K - {p} = -(K - {p})) ∧
      ∀ ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, ∀ t : ℝ,
        volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
        (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈ ℝ ∙ (ξ : EuclideanSpace ℝ (Fin d)) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨n, hdn⟩ := (even_iff_exists_two_mul.mp heven)
  have hn : 2 ≤ n := by omega
  subst d
  rcases exists_even_floating_profile_data_strict_v4 n hn with
    ⟨h, x, y, f, hsupp, hne, hcont, fsupp, fcont, fconc_strict, fcontIcc, fleft, fright, fpos,
      hendpoints, hnon_even, hmom1, hmom2⟩
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t := by
    intro t ht
    by_cases htneg : t = -1
    · subst t; simp [fleft]
    by_cases htpos : t = 1
    · subst t; simp [fright]
    have htIoo : t ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · exact lt_of_le_of_ne ht.1 (Ne.symm htneg)
      · exact lt_of_le_of_ne ht.2 htpos
    exact le_of_lt (fpos t htIoo)
  have hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f := fconc_strict.concaveOn
  have hf_ne_even : ¬ ∀ t : ℝ, f (-t) = f t := by
    rintro hEven
    rcases hnon_even with ⟨t, _ht, hne⟩
    exact hne (hEven t).symm
  let K : Set (EuclideanSpace ℝ (Fin (2 * n))) :=
    {x | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
  have hstrict : StrictConvex ℝ K := by
    exact strictConvex_body_of_revolution (R₁ := 1) (R₂ := 1) (f := f)
      hf_nonneg fconc_strict fcontIcc fleft fright fpos
  have hcomp : IsCompact K := by
    exact isCompact_body_of_revolution (R₁ := 1) (R₂ := 1) (f := f) fcontIcc
  have hinter : (interior K).Nonempty := by
    exact interior_nonempty_body_of_revolution (R₁ := 1) (R₂ := 1) (f := f)
      (by norm_num) fcont.continuousOn fpos
  have hnoncentral : ¬ ∃ p : EuclideanSpace ℝ (Fin (2 * n)), K - {p} = -(K - {p}) := by
    exact not_centrally_symmetric_body_of_revolution_of_not_even_v4 hd fsupp fleft fright fpos hf_ne_even
  have hfloat : ∀ ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * n))) 1, ∀ t : ℝ,
      volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈
        ℝ ∙ (ξ : EuclideanSpace ℝ (Fin (2 * n))) := by
    have hfloat' := floating_from_even_profile_moment_equations_tau n hn (1/10) (by norm_num) (by norm_num)
      h x y f hsupp hcont fsupp fcont hf_conc fleft fright fpos hendpoints hmom1 hmom2
    simpa [K] using hfloat'
  refine ⟨1, 1, f, fsupp, fcont, hf_conc, ?_⟩
  change StrictConvex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
    (¬ ∃ p : EuclideanSpace ℝ (Fin (2 * n)), K - {p} = -(K - {p})) ∧
    ∀ ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * n))) 1, ∀ t : ℝ,
      volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈ ℝ ∙ (ξ : EuclideanSpace ℝ (Fin (2 * n)))
  exact ⟨hstrict, hcomp, hinter, hnoncentral, hfloat⟩

end Commons.Geometry.Ulam
