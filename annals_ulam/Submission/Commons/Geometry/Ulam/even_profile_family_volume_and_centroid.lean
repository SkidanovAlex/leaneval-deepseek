import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_even
import Submission.Commons.Geometry.Ulam.even_profile_cap_volume_half
import Submission.Commons.Geometry.Ulam.even_profile_cap_centroid_span

namespace Commons.Geometry.Ulam

open scoped ContDiff Pointwise RealInnerProductSpace BigOperators

lemma even_profile_family_volume_and_centroid {d : ℕ} [NeZero d] (n : ℕ) (hdn : d = 2 * n) (hn : 2 ≤ n) {τ : ℝ} {h x y f : ℝ → ℝ} (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) (hh_cont : ContDiffOn ℝ ∞ h Set.univ) (hf_supp : Function.support f ⊆ Set.Icc (-1) 1) (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1) 1)) (hf_conc : ConcaveOn ℝ (Set.Icc (-1) 1) f) (hf_left : f (-1) = 0) (hf_right : f 1 = 0) (hf_pos : ∀ t ∈ Set.Ioo (-1) 1, 0 < f t) (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧ (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧ (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2) (hI : ∀ s : ℝ, 0 < s → (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) = (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)), ((1 - t ^ 2) - (s * t) ^ 2) ^ n)) (hJ : ∀ s : ℝ, 0 < s → (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) (h0 : h 0 = 0) :
    let K : Set (EuclideanSpace ℝ (Fin d)) := {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    ∀ s : ℝ, 0 < s → MeasureTheory.volume.real (K ∩ {x | x (Commons.Geometry.Ulam.lastFin d) ≤ s * x 0 + h s}) = MeasureTheory.volume.real K / 2 ∧ (⨍ x in K, x) - (⨍ x in (K ∩ {x | x (Commons.Geometry.Ulam.lastFin d) ≤ s * x 0 + h s}), x) ∈ ℝ ∙ ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) + (EuclideanSpace.single (Commons.Geometry.Ulam.lastFin d) (1:ℝ))) := by
  intro K s hs
  constructor
  · have hvol := even_profile_cap_volume_half (d := d) (n := n) hdn hn
      hf_supp hf_cont hf_conc hf_left hf_right hf_pos hh_cont h0 hxy hJ
    simpa [K] using (hvol s hs)
  · have hvol_all : ∀ r : ℝ, 0 < r →
        MeasureTheory.volume.real (K ∩ {x | x (lastFin d) ≤ r * x 0 + h r}) =
          MeasureTheory.volume.real K / 2 := by
      intro r hr
      have hvol := even_profile_cap_volume_half (d := d) (n := n) hdn hn
        hf_supp hf_cont hf_conc hf_left hf_right hf_pos hh_cont h0 hxy hJ
      simpa [K] using (hvol r hr)
    have hcent := even_profile_cap_centroid_span (d := d) (n := n) hdn hn
      hf_supp hf_cont hf_conc hf_left hf_right hf_pos hh_cont h0 hxy hI hJ hvol_all
    simpa [K] using (hcent s hs)

end Commons.Geometry.Ulam
