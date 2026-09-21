import Mathlib
import Submission.Commons.Geometry.Ulam.even_profile_family_volume_and_centroid
import Submission.Commons.Geometry.Ulam.even_floating_of_family

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

lemma floating_from_even_profile_moment_equations_tau (n : ℕ) (hn : 2 ≤ n)
    (τ : ℝ) (hτ : 0 < τ) (htau : 2 * τ < 1) (h x y f : ℝ → ℝ)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hcont : ContDiffOn ℝ ∞ h Set.univ)
    (fsupp : Function.support f ⊆ Set.Icc (-1) 1)
    (fcont : ContDiffOn ℝ ∞ f (Set.Ioo (-1) 1))
    (fconc : ConcaveOn ℝ (Set.Icc (-1) 1) f)
    (fleft : f (-1) = 0) (fright : f 1 = 0)
    (fpos : ∀ t ∈ Set.Ioo (-1) 1, 0 < f t)
    (hendpoints : ∀ s : ℝ, 0 < s →
      0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hmom1 : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) =
        (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
          ((1 - t ^ 2) - (s * t) ^ 2) ^ n))
    (hmom2 : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    let d : ℕ := 2 * n
    letI : NeZero d := ⟨by omega⟩
    let K : Set (EuclideanSpace ℝ (Fin d)) := {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    ∀ ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, ∀ t : ℝ,
      volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈ ℝ ∙ (ξ : EuclideanSpace ℝ (Fin d)) := by
  let d : ℕ := 2 * n
  letI : NeZero d := ⟨by omega⟩
  let K : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
  have h0 : h 0 = 0 := by
    by_contra hz
    have hmem : 0 ∈ Function.support h := by
      simpa [Function.mem_support] using hz
    have hsub : (0 : ℝ) ∈ Set.Icc (1 - 2 * τ) (1 - τ) := hsupp hmem
    have hlower_pos : 0 < 1 - 2 * τ := by nlinarith
    have hlower_le : 1 - 2 * τ ≤ 0 := hsub.1
    nlinarith
  have hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2 := by
    intro s hs
    exact hendpoints s hs
  have hh_cont_global : ContDiff ℝ ∞ h := by
    exact contDiffOn_univ.1 hcont
  have hfam := even_profile_family_volume_and_centroid (d := d) (n := n) rfl hn
    (τ := τ) hsupp hcont fsupp fcont fconc fleft fright fpos hxy hmom1 hmom2 h0
  have hfam_vol : ∀ s : ℝ, 0 < s →
      let K : Set (EuclideanSpace ℝ (Fin d)) :=
        {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      volume.real (K ∩ {x | x ⟨d - 1, by omega⟩ ≤ s * x 0 + h s}) =
        volume.real K / 2 := by
    intro s hs
    have hvol := (hfam s hs).1
    have hlast : (lastFin d) = (⟨d - 1, by omega⟩ : Fin d) := by
      ext; simp [lastFin]
    simpa [K, hlast] using hvol
  have hfam_cent : ∀ s : ℝ, 0 < s →
      let K : Set (EuclideanSpace ℝ (Fin d)) :=
        {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      let nvec : EuclideanSpace ℝ (Fin d) :=
        EuclideanSpace.single (0 : Fin d) (-s) +
          EuclideanSpace.single (⟨d - 1, by omega⟩ : Fin d) (1 : ℝ)
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | x ⟨d - 1, by omega⟩ ≤ s * x 0 + h s}), x) ∈
        ℝ ∙ nvec := by
    intro s hs
    have hcent := (hfam s hs).2
    have hlast : (lastFin d) = (⟨d - 1, by omega⟩ : Fin d) := by
      ext; simp [lastFin]
    have hsingle_smul : (EuclideanSpace.single (0 : Fin d) (-s)) =
        (-s) • (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) := by
      ext i
      by_cases hi0 : i = 0 <;> simp [hi0]
    have hnvec : (EuclideanSpace.single (0 : Fin d) (-s) +
          EuclideanSpace.single (⟨d - 1, by omega⟩ : Fin d) (1 : ℝ)) =
        ((-s) • (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) +
          (EuclideanSpace.single (lastFin d) (1 : ℝ))) := by
      rw [hsingle_smul, hlast]
    have hmem : (⨍ x in K, x) - (⨍ x in (K ∩ {x | x (lastFin d) ≤ s * x 0 + h s}), x) ∈
        ℝ ∙ ((-s) • (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) +
          (EuclideanSpace.single (lastFin d) (1 : ℝ))) := by
      simpa [K] using hcent
    have hmem' : (⨍ x in K, x) - (⨍ x in (K ∩ {x | x ⟨d - 1, by omega⟩ ≤ s * x 0 + h s}), x) ∈
        ℝ ∙ ((-s) • (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) +
          (EuclideanSpace.single (lastFin d) (1 : ℝ))) := by
      simpa [K, hlast] using hmem
    simpa [K, hnvec] using hmem'
  change ∀ ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, ∀ t : ℝ,
      volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈
        ℝ ∙ (ξ : EuclideanSpace ℝ (Fin d))
  exact even_floating_of_family (d := d) (n := n) rfl hn
    fsupp fcont fconc fleft fright fpos hh_cont_global h0 hfam_vol hfam_cent

end Commons.Geometry.Ulam
