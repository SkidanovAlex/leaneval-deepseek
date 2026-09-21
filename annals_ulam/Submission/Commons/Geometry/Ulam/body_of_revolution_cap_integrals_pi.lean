import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_pi_core

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

lemma body_of_revolution_cap_integrals_pi {d n : ℕ} [NeZero d] {a b s h : ℝ}
    {f : ℝ → ℝ} (hdn : d = 2 * n + 1) (hn : 1 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f) :
    let last : Fin d := ⟨d - 1, by omega⟩
    let K : Set (Fin d → ℝ) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    let H : Set (Fin d → ℝ) := {x | x last ≤ s * x 0 + h}
    let W : ℝ → ℝ → ℝ := fun t z =>
      (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
    let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
    volume.real (K ∩ H) =
      c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), W t z ∧
    (∫ x in K ∩ H, x 0) =
      c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), t * W t z ∧
    (∫ x in K ∩ H, x last) =
      c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), z * W t z ∧
    (∀ i : Fin d, i ≠ 0 → i ≠ last → (∫ x in K ∩ H, x i) = 0) := by
  intro last K H W c
  exact body_of_revolution_cap_integrals_pi_core hdn hn hab hf_nonneg hf_meas

end Commons.Geometry.Ulam
