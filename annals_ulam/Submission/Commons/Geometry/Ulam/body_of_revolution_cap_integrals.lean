import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_pi

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

lemma body_of_revolution_cap_integrals {d n : ℕ} [NeZero d] {a b s h : ℝ}
    {f : ℝ → ℝ} (hdn : d = 2 * n + 1) (hn : 1 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f) :
    let last : Fin d := ⟨d - 1, by omega⟩
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    let H : Set (EuclideanSpace ℝ (Fin d)) := {x | x last ≤ s * x 0 + h}
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
  let KP : Set (Fin d → ℝ) :=
    {q | q 0 ∈ Set.Icc a b ∧ ∑ i > 0, (q i)^2 ≤ f (q 0)^2}
  let HP : Set (Fin d → ℝ) := {q | q last ≤ s * q 0 + h}
  let e : (Fin d → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin d) := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have he : MeasurePreserving e volume volume := by
    simpa [e, MeasurableEquiv.coe_toLp] using (PiLp.volume_preserving_toLp (Fin d))
  have hpreK : e ⁻¹' K = KP := by
    ext q
    simp [e, K, KP, MeasurableEquiv.coe_toLp]
  have hpreH : e ⁻¹' H = HP := by
    ext q
    simp [e, H, HP, MeasurableEquiv.coe_toLp]
  have hpre_inter : e ⁻¹' (K ∩ H) = KP ∩ HP := by
    rw [Set.preimage_inter, hpreK, hpreH]
  have hcore := body_of_revolution_cap_integrals_pi (d := d) (n := n) (a := a) (b := b)
    (s := s) (h := h) (f := f) hdn hn hab hf_nonneg hf_meas
  have hcore' : volume.real (KP ∩ HP) =
      c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), W t z ∧
    (∫ q in KP ∩ HP, q 0) =
      c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), t * W t z ∧
    (∫ q in KP ∩ HP, q last) =
      c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), z * W t z ∧
    (∀ i : Fin d, i ≠ 0 → i ≠ last → (∫ q in KP ∩ HP, q i) = 0) := by
    simpa [KP, HP] using hcore
  constructor
  · -- volume
    have hvol_transfer : volume.real (K ∩ H) = volume.real (KP ∩ HP) := by
      have hvol_enn : volume (K ∩ H) = volume (KP ∩ HP) := by
        rw [← hpre_inter]
        exact (he.measure_preimage_emb e.measurableEmbedding (K ∩ H)).symm
      rw [measureReal_def, measureReal_def, hvol_enn]
    rw [hvol_transfer]
    exact hcore'.1
  constructor
  · -- x 0 moment
    have hx0_transfer : (∫ x in K ∩ H, x 0) = (∫ q in KP ∩ HP, q 0) := by
      have hmom := he.setIntegral_preimage_emb e.measurableEmbedding
        (fun x : EuclideanSpace ℝ (Fin d) => x 0) (K ∩ H)
      rw [← hmom]
      congr 1
    rw [hx0_transfer]
    exact hcore'.2.1
  constructor
  · -- x last moment
    have hlast_transfer : (∫ x in K ∩ H, x last) = (∫ q in KP ∩ HP, q last) := by
      have hmom := he.setIntegral_preimage_emb e.measurableEmbedding
        (fun x : EuclideanSpace ℝ (Fin d) => x last) (K ∩ H)
      rw [← hmom]
      congr 1
    rw [hlast_transfer]
    exact hcore'.2.2.1
  · -- other moments
    intro i hi0 hilast
    have hi_transfer : (∫ x in K ∩ H, x i) = (∫ q in KP ∩ HP, q i) := by
      have hmom := he.setIntegral_preimage_emb e.measurableEmbedding
        (fun x : EuclideanSpace ℝ (Fin d) => x i) (K ∩ H)
      rw [← hmom]
      congr 1
    rw [hi_transfer]
    exact hcore'.2.2.2 i hi0 hilast

end Commons.Geometry.Ulam
