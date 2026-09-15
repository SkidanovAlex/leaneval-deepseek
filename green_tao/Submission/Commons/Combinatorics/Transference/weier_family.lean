import Mathlib
import Submission.Commons.Combinatorics.Transference.weier_bound
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Green–Tao Proposition 6.5, uniform over a finite family of continuous functions.**
For a finite family `(Φ i)_{i ∈ s}` of continuous functions on the cube `[-M, M]^K` and any
`η > 0` there is a single constant `E ≥ 0` such that the estimate of `weier_bound` holds
for every `i ∈ s` with the same `E`.  This is the uniformity used in Proposition 6.6. -/
theorem weier_family {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d) {M : ℝ} (hM : 0 ≤ M)
    {ν τ : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x)
    (hcorr : ∀ h : Fin d → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p,
          ∏ ω : Fin d → Bool, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    {Cm : ℕ → ℝ} (hmom : ∀ q : ℕ,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ q ≤ Cm q)
    {ι : Type*} (s : Finset ι) (Φ : ι → (Fin K → ℝ) → ℝ)
    (hΦ : ∀ i, ContinuousOn (Φ i) (Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M)))
    {η : ℝ} (hη : 0 < η) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ i ∈ s, ∀ (f : ZMod p → ℝ) (F : Fin K → ZMod p → ℝ),
        (∀ (j : Fin K) (x : ZMod p), |F j x| ≤ ν x) →
        (∀ (j : Fin K) (x : ZMod p), |davg d (F j) x| ≤ M) →
      |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, f x * Φ i (fun j : Fin K => davg d (F j) x)|
        ≤ Unorm d f * E + η * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · exact ⟨0, le_refl 0, fun i hi => by simp at hi⟩
  · choose e he using fun i =>
      weier_bound (p := p) (d := d) (K := K) hd hM hν hτ hcorr hmom (Φ i) (hΦ i) hη
    refine ⟨s.sup' hs e, ?_, ?_⟩
    · obtain ⟨i₀, hi₀⟩ := hs
      exact le_trans (he i₀).1 (Finset.le_sup' e hi₀)
    · intro i hi f F hF hD
      have hE : e i ≤ s.sup' hs e := Finset.le_sup' e hi
      have hei : |((Fintype.card (ZMod p) : ℝ))⁻¹ *
            ∑ x : ZMod p, f x * Φ i (fun j : Fin K => davg d (F j) x)|
          ≤ Unorm d f * e i + η * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) :=
        (he i).2 f F hF hD
      have hUn : 0 ≤ Unorm d f := Unorm_nonneg d hd f
      calc |((Fintype.card (ZMod p) : ℝ))⁻¹ *
              ∑ x : ZMod p, f x * Φ i (fun j : Fin K => davg d (F j) x)|
          ≤ Unorm d f * e i + η * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) := hei
        _ ≤ Unorm d f * s.sup' hs e
              + η * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) :=
            add_le_add (mul_le_mul_of_nonneg_left hE hUn) le_rfl

end Commons.Combinatorics.Transference
