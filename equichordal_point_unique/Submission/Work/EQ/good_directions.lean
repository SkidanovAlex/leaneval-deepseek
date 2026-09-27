import Mathlib

/-!
# Good directions for a bounded holomorphic function on the disc

This refines Fatou's radial-limit theorem to the form used in Rychlik's proof of Theorems 10–11:
for a bounded holomorphic `g` on the unit disc and a *countable* set `L` of values that `g` does
not attain identically, almost every direction has a radial limit which is nonzero and avoids `L`.

The Fatou–Riesz input is taken as the hypothesis `FatouRiesz` (which is the workspace lemma
`Work.EQ.fatou_riesz`), so that this module has no dependency on the state of the equichordal
development.
-/

noncomputable section

open MeasureTheory Filter Complex Metric _root_.Topology

namespace Work.EQ

/-- The Fatou–Riesz theorem in the form used here (cf. the workspace lemma
`Work.EQ.fatou_riesz`): a bounded holomorphic function on the unit disc has radial limits almost
everywhere, and the set of directions with a given nonzero limit is null unless the function is
constantly that value. -/
def FatouRiesz : Prop :=
  ∀ (g : ℂ → ℂ), DifferentiableOn ℂ g (Metric.ball 0 1) → ∀ M : ℝ,
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖g z‖ ≤ M) →
    (∀ᵐ θ : ℝ, ∃ c : ℂ, Tendsto (fun t : ℝ => g (t * Complex.exp (θ * Complex.I)))
        (nhdsWithin 1 (Set.Iio 1)) (nhds c)) ∧
    ∀ c : ℂ, (∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ c) →
      volume {θ : ℝ | Tendsto (fun t : ℝ => g (t * Complex.exp (θ * Complex.I)))
        (nhdsWithin 1 (Set.Iio 1)) (nhds c)} = 0

/-- **Good directions.**  Almost every direction has a radial limit which is nonzero and avoids a
given countable set of values not attained identically by `g`. -/
theorem ae_radial_limit_ne_zero_notMem_countable (hfatou : FatouRiesz) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖g z‖ ≤ M)
    (hne : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0) (L : Set ℂ) (hL : L.Countable)
    (hLc : ∀ c ∈ L, ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ c) :
    ∀ᵐ θ : ℝ, ∃ c : ℂ, c ≠ 0 ∧ c ∉ L ∧
      Tendsto (fun t : ℝ => g (t * Complex.exp (θ * Complex.I)))
        (nhdsWithin 1 (Set.Iio 1)) (nhds c) := by
  obtain ⟨hae, hnull⟩ := hfatou g hg M hM
  -- the limit is nonzero almost everywhere
  have h0 : ∀ᵐ θ : ℝ, ¬ Tendsto (fun t : ℝ => g (t * Complex.exp (θ * Complex.I)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    rw [ae_iff]
    simpa using hnull 0 hne
  -- the limit avoids `L` almost everywhere
  have hLnull : volume (⋃ c ∈ L, {θ : ℝ | Tendsto
      (fun t : ℝ => g (t * Complex.exp (θ * Complex.I)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds c)}) = 0 :=
    (measure_biUnion_null_iff hL).mpr fun c hc => hnull c (hLc c hc)
  have hLae : ∀ᵐ θ : ℝ, ∀ c ∈ L, ¬ Tendsto (fun t : ℝ => g (t * Complex.exp (θ * Complex.I)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds c) := by
    rw [ae_iff]
    have hset : {θ : ℝ | ¬ ∀ c ∈ L, ¬ Tendsto
          (fun t : ℝ => g (t * Complex.exp (θ * Complex.I)))
          (nhdsWithin 1 (Set.Iio 1)) (nhds c)}
        = ⋃ c ∈ L, {θ : ℝ | Tendsto (fun t : ℝ => g (t * Complex.exp (θ * Complex.I)))
            (nhdsWithin 1 (Set.Iio 1)) (nhds c)} := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        by_contra hc
        exact h (fun c hcL hP => hc ⟨c, hcL, hP⟩)
      · rintro ⟨c, hcL, hP⟩ h
        exact h c hcL hP
    rw [hset]
    exact hLnull
  filter_upwards [hae, h0, hLae] with θ hlim hz hLθ
  obtain ⟨c, hc⟩ := hlim
  refine ⟨c, ?_, ?_, hc⟩
  · intro hc0
    exact hz (hc0 ▸ hc)
  · intro hcL
    exact hLθ c hcL hc

end Work.EQ
