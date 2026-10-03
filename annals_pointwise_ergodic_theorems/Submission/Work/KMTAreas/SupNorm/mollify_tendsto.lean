import Mathlib

/-!
# Mollification by a shrinking non-negative kernel of total mass one

`Work.KMTAreas.SupNorm.mollify_tendsto`: if `ρ n : ℝ → ℝ` is non-negative, has total mass
`∫ ρ n = 1`, and is supported in the shrinking interval `[-1/(n+1), 1/(n+1)]`, then for every
continuous `φ : ℝ → ℂ` and every `x₀ : ℝ`,

  `∫ b, ρ n b • φ (x₀ + b) → φ x₀`  as `n → ∞`.

The proof is the standard approximate-identity argument: subtract the "constant part"

  `∫ b, ((ρ n b : ℝ) : ℂ) * φ (x₀ + b) - φ x₀
     = ∫ b, ((ρ n b : ℝ) : ℂ) * (φ (x₀ + b) - φ x₀)`,

which is estimated by the modulus of continuity of `φ` at `x₀`: on the support of `ρ n` the
increment `φ (x₀ + b) - φ x₀` is at most `ε/2`, and since `ρ n ≥ 0` with `∫ ρ n = 1` this gives
the bound `ε/2`.

Note that the hypothesis `∫ ρ n = 1` *forces* `ρ n` to be Bochner integrable (the Bochner
integral is `0` by definition on non-integrable functions), which is what makes the splitting of
the integral and the integrability of the pieces available.
-/

namespace Work.KMTAreas.SupNorm

open MeasureTheory Filter Topology
open scoped Topology

/-- The single-scale estimate: if `φ` varies by at most `ε/2` on the support of `ρ n`, then the
mollified value is within `ε` of `φ x₀`. -/
private lemma mollify_step {φ : ℝ → ℂ} (hφ : Continuous φ) {x₀ : ℝ} {ρ : ℕ → ℝ → ℝ}
    (hρ : ∀ n, ∫ b, ρ n b = 1) (hρnn : ∀ n b, 0 ≤ ρ n b)
    (hρsupp : ∀ n b, ρ n b ≠ 0 → |b| ≤ (1 : ℝ) / (n + 1))
    {n : ℕ} {R ε : ℝ} (hε : 0 < ε)
    (hbd : ∀ y, |y - x₀| ≤ R → ‖φ y - φ x₀‖ ≤ ε / 2)
    (hδR : (1 : ℝ) / (n + 1) ≤ R) :
    dist (∫ b, ((ρ n b : ℝ) : ℂ) * φ (x₀ + b)) (φ x₀) < ε := by
  -- `∫ ρ n = 1 ≠ 0`, and the Bochner integral of a non-integrable function is `0`.
  have hρint : Integrable (ρ n) (volume : Measure ℝ) := by
    by_contra h
    have h0 : (∫ b, ρ n b) = 0 := integral_undef h
    have h1 := hρ n
    rw [h0] at h1
    exact one_ne_zero h1.symm
  -- Pointwise domination of the increment integrand by `(ε/2) * ρ n`.
  have hbound : ∀ b, ‖((ρ n b : ℝ) : ℂ) * (φ (x₀ + b) - φ x₀)‖ ≤ (ε/2) * ρ n b := by
    intro b
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρnn n b)]
    by_cases hb : ρ n b = 0
    · rw [hb]; simp
    · have hbR : |b| ≤ R := le_trans (hρsupp n b hb) hδR
      have hφb : ‖φ (x₀ + b) - φ x₀‖ ≤ ε/2 := hbd (x₀ + b) (by simpa using hbR)
      calc ρ n b * ‖φ (x₀ + b) - φ x₀‖ ≤ ρ n b * (ε/2) :=
            mul_le_mul_of_nonneg_left hφb (hρnn n b)
        _ = (ε/2) * ρ n b := by ring
  have hBint : Integrable (fun b => ((ρ n b : ℝ) : ℂ) * (φ (x₀ + b) - φ x₀))
      (volume : Measure ℝ) := by
    refine Integrable.mono' (hρint.const_mul (ε/2)) ?_ (Eventually.of_forall hbound)
    exact (hρint.ofReal.aestronglyMeasurable).mul
      ((hφ.comp (continuous_const.add continuous_id)).sub continuous_const).aestronglyMeasurable
  have hAint : Integrable (fun b => ((ρ n b : ℝ) : ℂ) * φ x₀) (volume : Measure ℝ) :=
    hρint.ofReal.mul_const (φ x₀)
  -- The "constant part" integrates to `φ x₀` because `∫ ρ n = 1`.
  have hAval : ∫ b, ((ρ n b : ℝ) : ℂ) * φ x₀ = φ x₀ := by
    have hfun : (fun b => ((ρ n b : ℝ) : ℂ) * φ x₀) = (fun b => φ x₀ * ((ρ n b : ℝ) : ℂ)) := by
      funext b; ring
    rw [hfun, integral_const_mul]
    have h2 : (∫ b, ((ρ n b : ℝ) : ℂ)) = ((∫ b, ρ n b : ℝ) : ℂ) := integral_ofReal
    rw [h2, hρ n]
    simp
  have hsplit := integral_add hAint hBint
  have harg : (fun b => ((ρ n b : ℝ) : ℂ) * φ (x₀ + b)) =
      (fun b => ((ρ n b : ℝ) : ℂ) * φ x₀ + ((ρ n b : ℝ) : ℂ) * (φ (x₀ + b) - φ x₀)) := by
    funext b; ring
  have hId : ∫ b, ((ρ n b : ℝ) : ℂ) * φ (x₀ + b)
      = φ x₀ + ∫ b, ((ρ n b : ℝ) : ℂ) * (φ (x₀ + b) - φ x₀) := by
    rw [harg, hsplit, hAval]
  have hnorm : ‖∫ b, ((ρ n b : ℝ) : ℂ) * (φ (x₀ + b) - φ x₀)‖ ≤ ε/2 := by
    calc ‖∫ b, ((ρ n b : ℝ) : ℂ) * (φ (x₀ + b) - φ x₀)‖
        ≤ ∫ b, ‖((ρ n b : ℝ) : ℂ) * (φ (x₀ + b) - φ x₀)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ b, (ε/2) * ρ n b :=
          integral_mono_of_nonneg (Eventually.of_forall (fun b => norm_nonneg _))
            (hρint.const_mul (ε/2)) (Eventually.of_forall hbound)
      _ = ε/2 := by rw [integral_const_mul, hρ n]; simp
  rw [dist_eq_norm, hId]
  have h2 : φ x₀ + (∫ b, ((ρ n b : ℝ) : ℂ) * (φ (x₀ + b) - φ x₀)) - φ x₀
      = ∫ b, ((ρ n b : ℝ) : ℂ) * (φ (x₀ + b) - φ x₀) := by ring
  rw [h2]
  linarith

theorem mollify_tendsto {φ : ℝ → ℂ} (hφ : Continuous φ) (x₀ : ℝ) (ρ : ℕ → ℝ → ℝ)
    (hρ : ∀ n, ∫ b, ρ n b = 1) (hρnn : ∀ n b, 0 ≤ ρ n b)
    (hρsupp : ∀ n b, ρ n b ≠ 0 → |b| ≤ (1 : ℝ) / (n + 1)) :
    Filter.Tendsto (fun n => ∫ b, ((ρ n b : ℝ) : ℂ) * φ (x₀ + b)) Filter.atTop (nhds (φ x₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Continuity of `φ` at `x₀` gives a radius `η/2` on which `φ` varies by at most `ε/2`.
  have hε2 : (0:ℝ) < ε/2 := by linarith
  obtain ⟨η, hηpos, hη⟩ := (Metric.continuousAt_iff.mp hφ.continuousAt) (ε/2) hε2
  have hRbound : ∀ y : ℝ, |y - x₀| ≤ η/2 → ‖φ y - φ x₀‖ ≤ ε/2 := by
    intro y hy
    have h1 : dist y x₀ < η := by
      rw [Real.dist_eq]
      linarith [abs_nonneg (y - x₀), hy]
    have h2 : ‖φ y - φ x₀‖ < ε / 2 := by
      simpa only [dist_eq_norm] using hη (x := y) h1
    exact le_of_lt h2
  -- `1/(n+1) → 0`, so eventually the support is contained in the ball of radius `η/2`.
  have hδ : Tendsto (fun n : ℕ => (1:ℝ) / (n + 1)) atTop (nhds 0) := by
    simpa [Nat.cast_add, Nat.cast_one] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine (hδ.eventually (Iic_mem_nhds (by linarith : (0:ℝ) < η/2))).mono ?_
  intro n hn
  exact mollify_step hφ hρ hρnn hρsupp hε hRbound hn

end Work.KMTAreas.SupNorm
