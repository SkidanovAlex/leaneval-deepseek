import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2
import Submission.Work.BourgainPlan.Oscillation.tsum_enorm_integral_sub_le
import Submission.Work.BourgainPlan.Oscillation.oscZ_le_of_increment_enorm_bound

/-!
# The block-oscillation functional of a slowly moving family of Fourier multipliers

Bourgain's oscillation inequality for the polynomial averages needs a *soft* step: if a family of
circle multipliers `m i` moves slowly in the scale, `‖m (i+1) θ - m i θ‖ ≤ a i`, then the
`ℓ²(ℤ)` block-oscillation functional `oscZ` of the associated convolution operators

`x ↦ ∫₀¹ m i θ · (Σ_n g n e(nθ)) · e(-xθ) dθ`

is bounded by `(Σ_{i < k_J} a i)² · ∫ |g|²`, uniformly in the block structure `k`.

The proof has two halves, each proved in its own module:

* `tsum_enorm_integral_sub_le` (Plancherel/Parseval): the `ℓ²(ℤ)` norm of one increment
  `A_{i+1} - A_i` is at most `a_i · ‖g‖₂`, because the increment is the Fourier coefficient
  sequence of the multiplier difference applied to the trigonometric polynomial `trigP s g`;
* `oscZ_le_of_increment_enorm_bound` (oscillation bookkeeping): telescoping inside a block,
  Minkowski in `ℓ²` and the disjointness of the blocks `[k_j, k_{j+1})` turn a chain of `ℓ²`
  bounds on the increments into a bound on the block oscillation, with no dependence on the
  block lengths.

This file connects the two: it rewrites the operator of the statement in the `trigP`/`Echar`
shape used by the Plancherel development, feeds the increment bound to the abstract estimate,
and performs the final `ℝ≥0∞` bookkeeping (`∫⁻ |g|²` against counting measure is
`Σ_{n ∈ s} ‖g n‖²`).
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The statement's integral kernel `∫ m θ · (Σ g n e(nθ)) · e(-xθ) dθ` is the same as the
`trigP`/`Echar` form used by the Plancherel lemmas of the `Lacunary` development. -/
private lemma integral_eq_trigP_Echar (m : ℝ → ℂ) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    (∫ θ in (0:ℝ)..1, m θ *
        (∑ n ∈ s, g n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
      = ∫ θ in (0:ℝ)..1, m θ * Lacunary.trigP s g θ * Lacunary.Echar x θ := by
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [Lacunary.trigP, Lacunary.Echar]
  congr 2
  · refine Finset.sum_congr rfl (fun n _ => ?_)
    congr 1
    ring_nf
  · congr 1
    ring_nf

/-- **The oscillation functional of a slowly moving multiplier family.**  If the increments of a
family of measurable, locally bounded circle multipliers are bounded by `a` and the increments of
the corresponding Fourier multipliers are summable along the scale, then the block oscillation of
the multiplier operators — on the `ℓ²(ℤ)` side, with counting measure — is bounded by the square
of the accumulated increment budget times the `ℓ²` norm of the data. -/
theorem oscZ_of_multiplier_family {m : ℕ → ℝ → ℂ}
    (hm : ∀ i, Measurable (m i))
    (hb : ∀ i, ∃ B : ℝ, ∀ θ, ‖m i θ‖ ≤ B)
    (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hinc : ∀ i θ, ‖m (i + 1) θ - m i θ‖ ≤ a i) :
    ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        Work.BourgainPlan.Oscillation.oscZ (fun i x => ∫ θ in (0:ℝ)..1, m i θ *
            (∑ n ∈ s, g n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ)))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))) J k
          ≤ ENNReal.ofReal ((∑ i ∈ Finset.range (k J), a i) ^ 2) *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  intro g s hg J k hk
  classical
  set A : ℕ → ℤ → ℂ := fun i x => ∫ θ in (0:ℝ)..1, m i θ *
      (∑ n ∈ s, g n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (θ : ℂ)))) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))) with hA
  -- the `trigP`/`Echar` shape of `A`
  have hA_trig : ∀ i x, A i x
      = ∫ θ in (0:ℝ)..1, m i θ * Lacunary.trigP s g θ * Lacunary.Echar x θ := by
    intro i x
    simp only [hA]
    exact integral_eq_trigP_Echar (m i) g s x
  -- the `ℓ²` size of the data
  set c : ℝ := Real.sqrt (∑ n ∈ s, ‖g n‖ ^ 2) with hcdef
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = ∑ n ∈ s, ‖g n‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun n _ => sq_nonneg _))
  -- the increment bound, from Plancherel
  have hδ : ∀ i, ∑' x : ℤ, ‖A (i + 1) x - A i x‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal ((a i * c) ^ 2) := by
    intro i
    have h := tsum_enorm_integral_sub_le (m₁ := m (i + 1)) (m₂ := m i)
      (hm (i + 1)) (hm i) (hb (i + 1)) (hb i) (hinc i) g s
    have hrw : (fun x : ℤ => ‖A (i + 1) x - A i x‖ₑ ^ (2:ℝ))
        = (fun x : ℤ => ‖(∫ θ in (0:ℝ)..1, m (i + 1) θ * Lacunary.trigP s g θ
              * Lacunary.Echar x θ)
            - (∫ θ in (0:ℝ)..1, m i θ * Lacunary.trigP s g θ * Lacunary.Echar x θ)‖ₑ ^ (2:ℝ)) := by
      funext x
      rw [hA_trig (i + 1) x, hA_trig i x]
    rw [hrw, mul_pow, hc2]
    exact h
  -- the abstract block-oscillation bound
  have hmain := oscZ_le_of_increment_enorm_bound A c hc0 a ha hδ J k hk
  -- bookkeeping
  calc oscZ A J k
      ≤ ENNReal.ofReal (((∑ i ∈ Finset.range (k J), a i) * c) ^ 2) := hmain
    _ = ENNReal.ofReal ((∑ i ∈ Finset.range (k J), a i) ^ 2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
        rw [Lacunary.f_lintegral s g hg, ← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        rw [mul_pow, hc2]

end

end Work.BourgainPlan.Oscillation
