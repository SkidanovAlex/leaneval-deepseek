import Mathlib
import Submission.Commons.Analysis.DiscreteCZ.hormander_reflect
import Submission.Commons.Analysis.DiscreteCZ.large_const_le
import Submission.Commons.Analysis.DiscreteCZ.lp_bound_of_finsupp
import Submission.Commons.Analysis.DiscreteCZ.adjoint_l2_bound
import Submission.Commons.Analysis.DiscreteCZ.lp_dual_bound_fin

open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Commons.Analysis.DiscreteCZ

/-- **The discrete Calderón--Zygmund `ℓᵖ` bound on `ℤ` for `p > 2`.**  Under the size, Hörmander
and `ℓ²`-boundedness hypotheses of `Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded`,
the convolution operator `T f x = ∑'_y K (x - y) • f y` is bounded on `ℓᵖ(ℤ; H)` also for
`2 < p < ∞`, with constant the same Marcinkiewicz expression evaluated at the dual exponent
`p' = p/(p-1) < 2`.  The proof is by duality: the adjoint `T^* g (m) = ∑'_n conj (K (n - m)) • g n`
is convolution with the kernel `K^*(z) = conj (K (-z))`, which satisfies the same size and
Hörmander conditions and has the same `ℓ²` operator norm, so the `p' < 2` case of
`discrete_convolution_lp_bounded` applies to it; `‖T‖_{ℓᵖ → ℓᵖ} = ‖T^*‖_{ℓᵖ' → ℓᵖ'}`.  Together
with `discrete_convolution_lp_bounded` this gives the discrete Calderón--Zygmund `ℓᵖ` bound for
all `1 < p < ∞`. -/
theorem discrete_convolution_lp_bounded_large {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] {p : ℝ} (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℤ → ℂ) (A2 Ak Bk : ℝ), 0 < A2 → 0 ≤ Ak →
      (∀ z : ℤ, ‖K z‖ ≤ Bk) →
      (∀ y : ℤ, y ≠ 0 → ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
          ‖K (x - y) - K x‖ₑ ∂MeasureTheory.Measure.count ≤ ENNReal.ofReal Ak) →
      (∀ f : ℤ → H, Summable f →
        MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • f y) 2
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal A2
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) →
      ∀ f : ℤ → H, Summable (fun n : ℤ => ‖f n‖ ^ p) →
        MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • f y) (ENNReal.ofReal p)
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (24 * A2 ^ 2 + 4 * Ak + 100) ^ (2 / (p / (p - 1)) - 1)
              * A2 ^ (2 - 2 / (p / (p - 1))))
            * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hpminus : (0 : ℝ) < p - 1 := by linarith
  have hp1 : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ hpminus]; linarith
  have hp2 : p / (p - 1) < 2 := by
    rw [div_lt_iff₀ hpminus]; linarith
  have hp0 : 0 < p := by linarith
  obtain ⟨C', hC'pos, hC'⟩ := discrete_convolution_lp_bounded (H := H →L[ℂ] ℂ) hp1 hp2
  refine ⟨8 * C', by positivity, ?_⟩
  intro K A2 Ak Bk hA2 hAk hsize hker hstrong
  have hdual_l2 : ∀ Ψ : ℤ → (H →L[ℂ] ℂ), Summable Ψ →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (-(x - y)) • Ψ y) 2
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (2 * A2) * MeasureTheory.eLpNorm Ψ 2 MeasureTheory.Measure.count := by
    intro Ψ hΨ
    have h := adjoint_l2_bound K A2 hA2 hstrong Ψ hΨ
    simpa only [neg_sub] using h
  have hsize' : ∀ z : ℤ, ‖(fun z : ℤ => K (-z)) z‖ ≤ Bk := by
    intro z; simpa using hsize (-z)
  have hker' : ∀ y : ℤ, y ≠ 0 → ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
      ‖(fun z : ℤ => K (-z)) (x - y) - (fun z : ℤ => K (-z)) x‖ₑ
        ∂MeasureTheory.Measure.count ≤ ENNReal.ofReal Ak := by
    intro y hy
    have h := hormander_reflect hker y hy
    simpa only using h
  have hΦ := hC' (fun z : ℤ => K (-z)) (2 * A2) Ak Bk (by linarith) hAk hsize' hker' hdual_l2
  set c : ℝ := C' * (24 * (2 * A2) ^ 2 + 4 * Ak + 100) ^ (2 / (p / (p - 1)) - 1)
      * (2 * A2) ^ (2 - 2 / (p / (p - 1))) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    have h1 : (0 : ℝ) < 24 * (2 * A2) ^ 2 + 4 * Ak + 100 := by positivity
    have h2 : (0 : ℝ) < 2 * A2 := by linarith
    exact mul_pos (mul_pos hC'pos (Real.rpow_pos_of_pos h1 _)) (Real.rpow_pos_of_pos h2 _)
  have hdual : ∀ Φ : ℤ → (H →L[ℂ] ℂ), Summable (fun n : ℤ => ‖Φ n‖ ^ (p / (p - 1))) →
      MeasureTheory.eLpNorm (fun y : ℤ => ∑' x : ℤ, K (x - y) • Φ x)
          (ENNReal.ofReal (p / (p - 1))) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal c * MeasureTheory.eLpNorm Φ (ENNReal.ofReal (p / (p - 1)))
            MeasureTheory.Measure.count := by
    intro Φ hΦs
    have h := hΦ Φ hΦs
    rw [hcdef]
    simpa only [neg_sub] using h
  have hfin : ∀ f : ℤ → H, (∃ t : Finset ℤ, ∀ x : ℤ, x ∉ t → f x = 0) →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • f y) (ENNReal.ofReal p)
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal c * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
    rintro f ⟨t, ht⟩
    exact lp_dual_bound_fin (H := H) (K := K) (p := p) (c := c) (by linarith) hcpos hdual f t ht
  have hgen := lp_bound_of_finsupp (H := H) (K := K) (p := p) (c := c) hp0 hcpos.le hfin
  intro f hf
  refine (hgen f hf).trans ?_
  gcongr
  rw [hcdef]
  exact large_const_le C' A2 Ak p hp hC'pos hA2 hAk

end Commons.Analysis.DiscreteCZ
