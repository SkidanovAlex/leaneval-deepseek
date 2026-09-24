import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled
import Submission.Commons.Analysis.Fourier.poisson_tsum_eq_tsum_fourier

/-!
# Poisson summation for the bump `psi1` (GM §9)

`psi1 K` is a smooth bump which is `1` on `[-K,K]` and vanishes off `(-(K+1), K+1)`.  Hence for
`M₃ > 0` the lattice sum

`∑_{m ∈ ℤ} ψ₁(m/M₃) e(x m)`

is a finite sum (only `|m| ≤ (K+1) M₃` contribute), and Poisson summation applied to the function
`t ↦ ψ₁(t/M₃) e(x t)` gives

`∑_{m ∈ ℤ} ψ₁(m/M₃) e(x m) = M₃ ∑_{ℓ ∈ ℤ} ψ̂₁(M₃ (ℓ - x))`,

where `ψ̂₁ = psi1hat K` is the Fourier transform of `ψ₁` and `e(y) = e^{2πiy}`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- `psi1 K` vanishes off `[-(K+1), K+1]`, so it has compact support. -/
lemma psi1_hasCompactSupport (K : ℝ) : HasCompactSupport (psi1 K) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(K + 1)) (K + 1))
    isCompact_Icc ?_
  intro t ht
  rw [Set.mem_Icc]
  have h : ¬ (K + 1 ≤ |t|) := fun h => ht (psi1_eq_zero h)
  rw [not_le, abs_lt] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `t ↦ psi1 K (t / M₃)` has compact support for `M₃ > 0`. -/
lemma psi1_div_hasCompactSupport {K M₃ : ℝ} (hM₃ : 0 < M₃) :
    HasCompactSupport (fun t : ℝ => psi1 K (t / M₃)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-((K + 1) * M₃)) ((K + 1) * M₃)) isCompact_Icc ?_
  intro t ht
  rw [Set.mem_Icc]
  have h : ¬ (K + 1 ≤ |t / M₃|) := fun h => ht (psi1_eq_zero h)
  rw [abs_div, abs_of_pos hM₃, not_le] at h
  have h2 : |t| < (K + 1) * M₃ := by
    rw [div_lt_iff₀ hM₃] at h
    exact h
  rw [abs_lt] at h2
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

theorem psi1_poisson {K M₃ : ℝ} (hK : 0 < K) (hM₃ : 0 < M₃) (x : ℝ) :
    (∑ m₃ ∈ R3ext K M₃, ((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) * efun (x * (m₃ : ℝ)))
      = (M₃ : ℂ) * ∑' ℓ : ℤ, psi1hat K (M₃ * ((ℓ : ℝ) - x)) := by
  -- The lattice sum is finite: `psi1 K (n/M₃)` vanishes outside `R3ext K M₃`.
  have hvan : ∀ n : ℤ, n ∉ R3ext K M₃ →
      ((psi1 K ((n : ℝ) / M₃) : ℝ) : ℂ) * efun (x * (n : ℝ)) = 0 := by
    intro n hn
    have hpsi : psi1 K ((n : ℝ) / M₃) = 0 := by
      have ha : (K + 1) * M₃ ≤ ((⌈(K + 1) * M₃⌉ : ℤ) : ℝ) := Int.le_ceil _
      have hn' : ¬ ((-⌈(K + 1) * M₃⌉ : ℤ) ≤ n ∧ n ≤ ⌈(K + 1) * M₃⌉) := by
        simpa [R3ext, Finset.mem_Icc] using hn
      rw [not_and_or, not_le, not_le] at hn'
      apply psi1_eq_zero
      rcases hn' with h | h
      · have h1 : (n : ℝ) < -((⌈(K + 1) * M₃⌉ : ℤ) : ℝ) := by exact_mod_cast h
        have h2 : (n : ℝ) < -((K + 1) * M₃) := by linarith
        have h3 : (n : ℝ) / M₃ < -(K + 1) := by
          rw [div_lt_iff₀ hM₃]; linarith
        have h4 : (n : ℝ) / M₃ < 0 := by linarith
        rw [abs_of_neg h4]; linarith
      · have h1 : ((⌈(K + 1) * M₃⌉ : ℤ) : ℝ) < (n : ℝ) := by exact_mod_cast h
        have h2 : (K + 1) * M₃ < (n : ℝ) := by linarith
        have h3 : K + 1 < (n : ℝ) / M₃ := by
          rw [lt_div_iff₀ hM₃]; linarith
        have h4 : 0 < (n : ℝ) / M₃ := by linarith
        rw [abs_of_pos h4]; linarith
    rw [hpsi]; simp
  have htsum : (∑' n : ℤ, ((psi1 K ((n : ℝ) / M₃) : ℝ) : ℂ) * efun (x * (n : ℝ)))
      = ∑ n ∈ R3ext K M₃, ((psi1 K ((n : ℝ) / M₃) : ℝ) : ℂ) * efun (x * (n : ℝ)) :=
    tsum_eq_sum (s := R3ext K M₃) hvan
  rw [← htsum]
  -- Smoothness and compact support of the summand `g t = ψ₁(t/M₃) e(x t)`.
  have hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ((psi1 K (t / M₃) : ℝ) : ℂ) * efun (x * t)) := by
    apply ContDiff.mul
    · exact (Complex.ofRealCLM.contDiff).comp
        ((psi1_contDiff K).comp (contDiff_id.div_const M₃))
    · have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * ((x * t : ℝ) : ℂ)) :=
        contDiff_const.mul ((Complex.ofRealCLM.contDiff).comp
          (contDiff_const.mul contDiff_id))
      have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ =>
            Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((x * t : ℝ) : ℂ))) :=
        Complex.contDiff_exp.comp h1
      simpa only [efun] using h2
  have hcs_c : HasCompactSupport (fun t : ℝ => ((psi1 K (t / M₃) : ℝ) : ℂ)) :=
    (psi1_div_hasCompactSupport (K := K) hM₃).comp_left Complex.ofReal_zero
  have hcs : HasCompactSupport
      (fun t : ℝ => ((psi1 K (t / M₃) : ℝ) : ℂ) * efun (x * t)) :=
    HasCompactSupport.mul_right (f := fun t : ℝ => ((psi1 K (t / M₃) : ℝ) : ℂ)) hcs_c
  -- Poisson summation.
  rw [Commons.Analysis.Fourier.poisson_tsum_eq_tsum_fourier
    (f := fun t : ℝ => ((psi1 K (t / M₃) : ℝ) : ℂ) * efun (x * t)) hcont hcs]
  -- Evaluate the `k`-th Fourier coefficient: it is `M₃ ψ̂₁(M₃ (k - x))`.
  have hInt : ∀ k : ℤ,
      (∫ t : ℝ, Complex.exp (((-2 * Real.pi * (t * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
          * (((psi1 K (t / M₃) : ℝ) : ℂ) * efun (x * t)))
        = (M₃ : ℂ) * psi1hat K (M₃ * ((k : ℝ) - x)) := by
    intro k
    have hpt : ∀ t : ℝ,
        Complex.exp (((-2 * Real.pi * (t * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
          * (((psi1 K (t / M₃) : ℝ) : ℂ) * efun (x * t))
        = ((psi1 K (t / M₃) : ℝ) : ℂ)
          * Complex.exp (((-2 * Real.pi * (t * ((k : ℝ) - x)) : ℝ) : ℂ) * Complex.I) := by
      intro t
      have hAB : Complex.exp (((-2 * Real.pi * (t * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * ((x * t : ℝ) : ℂ))
          = Complex.exp (((-2 * Real.pi * (t * ((k : ℝ) - x)) : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp only [efun]
      calc Complex.exp (((-2 * Real.pi * (t * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
              * (((psi1 K (t / M₃) : ℝ) : ℂ)
                * Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((x * t : ℝ) : ℂ)))
          = (Complex.exp (((-2 * Real.pi * (t * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
              * Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((x * t : ℝ) : ℂ)))
            * ((psi1 K (t / M₃) : ℝ) : ℂ) := by ring
        _ = Complex.exp (((-2 * Real.pi * (t * ((k : ℝ) - x)) : ℝ) : ℂ) * Complex.I)
            * ((psi1 K (t / M₃) : ℝ) : ℂ) := by rw [hAB]
        _ = ((psi1 K (t / M₃) : ℝ) : ℂ)
            * Complex.exp (((-2 * Real.pi * (t * ((k : ℝ) - x)) : ℝ) : ℂ) * Complex.I) := by
            ring
    calc (∫ t : ℝ, Complex.exp (((-2 * Real.pi * (t * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
            * (((psi1 K (t / M₃) : ℝ) : ℂ) * efun (x * t)))
        = ∫ t : ℝ, ((psi1 K (t / M₃) : ℝ) : ℂ)
            * Complex.exp (((-2 * Real.pi * (t * ((k : ℝ) - x)) : ℝ) : ℂ) * Complex.I) := by
          apply integral_congr_ae
          filter_upwards with t
          exact hpt t
      _ = 𝓕 (fun t : ℝ => ((psi1 K (t / M₃) : ℝ) : ℂ)) ((k : ℝ) - x) := by
          rw [Real.fourier_eq' (fun t : ℝ => ((psi1 K (t / M₃) : ℝ) : ℂ)) ((k : ℝ) - x)]
          apply integral_congr_ae
          filter_upwards with t
          simp only [smul_eq_mul, Real.inner_apply]
          ring
      _ = (M₃ : ℂ) * 𝓕 (fun t : ℝ => ((psi1 K t : ℝ) : ℂ)) (((k : ℝ) - x) * M₃) :=
          Commons.Analysis.Fourier.fourier_comp_div (fun t : ℝ => ((psi1 K t : ℝ) : ℂ)) hM₃
            ((k : ℝ) - x)
      _ = (M₃ : ℂ) * psi1hat K (M₃ * ((k : ℝ) - x)) := by
          rw [psi1hat, show ((k : ℝ) - x) * M₃ = M₃ * ((k : ℝ) - x) by ring]
  have hsum : (∑' k : ℤ, ∫ t : ℝ,
        Complex.exp (((-2 * Real.pi * (t * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
          * (((psi1 K (t / M₃) : ℝ) : ℂ) * efun (x * t)))
      = ∑' k : ℤ, (M₃ : ℂ) * psi1hat K (M₃ * ((k : ℝ) - x)) :=
    tsum_congr fun k => hInt k
  rw [hsum, tsum_mul_left]

end

end Work.GM.Affine
