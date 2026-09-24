import Mathlib
import Submission.Commons.Analysis.Fourier.perronKernelSigma_regionBound
import Submission.Commons.Analysis.Fourier.perronKernelSigma_oscTail
import Submission.Commons.Analysis.Fourier.perronKernelSigma_tendsto

noncomputable section

open Real Set Complex Filter intervalIntegral MeasureTheory
open scoped Topology Real

namespace Commons.Analysis.Fourier

/-!
# Uniform bound for the σ-shifted truncated Perron kernel deviation

`perron_kernel_sigma_bound`: for `1 ≤ σ`, `1 ≤ T`, `α ≠ 0`,

    ‖∫_{-T}^{T} e^{iαt}/(σ+it) dt − (if 0 < α then 2π·e^{−σα} else 0)‖
        ≤ C·min(1, 1/(T·|α|)).

The proof mirrors the σ = 1 case (`perron_kernel_bound`): on the small-`T|α|`
region the integral is bounded by an absolute constant (`perronKernelSigma_regionBound`)
and the limiting value by `2π`; for `T|α| ≥ 1`, an integration-by-parts oscillation
bound (`perronKernelSigma_oscTail`, plus its reflected `t ↦ -t` twin) shows
`‖I(R) − I(T)‖ ≤ 6/(|α|T)` uniformly in `R ≥ T`, and `I(R)` converges to the closed
form (`perronKernelSigma_tendsto`).  Passing to the limit `R → ∞` gives the tail bound.
-/

/-- The Perron integrand with a `σ`-shifted denominator. -/
noncomputable def pskKern (σ α : ℝ) (t : ℝ) : ℂ :=
  cexp (I * (↑α * ↑t)) / ((σ : ℂ) + I * ↑t)

/-- The symmetric truncated integral. -/
noncomputable def pskInt (σ T α : ℝ) : ℂ := ∫ t in -T..T, pskKern σ α t

/-- Continuity of the σ-shifted integrand for `σ ≠ 0`. -/
lemma psk_continuous (σ α : ℝ) (hσ : σ ≠ 0) : Continuous (pskKern σ α) := by
  unfold pskKern
  refine Continuous.div₀ ?hg ?hd ?hz
  · fun_prop
  · fun_prop
  · intro t
    exact sigma_denom_ne_zero σ t hσ

/-- Complex conjugation turns the integrand at `t` into the integrand at `-t`
(for real `σ`, `α`). -/
lemma psk_conj_neg (σ α t : ℝ) : (starRingEnd ℂ) (pskKern σ α t) = pskKern σ α (-t) := by
  unfold pskKern
  rw [map_div₀]
  congr 1
  · rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [Complex.ofReal_neg]
    ring
  · rw [map_add, Complex.conj_ofReal]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [Complex.ofReal_neg]
    ring

/-- Complex conjugation commutes with interval integrals. -/
lemma psk_conj_integral (f : ℝ → ℂ) (a b : ℝ) (hfi : IntervalIntegrable f volume a b) :
    (∫ x in a..b, (starRingEnd ℂ) (f x)) = (starRingEnd ℂ) (∫ x in a..b, f x) := by
  let L : ℂ →L[ℝ] ℂ := (starL' (R := ℝ) (A := ℂ) : ℂ ≃L[ℝ] ℂ)
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) (E := ℂ) (F := ℂ) L hfi
  simpa [L] using h

/-- Difference of two symmetric truncations splits into the two tails. -/
lemma psk_int_split (σ T R α : ℝ) (hσ : σ ≠ 0) :
    pskInt σ R α - pskInt σ T α =
      (∫ t in T..R, pskKern σ α t) + ∫ t in -R..-T, pskKern σ α t := by
  have hc : Continuous (pskKern σ α) := psk_continuous σ α hσ
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := fun t => pskKern σ α t) (a := -R) (b := -T) (c := T)
    (hc.intervalIntegrable (-R) (-T)) (hc.intervalIntegrable (-T) T)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := fun t => pskKern σ α t) (a := -R) (b := T) (c := R)
    (hc.intervalIntegrable (-R) T) (hc.intervalIntegrable T R)
  unfold pskInt
  have hE : (∫ t in -R..R, pskKern σ α t) =
      (∫ t in -R..-T, pskKern σ α t) + (∫ t in -T..T, pskKern σ α t) + (∫ t in T..R, pskKern σ α t) := by
    rw [← h2, ← h1]
  rw [hE]
  abel

/-- Norm of the reflected (negative-direction) tail, `≤ 3/(|α|·T)`. -/
lemma psk_neg_tail (σ T R α : ℝ) (hσ : 0 < σ) (hα : α ≠ 0) (hT : 1 ≤ T) (hTR : T ≤ R) :
    ‖(∫ t in -R..-T, pskKern σ α t)‖ ≤ 3 / (|α| * T) := by
  have hσnz : σ ≠ 0 := ne_of_gt hσ
  have hsub : (∫ t in -R..-T, pskKern σ α t) = ∫ u in T..R, pskKern σ α (-u) := by
    have h1 := intervalIntegral.integral_comp_neg (f := fun u : ℝ => pskKern σ α u) (a := T) (b := R)
    exact h1.symm
  have hconjpt : (fun u : ℝ => pskKern σ α (-u)) = fun u : ℝ => (starRingEnd ℂ) (pskKern σ α u) := by
    funext u
    exact (psk_conj_neg σ α u).symm
  have hfi : IntervalIntegrable (pskKern σ α) volume T R := (psk_continuous σ α hσnz).intervalIntegrable T R
  calc
    ‖(∫ t in -R..-T, pskKern σ α t)‖ = ‖∫ u in T..R, pskKern σ α (-u)‖ := by rw [hsub]
    _ = ‖∫ u in T..R, (starRingEnd ℂ) (pskKern σ α u)‖ := by rw [hconjpt]
    _ = ‖(starRingEnd ℂ) (∫ u in T..R, pskKern σ α u)‖ := by rw [psk_conj_integral (pskKern σ α) T R hfi]
    _ = ‖∫ u in T..R, pskKern σ α u‖ := by rw [Complex.norm_conj]
    _ ≤ 3 / (|α| * T) := by
      simpa [pskKern] using (perronKernelSigma_oscTail σ T R α hσ hα hT hTR)

/-- Two-sided tail bound for the symmetric truncations, `≤ 6/(|α|·T)`. -/
lemma psk_tail_bound (σ T R α : ℝ) (hσ : 0 < σ) (hα : α ≠ 0) (hT : 1 ≤ T) (hTR : T ≤ R) :
    ‖pskInt σ R α - pskInt σ T α‖ ≤ 6 / (|α| * T) := by
  rw [psk_int_split σ T R α (ne_of_gt hσ)]
  calc
    ‖(∫ t in T..R, pskKern σ α t) + ∫ t in -R..-T, pskKern σ α t‖
        ≤ ‖∫ t in T..R, pskKern σ α t‖ + ‖∫ t in -R..-T, pskKern σ α t‖ := norm_add_le _ _
    _ ≤ 3 / (|α| * T) + 3 / (|α| * T) := by
      exact add_le_add
        (by simpa [pskKern] using (perronKernelSigma_oscTail σ T R α hσ hα hT hTR))
        (psk_neg_tail σ T R α hσ hα hT hTR)
    _ = 6 / (|α| * T) := by ring

/-- Real value of the limit: `2π·e^{−σα}` for `α > 0`, `0` otherwise. -/
noncomputable def pskValReal (σ α : ℝ) : ℝ := if 0 < α then 2 * Real.pi * Real.exp (-(σ * α)) else 0

/-- The complex closed form equals the real limiting value lifted to `ℂ`. -/
lemma psk_value_eq_ofReal (σ α : ℝ) :
    (if 0 < α then (2 : ℂ) * ↑Real.pi * cexp (-((σ : ℂ) * ↑α)) else 0)
      = ((pskValReal σ α : ℝ) : ℂ) := by
  by_cases hα : 0 < α
  · rw [if_pos hα]
    unfold pskValReal
    rw [if_pos hα]
    have harg : -((σ : ℂ) * ↑α) = (↑(-(σ * α)) : ℂ) := by
      calc
        -((σ : ℂ) * ↑α) = -(↑(σ * α) : ℂ) := by congr 1; rw [← Complex.ofReal_mul]
        _ = (↑(-(σ * α)) : ℂ) := by rw [← Complex.ofReal_neg]
    rw [harg]
    rw [← Complex.ofReal_exp]
    apply Complex.ext <;> simp
  · rw [if_neg hα]
    unfold pskValReal
    rw [if_neg hα]
    simp

/-- `|pskValReal σ α| ≤ 2π` for `0 < σ`. -/
lemma psk_valReal_abs_le (σ α : ℝ) (hσ : 0 < σ) : |pskValReal σ α| ≤ 2 * Real.pi := by
  by_cases hα : 0 < α
  · unfold pskValReal
    rw [if_pos hα]
    have hsa : 0 < σ * α := mul_pos hσ hα
    have he1 : Real.exp (-(σ * α)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    calc
      |2 * Real.pi * Real.exp (-(σ * α))| = 2 * Real.pi * Real.exp (-(σ * α)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg Real.pi_pos.le,
          abs_of_nonneg (Real.exp_pos (-(σ * α))).le]
      _ ≤ 2 * Real.pi * 1 := by gcongr
      _ = 2 * Real.pi := by ring
  · unfold pskValReal
    rw [if_neg hα]
    simp
    nlinarith [Real.pi_pos]

/-- Norm bound for the closed-form limit. -/
lemma psk_value_norm (σ α : ℝ) (hσ : 0 < σ) :
    ‖(if 0 < α then (2 : ℂ) * ↑Real.pi * cexp (-((σ : ℂ) * ↑α)) else 0)‖ ≤ 2 * Real.pi := by
  rw [psk_value_eq_ofReal σ α]
  simpa [RCLike.norm_ofReal] using psk_valReal_abs_le σ α hσ

theorem perron_kernel_sigma_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (σ T α : ℝ), 1 ≤ σ → 1 ≤ T → α ≠ 0 →
        ‖(∫ (t : ℝ) in -T..T, Complex.exp (Complex.I * (↑α * ↑t)) / ((σ : ℂ) + Complex.I * ↑t))
            - if 0 < α then 2 * ↑Real.pi * Complex.exp (-((σ : ℂ) * ↑α)) else 0‖
          ≤ C * min 1 (1 / (T * |α|)) := by
  refine ⟨32, by norm_num, ?_⟩
  intro σ T α hσ1 hT hα
  have hσ : 0 < σ := lt_of_lt_of_le zero_lt_one hσ1
  change ‖pskInt σ T α - (if 0 < α then 2 * ↑Real.pi * Complex.exp (-((σ : ℂ) * ↑α)) else 0)‖
      ≤ 32 * min 1 (1 / (T * |α|))
  let V : ℂ := if 0 < α then 2 * ↑Real.pi * Complex.exp (-((σ : ℂ) * ↑α)) else 0
  have hconv : Tendsto (fun R : ℝ => pskInt σ R α) atTop (𝓝 V) := by
    simpa [V, pskInt, pskKern] using (perronKernelSigma_tendsto σ α hσ hα)
  have hδpos : 0 < T * |α| := mul_pos (lt_of_lt_of_le zero_lt_one hT) (abs_pos.mpr hα)
  by_cases hδle : T * |α| ≤ 1
  · have hmin : min 1 (1 / (T * |α|)) = 1 := by
      rw [min_eq_left]
      rw [one_le_div₀ hδpos]
      exact hδle
    rw [hmin]
    have hreg : ‖pskInt σ T α‖ ≤ Real.pi + 2 := by
      have hb : ‖pskInt σ T α‖ ≤ Real.pi + 2 * |α| * T := by
        simpa [pskInt, pskKern] using (perronKernelSigma_regionBound σ T α hσ (le_trans zero_le_one hT))
      have hbt : 2 * |α| * T ≤ 2 := by nlinarith
      nlinarith
    have hVnorm : ‖V‖ ≤ 2 * Real.pi := by
      simpa [V] using psk_value_norm σ α hσ
    have hmain : ‖pskInt σ T α - V‖ ≤ 32 := by
      calc
        ‖pskInt σ T α - V‖ ≤ ‖pskInt σ T α‖ + ‖V‖ := norm_sub_le _ _
        _ ≤ (Real.pi + 2) + 2 * Real.pi := add_le_add hreg hVnorm
        _ ≤ 32 := by nlinarith [Real.pi_lt_four]
    simpa using hmain
  · have hδgt1 : 1 < T * |α| := lt_of_not_ge hδle
    have hmin : min 1 (1 / (T * |α|)) = 1 / (T * |α|) := by
      rw [min_eq_right]
      rw [div_le_one₀ hδpos]
      exact le_of_lt hδgt1
    rw [hmin]
    have htail : ∀ R : ℝ, T ≤ R → ‖pskInt σ R α - pskInt σ T α‖ ≤ 6 / (|α| * T) := by
      intro R hR
      exact psk_tail_bound σ T R α hσ hα hT hR
    have hmain : ‖pskInt σ T α - V‖ ≤ 6 / (|α| * T) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hconvε : ∀ᶠ R in atTop, ‖pskInt σ R α - V‖ < ε := by
        have hh := (Metric.tendsto_nhds.mp hconv) ε hε
        simpa [dist_eq_norm] using hh
      rcases eventually_atTop.1 hconvε with ⟨R0, hR0⟩
      let R1 := max T R0
      have hTR1 : T ≤ R1 := le_max_left _ _
      have hR0R1 : R0 ≤ R1 := le_max_right _ _
      have hεR : ‖pskInt σ R1 α - V‖ ≤ ε := (hR0 R1 hR0R1).le
      have htri : ‖pskInt σ T α - V‖ ≤ ‖pskInt σ T α - pskInt σ R1 α‖ + ‖pskInt σ R1 α - V‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
        exact dist_triangle (pskInt σ T α) (pskInt σ R1 α) V
      calc
        ‖pskInt σ T α - V‖ ≤ ‖pskInt σ T α - pskInt σ R1 α‖ + ‖pskInt σ R1 α - V‖ := htri
        _ ≤ 6 / (|α| * T) + ε := add_le_add
            (by rw [norm_sub_rev]; exact htail R1 hTR1) hεR
    have hmain' : ‖pskInt σ T α - V‖ ≤ 6 / (T * |α|) := by
      simpa [mul_comm] using hmain
    have hcmp : 6 / (T * |α|) ≤ 32 * (1 / (T * |α|)) := by
      rw [div_eq_mul_inv]
      rw [one_div]
      exact mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 32)
        (by positivity : 0 ≤ (T * |α|)⁻¹)
    simpa [V] using hmain'.trans hcmp

end Commons.Analysis.Fourier
