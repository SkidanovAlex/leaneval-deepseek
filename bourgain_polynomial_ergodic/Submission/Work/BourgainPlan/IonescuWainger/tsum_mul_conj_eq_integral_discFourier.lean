import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc

open MeasureTheory Finset
open scoped BigOperators

namespace Work.BourgainPlan.IonescuWainger

/-- The integral of a character `fourier j` over the circle against the probability Haar measure:
`∫_𝕋 e^{2πi j ξ} dξ = δ_{j,0}`.  Obtained from Mathlib's orthonormality of the monomials. -/
private lemma integral_fourier_eq_ite (j : ℤ) :
    ∫ ξ : Circle, fourier j ξ ∂AddCircle.haarAddCircle = if j = 0 then 1 else 0 := by
  have h := ContinuousMap.inner_toLp (μ := (AddCircle.haarAddCircle : Measure Circle))
    (fourier (0 : ℤ)) (fourier j)
  have h2 := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) (0 : ℤ) j
  rw [h2] at h
  simp only [fourier_zero, map_one, mul_one] at h
  rw [← h]
  by_cases hj : j = 0
  · simp [hj]
  · simp [hj, eq_comm]

/-- A constant times a character is integrable for the probability Haar measure on the circle. -/
private lemma integrable_const_mul_fourier (c : ℂ) (j : ℤ) :
    Integrable (fun ξ : Circle => c * fourier j ξ) AddCircle.haarAddCircle :=
  Continuous.integrable_of_hasCompactSupport
    ((continuous_const : Continuous fun _ : Circle => c).mul (map_continuous (fourier j)))
    (HasCompactSupport.of_compactSpace _)

/-- Termwise integration of a finite combination of characters:
`∫_𝕋 Σ_{m ∈ s} c m · e^{2πi (n-m) ξ} dξ = Σ_{m ∈ s} c m · δ_{n,m}`. -/
private lemma integral_finsetSum_const_mul_fourier (s : Finset ℤ) (n : ℤ) (c : ℤ → ℂ) :
    ∫ ξ : Circle, (∑ m ∈ s, c m * fourier (n - m) ξ) ∂AddCircle.haarAddCircle
      = ∑ m ∈ s, c m * (if n = m then 1 else 0) := by
  have h1 : ∫ ξ : Circle, (∑ m ∈ s, c m * fourier (n - m) ξ) ∂AddCircle.haarAddCircle
      = ∑ m ∈ s, ∫ ξ : Circle, c m * fourier (n - m) ξ ∂AddCircle.haarAddCircle :=
    integral_finsetSum s (fun m _ => integrable_const_mul_fourier (c m) (n - m))
  rw [h1]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, integral_fourier_eq_ite]
  by_cases h : n = m <;> simp [h, sub_eq_zero]

/-- The two-variable version of `integral_finsetSum_const_mul_fourier`. -/
private lemma integral_finsetSum_finset_const_mul_fourier (s : Finset ℤ) (c : ℤ → ℤ → ℂ) :
    ∫ ξ : Circle, (∑ n ∈ s, ∑ m ∈ s, c n m * fourier (n - m) ξ) ∂AddCircle.haarAddCircle
      = ∑ n ∈ s, ∑ m ∈ s, c n m * (if n = m then 1 else 0) := by
  have h1 : ∫ ξ : Circle, (∑ n ∈ s, ∑ m ∈ s, c n m * fourier (n - m) ξ)
        ∂AddCircle.haarAddCircle
      = ∑ n ∈ s, ∫ ξ : Circle, (∑ m ∈ s, c n m * fourier (n - m) ξ)
        ∂AddCircle.haarAddCircle :=
    integral_finsetSum s (fun n _ =>
      integrable_finsetSum _ (fun m _ => integrable_const_mul_fourier (c n m) (n - m)))
  rw [h1]
  exact Finset.sum_congr rfl fun n _ => integral_finsetSum_const_mul_fourier s n (c n)

/-- **Parseval's identity for finitely supported functions on `ℤ`.**  For finitely supported
`h, k : ℤ → ℂ`,

`∑_n h n · conj (k n) = ∫_𝕋 𝓕h ξ · conj (𝓕k ξ) dξ`,

where `discFourier f ξ = ∑'_n f n · e^{2πi n ξ}` (`FreqArc.lean`) and the integral is with respect to
the probability Haar measure `AddCircle.haarAddCircle` on `𝕋 = ℝ/ℤ`.

This is the other half of the Fourier-side bridge to Tao's `ortho`(ii)/(iii)
(arXiv:2008.05066, §4): together with `discFourier_mul_eq_circConv` it identifies the pairing
`Σ_n ∏_j ⟨f_j(n), g_j(n)⟩` of a nonce tuple with
`∫_𝕋 (✻_j 𝓕f_j)(ξ) · conj ((✻_j 𝓕g_j)(ξ)) dξ`, whose vanishing is then supplied by
`integral_circConvFin_mul_conj_eq_zero` and the arithmetic of `ArcSep.lean`/`ArcNumOrth.lean`.

Proof ingredients: expand both sides as finite sums over the supports
(`discFourier_eq_sum_of_support`), use `conj (fourier m ξ) = fourier (-m) ξ` and Mathlib's
orthonormality `orthonormal_fourier` (equivalently
`∫ ξ, fourier j ξ ∂haarAddCircle = if j = 0 then 1 else 0`). -/
theorem tsum_mul_conj_eq_integral_discFourier {h k : ℤ → ℂ} (hh : (Function.support h).Finite)
    (hk : (Function.support k).Finite) :
    ∑' n : ℤ, h n * star (k n)
      = ∫ ξ : Circle, discFourier h ξ * star (discFourier k ξ)
          ∂AddCircle.haarAddCircle := by
  classical
  -- a single finite set containing the supports of both `h` and `k`
  obtain ⟨s, hs1, hs2⟩ : ∃ s : Finset ℤ, (∀ n, n ∉ s → h n = 0) ∧ (∀ n, n ∉ s → k n = 0) := by
    refine ⟨hh.toFinset ∪ hk.toFinset, ?_, ?_⟩
    · intro n hn
      by_contra hne
      exact hn (Finset.mem_union_left _ (hh.mem_toFinset.mpr hne))
    · intro n hn
      by_contra hne
      exact hn (Finset.mem_union_right _ (hk.mem_toFinset.mpr hne))
  have hF : ∀ ξ, discFourier h ξ = ∑ n ∈ s, h n * fourier n ξ := fun ξ =>
    discFourier_eq_sum_of_support hs1 ξ
  have hK : ∀ ξ, star (discFourier k ξ) = ∑ m ∈ s, star (k m) * fourier (-m) ξ := by
    intro ξ
    rw [discFourier_eq_sum_of_support hs2 ξ, star_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hstar : star (fourier m ξ) = fourier (-m) ξ := by
      rw [Complex.star_def]
      exact (fourier_neg (n := m) (x := ξ)).symm
    rw [star_mul, hstar]
    ring
  have hprod : ∀ ξ, discFourier h ξ * star (discFourier k ξ)
      = ∑ n ∈ s, ∑ m ∈ s, (h n * star (k m)) * fourier (n - m) ξ := by
    intro ξ
    rw [hF ξ, hK ξ, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [sub_eq_add_neg, fourier_add]
    ring
  rw [tsum_eq_sum (s := s) (fun n hn => by rw [hs1 n hn, zero_mul])]
  rw [show (fun ξ : Circle => discFourier h ξ * star (discFourier k ξ))
      = (fun ξ : Circle => ∑ n ∈ s, ∑ m ∈ s, (h n * star (k m)) * fourier (n - m) ξ)
      from funext hprod]
  rw [integral_finsetSum_finset_const_mul_fourier s (fun n m => h n * star (k m))]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hterm : ∀ m : ℤ, (h n * star (k m)) * (if n = m then (1 : ℂ) else 0)
      = if n = m then h n * star (k m) else 0 := by
    intro m
    by_cases h1 : n = m <;> simp [h1]
  rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_ite_eq, if_pos hn]

end Work.BourgainPlan.IonescuWainger
