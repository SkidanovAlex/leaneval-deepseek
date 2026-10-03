import Mathlib
import Submission.Work.A3.Defs

/-!
# Plancherel/Parseval for finitely supported functions on `ℤ`

`Work.A3.kmtFhat f θ = ∑_x f x e(-xθ)` is the Fourier transform of `f : ℤ → ℂ` evaluated at the
frequency `θ ∈ ℝ` (it is `1`-periodic).  Here we prove the Parseval identity

`∫₀¹ ‖kmtFhat f θ‖² dθ = ∑_x ‖f x‖²`

for `f` finitely supported — the `L²` Plancherel identity in the form used by Area A3.

The proof is the direct one: the `tsum` is a finite sum over the support, the square of the finite
sum is expanded into a double sum of characters, and the orthogonality relation
`∫₀¹ e(2πi k θ) dθ = δ_{k,0}` (for `k : ℤ`) collapses the double sum.
-/

namespace Work.A3

noncomputable section

open MeasureTheory Complex

/-- The character `x ↦ e(-xθ) = exp(-2πi x θ)` appearing in `kmtFhat`. -/
def parsevalE (x : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * θ)))

lemma parsevalE_star (x : ℤ) (θ : ℝ) :
    star (parsevalE x θ) = Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ)) := by
  unfold parsevalE
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

lemma star_parsevalE_mul (x y : ℤ) (θ : ℝ) :
    star (parsevalE x θ) * parsevalE y θ
      = Complex.exp (2 * Real.pi * Complex.I * (((x:ℝ) - (y:ℝ)) * θ)) := by
  rw [parsevalE_star]
  unfold parsevalE
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Orthogonality of the characters on `[0,1]`**: `∫₀¹ e(2πi k θ) dθ = δ_{k,0}` for `k : ℤ`. -/
lemma parseval_integral_cexp_int (k : ℤ) :
    ∫ θ in Set.Icc (0:ℝ) 1, Complex.exp (2 * Real.pi * Complex.I * ((k:ℝ) * θ))
      = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
    have hc : (k:ℂ) * (2 * Real.pi * Complex.I) ≠ 0 := by
      simp [hk, Complex.I_ne_zero, Real.pi_ne_zero]
    have hfun : (fun θ : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((k:ℝ) * θ)))
        = fun θ : ℝ => Complex.exp (((k:ℂ) * (2 * Real.pi * Complex.I)) * (θ:ℂ)) := by
      funext θ; congr 1; push_cast; ring
    rw [hfun, integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
    rw [Complex.exp_int_mul_two_pi_mul_I k]
    simp [hk]

/-- Pairwise orthogonality: `∫₀¹ star (e(-xθ)) * e(-yθ) dθ = δ_{x,y}` for `x y : ℤ`. -/
lemma parseval_integral_char_pair (x y : ℤ) :
    ∫ θ in Set.Icc (0:ℝ) 1, star (parsevalE x θ) * parsevalE y θ = if x = y then 1 else 0 := by
  have h : (fun θ : ℝ => star (parsevalE x θ) * parsevalE y θ)
      = fun θ : ℝ => Complex.exp (2 * Real.pi * Complex.I * (((x - y : ℤ) : ℝ) * θ)) := by
    funext θ
    rw [star_parsevalE_mul]
    congr 1
    push_cast
    ring
  rw [h, parseval_integral_cexp_int]
  congr 1
  simp [sub_eq_zero]

/-- The finite-sum Parseval identity, in complex form: for a finite support `s` and coefficients
`a`, the `L²` norm squared of the finite exponential sum is the `ℓ²` norm squared of the
coefficients. -/
lemma parseval_integral_star_finsum (s : Finset ℤ) (a : ℤ → ℂ) :
    ∫ θ in Set.Icc (0:ℝ) 1, star (∑ x ∈ s, a x * parsevalE x θ) * (∑ y ∈ s, a y * parsevalE y θ)
      = ∑ x ∈ s, ((‖a x‖^2 : ℝ) : ℂ) := by
  have hpoint : ∀ θ, star (∑ x ∈ s, a x * parsevalE x θ) * (∑ y ∈ s, a y * parsevalE y θ)
      = ∑ x ∈ s, ∑ y ∈ s, (star (a x) * a y) * (star (parsevalE x θ) * parsevalE y θ) := by
    intro θ
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
    rw [star_mul]
    ring
  have hpair : ∀ x y : ℤ,
      Integrable (fun θ : ℝ => (star (a x) * a y) * (star (parsevalE x θ) * parsevalE y θ))
        (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    intro x y
    have hcont : Continuous
        (fun θ : ℝ => (star (a x) * a y) * (star (parsevalE x θ) * parsevalE y θ)) := by
      unfold parsevalE; fun_prop
    exact ContinuousOn.integrableOn_compact (μ := volume) isCompact_Icc hcont.continuousOn
  rw [funext hpoint]
  rw [MeasureTheory.integral_finsetSum]
  swap
  · intro x hx
    exact MeasureTheory.integrable_finsetSum s (fun y hy => hpair x y)
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [MeasureTheory.integral_finsetSum]
  swap
  · intro y hy
    exact hpair x y
  have hinner : ∑ y ∈ s, (star (a x) * a y) * (if x = y then (1:ℂ) else 0) = star (a x) * a x := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [hx]
  rw [Finset.sum_congr rfl (fun y hy => by rw [integral_const_mul, parseval_integral_char_pair]),
    hinner, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]

theorem parseval_finsupp (f : ℤ → ℂ) (hf : ∃ s : Finset ℤ, ∀ x ∉ s, f x = 0) : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) (fun θ : ℝ => ‖Work.A3.kmtFhat f θ‖ ^ 2) = ∑' x : ℤ, ‖f x‖ ^ 2 := by
  obtain ⟨s, hs⟩ := hf
  have hpoint : ∀ θ, kmtFhat f θ = ∑ x ∈ s, f x * parsevalE x θ := by
    intro θ
    unfold kmtFhat
    exact tsum_eq_sum (fun x hx => by simp [hs x hx])
  have hG : ∀ θ, ((‖kmtFhat f θ‖^2 : ℝ) : ℂ) = star (kmtFhat f θ) * kmtFhat f θ := by
    intro θ
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
  have h2 : ∫ θ in Set.Icc (0:ℝ) 1, ((‖kmtFhat f θ‖^2 : ℝ) : ℂ)
      = ((∑ x ∈ s, ‖f x‖^2 : ℝ) : ℂ) := by
    calc ∫ θ in Set.Icc (0:ℝ) 1, ((‖kmtFhat f θ‖^2 : ℝ) : ℂ)
        = ∫ θ in Set.Icc (0:ℝ) 1, star (kmtFhat f θ) * kmtFhat f θ := by
          exact integral_congr_ae (Filter.Eventually.of_forall hG)
      _ = ∫ θ in Set.Icc (0:ℝ) 1,
            star (∑ x ∈ s, f x * parsevalE x θ) * (∑ y ∈ s, f y * parsevalE y θ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          simp only [hpoint θ]
      _ = ∑ x ∈ s, ((‖f x‖^2 : ℝ) : ℂ) := parseval_integral_star_finsum s f
      _ = ((∑ x ∈ s, ‖f x‖^2 : ℝ) : ℂ) := (Complex.ofReal_sum s (fun x => ‖f x‖^2)).symm
  have h3 : ((∫ θ in Set.Icc (0:ℝ) 1, ‖kmtFhat f θ‖^2 : ℝ) : ℂ)
      = ((∑ x ∈ s, ‖f x‖^2 : ℝ) : ℂ) :=
    (integral_ofReal (μ := volume.restrict (Set.Icc (0:ℝ) 1)) (𝕜 := ℂ)
      (f := fun θ : ℝ => ‖kmtFhat f θ‖^2)).symm.trans h2
  have h4 : (∫ θ in Set.Icc (0:ℝ) 1, ‖kmtFhat f θ‖^2 : ℝ) = ∑ x ∈ s, ‖f x‖^2 :=
    Complex.ofReal_injective h3
  change (∫ θ in Set.Icc (0:ℝ) 1, ‖kmtFhat f θ‖^2 : ℝ) = ∑' x : ℤ, ‖f x‖^2
  rw [h4, tsum_eq_sum (s := s) (fun x hx => by simp [hs x hx])]

end

end Work.A3
