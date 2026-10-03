/-
# Second-derivative off-diagonal decay of `λ_k − η_{≤jj} λ_k`

`Work.KMTAreas.A4.offBIteratedDeriv2Bound` is the *second* derivative companion of
`Work.KMTAreas.A4.offBDerivBound` (and of `offPieceMid`, which handles the `L¹`-mass itself):

  `∫ ‖(λ_k − η_{≤jj} λ_k)''‖ ≤ C · 2^k · (max (2^{k+jj-1}) 1)^{-N}`

for `k ≤ 0`, `jj ≥ 0`, `k + jj ≥ 0`, uniformly in `(k, jj)`.

## The mathematics

`x ↦ (λ_k − η_{≤jj}λ_k)(x) = λ_k(x)·(1 − η_{≤jj}(x))`, and the second derivative is

  `D'' = λ_k''·g + 2 λ_k'·g' + λ_k·g''`,   `g = 1 − η_{≤jj}`.

Every one of the three summands vanishes for `|x| < 2^{jj-1}` (there `η_{≤jj} ≡ 1`), so the
integrals localize to the tail `{|x| ≥ 2^{jj-1}}`, where `offLamTail` controls the tails of
`λ_k`, `λ_k'`, `λ_k''` by `C·(2^k)^i·(max (2^k·2^{jj-1}) 1)^{-N}`:

* `‖g‖ ≤ 1` and `2^{2k} ≤ 2^k` (as `k ≤ 0`) give the first summand the rate `2^k`;
* `‖g'‖ ≤ C 2^{-jj} ≤ C` and `‖g''‖ ≤ C 2^{-2jj}` give the other two;
* for the third summand the smallness of `λ_k` at the scale `2^{jj}` of `g''` is used:
  `‖λ_k(x)‖ = 2^k‖ψ(2^k x)‖ ≤ 2^k A (1+R)^{-N}` with `R = 2^{k+jj-1}`.

## Layout

* `norm_deriv_deriv_mul_le` — the pointwise second-derivative product rule estimate;
* `ofReal_two_mul_add` — the elementary `ENNReal` arithmetic combining three bounds;
* `offBIteratedDeriv2Bound_of_bounds` — the assembly: the three localized estimates for the
  three summands (proved in the companion files, or supplied as hypotheses) yield the claim;
* `offBIteratedDeriv2Bound` — the target, obtained from the three companion lemmas
  `integralIteratedDeriv2LamMulSubBmpLe`, `integralDerivLamMulDerivBmpLe`,
  `integralLamMulIteratedDeriv2BmpLe`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.integralIteratedDeriv2LamMulSubBmpLe
import Submission.Work.KMTAreas.A4.integralDerivLamMulDerivBmpLe
import Submission.Work.KMTAreas.A4.integralLamMulIteratedDeriv2BmpLe

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## The pointwise second-derivative product rule -/

/-- **Second-derivative product rule, in norm form.**  For `C²` functions `f g : ℝ → ℂ`,
`‖(f·g)''(x)‖ ≤ ‖f''(x)g(x)‖ + 2‖f'(x)g'(x)‖ + ‖f(x)g''(x)‖`. -/
lemma norm_deriv_deriv_mul_le {f g : ℝ → ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    ‖deriv (deriv (fun y => f y * g y)) x‖
      ≤ ‖iteratedDeriv 2 f x * g x‖ + 2 * ‖deriv f x * deriv g x‖
        + ‖f x * iteratedDeriv 2 g x‖ := by
  have h2 : iteratedDeriv 2 (fun y => f y * g y) = deriv (deriv (fun y => f y * g y)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [← h2]
  have hexp : iteratedDeriv 2 (fun y => f y * g y) x
      = iteratedDeriv 2 f x * g x + 2 * deriv f x * deriv g x + f x * iteratedDeriv 2 g x := by
    have h1 : (fun y => f y * g y) = f * g := rfl
    rw [h1, iteratedDeriv_mul hf hg]
    simp [Finset.sum_range_succ, Nat.choose, iteratedDeriv_one]
    ring
  rw [hexp]
  have h2norm : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hX : ‖2 * deriv f x * deriv g x‖ = 2 * ‖deriv f x * deriv g x‖ := by
    rw [norm_mul, norm_mul, norm_mul, h2norm]
    ring
  calc ‖iteratedDeriv 2 f x * g x + 2 * deriv f x * deriv g x + f x * iteratedDeriv 2 g x‖
      ≤ ‖iteratedDeriv 2 f x * g x + 2 * deriv f x * deriv g x‖
        + ‖f x * iteratedDeriv 2 g x‖ := norm_add_le _ _
    _ ≤ (‖iteratedDeriv 2 f x * g x‖ + ‖2 * deriv f x * deriv g x‖)
        + ‖f x * iteratedDeriv 2 g x‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = ‖iteratedDeriv 2 f x * g x‖ + 2 * ‖deriv f x * deriv g x‖
        + ‖f x * iteratedDeriv 2 g x‖ := by rw [hX]

/-! ## An `ENNReal` arithmetic identity -/

/-- `ofReal a + ofReal 2 * ofReal b + ofReal c = ofReal (a + 2b + c)` for `a, b, c ≥ 0`. -/
lemma ofReal_two_mul_add {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal a + ENNReal.ofReal 2 * ENNReal.ofReal b + ENNReal.ofReal c
      = ENNReal.ofReal (a + 2 * b + c) := by
  have h2b : ENNReal.ofReal 2 * ENNReal.ofReal b = ENNReal.ofReal (2 * b) :=
    (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hab : ENNReal.ofReal a + ENNReal.ofReal (2 * b) = ENNReal.ofReal (a + 2 * b) :=
    (ENNReal.ofReal_add ha (by linarith)).symm
  have habc : ENNReal.ofReal (a + 2 * b) + ENNReal.ofReal c
      = ENNReal.ofReal ((a + 2 * b) + c) := (ENNReal.ofReal_add (by linarith) hc).symm
  rw [h2b, hab, habc]

/-! ## The assembly -/

/-- **Assembly.**  Given the three localized estimates for the three summands of `D''`
(`λ_k''·(1−η_{≤jj})`, `λ_k'·η_{≤jj}'` and `λ_k·(1−η_{≤jj})''`), the target
`offBIteratedDeriv2Bound` follows. -/
theorem offBIteratedDeriv2Bound_of_bounds
    (hA : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj →
      ∫⁻ x : ℝ, ‖iteratedDeriv 2 (lam k) x * (1 - bmp jj x)‖ₑ
        ≤ ENNReal.ofReal (C * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))))
    (hB : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj →
      ∫⁻ x : ℝ, ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ
        ≤ ENNReal.ofReal (C * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))))
    (hC : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj →
      ∫⁻ x : ℝ, ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ₑ
        ≤ ENNReal.ofReal (C * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))))
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj →
      ∫ x : ℝ, ‖deriv (deriv (((lam k - mS (bmp jj) (lam k)) : SchwartzMap ℝ ℂ) : ℝ → ℂ)) x‖
        ≤ C * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
  obtain ⟨CA, hCApos, hCA⟩ := hA N
  obtain ⟨CB, hCBpos, hCB⟩ := hB N
  obtain ⟨CC, hCCpos, hCC⟩ := hC N
  refine ⟨CA + 2 * CB + CC, by positivity, ?_⟩
  intro k jj hk hjj hkjj
  -- the pointwise product form of the difference
  have hFcoe : ⇑((lam k - mS (bmp jj) (lam k)) : SchwartzMap ℝ ℂ)
      = fun x : ℝ => (lam k) x * (1 - (bmp jj) x) := by
    funext x
    show (lam k) x - (bmp jj) x * (lam k) x = (lam k) x * (1 - (bmp jj) x)
    ring
  rw [hFcoe]
  -- `iteratedDeriv 2` is `deriv ∘ deriv`
  have h2eq : iteratedDeriv 2 (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))
      = deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- the three pieces
  have hpt : ∀ x : ℝ,
      ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖ₑ
        ≤ ‖iteratedDeriv 2 (lam k) x * (1 - bmp jj x)‖ₑ
          + ENNReal.ofReal 2 * ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ
          + ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ₑ := by
    intro x
    have hf : ContDiffAt ℝ 2 (fun y : ℝ => (lam k) y) x := ((lam k).smooth 2).contDiffAt
    have hg : ContDiffAt ℝ 2 (fun y : ℝ => (1 : ℂ) - (bmp jj) y) x :=
      contDiffAt_const.sub (((bmp jj).smooth 2).contDiffAt)
    have hiter : iteratedDeriv 2 (fun y : ℝ => (1 : ℂ) - (bmp jj) y) x
        = - iteratedDeriv 2 (bmp jj) x := by
      have hsub := iteratedDeriv_sub (n := 2) (x := x) (f := fun _ : ℝ => (1 : ℂ))
        (g := fun y : ℝ => (bmp jj) y) contDiffAt_const (((bmp jj).smooth 2).contDiffAt)
      have h0 : iteratedDeriv 2 (fun _ : ℝ => (1 : ℂ)) x = 0 := by
        rw [iteratedDeriv_const]
        norm_num
      rw [show (fun y : ℝ => (1 : ℂ) - (bmp jj) y)
          = (fun _ : ℝ => (1 : ℂ)) - (fun y : ℝ => (bmp jj) y) from rfl]
      rw [hsub, h0, zero_sub]
    have hd : deriv (fun y : ℝ => (1 : ℂ) - (bmp jj) y) x = - deriv (bmp jj) x :=
      deriv_const_sub (1 : ℂ)
    have hreal := norm_deriv_deriv_mul_le (f := fun y : ℝ => (lam k) y)
      (g := fun y : ℝ => (1 : ℂ) - (bmp jj) y) hf hg
    have hreal' : ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖
        ≤ ‖iteratedDeriv 2 (lam k) x * (1 - bmp jj x)‖
          + 2 * ‖deriv (lam k) x * deriv (bmp jj) x‖
          + ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ := by
      refine hreal.trans (le_of_eq ?_)
      rw [hd, hiter]
      simp only [mul_neg, norm_neg]
    calc ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖ₑ
        = ENNReal.ofReal ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖ :=
          (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (‖iteratedDeriv 2 (lam k) x * (1 - bmp jj x)‖
            + 2 * ‖deriv (lam k) x * deriv (bmp jj) x‖
            + ‖lam k x * iteratedDeriv 2 (bmp jj) x‖) := ENNReal.ofReal_le_ofReal hreal'
      _ = ‖iteratedDeriv 2 (lam k) x * (1 - bmp jj x)‖ₑ
            + ENNReal.ofReal 2 * ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ
            + ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ₑ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_norm, ofReal_norm, ofReal_norm]
  -- measurability of the three integrands
  have hmeasA : Measurable (fun x : ℝ => ‖iteratedDeriv 2 (lam k) x * (1 - bmp jj x)‖ₑ) := by
    refine Measurable.enorm ?_
    refine Measurable.mul ?_ ?_
    · rw [← coe_iterate_derivCLM 2 (lam k)]
      exact (((SchwartzMap.derivCLM ℂ ℂ)^[2] (lam k)).continuous).measurable
    · exact (continuous_const.sub (bmp jj).continuous).measurable
  have hmeasB : Measurable (fun x : ℝ => ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ) := by
    refine Measurable.enorm ?_
    refine Measurable.mul ?_ ?_
    · have h : deriv (⇑(lam k)) = ⇑((SchwartzMap.derivCLM ℂ ℂ) (lam k)) := by
        have hc := coe_iterate_derivCLM 1 (lam k)
        simp only [Function.iterate_one, iteratedDeriv_one] at hc
        exact hc.symm
      rw [h]
      exact ((SchwartzMap.derivCLM ℂ ℂ) (lam k)).continuous.measurable
    · have h : deriv (⇑(bmp jj)) = ⇑((SchwartzMap.derivCLM ℂ ℂ) (bmp jj)) := by
        have hc := coe_iterate_derivCLM 1 (bmp jj)
        simp only [Function.iterate_one, iteratedDeriv_one] at hc
        exact hc.symm
      rw [h]
      exact ((SchwartzMap.derivCLM ℂ ℂ) (bmp jj)).continuous.measurable
  have hmeasC : Measurable (fun x : ℝ => ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ₑ) := by
    refine Measurable.enorm ?_
    refine Measurable.mul (lam k).continuous.measurable ?_
    rw [← coe_iterate_derivCLM 2 (bmp jj)]
    exact (((SchwartzMap.derivCLM ℂ ℂ)^[2] (bmp jj)).continuous).measurable
  -- splitting the integral of the sum
  have hsplit : ∫⁻ x : ℝ, (‖iteratedDeriv 2 (lam k) x * (1 - bmp jj x)‖ₑ
        + ENNReal.ofReal 2 * ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ
        + ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ₑ)
      = (∫⁻ x : ℝ, ‖iteratedDeriv 2 (lam k) x * (1 - bmp jj x)‖ₑ)
        + ENNReal.ofReal 2 * (∫⁻ x : ℝ, ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ)
        + ∫⁻ x : ℝ, ‖lam k x * iteratedDeriv 2 (bmp jj) x‖ₑ := by
    rw [lintegral_add_right (fun a : ℝ => ‖iteratedDeriv 2 (lam k) a * (1 - bmp jj a)‖ₑ
      + ENNReal.ofReal 2 * ‖deriv (lam k) a * deriv (bmp jj) a‖ₑ) hmeasC]
    congr 1
    rw [lintegral_add_left hmeasA,
      lintegral_const_mul' (ENNReal.ofReal 2) _ ENNReal.ofReal_ne_top]
  -- the three estimates
  have ha : (0 : ℝ) ≤ CA * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) :=
    mul_nonneg (mul_nonneg hCApos.le (le_of_lt (zpow_pos (by norm_num) k)))
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)
  have hb : (0 : ℝ) ≤ CB * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) :=
    mul_nonneg (mul_nonneg hCBpos.le (le_of_lt (zpow_pos (by norm_num) k)))
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)
  have hc : (0 : ℝ) ≤ CC * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) :=
    mul_nonneg (mul_nonneg hCCpos.le (le_of_lt (zpow_pos (by norm_num) k)))
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)
  have hbound : ∫⁻ x : ℝ, ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖ₑ
      ≤ ENNReal.ofReal ((CA + 2 * CB + CC) * (2 : ℝ) ^ k
          * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    refine (lintegral_mono hpt).trans ?_
    rw [hsplit]
    refine (add_le_add (add_le_add (hCA k jj hk hjj hkjj)
      (mul_le_mul_right (hCB k jj hk hjj hkjj) (ENNReal.ofReal 2)))
      (hCC k jj hk hjj hkjj)).trans (le_of_eq ?_)
    rw [ofReal_two_mul_add ha hb hc]
    congr 1
    ring
  -- pass to the Bochner integral
  have hint : Integrable (fun x : ℝ =>
      ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖) := by
    have heq : (fun x : ℝ => ‖⇑((SchwartzMap.derivCLM ℂ ℂ)^[2]
          ((lam k - mS (bmp jj) (lam k)) : SchwartzMap ℝ ℂ)) x‖)
        = fun x : ℝ => ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖ := by
      funext x
      rw [coe_iterate_derivCLM, hFcoe, h2eq]
    rw [← heq]
    exact (SchwartzMap.integrable _).norm
  have hnn : 0 ≤ᵐ[volume] (fun x : ℝ =>
      ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖) :=
    Filter.Eventually.of_forall (fun x => norm_nonneg _)
  have hof : ENNReal.ofReal (∫ x : ℝ,
        ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖)
      = ∫⁻ x : ℝ, ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖ₑ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact lintegral_congr (fun x => ofReal_norm _)
  have hle : ENNReal.ofReal (∫ x : ℝ,
        ‖deriv (deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))) x‖)
      ≤ ENNReal.ofReal ((CA + 2 * CB + CC) * (2 : ℝ) ^ k
          * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    rw [hof]
    exact hbound
  have hfin := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => norm_nonneg _)),
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (by positivity)
      (le_of_lt (zpow_pos (by norm_num) k)))
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) _))] at hfin
  exact hfin

theorem offBIteratedDeriv2Bound (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj → ∫ x : ℝ, ‖deriv (deriv (((Work.KMTAreas.A4.lam k - Work.KMTAreas.A4.mS (Work.KMTAreas.A4.bmp jj) (Work.KMTAreas.A4.lam k)) : SchwartzMap ℝ ℂ) : ℝ → ℂ)) x‖ ≤ C * (2:ℝ)^k * (max ((2:ℝ)^(k+jj-1)) 1) ^ (-(N:ℝ)) :=
  offBIteratedDeriv2Bound_of_bounds integralIteratedDeriv2LamMulSubBmpLe
    integralDerivLamMulDerivBmpLe integralLamMulIteratedDeriv2BmpLe N

end

end Work.KMTAreas.A4
