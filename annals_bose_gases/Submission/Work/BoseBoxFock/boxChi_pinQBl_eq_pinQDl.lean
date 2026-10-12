import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.K1pairingDefs
import Submission.Work.BoseBoxFock.pinQDl_eq_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxChi_pinQBl_eq_pinQDl` — the box average of the `χ̂`-row

`pinQBl ℓ W w = Σ'_n Ŵ(k_n)·χ̂(ℓ k_n)·e^{i⟪k_n,w⟫}` (`k_n = kmomInt ℓ n = ℓ⁻¹·2πn`) and
`pinQDl ℓ W = Σ'_n Ŵ(k_n)·χ̂(ℓ k_n)²` (`Work.BoseBoxFock.pinQLimDefs`) are the two `χ̂`-rows of the
limit pair kernel `K1lim`.  This file proves the identity that pairs the first against the box
window: the box average of `pinQBl` against `χ_ℓ = chiScale ℓ = χ(·/ℓ)` is `ℓ³` times the
constant `pinQDl`,

    `∫_{Λ(ℓ)} χ_ℓ(w)·pinQBl ℓ W w dw = ℓ³ · pinQDl ℓ W`.

This is the `χχ`-normalisation of the `θθ`-row `pinQDl` (`FINDING_pinQBl_eq_periodisation_PROVED.md`,
`Work.BoseBoxFock.pinQDl_eq_boxAvg` are the periodised/box-average companions).

## Route

Everything is termwise in the lattice sum.  The single analytic input is the box Fourier integral

    `∫_{ℝ³} χ_ℓ(w)·e^{i⟪k,w⟫} dw = ℓ³·χ̂(ℓ k)      (χ_ℓ real and even)`

(`integral_chiScale_mul_exp` below).  It is the complexification of FS's
`∫_{Λ(ℓ)} χ_Λ(x)cos(k·x)dx = ℓ³χ̂(ℓk)` (`Work.BoseB4.realIP_thetaFun_modeVec`), the `sin` part
vanishing by evenness: the `p`-convention transform `kinFT (χ_ℓ) k = ∫ e^{−i⟪k,w⟫}χ_ℓ w dw` is
`ℓ³χ̂(ℓk)` (`Work.OneBodyKin.kinFT_chiScale`), so the `+i` integral is its complex conjugate, and
`χ_ℓ` (hence its transform) is real.

The lattice sum `Σ'_n |Ŵ(k_n)|·|χ̂(ℓk_n)|` converges absolutely: `|Ŵ| ≤ ∫|W|` uniformly in the
momentum (`chat_abs_le_uniform`, no integrability needed), while `χ̂` has order-`52` decay on the
dual lattice (`hatChi_decay_52` + `summable_vec_inv_one_add_norm_sq`).  Hence the sum/integral
interchange is `hasSum_integral_of_summable_integral_norm`, and the `n`-th term of the resulting sum
is `Ŵ(k_n)·(ℓ³χ̂(ℓk_n))·χ̂(ℓk_n) = ℓ³·Ŵ(k_n)χ̂(ℓk_n)²`, i.e. exactly `ℓ³` times the `n`-th term of
`pinQDl`.

The hypothesis `Integrable W` is not used by the argument (`chat_abs_le_uniform` bounds `Ŵ` by the
always-defined `∫|W|`): the identity holds for an arbitrary `W`.  It is kept because it is part of
the requested statement.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- **The box Fourier integral of the bump.**  For `k : ℝ³` and `ℓ > 0`,

    `∫_w χ_ℓ(w)·e^{i⟪k,w⟫} dw = ℓ³·χ̂(ℓ k)`,

the complexification of FS's `∫_{Λ(ℓ)} χ_Λ(x)cos(k·x)dx = ℓ³χ̂(ℓk)`.  The proof goes through the
`p`-convention Fourier transform `kinFT (χ_ℓ) k = ∫ e^{−i⟪k,w⟫}χ_ℓ w dw = ℓ³χ̂(ℓ k)`
(`Work.OneBodyKin.kinFT_chiScale`) and complex conjugation: `χ_ℓ` is real, so the `−i` and `+i`
integrals are conjugate to each other, and the right-hand side is real. -/
theorem integral_chiScale_mul_exp {ℓ : ℝ} (hℓ : 0 < ℓ) (k : E3) :
    (∫ w : E3, (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ k w : ℂ)))
      = ((ℓ ^ 3 : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) := by
  have hconj : (∫ w : E3, (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ k w : ℂ)))
      = (starRingEnd ℂ) (∫ w : E3, (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ k w : ℂ)))) := by
    rw [← integral_conj (μ := volume)
      (f := fun w : E3 => (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ k w : ℂ))))]
    apply integral_congr_ae
    filter_upwards with w
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring_nf
  have hkin : (∫ w : E3, (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ k w : ℂ))))
      = Submission.BoseGases.kinFT (fun z : E3 => (((Submission.BoseGases.chiScale ℓ z : ℝ)) : ℂ)) k := by
    rw [Submission.BoseGases.kinFT]
    apply integral_congr_ae
    filter_upwards with w
    ring
  rw [hconj, hkin, Work.OneBodyKin.kinFT_chiScale hℓ k]
  rw [show Work.OneBodyKin.profHat (ℓ • k) = Work.BoseK15.corpusBox.hatChi (ℓ • k) from rfl]
  rw [← Complex.ofReal_pow]
  rw [map_mul, Complex.conj_ofReal, Complex.conj_ofReal]

theorem boxChi_pinQBl_eq_pinQDl {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWi : MeasureTheory.Integrable W) :
    (∫ w in Submission.BoseGases.acube ℓ,
        (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ) * Work.BoseBoxFock.pinQBl ℓ W w)
      = ((ℓ ^ 3 : ℝ) : ℂ) * Work.BoseBoxFock.pinQDl ℓ W := by
  classical
  -- `ℓ • kmomInt ℓ n = vec n`: the momentum argument of `χ̂` is the dual-lattice vector
  have hsmul : ∀ n : Fin 3 → ℤ, ℓ • kmomInt ℓ n = Work.BoseB4.vec n := by
    intro n; rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  -- the `n`-th lattice coefficient of the two rows
  set A : (Fin 3 → ℤ) → ℂ := fun n =>
    ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ) with hA
  -- the `n`-th integrand: `χ_ℓ(w)·A_n·e^{i⟪k_n,w⟫}`
  set F : (Fin 3 → ℤ) → E3 → ℂ := fun n w =>
    (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
      * (A n * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) w : ℂ))) with hF
  -- ### absolute convergence of the lattice coefficients
  have hsumm : Summable (fun n => ‖A n‖) := by
    rw [hA]
    obtain ⟨Kw, hKw0, hKw⟩ := chat_abs_le_uniform (W := W)
    obtain ⟨Cχ, hCχ0, hCχ⟩ := hatChi_decay_52
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)).mul_left (Kw * Cχ))
    rw [norm_mul, pinQ_norm_ofReal_complex, pinQ_norm_ofReal_complex, Real.norm_eq_abs,
      Real.norm_eq_abs, hsmul n]
    calc |Work.BoseFixR.chat W (kmomInt ℓ n)| * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)|
        ≤ Kw * (Cχ * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :=
          mul_le_mul (hKw _) (hCχ _) (abs_nonneg _) hKw0
      _ = (Kw * Cχ) * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by ring
  -- ### the bump factor: continuous, compactly supported
  have hbchi_c : Continuous (fun w : E3 => (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp (Submission.BoseGases.chiScale_continuous ℓ)
  have hbchi_cs : HasCompactSupport (fun w : E3 => (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)) :=
    (Submission.BoseGases.chiScale_hasCompactSupport hℓ.ne').comp_left
      (g := fun r : ℝ => (r : ℂ)) (by norm_num)
  -- ### integrability of every summand
  have hFint : ∀ n, Integrable (F n) volume := by
    intro n
    have hcont : Continuous (F n) := by
      rw [hF]
      exact hbchi_c.mul (continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)))))
    have hcs : HasCompactSupport (F n) := by
      rw [hF]
      exact HasCompactSupport.mul_right hbchi_cs
        (f' := fun w : E3 => A n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)))
    exact hcont.integrable_of_hasCompactSupport hcs
  -- ### the norm of the summand, and summability of its integral
  have hnorm_eq : ∀ n w, ‖F n w‖ = Submission.BoseGases.chiScale ℓ w * ‖A n‖ := by
    intro n w
    rw [hF, norm_mul, norm_mul, pinQ_norm_ofReal_complex, Real.norm_eq_abs,
      abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ w)]
    have hexp1 : ‖Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
    rw [hexp1, mul_one]
  have hFsumm : Summable (fun n => ∫ w : E3, ‖F n w‖) := by
    have hIntEq : ∀ n,
        (∫ w : E3, ‖F n w‖)
          = (∫ w : E3, Submission.BoseGases.chiScale ℓ w) * ‖A n‖ := by
      intro n
      rw [show (∫ w : E3, ‖F n w‖)
            = ∫ w : E3, Submission.BoseGases.chiScale ℓ w * ‖A n‖ from by
        apply integral_congr_ae; filter_upwards with w; exact hnorm_eq n w]
      rw [integral_mul_const]
    rw [show (fun n => ∫ w : E3, ‖F n w‖)
          = fun n => (∫ w : E3, Submission.BoseGases.chiScale ℓ w) * ‖A n‖ from
      funext hIntEq]
    exact Summable.mul_left _ hsumm
  -- ### the pointwise series form of the left-hand integrand
  have hpoint : ∀ w : E3,
      (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ) * pinQBl ℓ W w = ∑' n, F n w := by
    intro w
    rw [pinQBl, hF, hA]
    rw [tsum_mul_left]
  -- ### the `n`-th integral
  have hFn : ∀ n, (∫ w : E3, F n w)
      = A n * (((ℓ ^ 3 : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) := by
    intro n
    have h1 : (∫ w : E3, F n w)
        = A n * ∫ w : E3, (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with w
      rw [hF]
      ring
    rw [h1, integral_chiScale_mul_exp hℓ (kmomInt ℓ n)]
  -- ### support transfer to the centred cube `Λ(ℓ)`:
  -- `χ_ℓ` is supported in the ball of radius `ℓ/2`, which sits inside `acube ℓ`
  have hLHS : (∫ w in Submission.BoseGases.acube ℓ,
        (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ) * Work.BoseBoxFock.pinQBl ℓ W w)
      = ∫ w : E3, ∑' n, F n w := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => ?_)]
    · apply integral_congr_ae; filter_upwards with w; exact hpoint w
    · by_cases h : Submission.BoseGases.chiScale ℓ w = 0
      · simp [h]
      · exact absurd (Submission.BoseGases.chiScale_mem_acube hℓ h) hw
  -- ### the `ℓ³` bookkeeping and the identification with `pinQDl`
  have hfinal : (∑' n, A n * (((ℓ ^ 3 : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)))
      = ((ℓ ^ 3 : ℝ) : ℂ) * pinQDl ℓ W := by
    rw [pinQDl]
    rw [show (∑' n, A n * (((ℓ ^ 3 : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)))
          = ∑' n, ((ℓ ^ 3 : ℝ) : ℂ) * (A n
              * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) from
        tsum_congr (fun n => by ring)]
    rw [tsum_mul_left]
    congr 1
    apply tsum_congr
    intro n
    rw [hA]
    ring
  calc (∫ w in Submission.BoseGases.acube ℓ,
        (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ) * Work.BoseBoxFock.pinQBl ℓ W w)
      = ∫ w : E3, ∑' n, F n w := hLHS
    _ = ∑' n, ∫ w : E3, F n w :=
        (hasSum_integral_of_summable_integral_norm hFint hFsumm).tsum_eq.symm
    _ = ∑' n, A n * (((ℓ ^ 3 : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) := tsum_congr hFn
    _ = ((ℓ ^ 3 : ℝ) : ℂ) * Work.BoseBoxFock.pinQDl ℓ W := hfinal

end Work.BoseBoxFock
