import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Submission.Work.BoseBoxFock.L1Tails.foldH_contDiff
import Submission.Work.BoseBoxFock.L1Tails.hPair_tail_sum_le
import Submission.Work.BoseBoxFock.L1Tails.kinFT_foldH_eq_hPair
import Submission.Work.BoseBoxFock.L1Tails.latPer3_pairing_eq
import Submission.Work.BoseBoxFock.L1Tails.latPerC_fourierCoeff
import Submission.Work.BoseBoxFock.L1Tails.latPerC_hasSum_fourier
import Submission.Work.BoseBoxFock.L1Tails.summable_kinFT_kappaL
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.kernelTail` — the truncation tail of the `χχ` periodised kernel
(T6 of the `L¹`-tail design `sources/boseDCF/bose_L1tails.md`)

For an `L¹` weight `W` supported in the ball of radius `R`, a smooth kernel `H` supported in
`boxL ℓ × boxL ℓ` and any lattice truncation `c` (`‖c n‖ ≤ 1`, `c n = 1` below `Λ`) whose low modes
are contained in `S`, the difference between the pairing of the periodisation `latPer3 ℓ W` against
`H` and the truncated lattice sum is bounded by `2 √(τ ℓ⁹ D)`, where `τ` bounds the Coulomb tail
`(ℓ³)⁻¹ Σ_{n : ‖κ_n‖ ≥ Λ} ‖Ŵ(κ_n)‖²/‖κ_n‖²` and `D = ∫∫ Σ_j ‖∂_{w_j}H‖²`.

The proof is the one recorded in `L1Tails/DefsC.lean`: the pairing is first folded onto the smooth
kernel `foldH H` (`Work...latPer3_pairing_eq`), whose periodisation is expanded in an absolutely
convergent Fourier series (`Work...latPerC_hasSum_fourier`, `Work...summable_kinFT_kappaL`), the
terms being evaluated by `Work...kinFT_foldH_eq_hPair` and `Work...latPerC_fourierCoeff`; the
remaining tail is split by Cauchy–Schwarz between `hτ` and the sharp lattice bound
`Work...hPair_tail_sum_le`.  The assembly below (`pairing_tsum_expand` … `kernelTail_final`) is the
`ℓ¹`-interchange of the lattice series with the weight and the finite-tail Cauchy–Schwarz.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `‖vec n‖ = 2π ‖latVec n‖`. -/
lemma norm_vec_eq_latVec (n : Fin 3 → ℤ) :
    ‖Work.BoseB4.vec n‖ = 2 * Real.pi * ‖Work.BoseBoxFock.latVec n‖ := by
  have h : Work.BoseB4.vec n = (2 * Real.pi) • Work.BoseBoxFock.latVec n := by
    rw [Work.BoseB4.vec, Work.BoseBoxFock.latVec]
    ext i
    simp [mul_comm]
  rw [h, norm_smul, Real.norm_of_nonneg (by positivity)]

lemma norm_kappaL_eq_latVec {ℓ : ℝ} (hℓ : 0 < ℓ) (n : Fin 3 → ℤ) :
    ‖kappaL ℓ n‖ = (2 * Real.pi / ℓ) * ‖Work.BoseBoxFock.latVec n‖ := by
  rw [kappaL, Work.BoseBoxFock.kmomInt, norm_smul, norm_vec_eq_latVec,
    Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
  ring

/-- The lattice ball of the modes with `‖κ_n‖ ≤ Λ`. -/
noncomputable def lowLab (ℓ Λ : ℝ) : Finset (Fin 3 → ℤ) :=
  Work.BoseBoxFock.LatFourier.latBall (Λ * ℓ / (2 * Real.pi))

lemma mem_lowLab_of_norm_le {ℓ Λ : ℝ} (hℓ : 0 < ℓ) {n : Fin 3 → ℤ}
    (hn : ‖kappaL ℓ n‖ ≤ Λ) : n ∈ lowLab ℓ Λ := by
  rw [lowLab, Work.BoseBoxFock.LatFourier.mem_latBall]
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  have h4 : (2 * Real.pi / ℓ) * ‖Work.BoseBoxFock.latVec n‖ ≤ Λ := by
    rwa [norm_kappaL_eq_latVec hℓ] at hn
  rw [le_div_iff₀ h2]
  have key : (2 * Real.pi / ℓ) * ℓ = 2 * Real.pi := by field_simp
  calc ‖Work.BoseBoxFock.latVec n‖ * (2 * Real.pi)
      = ‖Work.BoseBoxFock.latVec n‖ * ((2 * Real.pi / ℓ) * ℓ) := by rw [key]
    _ = (2 * Real.pi / ℓ) * ‖Work.BoseBoxFock.latVec n‖ * ℓ := by ring
    _ ≤ Λ * ℓ := mul_le_mul_of_nonneg_right h4 hℓ.le

/-- `‖exp (I t)‖ = 1` for a real `t`. -/
lemma norm_exp_I_ofReal (t : ℝ) : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  rw [mul_comm Complex.I (t : ℂ)]
  exact Complex.norm_exp_ofReal_mul_I t

/-- **Interchange.**  Given the absolutely convergent Fourier expansion of the periodisation
`latPerC ℓ Φ` (`hexp`, with `hsumm` the summability of its coefficients) and an `L¹` weight `W`,
the pairing of `W` against `latPerC ℓ Φ` is the lattice sum of the products of the samples. -/
lemma pairing_tsum_expand {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) {Φ : E3 → ℂ}
    (hsumm : Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT Φ (kappaL ℓ n)‖))
    (hexp : ∀ z : E3, HasSum (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ *
        Submission.BoseGases.kinFT Φ (kappaL ℓ n)
        * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
      (latPerC ℓ Φ z)) :
    (∫ z, ((W z : ℝ) : ℂ) * latPerC ℓ Φ z)
      = ∑' n : Fin 3 → ℤ,
          (∫ z, ((W z : ℝ) : ℂ)
              * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
            * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (kappaL ℓ n)) := by
  set b : (Fin 3 → ℤ) → ℂ := fun n => Submission.BoseGases.kinFT Φ (kappaL ℓ n) with hb
  have hb_summ : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * ‖b n‖) := hsumm.mul_left _
  have hFmeas : ∀ n : Fin 3 → ℤ, AEStronglyMeasurable (fun z : E3 => ((W z : ℝ) : ℂ) *
      ((ℓ ^ 3)⁻¹ * b n * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))))
      (volume : Measure E3) := by
    intro n
    refine (Complex.continuous_ofReal.comp_aestronglyMeasurable hWi.aestronglyMeasurable).mul ?_
    fun_prop
  have hFbound : ∀ n : Fin 3 → ℤ, ∀ᵐ z ∂(volume : Measure E3), ‖((W z : ℝ) : ℂ) *
      ((ℓ ^ 3)⁻¹ * b n * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))‖
      ≤ (ℓ ^ 3)⁻¹ * ‖b n‖ * ‖W z‖ := by
    intro n
    refine Filter.Eventually.of_forall fun z => ?_
    have h1 : ‖((W z : ℝ) : ℂ)‖ = ‖W z‖ := by simp
    have h3 : ‖Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))‖ = 1 :=
      norm_exp_I_ofReal _
    have h2 : ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ = (ℓ ^ 3)⁻¹ := by
      rw [show ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ = |(ℓ ^ 3)⁻¹| from by simp,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3))]
    have h4 : ‖(((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * b n
        * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))‖
        ≤ (ℓ ^ 3)⁻¹ * ‖b n‖ := by
      rw [norm_mul, norm_mul, h2, h3, mul_one]
    calc ‖((W z : ℝ) : ℂ) * ((ℓ ^ 3)⁻¹ * b n
          * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))‖
        = ‖((W z : ℝ) : ℂ)‖ * ‖(((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * b n
            * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))‖ := by
          rw [norm_mul]
      _ ≤ ‖W z‖ * ((ℓ ^ 3)⁻¹ * ‖b n‖) := by
          rw [h1]
          exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = (ℓ ^ 3)⁻¹ * ‖b n‖ * ‖W z‖ := by ring
  have hsumm_bound : ∀ᵐ z ∂(volume : Measure E3),
      Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * ‖b n‖ * ‖W z‖) :=
    Filter.Eventually.of_forall fun z => hb_summ.mul_right _
  have hbound_int : Integrable (fun z : E3 =>
      ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖b n‖ * ‖W z‖) (volume : Measure E3) := by
    have hEq : (fun z : E3 => ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖b n‖ * ‖W z‖)
        = fun z : E3 => (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖b n‖) * ‖W z‖ := by
      funext z
      exact tsum_mul_right
    rw [hEq]
    exact hWi.norm.const_mul _
  have hconv : ∀ᵐ z ∂(volume : Measure E3), HasSum (fun n : Fin 3 → ℤ => ((W z : ℝ) : ℂ) *
      ((ℓ ^ 3)⁻¹ * b n * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))))
      (((W z : ℝ) : ℂ) * latPerC ℓ Φ z) :=
    Filter.Eventually.of_forall fun z => (hexp z).mul_left _
  have hmain := MeasureTheory.hasSum_integral_of_dominated_convergence
    (F := fun (n : Fin 3 → ℤ) (z : E3) => ((W z : ℝ) : ℂ) *
      ((ℓ ^ 3)⁻¹ * b n * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))))
    (f := fun z : E3 => ((W z : ℝ) : ℂ) * latPerC ℓ Φ z)
    (bound := fun (n : Fin 3 → ℤ) (z : E3) => (ℓ ^ 3)⁻¹ * ‖b n‖ * ‖W z‖)
    hFmeas hFbound hsumm_bound hbound_int hconv
  have hInt : ∀ n : Fin 3 → ℤ, (∫ z : E3, ((W z : ℝ) : ℂ) *
      ((ℓ ^ 3)⁻¹ * b n * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))))
      = (∫ z : E3, ((W z : ℝ) : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
          * ((ℓ ^ 3)⁻¹ * b n) := by
    intro n
    rw [show (fun z : E3 => ((W z : ℝ) : ℂ) *
        ((ℓ ^ 3)⁻¹ * b n * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))))
        = fun z : E3 =>
          (((W z : ℝ) : ℂ) * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
            * ((ℓ ^ 3)⁻¹ * b n) from by funext z; ring]
    exact MeasureTheory.integral_mul_const _ _
  rw [← hmain.tsum_eq]
  exact tsum_congr fun n => hInt n

/-- `wSample ℓ W (-n)` as an integral against the conjugate character. -/
lemma wSample_neg_eq {ℓ : ℝ} (W : E3 → ℝ) (n : Fin 3 → ℤ) :
    wSample ℓ W (-n)
      = ∫ z, ((W z : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)) := by
  unfold wSample
  rw [kappaL_neg]
  show ∫ y, Complex.exp (-(Complex.I * ((inner ℝ (-kappaL ℓ n) y : ℝ) : ℂ)))
      * ((W y : ℝ) : ℂ) = _
  rw [show (fun z : E3 => Complex.exp (-(Complex.I * ((inner ℝ (-kappaL ℓ n) z : ℝ) : ℂ)))
      * ((W z : ℝ) : ℂ)) = fun z : E3 =>
        ((W z : ℝ) : ℂ) * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)) from by
    funext z
    rw [inner_neg_left]
    have h : -(Complex.I * (((-inner ℝ (kappaL ℓ n) z : ℝ)) : ℂ))
        = Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ) := by push_cast; ring
    rw [h, mul_comm]]

/-- **The identity.**  The pairing of `latPer3 ℓ W` against `H` equals the full lattice sum of
`wSample ℓ W n * hPair ℓ H n`. -/
lemma kernelTail_identity {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ} (hWi : MeasureTheory.Integrable W)
    {H : E3 → E3 → ℂ}
    (hsumm : Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n)‖))
    (hexp : ∀ z : E3, HasSum (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ *
        Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n)
        * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
      (latPerC ℓ (foldH H) z))
    (hred : (∫ w, ∫ y, Work.BoseBoxFock.latPer3 ℓ W (w - y) * H w y)
      = (ℓ ^ 3 : ℂ) * ∫ z, ((W z : ℝ) : ℂ) * latPerC ℓ (foldH H) z)
    (hpair : ∀ n : Fin 3 → ℤ,
      Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n) = hPair ℓ H (-n)) :
    (∫ w, ∫ y, Work.BoseBoxFock.latPer3 ℓ W (w - y) * H w y)
      = ∑' n : Fin 3 → ℤ, wSample ℓ W n * hPair ℓ H n := by
  rw [hred, pairing_tsum_expand hℓ hWi hsumm hexp]
  have hG : ∀ n : Fin 3 → ℤ, (∫ z : E3, ((W z : ℝ) : ℂ)
      * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
      = wSample ℓ W (-n) := fun n => (wSample_neg_eq W n).symm
  simp only [hG]
  have hℓ3 : ((ℓ ^ 3 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  have hsummand : ∀ n : Fin 3 → ℤ,
      (ℓ ^ 3 : ℂ) * (wSample ℓ W (-n)
        * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n)))
      = wSample ℓ W (-n) * Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n) := by
    intro n
    have h6 : ((↑ℓ : ℂ))^3 ≠ 0 := pow_ne_zero 3 (by exact_mod_cast ne_of_gt hℓ)
    simp only [Complex.ofReal_inv, Complex.ofReal_pow]
    rw [show (↑ℓ : ℂ)^3 * (wSample ℓ W (-n)
        * (((↑ℓ : ℂ)^3)⁻¹ * Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n)))
        = ((↑ℓ : ℂ)^3 * ((↑ℓ : ℂ)^3)⁻¹)
          * (wSample ℓ W (-n) * Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n)) by ring]
    rw [mul_inv_cancel₀ h6, one_mul]
  calc (ℓ ^ 3 : ℂ) * (∑' n : Fin 3 → ℤ, wSample ℓ W (-n)
        * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n)))
      = ∑' n : Fin 3 → ℤ, (ℓ ^ 3 : ℂ) * (wSample ℓ W (-n)
          * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n))) :=
        tsum_mul_left.symm
    _ = ∑' n : Fin 3 → ℤ, wSample ℓ W (-n) * Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n) :=
        tsum_congr hsummand
    _ = ∑' m : Fin 3 → ℤ, wSample ℓ W m * Submission.BoseGases.kinFT (foldH H) (kappaL ℓ (-m)) := by
        have h := Equiv.tsum_eq (Equiv.neg (Fin 3 → ℤ))
          (fun m : Fin 3 → ℤ => wSample ℓ W m
            * Submission.BoseGases.kinFT (foldH H) (kappaL ℓ (-m)))
        simpa using h
    _ = ∑' m : Fin 3 → ℤ, wSample ℓ W m * hPair ℓ H m :=
        tsum_congr (fun m => by rw [hpair (-m), neg_neg])

/-- **Cauchy–Schwarz on the tail.** -/
lemma tail_cs {ℓ Λ τ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ) {W : E3 → ℝ} {H : E3 → E3 → ℂ}
    (hτ : ∀ T : Finset (Fin 3 → ℤ), (∀ n ∈ T, Λ ≤ ‖kappaL ℓ n‖) →
      (ℓ ^ 3)⁻¹ * ∑ n ∈ T, ‖wSample ℓ W n‖ ^ 2 / ‖kappaL ℓ n‖ ^ 2 ≤ τ)
    {D : ℝ}
    (htail : ∀ T : Finset (Fin 3 → ℤ),
      ∑ n ∈ T, ‖kappaL ℓ n‖ ^ 2 * ‖hPair ℓ H n‖ ^ 2 ≤ ℓ ^ 6 * D)
    {T : Finset (Fin 3 → ℤ)} (hT : ∀ n ∈ T, Λ ≤ ‖kappaL ℓ n‖) :
    ∑ n ∈ T, ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖
      ≤ Real.sqrt (τ * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D) := by
  have hτ0 : 0 ≤ τ := by
    have h := hτ ∅ (by simp)
    rw [Finset.sum_empty, mul_zero] at h
    exact h
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T
    (fun n => ‖wSample ℓ W n‖ / ‖kappaL ℓ n‖) (fun n => ‖kappaL ℓ n‖ * ‖hPair ℓ H n‖)
  have hpt : ∀ n ∈ T, ‖wSample ℓ W n‖ / ‖kappaL ℓ n‖ * (‖kappaL ℓ n‖ * ‖hPair ℓ H n‖)
      = ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖ := by
    intro n hn
    have hne : ‖kappaL ℓ n‖ ≠ 0 := by
      intro h0
      have h1 := hT n hn
      rw [h0] at h1
      exact absurd h1 (by linarith)
    field_simp
  have hu : ∑ n ∈ T, (‖wSample ℓ W n‖ / ‖kappaL ℓ n‖) ^ 2 ≤ τ * ℓ ^ 3 := by
    have h := hτ T hT
    have h3 : ∑ n ∈ T, (‖wSample ℓ W n‖ / ‖kappaL ℓ n‖) ^ 2
        = ∑ n ∈ T, ‖wSample ℓ W n‖ ^ 2 / ‖kappaL ℓ n‖ ^ 2 :=
      Finset.sum_congr rfl (fun n _ => div_pow _ _ 2)
    rw [h3]
    have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
    rw [inv_mul_le_iff₀ hℓ3] at h
    rw [mul_comm (ℓ ^ 3) τ] at h
    exact h
  have hv : ∑ n ∈ T, (‖kappaL ℓ n‖ * ‖hPair ℓ H n‖) ^ 2 ≤ ℓ ^ 6 * D := by
    refine le_trans ?_ (htail T)
    exact le_of_eq (Finset.sum_congr rfl (fun n _ => by rw [mul_pow]))
  have hsq : (∑ n ∈ T, ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖) ^ 2 ≤ (τ * ℓ ^ 3) * (ℓ ^ 6 * D) := by
    have h₁ : ∑ n ∈ T, ‖wSample ℓ W n‖ / ‖kappaL ℓ n‖ * (‖kappaL ℓ n‖ * ‖hPair ℓ H n‖)
        = ∑ n ∈ T, ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖ :=
      Finset.sum_congr rfl (fun n hn => hpt n hn)
    rw [← h₁]
    refine le_trans hcs ?_
    exact mul_le_mul hu hv (Finset.sum_nonneg (fun n _ => sq_nonneg _)) (by positivity)
  have hτℓ : 0 ≤ τ * ℓ ^ 3 := mul_nonneg hτ0 (by positivity)
  calc ∑ n ∈ T, ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖
      ≤ Real.sqrt ((τ * ℓ ^ 3) * (ℓ ^ 6 * D)) := Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt (τ * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D) := Real.sqrt_mul hτℓ _

/-- **The uniform finite-sum bound** for `‖wSample n‖‖hPair n‖`. -/
lemma summand_sum_le {ℓ Λ τ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ) {W : E3 → ℝ} {H : E3 → E3 → ℂ}
    (hτ : ∀ T : Finset (Fin 3 → ℤ), (∀ n ∈ T, Λ ≤ ‖kappaL ℓ n‖) →
      (ℓ ^ 3)⁻¹ * ∑ n ∈ T, ‖wSample ℓ W n‖ ^ 2 / ‖kappaL ℓ n‖ ^ 2 ≤ τ)
    {D : ℝ}
    (htail : ∀ T : Finset (Fin 3 → ℤ),
      ∑ n ∈ T, ‖kappaL ℓ n‖ ^ 2 * ‖hPair ℓ H n‖ ^ 2 ≤ ℓ ^ 6 * D)
    (T : Finset (Fin 3 → ℤ)) :
    ∑ n ∈ T, ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖
      ≤ (∑ n ∈ lowLab ℓ Λ, ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖)
        + Real.sqrt (τ * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun n => ‖kappaL ℓ n‖ < Λ)
    (fun n => ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖)
  rw [← hsplit]
  have hlow : ∑ n ∈ T.filter (fun n => ‖kappaL ℓ n‖ < Λ), ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖
      ≤ ∑ n ∈ lowLab ℓ Λ, ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro n hn
      rw [Finset.mem_filter] at hn
      exact mem_lowLab_of_norm_le hℓ hn.2.le
    · intro i hi _
      positivity
  have hhigh := tail_cs hℓ hΛ hτ htail (T := T.filter (fun n => ¬ ‖kappaL ℓ n‖ < Λ))
    (fun n hn => not_lt.mp (Finset.mem_filter.mp hn).2)
  linarith

/-- The summand family is summable. -/
lemma summable_summand {ℓ Λ τ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ) {W : E3 → ℝ} {H : E3 → E3 → ℂ}
    (hτ : ∀ T : Finset (Fin 3 → ℤ), (∀ n ∈ T, Λ ≤ ‖kappaL ℓ n‖) →
      (ℓ ^ 3)⁻¹ * ∑ n ∈ T, ‖wSample ℓ W n‖ ^ 2 / ‖kappaL ℓ n‖ ^ 2 ≤ τ)
    {D : ℝ}
    (htail : ∀ T : Finset (Fin 3 → ℤ),
      ∑ n ∈ T, ‖kappaL ℓ n‖ ^ 2 * ‖hPair ℓ H n‖ ^ 2 ≤ ℓ ^ 6 * D) :
    Summable (fun n : Fin 3 → ℤ => wSample ℓ W n * hPair ℓ H n) := by
  refine Summable.of_norm (summable_of_sum_le
    (f := fun n : Fin 3 → ℤ => ‖wSample ℓ W n * hPair ℓ H n‖)
    (c := (∑ n ∈ lowLab ℓ Λ, ‖wSample ℓ W n‖ * ‖hPair ℓ H n‖)
      + Real.sqrt (τ * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D))
    (fun n => norm_nonneg _) (fun u => ?_))
  rw [Finset.sum_congr rfl (fun n _ => norm_mul (wSample ℓ W n) (hPair ℓ H n))]
  exact summand_sum_le hℓ hΛ hτ htail u

/-- **The assembly**: the five analytic inputs give the target inequality. -/
theorem kernelTail_final {ℓ Λ τ R : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ)
    {W : E3 → ℝ} (hWi : MeasureTheory.Integrable W)
    (hsupp : ∀ x : E3, R ≤ ‖x‖ → W x = 0)
    (hτ : ∀ S : Finset (Fin 3 → ℤ), (∀ n ∈ S, Λ ≤ ‖kappaL ℓ n‖) →
      (ℓ ^ 3)⁻¹ * ∑ n ∈ S,
          ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ)) (kappaL ℓ n)‖ ^ 2
            / ‖kappaL ℓ n‖ ^ 2 ≤ τ)
    {H : E3 → E3 → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (c : (Fin 3 → ℤ) → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hc1 : ∀ n, ‖kappaL ℓ n‖ < Λ → c n = 1)
    (S : Finset (Fin 3 → ℤ)) (hS : ∀ n, ‖kappaL ℓ n‖ < Λ → n ∈ S)
    (hsumm : Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n)‖))
    (hexp : ∀ z : E3, HasSum (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ *
        Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n)
        * Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
      (latPerC ℓ (foldH H) z))
    (hred : (∫ w, ∫ y, Work.BoseBoxFock.latPer3 ℓ W (w - y) * H w y)
      = (ℓ ^ 3 : ℂ) * ∫ z, ((W z : ℝ) : ℂ) * latPerC ℓ (foldH H) z)
    (hpair : ∀ n : Fin 3 → ℤ,
      Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n) = hPair ℓ H (-n))
    (htail : ∀ T : Finset (Fin 3 → ℤ),
      ∑ n ∈ T, ‖kappaL ℓ n‖ ^ 2 * ‖hPair ℓ H n‖ ^ 2 ≤ ℓ ^ 6 *
        ∫ w, ∫ y, ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
    : ‖(∫ w, ∫ y, Work.BoseBoxFock.latPer3 ℓ W (w - y) * H w y)
        - ∑ n ∈ S, c n * Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
              (kappaL ℓ n)
            * (∫ w, ∫ y, Complex.exp (Complex.I *
                ((inner ℝ (kappaL ℓ n) (w - y) : ℝ) : ℂ)) * H w y)‖
      ≤ 2 * Real.sqrt (τ * ℓ ^ 9 * ∫ w, ∫ y, ∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
  set D : ℝ := ∫ w, ∫ y, ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 with hD
  have hid := kernelTail_identity hℓ hWi hsumm hexp hred hpair
  have hsummSum : Summable (fun n : Fin 3 → ℤ => wSample ℓ W n * hPair ℓ H n) :=
    summable_summand hℓ hΛ hτ htail
  set e : (Fin 3 → ℤ) → ℂ := fun n => 1 - (if n ∈ S then c n else 0) with he
  have he0 : ∀ n : Fin 3 → ℤ, ‖kappaL ℓ n‖ < Λ → e n = 0 := by
    intro n hn
    rw [he]
    simp only
    rw [if_pos (hS n hn), hc1 n hn]
    ring
  have hd_summ : Summable (fun n : Fin 3 → ℤ =>
      (if n ∈ S then c n else 0) * (wSample ℓ W n * hPair ℓ H n)) :=
    summable_of_ne_finset_zero (s := S) (fun n hn => by rw [if_neg hn, zero_mul])
  have he_summ : Summable (fun n : Fin 3 → ℤ => e n * (wSample ℓ W n * hPair ℓ H n)) :=
    (hsummSum.sub hd_summ).congr (fun n => by rw [he]; ring)
  have hdiff : (∑' n : Fin 3 → ℤ, wSample ℓ W n * hPair ℓ H n)
      - ∑ n ∈ S, c n * (wSample ℓ W n * hPair ℓ H n)
      = ∑' n : Fin 3 → ℤ, e n * (wSample ℓ W n * hPair ℓ H n) := by
    have htsumS : (∑' n : Fin 3 → ℤ,
        (if n ∈ S then c n else 0) * (wSample ℓ W n * hPair ℓ H n))
        = ∑ n ∈ S, c n * (wSample ℓ W n * hPair ℓ H n) := by
      rw [tsum_eq_sum (s := S) (fun n hn => by rw [if_neg hn, zero_mul])]
      exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
    rw [← htsumS, ← Summable.tsum_sub hsummSum hd_summ]
    exact tsum_congr (fun n => by rw [he]; ring)
  have hnorm_summ : Summable (fun n : Fin 3 → ℤ =>
      ‖e n * (wSample ℓ W n * hPair ℓ H n)‖) := he_summ.norm
  have hbound_all : ∀ T : Finset (Fin 3 → ℤ),
      ∑ n ∈ T, ‖e n * (wSample ℓ W n * hPair ℓ H n)‖
        ≤ 2 * (Real.sqrt (τ * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D)) := by
    intro T
    have hterm : ∀ n : Fin 3 → ℤ, ‖e n * (wSample ℓ W n * hPair ℓ H n)‖
        ≤ 2 * (‖wSample ℓ W n‖ * ‖hPair ℓ H n‖) := by
      intro n
      rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [he]
      simp only
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_one]
      by_cases hn : n ∈ S
      · rw [if_pos hn]; linarith [hc n]
      · rw [if_neg hn]; simp
    have hzero : ∑ n ∈ T.filter (fun n => ‖kappaL ℓ n‖ < Λ),
        ‖e n * (wSample ℓ W n * hPair ℓ H n)‖ = 0 := by
      refine Finset.sum_eq_zero (fun n hn => ?_)
      rw [Finset.mem_filter] at hn
      rw [he0 n hn.2, zero_mul, norm_zero]
    have hsplit := Finset.sum_filter_add_sum_filter_not T (fun n => ‖kappaL ℓ n‖ < Λ)
      (fun n => ‖e n * (wSample ℓ W n * hPair ℓ H n)‖)
    rw [← hsplit, hzero, zero_add]
    have h2 : ∑ n ∈ T.filter (fun n => ¬ ‖kappaL ℓ n‖ < Λ),
        ‖e n * (wSample ℓ W n * hPair ℓ H n)‖
        ≤ 2 * ∑ n ∈ T.filter (fun n => ¬ ‖kappaL ℓ n‖ < Λ),
            (‖wSample ℓ W n‖ * ‖hPair ℓ H n‖) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun n _ => hterm n)
    refine le_trans h2 (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact tail_cs hℓ hΛ hτ htail (T := T.filter (fun n => ¬ ‖kappaL ℓ n‖ < Λ))
      (fun n hn => not_lt.mp (Finset.mem_filter.mp hn).2)
  have hτ0 : 0 ≤ τ := by
    have h := hτ ∅ (by simp)
    rw [Finset.sum_empty, mul_zero] at h
    exact h
  have hτℓ3 : 0 ≤ τ * ℓ ^ 3 := mul_nonneg hτ0 (by positivity)
  calc ‖(∫ w, ∫ y, Work.BoseBoxFock.latPer3 ℓ W (w - y) * H w y)
        - ∑ n ∈ S, c n * Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
              (kappaL ℓ n)
            * (∫ w, ∫ y, Complex.exp (Complex.I *
                ((inner ℝ (kappaL ℓ n) (w - y) : ℝ) : ℂ)) * H w y)‖
      = ‖(∑' n : Fin 3 → ℤ, wSample ℓ W n * hPair ℓ H n)
          - ∑ n ∈ S, c n * (wSample ℓ W n * hPair ℓ H n)‖ := by
        rw [hid]
        rw [show (∑ n ∈ S, c n * Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
              (kappaL ℓ n)
            * (∫ w, ∫ y, Complex.exp (Complex.I *
                ((inner ℝ (kappaL ℓ n) (w - y) : ℝ) : ℂ)) * H w y))
            = ∑ n ∈ S, c n * (wSample ℓ W n * hPair ℓ H n) from
          Finset.sum_congr rfl (fun n _ => by simp only [wSample, hPair]; ring)]
    _ = ‖∑' n : Fin 3 → ℤ, e n * (wSample ℓ W n * hPair ℓ H n)‖ := by rw [hdiff]
    _ ≤ ∑' n : Fin 3 → ℤ, ‖e n * (wSample ℓ W n * hPair ℓ H n)‖ :=
        norm_tsum_le_tsum_norm hnorm_summ
    _ ≤ 2 * (Real.sqrt (τ * ℓ ^ 3) * Real.sqrt (ℓ ^ 6 * D)) :=
        le_of_tendsto hnorm_summ.hasSum (Filter.Eventually.of_forall hbound_all)
    _ = 2 * Real.sqrt (τ * ℓ ^ 9 * D) := by
        rw [← Real.sqrt_mul hτℓ3, show (τ * ℓ ^ 3) * (ℓ ^ 6 * D) = τ * ℓ ^ 9 * D by ring]
    _ = 2 * Real.sqrt (τ * ℓ ^ 9 * ∫ w, ∫ y, ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
        rw [hD]

/-- A compactly supported continuous complex function has a support radius. -/
lemma exists_support_radius {Φ : E3 → ℂ} (hc : HasCompactSupport Φ) :
    ∃ R : ℝ, ∀ x, R < ‖x‖ → Φ x = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E3)).mp hc.isCompact.isBounded
  refine ⟨R, fun x hx => ?_⟩
  by_contra hne
  have hxt : x ∈ tsupport Φ := subset_tsupport Φ (Function.mem_support.mpr hne)
  have h1 := hR hxt
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  linarith

theorem kernelTail {ℓ Λ τ R : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hsupp : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → W x = 0)
    (hτ : ∀ S : Finset (Fin 3 → ℤ), (∀ n ∈ S, Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖) →
      (ℓ ^ 3)⁻¹ * ∑ n ∈ S,
          ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
              (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2 ≤ τ)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (c : (Fin 3 → ℤ) → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hc1 : ∀ n, ‖Work.BoseBoxFock.kappaL ℓ n‖ < Λ → c n = 1)
    (S : Finset (Fin 3 → ℤ)) (hS : ∀ n, ‖Work.BoseBoxFock.kappaL ℓ n‖ < Λ → n ∈ S) :
    ‖(∫ w, ∫ y, Work.BoseBoxFock.latPer3 ℓ W (w - y) * H w y)
        - ∑ n ∈ S, c n * Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
              (Work.BoseBoxFock.kappaL ℓ n)
            * (∫ w, ∫ y, Complex.exp (Complex.I *
                ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) (w - y) : ℝ) : ℂ)) * H w y)‖
      ≤ 2 * Real.sqrt (τ * ℓ ^ 9 * ∫ w, ∫ y, ∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
  obtain ⟨hΦcont, hΦcpt⟩ := foldH_contDiff hℓ hH hHs
  obtain ⟨C, hC⟩ := hΦcpt.exists_bound_of_continuous hΦcont.continuous
  obtain ⟨R', hR'⟩ := exists_support_radius hΦcpt
  have hsumm : Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT (foldH H) (kappaL ℓ n)‖) :=
    summable_kinFT_kappaL hℓ hΦcont hΦcpt
  refine kernelTail_final hℓ hΛ hWi hsupp hτ hH hHs c hc hc1 S hS hsumm ?_ ?_ ?_ ?_
  · intro z
    exact latPerC_hasSum_fourier hℓ hΦcont hΦcpt hsumm
      (fun n => latPerC_fourierCoeff hℓ hΦcont.continuous.aestronglyMeasurable
        ⟨max C 0, fun x => le_trans (hC x) (le_max_left _ _)⟩ hR' n) z
  · exact latPer3_pairing_eq hℓ hWi hsupp hH hHs
  · exact kinFT_foldH_eq_hPair hℓ hH hHs
  · exact fun T => hPair_tail_sum_le hℓ hH hHs T

end Work.BoseBoxFock.L1Tails
