import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc
import Submission.Work.BourgainPlan.IonescuWainger.discFourier_mul_eq_circConv

/-!
# The Fourier transform turns products into convolutions, for `ℓ¹` data

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4 —
the step *"from inspecting the Fourier transform, it suffices to show …"* (see `FreqArc.lean`).

For a finitely supported `h : ℤ → ℂ` the identity `𝓕(h·k) = 𝓕h ✻ 𝓕k` is a finite computation
(`discFourier_mul_eq_circConv`).  The band-limited setting of the Ionescu–Wainger theorem needs the
same identity for data in `ℓ¹(ℤ)`, where both sides are *infinite* sums / integrals.  This file
proves that extension:

* `DiscFourierL1.continuous_discFourier`, `DiscFourierL1.norm_discFourier_le`: for `h ∈ ℓ¹(ℤ)` the
  discrete Fourier transform `𝓕h ξ = Σ'_n h n · e^{2πi n ξ}` is an absolutely and uniformly
  convergent series, hence a continuous function with `‖𝓕h‖_∞ ≤ ‖h‖_{ℓ¹}`;
* `DiscFourierL1.integral_norm_le_const`: an elementary bound on the Haar integral of the modulus;
* **`discFourier_mul_eq_circConv_l1`** — for `f, k ∈ ℓ¹(ℤ)` and every `ξ : 𝕋`,

`𝓕(f·k) ξ = (𝓕f ✻ 𝓕k) ξ = ∫_𝕋 𝓕f η · 𝓕k (ξ − η) dη`.

The computation is the standard one, carried out with two exchanges of a `tsum` against the Haar
integral (`MeasureTheory.integral_tsum_of_summable_integral_norm`, whose side conditions are the
summability of the `ℓ¹` tails) and the orthonormality `∫_𝕋 e^{2πi n η} e^{2πi m (ξ−η)} dη
= δ_{n,m} e^{2πi n ξ}` of the characters (`DiscFourierMul.integral_fourier_mul_fourier_sub`). -/

open MeasureTheory Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

namespace DiscFourierL1

/-- `‖e^{2πi n ξ}‖ = 1` for the Fourier monomials on the circle `𝕋 = ℝ/ℤ`. -/
lemma fourier_norm_apply (n : ℤ) (ξ : Circle) : ‖fourier n ξ‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- **The discrete Fourier transform of an `ℓ¹(ℤ)` sequence is continuous.**  The defining series
converges absolutely and uniformly (Weierstrass `M`-test with majorant `n ↦ ‖h n‖`), hence the
uniform limit of the continuous finite partial sums. -/
lemma continuous_discFourier {h : ℤ → ℂ} (hh : Summable fun n => ‖h n‖) :
    Continuous (discFourier h) := by
  show Continuous fun x : Circle => ∑' n : ℤ, h n * fourier n x
  refine continuous_tsum (u := fun n : ℤ => ‖h n‖) (fun n => ?_) hh (fun n x => ?_)
  · exact continuous_const.mul (map_continuous (fourier n))
  · rw [norm_mul, fourier_norm_apply, mul_one]

/-- **The transform of an `ℓ¹(ℤ)` sequence is bounded by its `ℓ¹` norm.** -/
lemma norm_discFourier_le {h : ℤ → ℂ} (hh : Summable fun n => ‖h n‖) (x : Circle) :
    ‖discFourier h x‖ ≤ ∑' n : ℤ, ‖h n‖ := by
  have hs : Summable fun n : ℤ => ‖h n * fourier n x‖ := by
    simpa [norm_mul, fourier_norm_apply, Circle.norm_coe, fourier_apply] using hh
  calc ‖discFourier h x‖ = ‖∑' n : ℤ, h n * fourier n x‖ := rfl
    _ ≤ ∑' n : ℤ, ‖h n * fourier n x‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' n : ℤ, ‖h n‖ := tsum_congr fun n => by rw [norm_mul, fourier_norm_apply, mul_one]

/-- A continuous function on the compact circle is Haar integrable. -/
lemma integrable_of_continuous {F : Circle → ℂ} (hF : Continuous F) :
    Integrable F AddCircle.haarAddCircle :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

/-- The Haar integral of the modulus of a continuous function bounded by the constant `C` is at
most `C` (the Haar measure of the circle is a probability measure). -/
lemma integral_norm_le_const {F : Circle → ℂ} (C : ℝ) (hF : Continuous F)
    (h : ∀ η, ‖F η‖ ≤ C) :
    ∫ η, ‖F η‖ ∂AddCircle.haarAddCircle ≤ C := by
  have hi1 : Integrable (fun η : Circle => ‖F η‖) AddCircle.haarAddCircle :=
    (hF.norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun _ : Circle => C) AddCircle.haarAddCircle := integrable_const C
  calc ∫ η, ‖F η‖ ∂AddCircle.haarAddCircle ≤ ∫ η, C ∂AddCircle.haarAddCircle :=
        integral_mono hi1 hi2 h
    _ = C := by simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def]

end DiscFourierL1

open DiscFourierL1 in
/-- **The Fourier transform turns pointwise products into convolutions** (`ℓ¹` case).  For
absolutely summable `f, k : ℤ → ℂ` and every `ξ : 𝕋 = ℝ/ℤ`,

`𝓕(f · k) ξ = (𝓕f ✻ 𝓕k) ξ = ∫_𝕋 𝓕f η · 𝓕k (ξ − η) dη`,

where `discFourier f ξ = ∑'_n f n · e^{2πi n ξ}` and the convolution is `circConv` of `FreqArc.lean`
with respect to the probability Haar measure `AddCircle.haarAddCircle`.

Expanding both series and using `e^{2πi n η} e^{2πi m (ξ−η)} = e^{2πi m ξ} e^{2πi (n−m) η}` together
with the orthonormality of the characters leaves `Σ_n f n · k n · e^{2πi n ξ} = 𝓕(f·k) ξ`.  The two
exchanges of the series against the integral are dominated by the `ℓ¹` tails, so the side conditions
of `MeasureTheory.integral_tsum_of_summable_integral_norm` reduce to the summability of
`n ↦ ‖f n‖ · ‖k‖_{ℓ¹}` (outer) and `m ↦ ‖f‖_{ℓ¹} · ‖k m‖` (inner). -/
theorem discFourier_mul_eq_circConv_l1 {f k : ℤ → ℂ} (hf : Summable fun n => ‖f n‖)
    (hk : Summable fun n => ‖k n‖) (ξ : Circle) :
    discFourier (fun m => f m * k m) ξ = circConv (discFourier f) (discFourier k) ξ := by
  classical
  have hcontK : Continuous (discFourier k) := continuous_discFourier hk
  have hKbd : ∀ ζ : Circle, ‖discFourier k ζ‖ ≤ ∑' n : ℤ, ‖k n‖ :=
    fun ζ => norm_discFourier_le hk ζ
  have key : circConv (discFourier f) (discFourier k) ξ = ∑' n : ℤ, f n * k n * fourier n ξ := by
    rw [circConv]
    -- expand the transform of `f` inside the integral
    have h1 : ∀ η : Circle, discFourier f η * discFourier k (ξ - η)
        = ∑' n : ℤ, (f n * fourier n η) * discFourier k (ξ - η) := by
      intro η
      show (∑' n : ℤ, f n * fourier n η) * discFourier k (ξ - η) = _
      exact tsum_mul_right.symm
    simp only [h1]
    -- exchange the outer series with the integral
    have hFint : ∀ n : ℤ, Integrable
        (fun η : Circle => (f n * fourier n η) * discFourier k (ξ - η))
        AddCircle.haarAddCircle := by
      intro n
      refine (Continuous.mul ?_ ?_).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
      · exact continuous_const.mul (map_continuous (fourier n))
      · exact hcontK.comp (continuous_const.sub continuous_id)
    have hFsum : Summable fun n : ℤ =>
        ∫ η, ‖(f n * fourier n η) * discFourier k (ξ - η)‖ ∂AddCircle.haarAddCircle := by
      refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun η => norm_nonneg _)
        (fun n => ?_) (hf.mul_right (∑' m : ℤ, ‖k m‖))
      refine integral_norm_le_const (‖f n‖ * ∑' m : ℤ, ‖k m‖) ?_ ?_
      · exact Continuous.mul (continuous_const.mul (map_continuous (fourier n)))
          (hcontK.comp (continuous_const.sub continuous_id))
      · intro η
        rw [norm_mul, norm_mul, fourier_norm_apply, mul_one]
        exact mul_le_mul_of_nonneg_left (hKbd (ξ - η)) (norm_nonneg _)
    rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
      (F := fun n η => (f n * fourier n η) * discFourier k (ξ - η)) hFint hFsum]
    refine tsum_congr fun n => ?_
    -- expand the transform of `k` inside the inner integral
    have h2 : ∀ η : Circle, (f n * fourier n η) * discFourier k (ξ - η)
        = ∑' m : ℤ, (f n * fourier n η) * (k m * fourier m (ξ - η)) := by
      intro η
      show (f n * fourier n η) * (∑' m : ℤ, k m * fourier m (ξ - η)) = _
      exact tsum_mul_left.symm
    have hGint : ∀ m : ℤ, Integrable
        (fun η : Circle => (f n * fourier n η) * (k m * fourier m (ξ - η)))
        AddCircle.haarAddCircle := by
      intro m
      refine (Continuous.mul ?_ ?_).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
      · exact continuous_const.mul (map_continuous (fourier n))
      · exact (continuous_const.mul (map_continuous (fourier m))).comp
          (continuous_const.sub continuous_id)
    have hGsum : Summable fun m : ℤ =>
        ∫ η, ‖(f n * fourier n η) * (k m * fourier m (ξ - η))‖ ∂AddCircle.haarAddCircle := by
      refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun η => norm_nonneg _)
        (fun m => ?_) (hk.mul_left ‖f n‖)
      refine integral_norm_le_const (‖f n‖ * ‖k m‖) ?_ ?_
      · exact Continuous.mul (continuous_const.mul (map_continuous (fourier n)))
          ((continuous_const.mul (map_continuous (fourier m))).comp
            (continuous_const.sub continuous_id))
      · intro η
        rw [norm_mul, norm_mul, norm_mul, fourier_norm_apply, fourier_norm_apply, mul_one, mul_one]
    rw [show (fun η : Circle => (f n * fourier n η) * discFourier k (ξ - η))
        = fun η => ∑' m : ℤ, (f n * fourier n η) * (k m * fourier m (ξ - η)) from funext h2]
    rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
      (F := fun m η => (f n * fourier n η) * (k m * fourier m (ξ - η))) hGint hGsum]
    -- evaluate each term by orthonormality of the characters
    have hInt : ∀ m : ℤ, ∫ η, (f n * fourier n η) * (k m * fourier m (ξ - η))
        ∂AddCircle.haarAddCircle = f n * k m * (if n = m then fourier n ξ else 0) := by
      intro m
      rw [show (fun η : Circle => (f n * fourier n η) * (k m * fourier m (ξ - η)))
          = fun η => (f n * k m) * (fourier n η * fourier m (ξ - η)) from
            funext fun η => by ring]
      rw [MeasureTheory.integral_const_mul, DiscFourierMul.integral_fourier_mul_fourier_sub]
    -- only the diagonal term survives
    calc ∑' m : ℤ, ∫ η, (f n * fourier n η) * (k m * fourier m (ξ - η))
            ∂AddCircle.haarAddCircle
        = ∑' m : ℤ, f n * k m * (if n = m then fourier n ξ else 0) := tsum_congr hInt
      _ = f n * k n * fourier n ξ := by
          rw [tsum_eq_single n]
          · simp
          · intro m hm
            rw [if_neg (fun h : n = m => hm h.symm), mul_zero]
  rw [key]
  rfl

end Work.BourgainPlan.IonescuWainger
