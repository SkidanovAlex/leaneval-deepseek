import Submission.Work.BourgainPlan.Maximal.mstMaximal_single
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Commons.Analysis.Maximal.lintegral_rpow_hlMax_le

/-!
# The pointwise Hardy–Littlewood domination of the polynomial-curve maximal function

`mstMS_curve_neg_le_hlMax` bounds the *average of a measurable function along the polynomial curve*
`u ↦ P(2^n u)` by a finite sum of Hardy–Littlewood maximal functions of that function.  Combined
with the curve identity `mstMax_curve` (the inverse Fourier transform of a profile-modulated
amplitude is the average of the inverse Fourier transform of the amplitude along the curve) this
gives the *pointwise* bound

`sup_n ‖F⁻¹(Φ_{2^n}(−·)·W)‖ ≤ K Σ_{c∈T} hlMax ‖F⁻¹ W‖ (· − c)`

which is the mechanism that turns the maximal function of the level model into a Hardy–Littlewood
maximal function — and hence, for every `p > 1`, an `ℓᵖ`-bounded operator, with a constant that is
*uniform in the level* `s`.  This is the first half of `MST_ROUTE.md` §5's `ℓᵖ` level estimate;
the second half (bounding the `Lᵖ(ℝ)` norm of the amplitude `‖F⁻¹ W‖` by the `ℓᵖ` norm of the
coefficient sequence, which is where the narrowness of the bump enters) is
`mstEta_window_lintegral_rpow_le`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- **The pointwise curve/HL domination.**  For every integer polynomial `P` of degree `≥ 2` there
are `K > 0` and a finite set `T ⊆ ℝ` (the critical values of the curve) such that for every `N`,
every integrable amplitude `W` and every `x ∈ ℝ`,
`sup_n ‖F⁻¹(Φ_N(−·)·W)‖(x) ≤ K Σ_{c∈T} hlMax (‖F⁻¹W‖ₑ) (x − c)`.

Proof: `mstMax_curve` writes the left-hand side as the curve average
`∫_{Ioc 0 1} F⁻¹W (x − P(Nu)) du`, the integral is bounded by the `∫⁻` of the modulus, and
`mstMS_curve_neg_le_hlMax` bounds that `∫⁻` by the sum of HL maximal functions. -/
theorem curve_max_le_hlMax (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : Finset ℝ, ∀ (n : ℕ) (W : ℝ → ℂ) (hW : Integrable W) (x : ℝ),
      ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => polyProfile P (2 ^ n) (-ξ) * W ξ) x‖ₑ
        ≤ ENNReal.ofReal K * ∑ c ∈ T,
            Commons.Analysis.Maximal.hlMax (fun z : ℝ => ‖FourierTransformInv.fourierInv W z‖ₑ)
              (x - c) := by
  obtain ⟨K, hK, T, hT⟩ := mstMS_curve_neg_le_hlMax P hd
  refine ⟨K, hK, T, fun n W hW x => ?_⟩
  have hcont : Continuous (FourierTransformInv.fourierInv W) :=
    Commons.Analysis.Fourier.continuous_fourierInv_of_integrable W hW
  have hmeas : Measurable (fun z : ℝ => ‖FourierTransformInv.fourierInv W z‖ₑ) :=
    hcont.enorm.measurable
  rw [show ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => polyProfile P (2 ^ n) (-ξ) * W ξ) x‖ₑ
      = ‖∫ u in (0:ℝ)..1, FourierTransformInv.fourierInv W
          (x - Polynomial.eval (((2 ^ n : ℕ) : ℝ) * u) (Polynomial.map (Int.castRingHom ℝ) P))‖ₑ from by
      rw [Work.Maximal.mstMax_curve P (2 ^ n) W hW x]]
  have h1 : ‖∫ u in (0:ℝ)..1, FourierTransformInv.fourierInv W
        (x - Polynomial.eval (((2 ^ n : ℕ) : ℝ) * u) (Polynomial.map (Int.castRingHom ℝ) P))‖ₑ
      ≤ ∫⁻ u in Set.Ioc (0:ℝ) 1, ‖FourierTransformInv.fourierInv W
        (x - Polynomial.eval (((2 ^ n : ℕ) : ℝ) * u) (Polynomial.map (Int.castRingHom ℝ) P))‖ₑ := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact enorm_integral_le_lintegral_enorm _
  refine le_trans h1 ?_
  have h2 := hT n (fun z : ℝ => ‖FourierTransformInv.fourierInv W z‖ₑ) hmeas x
  have h3 : (∫⁻ u in Set.Ioc (0:ℝ) 1, ‖FourierTransformInv.fourierInv W
        (x - Polynomial.eval (((2 ^ n : ℕ) : ℝ) * u) (Polynomial.map (Int.castRingHom ℝ) P))‖ₑ)
      = ∫⁻ s in Set.Ioc (0:ℝ) 1, (fun z : ℝ => ‖FourierTransformInv.fourierInv W z‖ₑ)
          (x - Polynomial.eval ((2:ℝ)^n * s) (Polynomial.map (Int.castRingHom ℝ) P)) := by
    refine lintegral_congr fun s => ?_
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [h3]
  exact h2

end

end Work.BourgainPlan.Maximal
