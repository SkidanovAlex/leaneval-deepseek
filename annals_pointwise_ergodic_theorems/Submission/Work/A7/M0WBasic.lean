/-
# The differentiated oscillatory weight `m0w` of the sharp `M₀` estimate

The paper's Proposition `mod-approx` compares the discrete average
`E_{n∈[N]} e(α₁n+α₂P(n)) e(ξ₁n+ξ₂P(n)) 1_{n>N/2}` with the product
`m_Ẑ(α₁,α₂) m̃_{N,ℝ}(ξ₁,ξ₂)`.  Its `ξ`-derivatives bring down the factors `2πi n`, `2πi P(n)` in the
sum and `2πi Nt`, `2πi P(Nt)` in the integral (see `Work.KMTAreas.A7.ModelApproxM0Deriv`).

This module introduces the single function

`m0w P ξ₁ ξ₂ j₁ j₂ t = (2πi t)^{j₁} (2πi P(t))^{j₂} e(ξ₁t+ξ₂P(t))`

which is *simultaneously* the weight of the discrete summand `momPhaseDeriv` and of the
integrand of the oscillatory integral `mTildeDeriv`: the two identification lemmas
`momPhaseDeriv_eq_arithW_m0w` and `mTildeDeriv_eq_integral_m0w` below make this precise.  This
reduces the sharp bound

`‖M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂‖ ≤ C q² (1 + S²/N) N^{j₁+dj₂-1}`

to (i) a pointwise bound on `m0w` and its second derivative on `[0,N]`, and (ii) the comparison of
the `q`-periodic arithmetic character `arithW` with its average `mZ` against the integral of `m0w`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxM0Deriv
import Submission.Work.A7.ModelApproxCore_M0_defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.A7

noncomputable section

open MeasureTheory Polynomial Finset Topology
open scoped BigOperators

/-- The polynomial weight `(2πi t)^{j₁}(2πi P(t))^{j₂}` of the differentiated symbol difference. -/
noncomputable def m0poly (P : ℤ[X]) (j₁ j₂ : ℕ) (t : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I * (t : ℂ)) ^ j₁
    * (2 * Real.pi * Complex.I * ((Work.KMTAreas.A7.PevalR P t : ℝ) : ℂ)) ^ j₂

/-- **The differentiated oscillatory weight**: the common weight of the discrete summand
`momPhaseDeriv` and of the integrand of `mTildeDeriv`. -/
noncomputable def m0w (P : ℤ[X]) (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) (t : ℝ) : ℂ :=
  m0poly P j₁ j₂ t * momFun P ξ₁ ξ₂ t

/-- The weight `m0w` is the polynomial part times the oscillatory phase. -/
lemma m0w_eq (P : ℤ[X]) (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) (t : ℝ) :
    m0w P ξ₁ ξ₂ j₁ j₂ t = m0poly P j₁ j₂ t * momFun P ξ₁ ξ₂ t := rfl

/-- **The discrete summand `momPhaseDeriv` is `arithW` times the weight `m0w`.** -/
lemma momPhaseDeriv_eq_arithW_m0w (P : ℤ[X]) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ) (n : ℕ) (j₁ j₂ : ℕ) :
    Work.KMTAreas.A7.momPhaseDeriv P N α₁ α₂ ξ₁ ξ₂ (n : ℤ) j₁ j₂
      = arithW P α₁ α₂ (n : ℤ) * m0w P ξ₁ ξ₂ j₁ j₂ (n : ℝ) := by
  unfold Work.KMTAreas.A7.momPhaseDeriv m0w m0poly
  rw [momPhase_eq]
  simp only [Int.cast_natCast, Complex.ofReal_natCast]
  ring_nf

/-- **The integrand of `mTildeDeriv` is the weight `m0w` at `N t`.** -/
lemma mTildeDeriv_eq_integral_m0w (P : ℤ[X]) (N : ℕ) (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) :
    Work.KMTAreas.A7.mTildeDeriv P N ξ₁ ξ₂ j₁ j₂
      = ∫ t in (1 / 2 : ℝ)..1, m0w P ξ₁ ξ₂ j₁ j₂ ((N : ℝ) * t) := by
  rw [Work.KMTAreas.A7.mTildeDeriv]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [m0w, m0poly, momFun]
  have harg : ξ₁ * (N : ℝ) * t + ξ₂ * Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)
      = ξ₁ * ((N : ℝ) * t) + ξ₂ * Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) := by ring
  rw [harg]
  ring

/-- The real polynomial `P` evaluated at a real point is `C^∞`. -/
lemma contDiff_PevalR (P : ℤ[X]) : ContDiff ℝ ⊤ (fun t : ℝ => Work.KMTAreas.A7.PevalR P t) := by
  have h : (fun t : ℝ => Work.KMTAreas.A7.PevalR P t)
      = fun t : ℝ => (P.map (Int.castRingHom ℝ)).eval t := rfl
  rw [h]
  have h2 : (fun t : ℝ => (P.map (Int.castRingHom ℝ)).eval t)
      = fun t : ℝ => ∑ i ∈ Finset.range ((P.map (Int.castRingHom ℝ)).natDegree + 1),
          (P.map (Int.castRingHom ℝ)).coeff i * t ^ i := by
    funext t; rw [Polynomial.eval_eq_sum_range]
  rw [h2]
  exact ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_id.pow i))

/-- The weight `m0poly` is `C^∞`. -/
lemma contDiff_m0poly (P : ℤ[X]) (j₁ j₂ : ℕ) : ContDiff ℝ ⊤ (m0poly P j₁ j₂) := by
  unfold m0poly
  refine ContDiff.mul ?_ ?_
  · exact (contDiff_const.mul Complex.ofRealCLM.contDiff).pow j₁
  · apply ContDiff.pow
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_PevalR P)))

/-- `m0w` is `C²` (the order needed for the Euler--Maclaurin comparison). -/
lemma contDiff_two_m0w (P : ℤ[X]) (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) : ContDiff ℝ 2 (m0w P ξ₁ ξ₂ j₁ j₂) := by
  unfold m0w
  exact ((contDiff_m0poly P j₁ j₂).of_le le_top).mul (momFun_contDiff P ξ₁ ξ₂)

end

end Work.A7
