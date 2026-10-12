import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxPairMomentum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-276 — D1 step (i) proper: the `Q_B`-projected χ-momentum mode

FS's `lm:appbogolubov` writes the pair term `A₂` in the momentum form

    A₂ = ½(2π)^{-3} ∫_p 𝓑(p)(b_p†b_{−p}† + b_{−p}b_p) dp ,
    b_p† = |B|^{−1/2} a†(Q_B χ_Be^{−ipx}) a_0 ,   𝓑(p) = \widehat{WS₁}(p) ,

and the identification with the corpus's position-space pair word
`q4PairWord = Σ_{i≠j}∫(P_iP_jΦ)(Q_jQ_iΦ)w₁(x_i,x_j)` (whose momentum form is
`SmallBoxPairMomentum.q4PairWord_eq_fourier_integral`) rests on the χ-algebra
cancellation verified numerically in `Submission/Work/numerics/d1c2_identity_N2.py`
(ratio RHS/LHS = 1 to 12 digits for box sides 0.8, 1.0, 1.6, 2.5).

This module introduces the mode

    g_p(y) = Q_B(χ_Be^{−i⟨p,y⟩})(y) = χ_B(y)e^{−i⟨p,y⟩} − |B|^{−1}c_p ,
    c_p = ∫_B χ_Be^{−i⟨p,y⟩}dy ,

as a COMPLEX-valued function (`modeChat` = `c_p`, `qMode` = `g_p`), proves the key
pointwise algebra

    g_p(y)·g_{−p}(z) = χ(y)χ(z)e^{i⟨p,z−y⟩}
        − |B|^{−1}c_p·χ(z)e^{i⟨p,z⟩} − |B|^{−1}c_{−p}·χ(y)e^{−i⟨p,y⟩}
        + |B|^{−2}c_p c_{−p}

and the mean-vanishing `∫_B g_p = 0` — the two facts that make the three correction
terms drop out in the `Q`-sector (`∫_x(Q_iQ_jΦ)(x,y)dx = ∫_y(Q_iQ_jΦ)(x,y)dy = 0`).
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators Convolution

namespace Submission

open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


/-- χ-mean of the momentum mode `χ_B(y)e^{-i⟨p,y⟩}` over the box. -/
noncomputable def modeChat (ℓ : ℝ) (p : ℝ³) : ℂ :=
  ∫ y in acube ℓ, (chiScale ℓ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))

/-- The `Q_B`-projected (`1_B`-mean-free) χ-momentum mode
`g_p(y) = χ_B(y)e^{-i⟨p,y⟩} − |B|^{-1}c_p`. -/
noncomputable def qMode (ℓ : ℝ) (p y : ℝ³) : ℂ :=
  (chiScale ℓ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
    - ((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ p

lemma inner_neg_right' (p y : ℝ³) : inner ℝ (-p) y = - inner ℝ p y := by
  rw [inner_neg_left]

theorem qMode_mul {ℓ : ℝ} (p y z : ℝ³) :
    qMode ℓ p y * qMode ℓ (-p) z
      = (chiScale ℓ y : ℂ) * (chiScale ℓ z : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ p (z - y) : ℝ) : ℂ))
        - ((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ p * (chiScale ℓ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ p z : ℝ) : ℂ))
        - ((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ (-p) * (chiScale ℓ y : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        + ((ℓ ^ 3)⁻¹ : ℂ) * ((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ p * modeChat ℓ (-p) := by
  have hy : Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * Complex.exp (Complex.I * ((inner ℝ p z : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((inner ℝ p (z - y) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_right]
    push_cast
    ring
  have hz : Complex.exp (-(Complex.I * ((inner ℝ (-p) z : ℝ) : ℂ)))
      = Complex.exp (Complex.I * ((inner ℝ p z : ℝ) : ℂ)) := by
    rw [inner_neg_right']
    push_cast
    ring_nf
  simp only [qMode, modeChat]
  rw [hz, hy.symm]
  ring

lemma continuous_qMode {ℓ : ℝ} (p : ℝ³) : Continuous (fun y : ℝ³ => qMode ℓ p y) := by
  have h1 : Continuous (fun y : ℝ³ => (chiScale ℓ y : ℂ)) :=
    Complex.continuous_ofReal.comp (chiScale_continuous ℓ)
  have h2 : Continuous (fun y : ℝ³ => Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) := by
    refine Complex.continuous_exp.comp ?_
    have hinner : Continuous (fun y : ℝ³ => ((inner ℝ p y : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)
    exact (continuous_const.mul hinner).neg
  simp only [qMode]
  exact (h1.mul h2).sub continuous_const

theorem integral_qMode_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) :
    ∫ y in acube ℓ, qMode ℓ p y = 0 := by
  have h1 : ∫ y in acube ℓ, (chiScale ℓ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
      = modeChat ℓ p := rfl
  have _ : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
  have h2 : ∫ y in acube ℓ, ((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ p
      = (ℓ ^ 3 : ℝ) • (((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ p) := by
    rw [MeasureTheory.integral_const, real_volume_acube ℓ hℓ.le]
  have hmode : (fun y : ℝ³ => (chiScale ℓ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))))
      = fun y : ℝ³ => qMode ℓ p y + ((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ p := by
    funext y
    simp only [qMode]
    ring
  have hInt1 : IntegrableOn
      (fun y : ℝ³ => (chiScale ℓ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))))
      (acube ℓ) volume := by
    rw [hmode]
    exact ContinuousOn.integrableOn_compact (acube_compact hℓ)
      (((continuous_qMode p).continuousOn).add continuousOn_const)
  have hInt2 : IntegrableOn (fun y : ℝ³ => ((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ p) (acube ℓ) volume :=
    integrableOn_const (hs := ne_of_lt (acube_lt_top ℓ hℓ.le))
  simp only [qMode]
  rw [MeasureTheory.integral_sub hInt1 hInt2, h1, h2]
  have hcast : (((ℓ ^ 3 : ℝ)) : ℂ) = ((ℓ : ℂ)) ^ 3 := by push_cast; ring
  rw [Algebra.smul_def]
  push_cast
  have hne : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  field_simp
  simp



end BoseGases
end Submission
