import Mathlib.Analysis.Convolution
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The convolution theorem for the `p`-convention Fourier transform `kinFT`

`Submission.BoseGases.kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy` is the Fourier transform of `u` in the
`p`-convention (Mathlib's `𝓕 u ((2π)⁻¹•p)`).  For **integrable** `K, w` the convolution
`z ↦ ∫_y K y · w (z − y) dy` is again integrable and its Fourier transform factorises:

  `kinFT (K ⋆ w) p = kinFT K p · kinFT w p`.

This is the classical `L¹` convolution theorem.  The proof below is the direct Fubini
computation (no Schwartz / density argument):

* `∫_z φ_p(z) ∫_y K y w(z−y) = ∫_z ∫_y φ_p(z) K y w(z−y)`  (pull the phase inside; this is
  `integral_const_mul` and needs no integrability);
* Fubini (`integral_integral_swap`) — here integrability of the joint integrand is exactly
  Mathlib's `Integrable.convolution_integrand`;
* the phase factorises as `φ_p(z) = φ_p(y) · φ_p(z−y)` (`inner_add_right`), so the inner integral
  over `z` is a translate of `∫_t φ_p(t)w(t)`: translation invariance of Lebesgue measure
  (`integral_sub_right_eq_self`).
-/

namespace Work.BoseBoxFock.FRK

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The phase of the `p`-convention Fourier transform at frequency `p`. -/
private noncomputable def ph (p : E3) (z : E3) : ℂ :=
  Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))

/-- The phase has modulus one. -/
private lemma norm_ph (p z : E3) : ‖ph p z‖ = 1 := by
  simp only [ph]
  have h : -(Complex.I * (inner ℝ p z : ℂ)) = ((-(inner ℝ p z) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The phase is multiplicative in the vector variable. -/
private lemma ph_add (p y z : E3) : ph p y * ph p (z - y) = ph p z := by
  simp only [ph]
  rw [← Complex.exp_add]
  congr 1
  have h' : inner ℝ p y + inner ℝ p (z - y) = inner ℝ p z := by
    rw [← inner_add_right]
    congr 1
    abel
  have h : (inner ℝ p y : ℂ) + (inner ℝ p (z - y) : ℂ) = (inner ℝ p z : ℂ) := by
    exact_mod_cast h'
  rw [← h]
  ring

theorem kinFT_conv_mul {K w : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hK : MeasureTheory.Integrable K) (hw : MeasureTheory.Integrable w)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z => MeasureTheory.integral MeasureTheory.volume
        (fun y : EuclideanSpace ℝ (Fin 3) => K y * w (z - y))) p
      = Submission.BoseGases.kinFT K p * Submission.BoseGases.kinFT w p := by
  have hcont : Continuous (fun z : E3 => ph p z) := by
    simp only [ph]
    fun_prop
  -- integrability of the joint integrand `(z,y) ↦ K y w (z−y)`: Mathlib's convolution API
  have hc : Integrable (fun q : E3 × E3 => K q.2 * w (q.1 - q.2)) (volume.prod volume) :=
    Integrable.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℂ) hK hw
  -- the same with the phase inserted (the phase has modulus one: `Integrable.bdd_mul`)
  have hjoint : Integrable (fun q : E3 × E3 => ph p q.1 * (K q.2 * w (q.1 - q.2)))
      (volume.prod volume) :=
    Integrable.bdd_mul hc (hcont.comp continuous_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => le_of_eq (norm_ph p q.1))
  -- `Function.uncurry` does not reduce definitionally, so record the identification explicitly
  have huncurry : Function.uncurry (fun z y : E3 => ph p z * (K y * w (z - y)))
      = fun q : E3 × E3 => ph p q.1 * (K q.2 * w (q.1 - q.2)) := by
    funext q
    exact Function.uncurry_apply_pair _ q.1 q.2
  -- step 1: pull the phase inside the inner integral
  have hstep1 : ∀ z : E3, ph p z * (∫ y, K y * w (z - y))
      = ∫ y, ph p z * (K y * w (z - y)) := by
    intro z
    exact (integral_const_mul (ph p z) (fun y : E3 => K y * w (z - y))).symm
  -- step 2: the inner integral over `z` is a translate of `∫_t ph p t w t`
  have hstep2 : ∀ y : E3, (∫ z, ph p z * (K y * w (z - y)))
      = K y * (ph p y * ∫ t, ph p t * w t) := by
    intro y
    calc (∫ z, ph p z * (K y * w (z - y)))
        = ∫ z, K y * (ph p z * w (z - y)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      _ = K y * ∫ z, ph p z * w (z - y) := integral_const_mul _ _
      _ = K y * ∫ z, ph p y * (ph p (z - y) * w (z - y)) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with z
          show ph p z * w (z - y) = ph p y * (ph p (z - y) * w (z - y))
          rw [← mul_assoc, ← ph_add p y z]
      _ = K y * (ph p y * ∫ z, ph p (z - y) * w (z - y)) := by
          rw [integral_const_mul]
      _ = K y * (ph p y * ∫ t, ph p t * w t) := by
          rw [integral_sub_right_eq_self (fun t : E3 => ph p t * w t) y]
  -- step 3: separate the two one-variable integrals
  have hstep3 : (∫ y, K y * (ph p y * ∫ t, ph p t * w t))
      = (∫ y, K y * ph p y) * (∫ t, ph p t * w t) := by
    rw [show (∫ y, K y * (ph p y * ∫ t, ph p t * w t))
        = ∫ y, (K y * ph p y) * (∫ t, ph p t * w t) from
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)]
    rw [integral_mul_const]
  have hstep4 : (∫ y, K y * ph p y) = Submission.BoseGases.kinFT K p := by
    simp only [Submission.BoseGases.kinFT, ph]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  have hstep5 : (∫ t, ph p t * w t) = Submission.BoseGases.kinFT w p := by
    simp only [Submission.BoseGases.kinFT, ph]
  calc Submission.BoseGases.kinFT (fun z => ∫ y, K y * w (z - y)) p
      = ∫ z, ph p z * (∫ y, K y * w (z - y)) := by
          simp only [Submission.BoseGases.kinFT, ph]
    _ = ∫ z, ∫ y, ph p z * (K y * w (z - y)) :=
          integral_congr_ae (Filter.Eventually.of_forall hstep1)
    _ = ∫ y, ∫ z, ph p z * (K y * w (z - y)) :=
          integral_integral_swap (by rw [huncurry]; exact hjoint)
    _ = ∫ y, K y * (ph p y * ∫ t, ph p t * w t) :=
          integral_congr_ae (Filter.Eventually.of_forall hstep2)
    _ = (∫ y, K y * ph p y) * (∫ t, ph p t * w t) := hstep3
    _ = Submission.BoseGases.kinFT K p * Submission.BoseGases.kinFT w p := by
          rw [hstep4, hstep5]

end Work.BoseBoxFock.FRK
