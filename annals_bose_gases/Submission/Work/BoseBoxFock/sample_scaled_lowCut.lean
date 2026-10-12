import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFix.Defs
import Submission.Work.BoseBoxFock.LatSamplingAux.sampleTransScale
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sample_scaled_lowCut`

The **scaling identity** for the lattice-sampling transform of the low-momentum symbol.

For a real profile `fc.f : ℝ → ℝ` and `K = 2π/ℓ`, the substitution `p = K • x` in the Bochner
integral over `ℝ³` (Lebesgue measure, Jacobian `K⁻³`) turns

    ∫_x f(‖K x‖/κ) e^{i⟪Kx,w⟫} e^{−2πi⟪x,L⟫} dx

into

    K⁻³ ∫_p f(‖p‖/κ) e^{i⟪p, w − ℓ L⟫} dp ,      `L = latVec m` ,

because `K ⟪x,L⟫ = (2π/ℓ)⟪x,L⟫`, so the momentum transfer `w` of the sampling phase is shifted by
`−ℓ•L` once the `2π`-convention phase is written in the frequency variable `p = (2π/ℓ)•x`.  This is
the `z`-part of the corpus's `latSampling_decay` (`sampleTransScale`), taken after the scaling
change of variables, i.e. the identity that lets the periodised (position-space) kernel of the low
cut-off be expanded in the lattice phases `e^{i⟪(2π/ℓ)•latVec m, ·⟫}`.

Both sides are honest Bochner integrals of a bounded integrand with compact support in the momentum
variable (`fc.f` vanishes for argument `≥ 2`), so no integrability side condition is needed: the
change of variables `Measure.integral_comp_smul_of_nonneg` holds unconditionally.
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- **Change of variables `x ↦ c • x`** for a positive scalar `c` on `ℝ³` (Lebesgue measure):
the Jacobian is `(c³)⁻¹`. -/
private lemma integral_comp_smul_scale3 {c : ℝ} (hc : 0 < c) (G : EuclideanSpace ℝ (Fin 3) → ℂ) :
    (∫ x : EuclideanSpace ℝ (Fin 3), G (c • x))
      = (((c ^ 3 : ℝ)) : ℂ)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), G p := by
  rw [Measure.integral_comp_smul_of_nonneg (hR := hc.le) volume G c, finrank_euclideanSpace,
    Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv]

theorem sample_scaled_lowCut (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) (w : EuclideanSpace ℝ (Fin 3)) (m : Fin 3 → ℤ) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ((fc.f (‖(2 * Real.pi / ℓ) • x‖ / κ) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • x) w : ℂ))
        * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (Work.BoseBoxFock.latVec m) : ℂ))))
      = ((((2 * Real.pi / ℓ) ^ 3 : ℝ) : ℂ))⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ p (w - ℓ • Work.BoseBoxFock.latVec m) : ℂ)) := by
  have hc : 0 < 2 * Real.pi / ℓ := by positivity
  -- the change of variables `p = (2π/ℓ) • x`, applied to the momentum-space integrand of the RHS
  have hscale := integral_comp_smul_scale3 (c := 2 * Real.pi / ℓ) hc
      (fun p : EuclideanSpace ℝ (Fin 3) => ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ p (w - ℓ • Work.BoseBoxFock.latVec m) : ℂ)))
  rw [← hscale]
  -- it remains to identify the two integrands pointwise
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  -- `⟪K x, w − ℓ L⟫ = ⟪K x, w⟫ − 2π ⟪x, L⟫` in `ℝ` (`K = 2π/ℓ`, so `ℓ K = 2π`)
  have hinnerR : inner ℝ ((2 * Real.pi / ℓ) • x) (w - ℓ • Work.BoseBoxFock.latVec m)
      = inner ℝ ((2 * Real.pi / ℓ) • x) w
        - 2 * Real.pi * inner ℝ x (Work.BoseBoxFock.latVec m) := by
    simp only [inner_sub_right, real_inner_smul_right, real_inner_smul_left]
    have h : ℓ * (2 * Real.pi / ℓ) = 2 * Real.pi := by field_simp
    have h2 : ℓ * ((2 * Real.pi / ℓ) * inner ℝ x (Work.BoseBoxFock.latVec m))
        = 2 * Real.pi * inner ℝ x (Work.BoseBoxFock.latVec m) := by
      rw [← mul_assoc, h]
    rw [h2]
  have hinner : (inner ℝ ((2 * Real.pi / ℓ) • x) (w - ℓ • Work.BoseBoxFock.latVec m) : ℂ)
      = (inner ℝ ((2 * Real.pi / ℓ) • x) w : ℂ)
        - 2 * (Real.pi : ℂ) * (inner ℝ x (Work.BoseBoxFock.latVec m) : ℂ) := by
    rw [hinnerR]; push_cast; ring
  -- and `e^{i(a−b)} = e^{ia} e^{−2πi b}` for `a = ⟪K x, w⟫`, `b = ⟪x, L⟫`
  rw [hinner]
  have harg : Complex.I * ((inner ℝ ((2 * Real.pi / ℓ) • x) w : ℂ)
        - 2 * (Real.pi : ℂ) * (inner ℝ x (Work.BoseBoxFock.latVec m) : ℂ))
      = Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • x) w : ℂ)
        + -(2 * Real.pi * Complex.I * (inner ℝ x (Work.BoseBoxFock.latVec m) : ℂ)) := by ring
  rw [harg, Complex.exp_add]
  ring

end Work.BoseBoxFock
