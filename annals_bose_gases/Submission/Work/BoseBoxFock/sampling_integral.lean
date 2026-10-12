import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.KinRowQuant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sampling_integral`

Term-by-term integration of a `p`-Fourier series against an integrable `g`:

    ∫ s, g s * (∑' m, c m e^{-i⟪p_m,s⟫}) = ∑' m, c m ∫ s, g s e^{-i⟪p_m,s⟫} ,

for `∑' m ‖c m‖ < ∞` (so that `∫ s ‖g s * c m e^{-i⟪p_m,s⟫}‖ = ‖c m‖ ∫ s ‖g s‖` is a
summable family of integrals, which is exactly the hypothesis of
`MeasureTheory.integral_tsum_of_summable_integral_norm`).

The target identity follows by specialising to `p m = kmomInt ℓ m` and identifying each
term with `Submission.BoseGases.kinFT g (kmomInt ℓ m)` — the `p`-convention Fourier
transform of the corpus (`kinFT u p = ∫ y, e^{−i⟪p,y⟫}u y`).
-/

namespace Work.BoseBoxFock

/-- The `p`-phase factor `e^{-i⟪p,s⟫}` has modulus one. -/
lemma sampling_norm_exp_neg_inner (p s : ℝ³) :
    ‖Complex.exp (-(Complex.I * (inner ℝ p s : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (inner ℝ p s : ℂ)) = ((-(inner ℝ p s) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I (-(inner ℝ p s))

/-- `Submission.BoseGases.kinFT` in the position-space form appearing in the target:
`kinFT g p = ∫ s, g s * e^{-i⟪p,s⟫}` (the definition writes the phase on the left). -/
lemma sampling_kinFT_eq_integral (g : ℝ³ → ℂ) (p : ℝ³) :
    Submission.BoseGases.kinFT g p
      = ∫ s, g s * Complex.exp (-(Complex.I * (inner ℝ p s : ℂ))) := by
  show (∫ s, Complex.exp (-(Complex.I * (inner ℝ p s : ℂ))) * g s)
      = ∫ s, g s * Complex.exp (-(Complex.I * (inner ℝ p s : ℂ)))
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => mul_comm _ _)

/-- **Term-by-term integration of a `p`-Fourier series.**  For summable coefficients
`∑' m ‖c m‖ < ∞` and an integrable `g`, the integral of the series `∑' m, c m e^{-i⟪p_m,·⟫}`
weighted by `g` is the series of the weighted integrals.  All `p`-phases have modulus one,
whence the dominating family `‖c m‖ * ∫ s, ‖g s‖` is summable. -/
lemma sampling_integral_tsum {ι : Type*} [Countable ι] {c : ι → ℂ}
    (hc : Summable fun m => ‖c m‖) {p : ι → ℝ³} {g : ℝ³ → ℂ}
    (hg : MeasureTheory.Integrable g) :
    (∫ s, g s * (∑' m, c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ)))))
      = ∑' m, c m * (∫ s, g s * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ)))) := by
  -- continuity (hence a.e. strong measurability) of the individual phases
  have hcont : ∀ m : ι, Continuous (fun s : ℝ³ =>
      c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ)))) := by
    intro m
    have hpair : Continuous fun s : ℝ³ => (p m, s) :=
      continuous_const.prodMk continuous_id
    have hin : Continuous fun s : ℝ³ => ((inner ℝ (p m) s : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_inner.comp hpair)
    exact continuous_const.mul
      (Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul hin)))
  -- integrability of the individual terms
  have hFint : ∀ m : ι, MeasureTheory.Integrable (fun s : ℝ³ =>
      g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ))))) := by
    intro m
    refine MeasureTheory.Integrable.mono' (hg.norm.const_mul ‖c m‖) ?_ ?_
    · exact hg.1.mul (hcont m).aestronglyMeasurable
    · filter_upwards with s
      have hnorm : ‖g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ))))‖
          = ‖c m‖ * ‖g s‖ := by
        rw [norm_mul, norm_mul, sampling_norm_exp_neg_inner, mul_one, mul_comm]
      exact le_of_eq hnorm
  -- the integrals of the norms are the summable family `m ↦ ‖c m‖ * ∫ ‖g‖`
  have hInt : ∀ m : ι,
      (∫ s, ‖g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ))))‖)
        = ‖c m‖ * ∫ s, ‖g s‖ := by
    intro m
    rw [show (fun s : ℝ³ =>
          ‖g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ))))‖)
        = fun s : ℝ³ => ‖c m‖ * ‖g s‖ from funext fun s => by
          rw [norm_mul, norm_mul, sampling_norm_exp_neg_inner, mul_one, mul_comm]]
    rw [MeasureTheory.integral_const_mul]
  have hsum : Summable fun m : ι =>
      ∫ s, ‖g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ))))‖ := by
    rw [show (fun m : ι =>
          ∫ s, ‖g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ))))‖)
        = fun m : ι => ‖c m‖ * ∫ s, ‖g s‖ from funext hInt]
    exact Summable.mul_right (∫ s, ‖g s‖) hc
  -- the interchange, in the `∑' ∘ ∫` order
  have hmain : (∫ s, ∑' m : ι, g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ)))))
      = ∑' m : ι, ∫ s, g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ)))) :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm
      (F := fun m s => g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ)))))
      hFint hsum).symm
  -- `g s` is pulled out of the (unconditionally summable) series
  have h1 : (∫ s, g s * (∑' m : ι, c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ)))))
      = ∫ s, ∑' m : ι, g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ)))) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    exact (tsum_mul_left (a := g s)
      (f := fun m : ι => c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ))))).symm
  rw [h1, hmain]
  refine tsum_congr fun m => ?_
  rw [show (fun s : ℝ³ => g s * (c m * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ)))))
      = fun s : ℝ³ => c m * (g s * Complex.exp (-(Complex.I * (inner ℝ (p m) s : ℂ)))) from
        funext fun s => by ring]
  rw [MeasureTheory.integral_const_mul]

theorem sampling_integral {ℓ : ℝ} {c : (Fin 3 → ℤ) → ℂ} (hc : Summable fun m => ‖c m‖)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : MeasureTheory.Integrable g) :
    (∫ s, g s * (∑' m : Fin 3 → ℤ, c m
        * Complex.exp (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) s : ℂ)))))
      = ∑' m : Fin 3 → ℤ, c m * Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ m) := by
  have key := sampling_integral_tsum (ι := Fin 3 → ℤ) (c := c) (p := kmomInt ℓ) hc hg
  rw [key]
  refine tsum_congr fun m => ?_
  rw [sampling_kinFT_eq_integral]

end Work.BoseBoxFock
