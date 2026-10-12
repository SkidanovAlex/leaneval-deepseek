import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Analysis.BoseBand.MomWordOffdiag.continuous_kFT_boxState_fibre`

Continuity, in the configuration variable `x : X n`, of the fibre-localised `p`-Fourier
transform

`x ↦ kinFT (boxState ℓ 0 (fibre n j A x)) p`

for a continuous `A : X n → ℝ` and a positive localisation scale `ℓ > 0`.

The state `boxState ℓ 0 ψ = 1_{Λ(0)}·(Q_0ψ)` is supported in the (compact) centre cube
`acube ℓ = Λ(0)`, so `kinFT (boxState ℓ 0 ψ) p` is an integral over the *compact* cube
`acube ℓ` of the jointly continuous integrand

`(x,y) ↦ e^{−i⟪p,y⟫}·(A(x with xⱼ = y) − (ℓ³)⁻¹∫_{acube ℓ} A(x with xⱼ = z) dz)`.

Continuity then follows from the parametric-integral theorem
`MeasureTheory.continuous_parametric_integral_of_continuous`: the fibre insertion
`(x,y) ↦ Function.update x j y` is continuous, `A` is continuous, and the box mean — itself
a parametric integral over the compact cube — is continuous.

## Contents

* `Work.Analysis.BoseBand.MomWordOffdiag.continuous_update_pair` — joint continuity of the
  fibre insertion `(x,y) ↦ Function.update x j y`;
* `kFT_boxState_fibre_eq_integral` / `_eq_integral'` — the identification of the transform
  with the integral over `acube ℓ` (the two forms differ only by the `fibre` unfolding);
* `continuous_kFT_boxState_fibre` — the target.
-/

namespace Work.Analysis.BoseBand.MomWordOffdiag

noncomputable section

open MeasureTheory Filter

/-- The fibre insertion `(x, y) ↦ Function.update x j y` is jointly continuous on
`X n × ℝ³` (coordinatewise: the `j`-th coordinate is the second projection, every other
coordinate is the corresponding coordinate of the first projection). -/
theorem continuous_update_pair {n : ℕ} (j : Fin n) :
    Continuous (fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      Function.update q.1 j q.2) := by
  rw [continuous_pi_iff]
  intro i
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self]
    exact continuous_snd
  · have h : (fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
        (Function.update q.1 j q.2) i) = fun q => q.1 i := by
      funext q; exact Function.update_of_ne hij q.2 q.1
    rw [h]; exact (continuous_apply i).comp continuous_fst

/-- **The `p`-transform of the localised mean-free fibre state is the box integral of the
mean-free fibre.**  Since `boxState ℓ 0 (fibre n j A x) = 1_{Λ(0)}·(Q_0 (fibre n j A x))`
and `Λ(0) = acube ℓ`, the transform

`kinFT (boxState ℓ 0 (fibre n j A x)) p = ∫_y e^{−i⟪p,y⟫}·1_{Λ(0)}(y)·(Q_0(fibre)(y))`

equals the integral over `acube ℓ` of `e^{−i⟪p,y⟫}` times the mean-free fibre. -/
theorem kFT_boxState_fibre_eq_integral {ℓ : ℝ} {n : ℕ} (j : Fin n)
    {A : Submission.BoseGases.X n → ℝ} (x : Submission.BoseGases.X n)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
        (Work.BoseKinLoc.fibre n j A x)) p
    = ∫ y in Submission.BoseGases.acube ℓ,
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
          * ((Work.BoseKinLoc.fibre n j A x y
              - (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ,
                  Work.BoseKinLoc.fibre n j A x z : ℝ) : ℂ) := by
  have hLam : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
    ext y; simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
  have hmean : Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.fibre n j A x)
      = (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ,
          Work.BoseKinLoc.fibre n j A x z := by
    simp [Work.BSKinetic.bsMean]
  rw [Submission.BoseGases.kinFT]
  have key : ∀ y : EuclideanSpace ℝ (Fin 3),
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
        * (Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j A x) y)
      = (Submission.BoseGases.acube ℓ).indicator
          (fun y => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
            * (((Work.BoseKinLoc.fibre n j A x y
                - (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ,
                    Work.BoseKinLoc.fibre n j A x z) : ℝ) : ℂ)) y := by
    intro y
    rw [Work.BoseKinLoc.Kinetic.boxState, Work.BoseKinLoc.indU, hLam, Work.BoseKinLoc.Qfree,
      Work.BSKinetic.bsQ, hmean]
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      simp
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      simp
  rw [show (∫ y : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
        * (Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j A x) y))
      = ∫ y : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.acube ℓ).indicator
          (fun y => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
            * (((Work.BoseKinLoc.fibre n j A x y
                - (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ,
                    Work.BoseKinLoc.fibre n j A x z) : ℝ) : ℂ)) y from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key)]
  exact MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)

/-- The same identity with the fibre `fibre n j A x` unfolded into the insertion
`y ↦ A (Function.update x j y)` — the form used for the parametric-integral argument. -/
theorem kFT_boxState_fibre_eq_integral' {ℓ : ℝ} {n : ℕ} (j : Fin n)
    {A : Submission.BoseGases.X n → ℝ} (x : Submission.BoseGases.X n)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
        (Work.BoseKinLoc.fibre n j A x)) p
    = ∫ y in Submission.BoseGases.acube ℓ,
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
          * ((A (Function.update x j y)
              - (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ,
                  A (Function.update x j z) : ℝ) : ℂ) := by
  simpa only [Work.BoseKinLoc.fibre] using kFT_boxState_fibre_eq_integral (ℓ := ℓ) j x p

theorem continuous_kFT_boxState_fibre {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {A : Submission.BoseGases.X n → ℝ} (hA : Continuous A) (p : EuclideanSpace ℝ (Fin 3)) :
    Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
        (Work.BoseKinLoc.fibre n j A x)) p) := by
  have hupd := continuous_update_pair (n := n) j
  have hK : Continuous (fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      A (Function.update q.1 j q.2)) := hA.comp hupd
  have hmean : Continuous (fun x : Submission.BoseGases.X n =>
      (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, A (Function.update x j z)) :=
    (continuous_parametric_integral_of_continuous (μ := volume) hK
      (Submission.BoseGases.acube_compact hℓ)).const_mul ((ℓ ^ 3)⁻¹)
  have hf : Continuous (fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * ((inner ℝ p q.2 : ℝ) : ℂ))) *
        (((A (Function.update q.1 j q.2)
            - (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ,
                A (Function.update q.1 j z) : ℝ) : ℂ))) := by
    have h1 : Continuous (fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * ((inner ℝ p q.2 : ℝ) : ℂ)))) :=
      Complex.continuous_exp.comp ((continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.inner continuous_snd))).neg)
    have h2 : Continuous (fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
        (((A (Function.update q.1 j q.2)
            - (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ,
                A (Function.update q.1 j z) : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.comp (hK.sub (hmean.comp continuous_fst))
    exact h1.mul h2
  have hmain : Continuous (Function.uncurry (fun x : Submission.BoseGases.X n =>
      fun y : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
          (((A (Function.update x j y)
              - (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ,
                  A (Function.update x j z) : ℝ) : ℂ)))) := hf
  have hint := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun x : Submission.BoseGases.X n => fun y : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
          (((A (Function.update x j y)
              - (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ,
                  A (Function.update x j z) : ℝ) : ℂ)))
    hmain (Submission.BoseGases.acube_compact hℓ)
  exact hint.congr (fun x => (kFT_boxState_fibre_eq_integral' (ℓ := ℓ) j x p).symm)

end

end Work.Analysis.BoseBand.MomWordOffdiag
