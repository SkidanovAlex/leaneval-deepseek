import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxD1Defs
import Submission.Work.BoseFixB1.boxOpG_adjoint_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxTauPairingDefs` — the *smooth* (indicator-free) windowed modes

The "genuine" box modes of `BoxTauGen.lean` carry the box indicator,

`boxWinModeReGen volA A χ p z = 1_A(z)·(χ z cos⟪p,z⟫ − volA⁻¹∫_A χ·cos⟪p,·⟫)`,

so they are discontinuous across `∂A`.  But every operator of the pairing chain uses the mode
only through the product `1_A(x_i)·g(x_i)`, and `1_A(x_i)·1_A(x_i) = 1_A(x_i)`; likewise the inner
`∫_A g·Ψ` only sees `g` on `A`, where the indicator is `1`.  Hence the mode `boxWinModeReGen` and
the indicator-free profile

`boxWinModeReSmooth volA A χ p z = χ z·cos⟪p,z⟫ − volA⁻¹∫_A χ·cos⟪p,·⟫`

produce **the same** `boxTauDagGen` / `boxTauAnnGen` / `boxModeRGen` operators.  The smooth
profiles are continuous as soon as `χ` is, which is what the analytic statements (the two-slot
commutator `boxTauDagGen_comm_cre`, the one-slot peel `boxOpG_adjoint_one`) need.

## Contents

* `boxWinModeReSmooth`, `boxWinModeImSmooth`, `boxWinModeCSmooth` — the indicator-free modes;
* their continuity;
* the pointwise dictionary `…Gen = 1_A·…Smooth`;
* the operator dictionary (`boxTauDagGen_congr_mode`, `boxTauDagGen_gen_eq_smooth`,
  `boxTauAnnGen_gen_eq_smooth`, `boxModeRGen_gen_eq_smooth`, and the complexified versions);
* `boxWinModeCSmooth_eq` — `boxWinModeCSmooth = boxWinModeReSmooth + i·boxWinModeImSmooth`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The indicator-free (continuous) real part of the mean-free windowed exponential on `A`:
`χ z·cos⟪p,z⟫ − volA⁻¹∫_A χ·cos⟪p,·⟫`. -/
noncomputable def boxWinModeReSmooth (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  χ z * Real.cos (inner ℝ p z)
    - volA⁻¹ * ∫ w in A, χ w * Real.cos (inner ℝ p w)

/-- The indicator-free (continuous) imaginary part of the mean-free windowed exponential on `A`:
`−(χ z·sin⟪p,z⟫ − volA⁻¹∫_A χ·sin⟪p,·⟫)`. -/
noncomputable def boxWinModeImSmooth (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  - (χ z * Real.sin (inner ℝ p z)
      - volA⁻¹ * ∫ w in A, χ w * Real.sin (inner ℝ p w))

/-- The indicator-free complex mode `χ z·e^{−i⟪p,z⟫} − volA⁻¹∫_A χ·e^{−i⟪p,·⟫}`. -/
noncomputable def boxWinModeCSmooth (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p z : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))
    - ((volA⁻¹ : ℝ) : ℂ) * ∫ w in A,
        (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))

/-! ## Continuity -/

lemma continuous_boxWinModeReSmooth (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Continuous (boxWinModeReSmooth volA A χ p) := by
  unfold boxWinModeReSmooth
  exact (hχ.mul (Real.continuous_cos.comp (continuous_const.inner continuous_id))).sub
    continuous_const

lemma continuous_boxWinModeImSmooth (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Continuous (boxWinModeImSmooth volA A χ p) := by
  unfold boxWinModeImSmooth
  exact ((hχ.mul (Real.continuous_sin.comp (continuous_const.inner continuous_id))).sub
    continuous_const).neg

lemma continuous_boxWinModeCSmooth (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Continuous (boxWinModeCSmooth volA A χ p) := by
  have hθ : Continuous fun z : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp
      (((continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin 3) => Complex.I).mul
        (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).neg)
  unfold boxWinModeCSmooth
  exact ((Complex.continuous_ofReal.comp hχ).mul hθ).sub (continuous_const.mul continuous_const)

/-! ## The pointwise dictionary `…Gen = 1_A · …Smooth` -/

lemma boxWinModeReGen_eq_indicator_smooth (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p z : EuclideanSpace ℝ (Fin 3)) :
    boxWinModeReGen volA A χ p z
      = A.indicator (fun _ => (1 : ℝ)) z * boxWinModeReSmooth volA A χ p z := rfl

lemma boxWinModeImGen_eq_indicator_smooth (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p z : EuclideanSpace ℝ (Fin 3)) :
    boxWinModeImGen volA A χ p z
      = A.indicator (fun _ => (1 : ℝ)) z * boxWinModeImSmooth volA A χ p z := by
  rw [boxWinModeImGen, boxWinModeImSmooth, mul_neg]

lemma boxWinModeC_eq_indicator_smooth (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p z : EuclideanSpace ℝ (Fin 3)) :
    boxWinModeC volA A χ p z
      = A.indicator (fun _ => (1 : ℂ)) z * boxWinModeCSmooth volA A χ p z := rfl

/-! ## The complex mode and its real and imaginary parts -/

/-- `boxWinModeCSmooth = boxWinModeReSmooth + i·boxWinModeImSmooth` (the smooth companion of
`Work.BoseFixB1.boxWinModeC_eq`, now without the box indicator). -/
lemma boxWinModeCSmooth_eq (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (p z : EuclideanSpace ℝ (Fin 3)) :
    boxWinModeCSmooth volA A χ p z
      = (boxWinModeReSmooth volA A χ p z : ℂ)
        + Complex.I * (boxWinModeImSmooth volA A χ p z : ℂ) := by
  rw [boxWinModeCSmooth, boxChat_eq hχc hχs p, boxWinModeReSmooth, boxWinModeImSmooth,
    cexp_neg_I_eq]
  push_cast
  ring

/-! ## Operator dictionary

Every operator below depends on its mode only through the *products* `1_A(x_i)·g(x_i)` and the
inner integrals `∫_A g·Ψ`; on `A` the indicator is `1`, so replacing `g` by `1_A·g` or by the
indicator-free profile changes nothing. -/

/-- Two modes that agree pointwise give the same `boxTauDagGen`. -/
lemma boxTauDagGen_congr_mode {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {g g' : EuclideanSpace ℝ (Fin 3) → ℝ} (h : ∀ z, g z = g' z)
    (Ψ : X N → ℝ) :
    boxTauDagGen volA A g Ψ = boxTauDagGen volA A g' Ψ := by
  funext x
  unfold boxTauDagGen
  refine congrArg (fun t : ℝ => (Real.sqrt volA)⁻¹ * t) ?_
  exact Finset.sum_congr rfl (fun i _ => by rw [h (x i)])

/-- Two modes that agree pointwise give the same `boxTauDagGenC`. -/
lemma boxTauDagGenC_congr_mode {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {g g' : EuclideanSpace ℝ (Fin 3) → ℂ} (h : ∀ z, g z = g' z)
    (Ψ : X N → ℂ) :
    boxTauDagGenC volA A g Ψ = boxTauDagGenC volA A g' Ψ := by
  funext x
  unfold boxTauDagGenC
  refine congrArg (fun t : ℂ => (Real.sqrt volA)⁻¹ * t) ?_
  exact Finset.sum_congr rfl (fun i _ => by rw [h (x i)])

/-- Two modes that agree on `A` give the same `boxTauAnnGen`. -/
lemma boxTauAnnGen_congr_mode {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (volA : ℝ)
    {g g' : EuclideanSpace ℝ (Fin 3) → ℝ} (h : ∀ z ∈ A, g z = g' z)
    (Ψ : X N → ℝ) :
    boxTauAnnGen volA A g Ψ = boxTauAnnGen volA A g' Ψ := by
  funext x
  unfold boxTauAnnGen
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hA] with z hz
  rw [h z hz]

/-- The genuine creation operator at `boxWinModeReGen` equals the one at its indicator-free
profile `boxWinModeReSmooth`. -/
lemma boxTauDagGen_reGen_eq_smooth {N : ℕ} (volA : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) (Ψ : X N → ℝ) :
    boxTauDagGen volA A (boxWinModeReGen volA A χ p) Ψ
      = boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ := by
  funext x
  unfold boxTauDagGen
  refine congrArg (fun t : ℝ => (Real.sqrt volA)⁻¹ * t) ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [boxWinModeReGen_eq_indicator_smooth]
  by_cases hz : x i ∈ A
  · rw [Set.indicator_of_mem hz, one_mul]
  · rw [Set.indicator_of_notMem hz, zero_mul]
    ring

/-- The genuine creation operator at `boxWinModeImGen` equals the one at its indicator-free
profile `boxWinModeImSmooth`. -/
lemma boxTauDagGen_imGen_eq_smooth {N : ℕ} (volA : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) (Ψ : X N → ℝ) :
    boxTauDagGen volA A (boxWinModeImGen volA A χ p) Ψ
      = boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ := by
  funext x
  unfold boxTauDagGen
  refine congrArg (fun t : ℝ => (Real.sqrt volA)⁻¹ * t) ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [boxWinModeImGen_eq_indicator_smooth]
  by_cases hz : x i ∈ A
  · rw [Set.indicator_of_mem hz, one_mul]
  · rw [Set.indicator_of_notMem hz, zero_mul]
    ring

/-- The genuine annihilation operator at `boxWinModeReGen` equals the one at its indicator-free
profile. -/
lemma boxTauAnnGen_reGen_eq_smooth {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (volA : ℝ) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) (Ψ : X N → ℝ) :
    boxTauAnnGen volA A (boxWinModeReGen volA A χ p) Ψ
      = boxTauAnnGen volA A (boxWinModeReSmooth volA A χ p) Ψ := by
  refine boxTauAnnGen_congr_mode hA volA (fun z hz => ?_) Ψ
  rw [boxWinModeReGen_eq_indicator_smooth, Set.indicator_of_mem hz, one_mul]

/-- The genuine annihilation operator at `boxWinModeImGen` equals the one at its indicator-free
profile. -/
lemma boxTauAnnGen_imGen_eq_smooth {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (volA : ℝ) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) (Ψ : X N → ℝ) :
    boxTauAnnGen volA A (boxWinModeImGen volA A χ p) Ψ
      = boxTauAnnGen volA A (boxWinModeImSmooth volA A χ p) Ψ := by
  refine boxTauAnnGen_congr_mode hA volA (fun z hz => ?_) Ψ
  rw [boxWinModeImGen_eq_indicator_smooth, Set.indicator_of_mem hz, one_mul]

/-- The genuine pairing content at `boxWinModeReGen` equals the one at its indicator-free
profile. -/
lemma boxModeRGen_reGen_eq_smooth {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (ℓ volA : ℝ) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) (Ψ : X N → ℝ) :
    boxModeRGen ℓ volA A (boxWinModeReGen volA A χ p) Ψ
      = boxModeRGen ℓ volA A (boxWinModeReSmooth volA A χ p) Ψ := by
  unfold boxModeRGen
  rw [boxTauAnnGen_reGen_eq_smooth hA volA χ p Ψ,
    boxTauDagGen_reGen_eq_smooth volA A χ p Ψ]

/-- The genuine pairing content at `boxWinModeImGen` equals the one at its indicator-free
profile. -/
lemma boxModeRGen_imGen_eq_smooth {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (ℓ volA : ℝ) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) (Ψ : X N → ℝ) :
    boxModeRGen ℓ volA A (boxWinModeImGen volA A χ p) Ψ
      = boxModeRGen ℓ volA A (boxWinModeImSmooth volA A χ p) Ψ := by
  unfold boxModeRGen
  rw [boxTauAnnGen_imGen_eq_smooth hA volA χ p Ψ,
    boxTauDagGen_imGen_eq_smooth volA A χ p Ψ]

/-- The complexified genuine creation operator at `boxWinModeC` equals the one at the
indicator-free profile `boxWinModeCSmooth`. -/
lemma boxTauDagGenC_modeC_eq_smooth {N : ℕ} (volA : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) (Ψ : X N → ℂ) :
    boxTauDagGenC volA A (boxWinModeC volA A χ p) Ψ
      = boxTauDagGenC volA A (boxWinModeCSmooth volA A χ p) Ψ := by
  funext x
  unfold boxTauDagGenC
  refine congrArg (fun t : ℂ => (Real.sqrt volA)⁻¹ * t) ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [boxWinModeC_eq_indicator_smooth]
  by_cases hz : x i ∈ A
  · rw [Set.indicator_of_mem hz, one_mul]
  · rw [Set.indicator_of_notMem hz, zero_mul]
    ring

/-! ## Indicator collapse for the operators -/

/-- Collapsing the box indicator of the mode in a `boxTauDagGenC`. -/
lemma boxTauDagGenC_indicator_mode {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → ℂ) (Ψ : X N → ℂ) :
    boxTauDagGenC volA A (fun z => A.indicator (fun _ => (1 : ℂ)) z * g z) Ψ
      = boxTauDagGenC volA A g Ψ := by
  funext x
  unfold boxTauDagGenC
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hz : x i ∈ A <;> simp [hz] <;> ring

/-- Collapsing the box indicator of the mode in a `boxTauDagGen`. -/
lemma boxTauDagGen_indicator_mode {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ) :
    boxTauDagGen volA A (fun z => A.indicator (fun _ => (1 : ℝ)) z * g z) Ψ
      = boxTauDagGen volA A g Ψ := by
  funext x
  unfold boxTauDagGen
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hz : x i ∈ A <;> simp [hz] <;> ring

/-- Collapsing the box indicator of the mode in a `boxTauAnnGen` (the inner `∫_A` only sees the
mode on `A`). -/
lemma boxTauAnnGen_indicator_mode {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (volA : ℝ)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ) :
    boxTauAnnGen volA A (fun z => A.indicator (fun _ => (1 : ℝ)) z * g z) Ψ
      = boxTauAnnGen volA A g Ψ := by
  funext x
  unfold boxTauAnnGen
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hA] with z hz
  rw [Set.indicator_of_mem hz, one_mul]

end Work.BoseFixB1
