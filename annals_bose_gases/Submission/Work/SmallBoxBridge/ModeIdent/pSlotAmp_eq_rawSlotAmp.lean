import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Q_B`-projection is free for the slot amplitude

`qMode s p y = χ_s(y)e^{−i⟪p,y⟫} − (s³)⁻¹∫_{acube s}χ_s e^{−i⟪p,·⟫}` is the `1_B`-mean-free
(`Q_B`-projected) windowed exponential, and `aQ s i Ψ = Ψ − aP s i Ψ` is the `Q_i`-projection of
the corpus's sector decomposition (the mean `aP s i Ψ` is taken over the `i`-th slot).

Since the `i`-th slot mean `aP s i Ψ (x_{i↦z})` is *constant in* `z`, and since
`∫_{acube s} qMode s p = 0`, the slot amplitude of the mean-free mode at `Ψ` equals the plain
windowed-exponential amplitude of the `Q_i`-projected fibre `aQ s i Ψ`:

`∫_{acube s} qMode s p z·Ψ(x_{i↦z})dz = ∫_{acube s} χ_s(z)e^{−i⟪p,z⟫}·(aQ s i Ψ)(x_{i↦z})dz`.

Concretely, with `E z = χ_s(z)e^{−i⟪p,z⟫}` and `C = (s³)⁻¹∫ E` we split the integrand along
`Ψ = aQΨ + aP`,

`(E − C)·Ψ(x_{i↦z}) = E·(aQΨ)(x_{i↦z}) + (E·(aPΨ)(x) − C·Ψ(x_{i↦z}))`,

and the integral of the bracket vanishes: `∫E·(aPΨ)(x) = C·(aPΨ)(x)` while
`∫Ψ(x_{i↦z})dz = s³·(aPΨ)(x)`, and `C·s³ = C` by definition of `C`.
-/

open MeasureTheory
open scoped Topology Real BigOperators

namespace Work.SmallBoxBridge.ModeIdent

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

theorem pSlotAmp_eq_rawSlotAmp {N : ℕ} {s : ℝ} (hs : 0 < s)
    (p : EuclideanSpace ℝ (Fin 3)) {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hΨ : Continuous Ψ) (i : Fin N) (x : Fin N → EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.pSlotAmp s p Ψ i x
      = Submission.BoseGases.rawSlotAmp s p (Submission.BoseGases.aQ s i Ψ) i x := by
  have hs3 : s ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hs)
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hcan : ((s ^ 3)⁻¹ : ℂ) * ((s : ℂ) ^ 3) = 1 := inv_mul_cancel₀ (pow_ne_zero 3 hsc)
  -- the bare windowed exponential `E`, and the projection correction `C`
  set E : ℝ³ → ℂ := fun z => (chiScale s z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
    with hE
  set C : ℂ := ((s ^ 3)⁻¹ : ℂ) * modeChat s p with hC
  have hqm : ∀ z : ℝ³, qMode s p z = E z - C := by
    intro z
    simp only [hE, hC, qMode]
  have hcontE : Continuous E := by
    rw [hE]
    exact (Complex.continuous_ofReal.comp (chiScale_continuous s)).mul
      (Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.inner continuous_id))).neg))
  have hcontΨu : Continuous fun z : ℝ³ => Ψ (Function.update x i z) :=
    hΨ.comp (continuous_const.update i continuous_id)
  have hcontQu : Continuous fun z : ℝ³ => (aQ s i Ψ) (Function.update x i z) :=
    (aQ_continuous hs i hΨ).comp (continuous_const.update i continuous_id)
  have hInt1 : IntegrableOn (fun z : ℝ³ => E z * ((aQ s i Ψ) (Function.update x i z) : ℂ))
      (acube s) volume :=
    ContinuousOn.integrableOn_compact (acube_compact hs)
      ((hcontE.mul (Complex.continuous_ofReal.comp hcontQu)).continuousOn)
  have hInt2 : IntegrableOn (fun z : ℝ³ => E z * ((aP s i Ψ x : ℝ) : ℂ)) (acube s) volume :=
    ContinuousOn.integrableOn_compact (acube_compact hs)
      ((hcontE.mul continuous_const).continuousOn)
  have hInt3 : IntegrableOn (fun z : ℝ³ => C * (Ψ (Function.update x i z) : ℂ)) (acube s) volume :=
    ContinuousOn.integrableOn_compact (acube_compact hs)
      ((continuous_const.mul (Complex.continuous_ofReal.comp hcontΨu)).continuousOn)
  -- the pointwise splitting of the integrand along `Ψ = aQ Ψ + aP Ψ`
  have hpt : ∀ z : ℝ³,
      (E z - C) * (Ψ (Function.update x i z) : ℂ)
      = E z * ((aQ s i Ψ) (Function.update x i z) : ℂ)
        + (E z * ((aP s i Ψ x : ℝ) : ℂ) - C * (Ψ (Function.update x i z) : ℂ)) := by
    intro z
    have h : Ψ (Function.update x i z) = (aQ s i Ψ) (Function.update x i z) + aP s i Ψ x := by
      unfold aQ
      rw [aP_const_in_coord hs i hΨ x z]
      ring
    rw [h]
    push_cast
    ring
  -- the slot integral of the fibre is `s³` times the slot mean
  have hIntΨ : (∫ z in acube s, Ψ (Function.update x i z)) = s ^ 3 * aP s i Ψ x := by
    unfold aP
    field_simp
  -- `∫ E = modeChat`
  have hEint : (∫ z in acube s, E z) = modeChat s p := by
    rw [hE]; rfl
  -- the bracket integrates to zero
  have hbracket : modeChat s p * ((aP s i Ψ x : ℝ) : ℂ)
      - C * ((s ^ 3 * aP s i Ψ x : ℝ) : ℂ) = 0 := by
    rw [hC]
    have hcast : ((s ^ 3 * aP s i Ψ x : ℝ) : ℂ) = (s : ℂ) ^ 3 * ((aP s i Ψ x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast]
    have h : ((s ^ 3)⁻¹ : ℂ) * modeChat s p * ((s : ℂ) ^ 3 * ((aP s i Ψ x : ℝ) : ℂ))
        = (modeChat s p * ((aP s i Ψ x : ℝ) : ℂ)) * (((s ^ 3)⁻¹ : ℂ) * (s : ℂ) ^ 3) := by
      ring
    rw [h, hcan, mul_one, sub_self]
  have step0 : (∫ z in acube s, (E z - C) * (Ψ (Function.update x i z) : ℂ))
      = ∫ z in acube s, (E z * ((aQ s i Ψ) (Function.update x i z) : ℂ)
          + (E z * ((aP s i Ψ x : ℝ) : ℂ) - C * (Ψ (Function.update x i z) : ℂ))) :=
    setIntegral_congr_fun (acube_measurable s) (fun z _ => hpt z)
  have step1 : (∫ z in acube s, (E z * ((aQ s i Ψ) (Function.update x i z) : ℂ)
          + (E z * ((aP s i Ψ x : ℝ) : ℂ) - C * (Ψ (Function.update x i z) : ℂ))))
      = (∫ z in acube s, E z * ((aQ s i Ψ) (Function.update x i z) : ℂ))
        + ∫ z in acube s, (E z * ((aP s i Ψ x : ℝ) : ℂ)
            - C * (Ψ (Function.update x i z) : ℂ)) :=
    MeasureTheory.integral_add hInt1 (hInt2.sub hInt3)
  have step2 : (∫ z in acube s, (E z * ((aP s i Ψ x : ℝ) : ℂ)
          - C * (Ψ (Function.update x i z) : ℂ)))
      = (∫ z in acube s, E z * ((aP s i Ψ x : ℝ) : ℂ))
        - ∫ z in acube s, C * (Ψ (Function.update x i z) : ℂ) :=
    MeasureTheory.integral_sub hInt2 hInt3
  have step3 : (∫ z in acube s, E z * ((aP s i Ψ x : ℝ) : ℂ))
      = modeChat s p * ((aP s i Ψ x : ℝ) : ℂ) := by
    rw [MeasureTheory.integral_mul_const, hEint]
  have step4 : (∫ z in acube s, C * (Ψ (Function.update x i z) : ℂ))
      = C * ((s ^ 3 * aP s i Ψ x : ℝ) : ℂ) := by
    rw [MeasureTheory.integral_const_mul]
    rw [show (∫ z in acube s, (Ψ (Function.update x i z) : ℂ))
        = ((∫ z in acube s, Ψ (Function.update x i z) : ℝ) : ℂ) from integral_ofReal]
    rw [hIntΨ]
  have hmain : (∫ z in acube s, (E z - C) * (Ψ (Function.update x i z) : ℂ))
      = ∫ z in acube s, E z * ((aQ s i Ψ) (Function.update x i z) : ℂ) := by
    rw [step0, step1, step2, step3, step4, hbracket, add_zero]
  rw [show pSlotAmp s p Ψ i x
      = ∫ z in acube s, (E z - C) * (Ψ (Function.update x i z) : ℂ) from by
    unfold pSlotAmp
    exact setIntegral_congr_fun (acube_measurable s) (fun z _ => by rw [hqm z])]
  rw [hmain]
  unfold rawSlotAmp
  rw [hE]

end Work.SmallBoxBridge.ModeIdent
