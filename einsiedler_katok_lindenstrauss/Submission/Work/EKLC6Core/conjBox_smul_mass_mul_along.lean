import Mathlib
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.conjBox_smul_mass_mul

/-!
# `EKLC6Core.conjBox_smul_mass_mul_along`

The two-box normalisation identity of `conjBox_smul_mass_mul`, with the full `A`-covariance
`ACovariant ν X''` replaced by the covariance along the integer multiples of a *single*
direction `t` (`ACovariantAlong ν t X''`, EKL (4) restricted to `ℤ·t`), and with the exponent
vector `s` restricted accordingly to `s = z • t`, `z : ℤ`.

The point is that the one-step covariance `covariant_step` uses the covariance hypothesis at a
single parameter only — namely at the parameter of the shift — so `covariant_step_along` below
is proved by literally the same argument, reading `hcov` at that one integer multiple.  The
final assembly is then line-for-line the one in `conjBox_smul_mass_mul`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **One step of the covariance along a single direction.**  This is `covariant_step` with the
`A`-covariance `ACovariant ν X''` replaced by `ACovariantAlong ν t X''` and the shift taken to be
the integer multiple `(z : ℝ) • t` of the direction `t`: the covariance is read at exactly that
one parameter.

`ν (aDiag ((z:ℝ)•t) · y) C * ν y (conjBox U (-((z:ℝ)•t))) = ν y (conjBy (-((z:ℝ)•t)) C)`. -/
theorem covariant_step_along {μ : Measure X3} {U : Subgroup SL3} {ν : X3 → Measure SL3}
    {X' X'' : Set X3} {t : Fin 3 → ℝ} (hL : IsLeafwise μ U ν X')
    (hcov : ACovariantAlong ν t X'') (hBox1 : MeasurableSet (Box1 U))
    (z : ℤ) {y : X3} (hy : y ∈ X' ∩ X'')
    (hy' : aDiag ((z : ℝ) • t) • y ∈ X' ∩ X'') {C : Set SL3} (hC : MeasurableSet C) :
    ν (aDiag ((z : ℝ) • t) • y) C * ν y (conjBox U (-((z : ℝ) • t))) =
      ν y (conjBy (-((z : ℝ) • t)) C) := by
  set w : Fin 3 → ℝ := (z : ℝ) • t with hw
  obtain ⟨c, -, -, hceq⟩ := hcov z y hy.2 (by rw [← hw]; exact hy'.2)
  have hmap : Measurable (fun g : SL3 => aDiag w * g * (aDiag w)⁻¹) := measurable_conj _
  have hpre : ∀ D : Set SL3, (fun g : SL3 => aDiag w * g * (aDiag w)⁻¹) ⁻¹' D = conjBy (-w) D := by
    intro D
    have h := preimage_conj_neg (-w) D
    simpa using h
  have key : ∀ {D : Set SL3}, MeasurableSet D → ν (aDiag w • y) D = c * ν y (conjBy (-w) D) := by
    intro D hD
    rw [hceq, Measure.smul_apply, smul_eq_mul, Measure.map_apply hmap hD, hpre D]
  have h1 : ν (aDiag w • y) (Box1 U) = c * ν y (conjBox U (-w)) := key hBox1
  have h2 : ν (aDiag w • y) (Box1 U) = 1 := hL.normalised _ hy'.1
  calc ν (aDiag w • y) C * ν y (conjBox U (-w))
      = (c * ν y (conjBy (-w) C)) * ν y (conjBox U (-w)) := by rw [key hC]
    _ = (c * ν y (conjBox U (-w))) * ν y (conjBy (-w) C) := by ac_rfl
    _ = ν y (conjBy (-w) C) := by rw [← h1, h2, one_mul]

/-- **The two-box normalisation identity along a single direction.**  For a leaf-wise system
`(μ, ν)` on `X'` carried by the horospherical subgroup `U`, with `A`-covariance along the
integer multiples of the direction `t` on `X''`, and for any `s = z • t`, `z : ℤ`, and any
`y ∈ X' ∩ X''` with `aDiag s · y ∈ X' ∩ X''`,

`ν (aDiag s · y) (conjBox U s) * ν y (conjBox U (-s)) = 1`. -/
theorem conjBox_smul_mass_mul_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'')
    (hU : Work.EKLContract.IsHoro U)
    (s : Fin 3 → ℝ) (hs : ∃ z : ℤ, s = (z : ℝ) • t) {y : Work.EKLContract.X3}
    (hy : y ∈ X' ∩ X'') (hy' : Work.EKLContract.aDiag s • y ∈ X' ∩ X'') :
    ν (Work.EKLContract.aDiag s • y) (Work.EKLC6Core.conjBox U s) *
      ν y (Work.EKLC6Core.conjBox U (-s)) = 1 := by
  obtain ⟨z, rfl⟩ := hs
  have hstep := covariant_step_along hL hcov (measurableSet_box1 hU) z hy hy'
    (C := conjBox U ((z : ℝ) • t)) (conjBox_measurable hU _)
  rw [conjBy_conjBox, neg_add_cancel, conjBox_zero] at hstep
  rw [hstep, hL.normalised y hy.1]

end Work.EKLC6Core

end
