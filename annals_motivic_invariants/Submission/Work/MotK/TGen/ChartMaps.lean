/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.ChartDefs
import Submission.Work.MotK.TGen.Phi0GambT
import Submission.Work.MotK.TGen.Phi0FwVec
import Submission.Work.MotK.TGen.Psi0FambT
import Submission.Work.MotK.TGen.Psi0BwVec
import Submission.Work.MotK.TGen.KleinTwRChart0
import Submission.Work.MotK.TGen.KleinTwFhomPi
import Submission.Work.MotK.AwayAlgEquivOfComp

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ChartMaps` — the two maps of the chart isomorphism of the T-twisted link

This file continues `Work.MotK.TGen.ChartDefs`: it upgrades the two chart pullbacks `Phi0 = χ^*`
and `Psi0 = f^*` to `K`-algebra homomorphisms of the two localisations

* `PhiT a b h : R[1/Fdiv] →ₐ[K] R[1/Gdiv]`,
* `PsiT a b h : R[1/Gdiv] →ₐ[K] R[1/Fdiv]`,

(`Fdiv = GambT · f̂₄`, `Gdiv = FambT · ǧ₄`), by showing that the images of the two divisors are
units; the unit conditions are the value lemmas `Phi0GambT`, `Phi0FwVec`, `Psi0FambT`,
`Psi0BwVec` of the sibling files, whose right-hand sides are a power of `invF4`/`invG4` times
the `algebraMap` of a product of *factors* of the divisor at hand.

The two composites `PsiT ∘ PhiT = id` and `PhiT ∘ PsiT = id` on the generators are in the sibling
files `Work.MotK.TGen.PsiTPhiTX` and `Work.MotK.TGen.PhiTPsiTX`; the final isomorphism is
`Work.MotK.TGen.chartIsoT`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-! ## The index shift and the two chart points -/

/-- The index shift `Fin 3 → Fin 5`, `j ↦ j + 1`. -/
def ch3 (j : Fin 3) : Fin 5 := ⟨j.val + 1, by omega⟩

@[simp] theorem ch3_zero : ch3 0 = 1 := rfl
@[simp] theorem ch3_one : ch3 1 = 2 := rfl
@[simp] theorem ch3_two : ch3 2 = 3 := rfl

theorem chart3_ch3 (j : Fin 3) : chart3 K (ch3 j) = MvPolynomial.X j := by
  fin_cases j <;> rfl

@[simp] theorem chart3_zero : chart3 K 0 = 0 := rfl
@[simp] theorem chart3_four : chart3 K 4 = 1 := rfl

theorem psiG_apply (a b h : K) (j : Fin 3) :
    psiG a b h j = invG4 a b h * algebraMap _ _ (bwVec a b h (ch3 j)) := by
  fin_cases j <;> simp [psiG, ch3]

theorem phiF_apply (a b h : K) (j : Fin 3) :
    phiF a b h j = invF4 a b h * algebraMap _ _ (fwVec a b h (ch3 j)) := by
  fin_cases j <;> simp [phiF, ch3]

theorem Phi0_X (a b h : K) (j : Fin 3) : Phi0 a b h (MvPolynomial.X j) = psiG a b h j := by
  fin_cases j <;> simp [Phi0, psiG, MvPolynomial.aeval_X]

theorem Psi0_X (a b h : K) (j : Fin 3) : Psi0 a b h (MvPolynomial.X j) = phiF a b h j := by
  fin_cases j <;> simp [Psi0, phiF, MvPolynomial.aeval_X]

/-! ## Units -/

/-- `GambT ∣ Fdiv`. -/
theorem gambT_dvd_Fdiv (a b h : K) : GambT a b h ∣ Fdiv a b h :=
  ⟨fwVec a b h 4, rfl⟩

/-- `FambT ∣ Gdiv`. -/
theorem fambT_dvd_Gdiv (a b h : K) : FambT a b h ∣ Gdiv a b h :=
  ⟨bwVec a b h 4, rfl⟩

/-- `1/f̂₄` is a unit of `R[1/Fdiv]`. -/
theorem isUnit_invF4 (a b h : K) : IsUnit (invF4 a b h) :=
  isUnit_of_dvd_unit ⟨algebraMap _ _ (Fdiv a b h), (invF4_spec a b h).symm⟩
    (IsLocalization.Away.isUnit_of_dvd (Fdiv a b h) (gambT_dvd_Fdiv a b h))

/-- `1/ǧ₄` is a unit of `R[1/Gdiv]`. -/
theorem isUnit_invG4 (a b h : K) : IsUnit (invG4 a b h) :=
  isUnit_of_dvd_unit ⟨algebraMap _ _ (Gdiv a b h), (invG4_spec a b h).symm⟩
    (IsLocalization.Away.isUnit_of_dvd (Gdiv a b h) (fambT_dvd_Gdiv a b h))

theorem isUnit_alg_GambT (a b h : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
      (GambT a b h)) :=
  IsLocalization.Away.isUnit_of_dvd (Fdiv a b h) (gambT_dvd_Fdiv a b h)

theorem isUnit_alg_FambT (a b h : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
      (FambT a b h)) :=
  IsLocalization.Away.isUnit_of_dvd (Gdiv a b h) (fambT_dvd_Gdiv a b h)

theorem kleinTwBilin_bwVec_eq (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
        (bwVec a b h)
      = kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
        (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K)) :=
  kleinTwBilin_pi_eq (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
    (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K))
    (kleinTwQ_pRa a b h ha hh)

/-- On the `G`-side, the first factor `b(p, ǧ)` of `FambT` (i.e. `b(p, R(chart))`) is a unit. -/
theorem isUnit_alg_bilinG (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
      (kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
        (bwVec a b h))) :=
  IsLocalization.Away.isUnit_of_dvd (Gdiv a b h)
    ⟨kleinTwSDualV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K)
        * bwVec a b h 4, by
      rw [kleinTwBilin_bwVec_eq a b h ha hh]
      simp only [Gdiv, FambT, kleinTwGhomV]
      ring⟩

/-- On the `G`-side, the second factor `s'(chart)` of `FambT` is a unit. -/
theorem isUnit_alg_sdualG (a b h : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
      (kleinTwSDualV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K))) :=
  IsLocalization.Away.isUnit_of_dvd (Gdiv a b h)
    ⟨kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
        (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K))
        * bwVec a b h 4, by
      simp only [Gdiv, FambT, kleinTwGhomV]
      ring⟩

/-- On the `F`-side, the first factor `b(p, chart)` of `GambT` is a unit. -/
theorem isUnit_alg_bilinF (a b h : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
      (kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
        (chart3 K))) :=
  IsLocalization.Away.isUnit_of_dvd (Fdiv a b h)
    ⟨kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
          (chart3 K)) * fwVec a b h 4, by
      simp only [Fdiv, GambT, kleinTwFhom]
      ring⟩

/-- On the `F`-side, the second factor `s(y(chart))` of `GambT` is a unit. -/
theorem isUnit_alg_sF (a b h : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
      (kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
          (chart3 K)))) :=
  IsLocalization.Away.isUnit_of_dvd (Fdiv a b h)
    ⟨kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
        (chart3 K) * fwVec a b h 4, by
      simp only [Fdiv, GambT, kleinTwFhom]
      ring⟩

/-- `Phi0 (GambT)` is a unit. -/
theorem isUnit_Phi0_gambT (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    IsUnit (Phi0 a b h (GambT a b h)) := by
  rw [Phi0GambT a b h ha hb hh, map_mul, map_mul, map_neg, map_pow, map_pow]
  simp only [mul_assoc]
  exact ((isUnit_invG4 a b h).pow 11).mul
    ((((isUnit_alg_bilinG a b h ha hh).pow 5).neg).mul
      (((isUnit_alg_sdualG a b h).pow 2).mul (isUnit_alg_FambT a b h)))

/-- `Phi0 (f̂ 4)` is a unit. -/
theorem isUnit_Phi0_fwVec4 (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    IsUnit (Phi0 a b h (fwVec a b h 4)) := by
  rw [Phi0FwVec a b h ha hb hh 4, map_mul, map_mul, map_pow, chart3_four, map_one, mul_one]
  exact ((isUnit_invG4 a b h).pow 4).mul
    (((isUnit_alg_bilinG a b h ha hh).pow 2).mul (isUnit_alg_sdualG a b h))

/-- `Psi0 (FambT)` is a unit. -/
theorem isUnit_Psi0_fambT (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    IsUnit (Psi0 a b h (FambT a b h)) := by
  rw [Psi0FambT a b h ha hh, map_mul, map_mul, map_neg, map_pow]
  simp only [mul_assoc]
  exact ((isUnit_invF4 a b h).pow 8).mul
    ((((isUnit_alg_sF a b h).pow 2).neg).mul
      ((isUnit_alg_bilinF a b h).mul (isUnit_alg_GambT a b h)))

/-- `Psi0 (ǧ 4)` is a unit. -/
theorem isUnit_Psi0_bwVec4 (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    IsUnit (Psi0 a b h (bwVec a b h 4)) := by
  rw [Psi0BwVec a b h ha hb hh 4, map_mul, map_neg, chart3_four, map_one, mul_one]
  exact ((isUnit_invF4 a b h).pow 3).mul (isUnit_alg_GambT a b h).neg

/-- `Phi0 (Fdiv)` is a unit, so `Phi0` descends to the localisation at `Fdiv`. -/
theorem isUnit_Phi0_Fdiv (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    IsUnit (Phi0 a b h (Fdiv a b h)) := by
  rw [show Fdiv a b h = GambT a b h * fwVec a b h 4 from rfl, map_mul]
  exact IsUnit.mul (isUnit_Phi0_gambT a b h ha hb hh) (isUnit_Phi0_fwVec4 a b h ha hb hh)

/-- `Psi0 (Gdiv)` is a unit, so `Psi0` descends to the localisation at `Gdiv`. -/
theorem isUnit_Psi0_Gdiv (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    IsUnit (Psi0 a b h (Gdiv a b h)) := by
  rw [show Gdiv a b h = FambT a b h * bwVec a b h 4 from rfl, map_mul]
  exact IsUnit.mul (isUnit_Psi0_fambT a b h ha hh) (isUnit_Psi0_bwVec4 a b h ha hb hh)

/-! ## The two maps of localisations -/

/-- The pullback `χ^*` of the inverse link map, as a `K`-algebra homomorphism
`R[1/Fdiv] →ₐ[K] R[1/Gdiv]`. -/
noncomputable def PhiT (a b h : K) (hu : IsUnit (Phi0 a b h (Fdiv a b h))) :
    Localization.Away (Fdiv a b h) →ₐ[K] Localization.Away (Gdiv a b h) :=
  IsLocalization.Away.liftAlgHom (Fdiv a b h) hu

/-- The pullback `f^*` of the forward link map, as a `K`-algebra homomorphism
`R[1/Gdiv] →ₐ[K] R[1/Fdiv]`. -/
noncomputable def PsiT (a b h : K) (hu : IsUnit (Psi0 a b h (Gdiv a b h))) :
    Localization.Away (Gdiv a b h) →ₐ[K] Localization.Away (Fdiv a b h) :=
  IsLocalization.Away.liftAlgHom (Gdiv a b h) hu

theorem PhiT_algebraMap (a b h : K) (hu : IsUnit (Phi0 a b h (Fdiv a b h)))
    (x : MvPolynomial (Fin 3) K) :
    PhiT a b h hu (algebraMap _ _ x) = Phi0 a b h x :=
  IsLocalization.Away.lift_eq (Fdiv a b h) hu x

theorem PsiT_algebraMap (a b h : K) (hu : IsUnit (Psi0 a b h (Gdiv a b h)))
    (x : MvPolynomial (Fin 3) K) :
    PsiT a b h hu (algebraMap _ _ x) = Psi0 a b h x :=
  IsLocalization.Away.lift_eq (Gdiv a b h) hu x

end Work.MotK.TGen
