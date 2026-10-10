/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TwAmbh
import Submission.Work.MotK.KleinTwLinkComp1
import Submission.Work.MotK.KleinTwLinkComp2
import Submission.Work.MotK.TGen.TwPoly
import Submission.Work.MotK.TGen.AevalFhomPoly
import Submission.Work.MotK.TGen.AevalGhomPoly
import Submission.Work.MotK.TGen.AevalFwPoly
import Submission.Work.MotK.TGen.AevalBwPoly
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ChartDefs` — the two chart maps of the T-twisted link as `AlgHom`s

This file is the *definition* layer of `A4`, second half (the chart isomorphism of the
T-twisted Crauder--Katz link).  The certificate `Work.MotV.LinkCert` of
`Submission/Work/MotK/LinkCertTGenInf.lean` wants an isomorphism

  `Φ : Localization.Away F ≃ₐ[K] Localization.Away G`

of the two affine charts of the link, where

* `GambT a b h = b(p, chart)·s(y(chart))` is the source equation (dehomogenised
  `kleinTwFhom`) and `FambT a b h = b(p, R(chart))·s'(chart)` the target equation
  (dehomogenised `kleinTwGhomV`);  we take

  * `Fdiv a b h = GambT a b h * fwVec a b h 4`   (source: the equation times the denominator
    `f̂₄` of the forward chart map),
  * `Gdiv a b h = FambT a b h * bwVec a b h 4`   (target: the equation times the denominator
    `ǧ₄` of the inverse chart map);

* the *source* chart coordinates are the fractions `f̂_{j+1}/f̂₄` and the *target* ones
  `ǧ_{j+1}/ǧ₄`, where `f̂ = kleinTwP ∘ kleinTwStereo` and `ǧ = kleinTwPi p ∘ kleinTwR` are the
  two link maps restricted to the affine chart `V₀ = 0, V₄ = 1`.

Since a general `CommRing` has no inversion, the fractions are written with
`IsLocalization.mk'`:  with

* `W = invF4 a b h = mk' (GambT, Fdiv) = 1/f̂₄ ∈ R[1/Fdiv]`,
* `V = invG4 a b h = mk' (FambT, Gdiv) = 1/ǧ₄ ∈ R[1/Gdiv]`,

the chart coordinates are `phiF a b h : Fin 3 → R[1/Fdiv]`, `phiF a b h j = W * f̂_{j+1}` and
`psiG a b h : Fin 3 → R[1/Gdiv]`, `psiG a b h j = V * ǧ_{j+1}`, and the two `K`-algebra
homomorphisms are `Phi0 a b h = aeval (psiG a b h)`, `Psi0 a b h = aeval (phiF a b h)`.

The value lemmas (`Phi0_GambT`, `Phi0_fwVec`, `Psi0_FambT`, `Psi0_bwVec`), the unit conditions
that make `Phi0`, `Psi0` descend to the localisations, and the identification of the two
composites with the identity are in the sibling files.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

/-- **The forward link map on the affine chart**, in the chart ring `K[x₀,x₁,x₂]`:
`f̂ = kleinTwP ∘ kleinTwStereo` at the chart vector `(0, x₀, x₁, x₂, 1)` and the point
`p = kleinPointT a b h`. -/
noncomputable def fwVec (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
      (chart3 K))

/-- **The inverse link map on the affine chart**: `ǧ = kleinTwPi p ∘ kleinTwR` at the chart
vector `(0, x₀, x₁, x₂, 1)`. -/
noncomputable def bwVec (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  kleinTwPi (pRa a b h)
    (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K))

/-- `f̂₀ = 0`: the forward map lands in the hyperplane `{w₀ = 0}`. -/
theorem fwVec_zero (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) : fwVec a b h 0 = 0 := by
  show kleinTwQ (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
      (chart3 K)) = 0
  rw [KleinTwQ_stereo, kleinTwQ_pRa a b h ha hh, mul_zero]

/-- `ǧ₀ = 0`: the projection `π_p` lands in the hyperplane `{v₀ = 0}`. -/
theorem bwVec_zero (a b h : K) : bwVec a b h 0 = 0 := by
  simp only [bwVec, kleinTwPi, pRa_apply, Pi.sub_apply, Pi.mul_apply, kleinPointT, map_one]
  first | refl_ring1 | ring

/-! ## The two divisor polynomials and the two unit denominators -/

/-- The **source-side** divisor of the certificate: the source equation times the denominator
`f̂₄` of the forward chart map. -/
noncomputable def Fdiv (a b h : K) : MvPolynomial (Fin 3) K :=
  GambT a b h * fwVec a b h 4

/-- The **target-side** divisor of the certificate: the target equation times the denominator
`ǧ₄` of the inverse chart map. -/
noncomputable def Gdiv (a b h : K) : MvPolynomial (Fin 3) K :=
  FambT a b h * bwVec a b h 4

/-- `1/f̂₄ ∈ R[1/Fdiv]`, written as `GambT / (GambT · f̂₄)`. -/
noncomputable def invF4 (a b h : K) : Localization.Away (Fdiv a b h) :=
  IsLocalization.mk' (Localization.Away (Fdiv a b h)) (GambT a b h)
    ⟨Fdiv a b h, (Submonoid.mem_powers_iff (Fdiv a b h) (Fdiv a b h)).mpr ⟨1, pow_one _⟩⟩

/-- `1/ǧ₄ ∈ R[1/Gdiv]`, written as `FambT / (FambT · ǧ₄)`. -/
noncomputable def invG4 (a b h : K) : Localization.Away (Gdiv a b h) :=
  IsLocalization.mk' (Localization.Away (Gdiv a b h)) (FambT a b h)
    ⟨Gdiv a b h, (Submonoid.mem_powers_iff (Gdiv a b h) (Gdiv a b h)).mpr ⟨1, pow_one _⟩⟩

theorem invF4_spec (a b h : K) :
    invF4 a b h * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
        (Fdiv a b h)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h)) (GambT a b h) :=
  IsLocalization.mk'_spec _ _ _

theorem invG4_spec (a b h : K) :
    invG4 a b h * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
        (Gdiv a b h)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h)) (FambT a b h) :=
  IsLocalization.mk'_spec _ _ _

/-- `1/f̂₄ * f̂₄ = 1` in `R[1/Fdiv]`. -/
theorem invF4_mul_fwVec4 (a b h : K) :
    invF4 a b h
      * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h)) (fwVec a b h 4)
      = 1 := by
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
      (GambT a b h)) :=
    IsLocalization.Away.isUnit_of_dvd (Fdiv a b h) (dvd_mul_right _ _)
  have hF : algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h)) (Fdiv a b h)
      = algebraMap _ _ (GambT a b h) * algebraMap _ _ (fwVec a b h 4) := by
    change algebraMap _ _ (GambT a b h * fwVec a b h 4) = _
    rw [map_mul]
  have hs := invF4_spec a b h
  rw [hF] at hs
  refine hunit.mul_left_cancel ?_
  rw [mul_one, ← mul_assoc, mul_comm (algebraMap _ _ (GambT a b h)) (invF4 a b h)]
  simpa only [← mul_assoc] using hs

/-- `1/ǧ₄ * ǧ₄ = 1` in `R[1/Gdiv]`. -/
theorem invG4_mul_bwVec4 (a b h : K) :
    invG4 a b h
      * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h)) (bwVec a b h 4)
      = 1 := by
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
      (FambT a b h)) :=
    IsLocalization.Away.isUnit_of_dvd (Gdiv a b h) (dvd_mul_right _ _)
  have hG : algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h)) (Gdiv a b h)
      = algebraMap _ _ (FambT a b h) * algebraMap _ _ (bwVec a b h 4) := by
    change algebraMap _ _ (FambT a b h * bwVec a b h 4) = _
    rw [map_mul]
  have hs := invG4_spec a b h
  rw [hG] at hs
  refine hunit.mul_left_cancel ?_
  rw [mul_one, ← mul_assoc, mul_comm (algebraMap _ _ (FambT a b h)) (invG4 a b h)]
  simpa only [← mul_assoc] using hs

/-! ## The two chart points -/

/-- The chart coordinates of the inverse map `χ`, in `R[1/Gdiv]`. -/
noncomputable def psiG (a b h : K) : Fin 3 → Localization.Away (Gdiv a b h) :=
  ![invG4 a b h * algebraMap _ _ (bwVec a b h 1),
    invG4 a b h * algebraMap _ _ (bwVec a b h 2),
    invG4 a b h * algebraMap _ _ (bwVec a b h 3)]

/-- The chart coordinates of the forward map `f`, in `R[1/Fdiv]`. -/
noncomputable def phiF (a b h : K) : Fin 3 → Localization.Away (Fdiv a b h) :=
  ![invF4 a b h * algebraMap _ _ (fwVec a b h 1),
    invF4 a b h * algebraMap _ _ (fwVec a b h 2),
    invF4 a b h * algebraMap _ _ (fwVec a b h 3)]

/-- The chart point of `χ`: `(0, ǧ₁/ǧ₄, ǧ₂/ǧ₄, ǧ₃/ǧ₄, 1) = (1/ǧ₄) • ǧ`. -/
theorem chartPt3_psiG (a b h : K) :
    chartPt3 (psiG a b h)
      = fun i => invG4 a b h * algebraMap _ _ (bwVec a b h i) := by
  funext i
  fin_cases i <;> simp [chartPt3, psiG, bwVec_zero a b h, invG4_mul_bwVec4 a b h]

/-- The chart point of `f`: `(0, f̂₁/f̂₄, f̂₂/f̂₄, f̂₃/f̂₄, 1) = (1/f̂₄) • f̂`. -/
theorem chartPt3_phiF (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    chartPt3 (phiF a b h)
      = fun i => invF4 a b h * algebraMap _ _ (fwVec a b h i) := by
  funext i
  fin_cases i <;> simp [chartPt3, phiF, fwVec_zero a b h ha hh, invF4_mul_fwVec4 a b h]

/-! ## The two `K`-algebra homomorphisms of the chart rings -/

/-- The pullback `χ^*` of the inverse link map on the chart ring, as a `K`-algebra homomorphism
into the localisation `R[1/Gdiv]`. -/
noncomputable def Phi0 (a b h : K) : MvPolynomial (Fin 3) K →ₐ[K] Localization.Away (Gdiv a b h) :=
  MvPolynomial.aeval (psiG a b h)

/-- The pullback `f^*` of the forward link map on the chart ring, as a `K`-algebra homomorphism
into the localisation `R[1/Fdiv]`. -/
noncomputable def Psi0 (a b h : K) : MvPolynomial (Fin 3) K →ₐ[K] Localization.Away (Fdiv a b h) :=
  MvPolynomial.aeval (phiF a b h)

theorem Phi0_chart3 (a b h : K) :
    (fun i => Phi0 a b h (chart3 K i)) = chartPt3 (psiG a b h) := by
  funext i
  fin_cases i <;> simp [Phi0, chartPt3, psiG, chart3, MvPolynomial.aeval_X]

theorem Psi0_chart3 (a b h : K) :
    (fun i => Psi0 a b h (chart3 K i)) = chartPt3 (phiF a b h) := by
  funext i
  fin_cases i <;> simp [Psi0, chartPt3, phiF, chart3, MvPolynomial.aeval_X]

/-! ## `aeval` computes the chart equations -/

/-- The dehomogenisation `GambT` of the source equation is the evaluation of `FhomPoly` at the
chart vector. -/
theorem GambT_eq_aeval (a b h : K) :
    GambT a b h = MvPolynomial.aeval (chart3 K) (FhomPoly K a b h) := by
  rw [GambT, AevalFhomPoly (K := K) (A := MvPolynomial (Fin 3) K) a b h (chart3 K)]
  simp only [MvPolynomial.algebraMap_eq]
  rfl

/-- The dehomogenisation `FambT` of the target equation is the evaluation of `GhomPoly` at the
chart vector. -/
theorem FambT_eq_aeval (a b h : K) :
    FambT a b h = MvPolynomial.aeval (chart3 K) (GhomPoly K a b h) := by
  rw [FambT, AevalGhomPoly (K := K) (A := MvPolynomial (Fin 3) K) a b h (chart3 K)]
  simp only [MvPolynomial.algebraMap_eq]
  rfl

theorem fwVec_eq_aeval (a b h : K) (i : Fin 5) :
    fwVec a b h i = MvPolynomial.aeval (chart3 K) (fwPoly K a b h i) := by
  rw [fwVec, AevalFwPoly (K := K) (A := MvPolynomial (Fin 3) K) a b h (chart3 K) i]
  simp only [MvPolynomial.algebraMap_eq]
  rfl

theorem bwVec_eq_aeval (a b h : K) (i : Fin 5) :
    bwVec a b h i = MvPolynomial.aeval (chart3 K) (bwPoly K a b h i) := by
  rw [bwVec, AevalBwPoly (K := K) (A := MvPolynomial (Fin 3) K) a b h (chart3 K) i]
  simp only [MvPolynomial.algebraMap_eq]
  rfl

/-! ## Homogeneity of the chart equations in the coordinate vector -/

/-- `kleinTwFhom` is homogeneous of degree `11` in its vector argument. -/
theorem aeval_smul_FhomPoly {A : Type*} [CommRing A] [Algebra K A] (a b h : K) (c : A)
    (y : Fin 5 → A) :
    MvPolynomial.aeval (fun i => c * y i) (FhomPoly K a b h)
      = c ^ 11 * MvPolynomial.aeval y (FhomPoly K a b h) := by
  simp only [AevalFhomPoly, kleinTwFhom_smul]

/-- `kleinTwGhomV` is homogeneous of degree `8` in its vector argument. -/
theorem aeval_smul_GhomPoly {A : Type*} [CommRing A] [Algebra K A] (a b h : K) (c : A)
    (y : Fin 5 → A) :
    MvPolynomial.aeval (fun i => c * y i) (GhomPoly K a b h)
      = c ^ 8 * MvPolynomial.aeval y (GhomPoly K a b h) := by
  simp only [AevalGhomPoly, kleinTwGhomV_smul]

/-- The forward chart map `f̂ = kleinTwP ∘ kleinTwStereo` is homogeneous of degree `4`. -/
theorem kleinTwP_kleinTwStereo_smul {R : Type*} [CommRing R] (a b h c : R) (p v : Fin 5 → R)
    (k : Fin 5) :
    kleinTwP a b h (kleinTwStereo a b h p (fun i => c * v i)) k
      = c ^ 4 * kleinTwP a b h (kleinTwStereo a b h p v) k := by
  rw [kleinTwStereo_smul, kleinTwP_homog]
  first | refl_ring1 | ring

/-- The projection `π_p` is linear. -/
theorem kleinTwPi_smul {R : Type*} [CommRing R] (p x : Fin 5 → R) (c : R) :
    kleinTwPi p (fun i => c * x i) = fun i => c * kleinTwPi p x i := by
  funext i
  simp only [kleinTwPi]
  first | refl_ring1 | ring

/-- `ǧ = kleinTwPi p ∘ kleinTwR` is homogeneous of degree `3`. -/
theorem kleinTwPi_kleinTwR_smul {R : Type*} [CommRing R] (a b h c : R) (p z : Fin 5 → R) :
    kleinTwPi p (kleinTwR a b h (fun i => c * z i))
      = fun k => c ^ 3 * kleinTwPi p (kleinTwR a b h z) k := by
  rw [kleinTwR_homog, kleinTwPi_smul]

/-- `fwPoly` is homogeneous of degree `4` in the coordinate vector. -/
theorem aeval_smul_fwPoly {A : Type*} [CommRing A] [Algebra K A] (a b h : K) (c : A)
    (y : Fin 5 → A) (j : Fin 5) :
    MvPolynomial.aeval (fun i => c * y i) (fwPoly K a b h j)
      = c ^ 4 * MvPolynomial.aeval y (fwPoly K a b h j) := by
  simp only [AevalFwPoly, kleinTwP_kleinTwStereo_smul]

/-- `bwPoly` is homogeneous of degree `3` in the coordinate vector. -/
theorem aeval_smul_bwPoly {A : Type*} [CommRing A] [Algebra K A] (a b h : K) (c : A)
    (y : Fin 5 → A) (j : Fin 5) :
    MvPolynomial.aeval (fun i => c * y i) (bwPoly K a b h j)
      = c ^ 3 * MvPolynomial.aeval y (bwPoly K a b h j) := by
  simp only [AevalBwPoly, kleinTwPi_kleinTwR_smul]

end Work.MotK.TGen
