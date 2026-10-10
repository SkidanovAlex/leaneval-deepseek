/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.ChartMaps
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.BwVec4Defs` — the cubic `bwVec a b h 4` in normal form

`bwVec a b h 4 = ǧ₄` is the fourth component of the inverse link map `χ = π_p ∘ kleinTwR` on the
affine chart `{v₀ = 0, v₄ = 1}`; it is the denominator of the affine coordinates of `χ`, i.e. the
strict transform of the hyperplane `{w₄ = 0}` under `kleinTwR`.  It is a *cubic* in
`K[x₀,x₁,x₂] = MvPolynomial (Fin 3) K`, and this file puts it in the normal form

  `bwF a b h = γ - β · X₂`   (`γ = C (a²b²h)·X₁³ + C (a³bh)·X₀²`, `β = C (ab³) + C (a⁴h)·X₀X₁`),

i.e. a polynomial of degree one in `X₂` with coefficients `β, γ ∈ K[X₀,X₁]`.  The two
`Fin 3 → Polynomial (Fin 2)` reductions used below are

* `bwVec_four_eq : bwVec a b h 4 = bwF a b h` — the explicit cubic (a pure `ring` computation);
* `bwTau : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K)`, `X₂ ↦ X`,
  `X₀ ↦ C X₀`, `X₁ ↦ C X₁` (`MvPolynomial.renameEquiv` composed with
  `MvPolynomial.finSuccEquiv`), with `bwTau_bwF : bwTau (bwF a b h) = bwFpoly a b h` where
  `bwFpoly a b h = Polynomial.C (bwGamma a b h) - Polynomial.C (bwBeta a b h) * Polynomial.X`.

The evaluation map `bwTheta a b h : (K[X₀,X₁])[X] →ₐ[K] FractionRing (K[X₀,X₁])` with
`X ↦ γ/β` is the map of which the kernel is computed in `Submission/Work/MotK/TGen/BwVec4Ker.lean`;
here we record the three evaluations `bwTheta_C`, `bwTheta_X`, `bwTheta_Fpoly` and the non-vanishing
`bwBeta_ne_zero`.

## The mathematics of the normal form

For `a, b, h ≠ 0`

  `β = C a · (C (b³) + C (a³h)·X₀X₁)`,  `γ = C a · (C (ab²h)·X₁³ + C (a²bh)·X₀²)`,

so `β` is a unit multiple of the primitive (in `X₀`) linear polynomial `C (b³) + C (a³h)·X₀X₁`:
`β` is *prime* in `K[X₀,X₁]`, and `β ∤ γ` because `γ` has `X₀`-degree `2` while
`C (b³) + C (a³h)X₀X₁` has `X₀`-degree `1` with `X₀²`-coefficient comparison giving the
contradiction `C (a³h)X₁·q₁ = C (a²bh)`.  Consequently `bwFpoly` is irreducible (hence prime) in
the UFD `K[X₀,X₁][X]`, and the map `bwTheta` has kernel exactly `(bwFpoly)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

noncomputable section

variable {K : Type} [Field K]

/-! ## The variable identification `K[X₀,X₁,X₂] ≃ₐ[K] K[X₀,X₁][X]` with `X₂ ↦ X` -/

/-- The cyclic permutation `0 ↦ 1 ↦ 2 ↦ 0` of `Fin 3`. -/
def bwC3 : Fin 3 ≃ Fin 3 where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

@[simp] theorem bwC3_zero : bwC3 0 = (1 : Fin 3) := rfl
@[simp] theorem bwC3_one : bwC3 1 = (2 : Fin 3) := rfl
@[simp] theorem bwC3_two : bwC3 2 = (0 : Fin 3) := rfl

/-- The `K`-algebra isomorphism `K[X₀,X₁,X₂] ≃ₐ[K] K[X₀,X₁][X]` sending `X₂` to the polynomial
variable `X`, `X₀` to `C X₀` and `X₁` to `C X₁`. -/
def bwTau (K : Type) [Field K] :
    MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  (MvPolynomial.renameEquiv K bwC3).trans (MvPolynomial.finSuccEquiv K 2)

theorem bwTau_X_zero : bwTau K (MvPolynomial.X 0) = Polynomial.C (MvPolynomial.X 0) := by
  rw [bwTau, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    bwC3_zero]
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl]
  exact MvPolynomial.finSuccEquiv_X_succ

theorem bwTau_X_one : bwTau K (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 1) := by
  rw [bwTau, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    bwC3_one]
  rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl]
  exact MvPolynomial.finSuccEquiv_X_succ

theorem bwTau_X_two : bwTau K (MvPolynomial.X 2) = Polynomial.X := by
  rw [bwTau, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    bwC3_two]
  exact MvPolynomial.finSuccEquiv_X_zero

theorem bwTau_C (K : Type) [Field K] (r : K) :
    bwTau K (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [← MvPolynomial.algebraMap_eq K (Fin 3), (bwTau K).commutes,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq K (Fin 2)]

/-! ## The cubic `bwVec a b h 4` and its normal form -/

/-- The coefficient of `X₂` in the normal form of `bwVec a b h 4`:
`β = a b³ + a⁴h·X₀X₁ ∈ K[X₀,X₁]`. -/
def bwBeta (a b h : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (a * b ^ 3) + MvPolynomial.C (a ^ 4 * h) * MvPolynomial.X 0 * MvPolynomial.X 1

/-- The constant term of the normal form of `bwVec a b h 4`:
`γ = a²b²h·X₁³ + a³bh·X₀² ∈ K[X₀,X₁]`. -/
def bwGamma (a b h : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (a ^ 2 * b ^ 2 * h) * MvPolynomial.X 1 ^ 3
    + MvPolynomial.C (a ^ 3 * b * h) * MvPolynomial.X 0 ^ 2

/-- The explicit cubic `bwVec a b h 4 = γ - β·X₂ ∈ K[X₀,X₁,X₂]`. -/
def bwF (a b h : K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.C (a ^ 2 * b ^ 2 * h) * MvPolynomial.X 1 ^ 3
    + MvPolynomial.C (a ^ 3 * b * h) * MvPolynomial.X 0 ^ 2
    - MvPolynomial.C (a * b ^ 3) * MvPolynomial.X 2
    - MvPolynomial.C (a ^ 4 * h) * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2

/-- The normal form of `bwVec a b h 4` in `K[X₀,X₁][X]`: `C γ - C β · X`
(so that in the quotient, `β · x = γ`). -/
def bwFpoly (a b h : K) : Polynomial (MvPolynomial (Fin 2) K) :=
  Polynomial.C (bwGamma a b h) - Polynomial.C (bwBeta a b h) * Polynomial.X

/-- **The cubic `bwVec a b h 4` in explicit form.**  This is the fourth component of
`χ = π_p ∘ kleinTwR` on the chart `{v₀ = 0, v₄ = 1}`, at the rational point `p = kleinPointT`;
the fourth coordinate of `π_p x = x - x₀·p` contributes nothing because `p₄ = 0`. -/
theorem bwVec_four_eq (a b h : K) : bwVec a b h 4 = bwF a b h := by
  simp only [bwVec, Work.MotK.kleinTwPi, Work.MotK.pRa_apply, Work.MotK.kleinPointT,
    Work.MotK.chart3, Work.MotK.kleinTwR_four, Work.MotK.kleinTwR4, bwF]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_succ]
  first | refl_ring1 | ring

/-- The normal form of the cubic under the variable identification `bwTau`. -/
theorem bwTau_bwF (a b h : K) : bwTau K (bwF a b h) = bwFpoly a b h := by
  simp only [bwF, bwFpoly, bwBeta, bwGamma, map_add, map_sub, map_mul, map_pow]
  rw [bwTau_X_zero, bwTau_X_one, bwTau_X_two]
  simp only [bwTau_C]
  first | refl_ring1 | ring

theorem bwBeta_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) : bwBeta a b h ≠ 0 := by
  intro hc
  have h := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : K))) hc
  simp only [bwBeta, map_zero, map_add, map_mul, map_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, mul_zero, add_zero] at h
  exact (mul_ne_zero ha (pow_ne_zero 3 hb)) h

/-! ## The evaluation map `X ↦ γ/β` -/

/-- The `K`-algebra homomorphism `K[X₀,X₁][X] →ₐ[K] FractionRing (K[X₀,X₁])` sending the
indeterminate to `γ/β`; its kernel is the ideal generated by `bwFpoly a b h` (see
`Submission/Work/MotK/TGen/BwVec4Ker.lean`). -/
def bwTheta (a b h : K) :
    Polynomial (MvPolynomial (Fin 2) K) →ₐ[K] FractionRing (MvPolynomial (Fin 2) K) :=
  (Polynomial.aeval (algebraMap (MvPolynomial (Fin 2) K)
      (FractionRing (MvPolynomial (Fin 2) K)) (bwGamma a b h) *
    (algebraMap (MvPolynomial (Fin 2) K)
      (FractionRing (MvPolynomial (Fin 2) K)) (bwBeta a b h))⁻¹)).restrictScalars K

theorem bwTheta_C (a b h : K) (p : MvPolynomial (Fin 2) K) :
    bwTheta a b h (Polynomial.C p) = algebraMap _ _ p := by
  simp [bwTheta]

theorem bwTheta_X (a b h : K) :
    bwTheta a b h Polynomial.X
      = algebraMap _ _ (bwGamma a b h) * (algebraMap _ _ (bwBeta a b h))⁻¹ := by
  simp [bwTheta]

theorem bwTheta_Fpoly (a b h : K) (hβ : bwBeta a b h ≠ 0) :
    bwTheta a b h (bwFpoly a b h) = 0 := by
  have h0 : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (bwBeta a b h) ≠ 0 := fun hc => hβ (IsFractionRing.injective _ _
        (by rw [hc, map_zero]))
  have key : (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (bwBeta a b h)) *
      ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (bwGamma a b h)) *
        ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (bwBeta a b h)))⁻¹) =
      algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (bwGamma a b h) := by
    rw [← mul_assoc, mul_comm (algebraMap _ _ (bwBeta a b h)) (algebraMap _ _ (bwGamma a b h)),
      mul_assoc, mul_inv_cancel₀ h0, mul_one]
  rw [bwFpoly, map_sub, map_mul, bwTheta_C a b h (bwGamma a b h),
    bwTheta_C a b h (bwBeta a b h), bwTheta_X a b h, key, sub_self]

end

end Work.MotK.TGen
