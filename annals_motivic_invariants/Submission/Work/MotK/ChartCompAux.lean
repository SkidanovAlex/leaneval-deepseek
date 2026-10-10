/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.LinkCertDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary lemmas for `Work.MotK.ChartCompC`

`Work.MotK.ChartCompC` (`Submission/Work/MotK/ChartCompC.lean`) states that the two affine chart
maps of the T-twisted Crauder--Katz link -- the forward map `f = P ∘ y` (whose chart coordinates
are `φ_j = f̂_{j+1}/f̂_4`) and the inverse map `χ = π_p ∘ R` (chart coordinates
`η_j = ǧ_{j+1}/ǧ_4`) -- are mutually inverse on the coordinate generators.

The present file collects the *polynomial* infrastructure used in the assembly:

* the general commutation lemmas `map_kleinTw*`, which say that a ring homomorphism `σ : R →+* S`
  commutes with the (purely polynomial) link data `kleinTwQ`, `kleinTwBilin`, `kleinTwStereo`,
  `kleinTwP`, `kleinTwPi`, `kleinTwR`, `kleinTwS`, `kleinTwSDualInv`, `kleinTwFhom`,
  `kleinTwGhom'`  (so that `aeval φ` computes the link data in the fraction field);
* the vanishing of the first coordinate `f̂_0 = 0` (the forward chart map lands in the hyperplane
  `{v₀ = 0}`), which is what makes the chart point `(0,φ,1)` proportional to the coordinate vector
  of the forward link map;
* the "division-free" rescaling `GambC = C((a·h)⁻¹)^6 · GambTil`, where `GambTil` is the source
  equation `F̃(p̃, chart)` computed at the point `p̃ = (a·h, 0, a·h, b, 0) = (a·h)·pointC` (a
  scalar multiple of `pointC` with no `1/(a·h)` entry), together with the elementary
  homogeneity/linearity lemmas it rests on.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK

/-! ## Commutation of the link data with a ring homomorphism -/

section Commute

variable {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S)

theorem map_kleinTwQ (a b h : R) (y : Fin 5 → R) :
    σ (kleinTwQ a b h y) = kleinTwQ (σ a) (σ b) (σ h) (fun i => σ (y i)) := by
  simp only [kleinTwQ, kleinTwP0, map_add, map_mul, map_pow, map_neg, map_sub, map_ofNat]

theorem map_kleinTwBilin (a b h : R) (u v : Fin 5 → R) :
    σ (kleinTwBilin a b h u v) = kleinTwBilin (σ a) (σ b) (σ h) (fun i => σ (u i))
      (fun i => σ (v i)) := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply, map_add, map_mul, map_pow, map_neg,
    map_sub, map_ofNat]

theorem map_kleinTwStereo (a b h : R) (p v : Fin 5 → R) :
    (fun i => σ (kleinTwStereo a b h p v i)) = kleinTwStereo (σ a) (σ b) (σ h)
      (fun i => σ (p i)) (fun i => σ (v i)) := by
  funext i
  simp only [kleinTwStereo, kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply, map_add, map_mul,
    map_pow, map_neg, map_sub, map_ofNat]

theorem map_kleinTwP (a b h : R) (y : Fin 5 → R) :
    (fun i => σ (kleinTwP a b h y i)) = kleinTwP (σ a) (σ b) (σ h) (fun i => σ (y i)) := by
  funext i
  fin_cases i <;>
    simp only [kleinTwP, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4, Fin.mk_zero,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, map_add, map_mul, map_pow,
      map_neg, map_sub, map_ofNat] <;>
    first | refl_ring1 | ring

theorem map_kleinTwPi (p x : Fin 5 → R) :
    (fun i => σ (kleinTwPi p x i)) = kleinTwPi (fun i => σ (p i)) (fun i => σ (x i)) := by
  funext i
  simp only [kleinTwPi, map_sub, map_mul]

theorem map_kleinTwR (a b h : R) (y : Fin 5 → R) :
    (fun i => σ (kleinTwR a b h y i)) = kleinTwR (σ a) (σ b) (σ h) (fun i => σ (y i)) := by
  funext i
  fin_cases i <;>
    simp only [kleinTwR, kleinTwR0, kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4, Fin.mk_zero,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, map_add, map_mul, map_pow,
      map_neg, map_sub, map_ofNat] <;>
    first | refl_ring1 | ring

theorem map_kleinTwS (a b h : R) (y : Fin 5 → R) :
    σ (kleinTwS a b h y) = kleinTwS (σ a) (σ b) (σ h) (fun i => σ (y i)) := by
  simp only [kleinTwS, map_add, map_mul, map_pow, map_neg, map_sub, map_ofNat]

theorem map_kleinTwSDualInv (a b h : R) (y : Fin 5 → R) :
    σ (kleinTwSDualInv a b h y) = kleinTwSDualInv (σ a) (σ b) (σ h) (fun i => σ (y i)) := by
  simp only [kleinTwSDualInv, map_add, map_mul, map_pow, map_neg, map_sub, map_ofNat]

theorem map_kleinTwFhom (a b h : R) (p v : Fin 5 → R) :
    σ (kleinTwFhom a b h p v) = kleinTwFhom (σ a) (σ b) (σ h) (fun i => σ (p i))
      (fun i => σ (v i)) := by
  simp only [kleinTwFhom, map_mul]
  rw [map_kleinTwBilin σ, map_kleinTwS σ, map_kleinTwStereo σ]

theorem map_kleinTwGhom' (a b h : R) (p w : Fin 5 → R) :
    σ (kleinTwGhom' a b h p w) = kleinTwGhom' (σ a) (σ b) (σ h) (fun i => σ (p i))
      (fun i => σ (w i)) := by
  simp only [kleinTwGhom', map_mul]
  rw [map_kleinTwBilin σ, map_kleinTwSDualInv σ, map_kleinTwR σ]

end Commute

/-! ## The first coordinate of the forward chart map vanishes -/

section Zero

variable {K : Type*} [Field K]

@[simp] theorem pRaC_apply (a b h : K) (i : Fin 5) :
    pRaC K a b h i = MvPolynomial.C (pointC K a b h i) := rfl

@[simp] theorem pointC_apply_zero (a b h : K) : pointC K a b h 0 = 1 := rfl
@[simp] theorem pointC_apply_one (a b h : K) : pointC K a b h 1 = 0 := rfl
@[simp] theorem pointC_apply_two (a b h : K) : pointC K a b h 2 = 1 := rfl
@[simp] theorem pointC_apply_three (a b h : K) : pointC K a b h 3 = b / (a * h) := rfl
@[simp] theorem pointC_apply_four (a b h : K) : pointC K a b h 4 = 0 := rfl


@[simp] theorem chartC_apply (i : Fin 5) :
    chartC K i = (![0, (MvPolynomial.X 0 : MvPolynomial (Fin 3) K),
      MvPolynomial.X 1, MvPolynomial.X 2, 1]) i := rfl

/-- The `0`-th component of the forward chart map vanishes: the stereographic parametrisation of
the quadric lies on `{p₀ = 0}` (`kleinTwP0 (y v) = kleinTwQ (y v) = kleinTwQ v ^ 2 * kleinTwQ p`,
and `kleinTwQ pRaC = 0`). -/
theorem fhatC_zero (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) : fhatC K a b h 0 = 0 := by
  rw [show fhatC K a b h 0 = kleinTwQ (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (pRaC K a b h) (chartC K)) from rfl]
  rw [KleinTwQ_stereo, kleinTwQ_pRaC K a b h ha hh, mul_zero]

theorem ghatC_zero (a b h : K) : ghatC K a b h 0 = 0 := by
  simp only [ghatC, kleinTwPi, chartC, pRaC, pointC, pointC_apply_zero, Fin.isValue,
    Matrix.cons_val, MvPolynomial.C_1, mul_one, sub_self]

end Zero

/-! ## The source equation at the division-free point `p̃` -/

section Til

variable (K : Type*) [CommRing K]

/-- The `K`-rational point `p̃ = (a·h, 0, a·h, b, 0) = (a·h)·pointC` of the twisted quadric, as a
vector of constants of the chart ring.  Unlike `pRaC = pointC` it has no `1/(a·h)` entry, which
makes the polynomial identities involving it (in particular the nonvanishing of the source
equation) division-free. -/
def ptilPt (K : Type*) [CommRing K] (a b h : K) : Fin 5 → K
  | 0 => a * h
  | 1 => 0
  | 2 => a * h
  | 3 => b
  | 4 => 0

/-- The point `p̃` as a vector of constants of the chart ring. -/
noncomputable def ptilVec (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  fun i => MvPolynomial.C (ptilPt K a b h i)

@[simp] theorem ptilPt_apply_zero (a b h : K) : ptilPt K a b h 0 = a * h := rfl
@[simp] theorem ptilPt_apply_one (a b h : K) : ptilPt K a b h 1 = 0 := rfl
@[simp] theorem ptilPt_apply_two (a b h : K) : ptilPt K a b h 2 = a * h := rfl
@[simp] theorem ptilPt_apply_three (a b h : K) : ptilPt K a b h 3 = b := rfl
@[simp] theorem ptilPt_apply_four (a b h : K) : ptilPt K a b h 4 = 0 := rfl

/-- The source equation `F̃(p̃, chartC)` of the twisted link evaluated at the division-free point
`p̃`; it equals `(a·h)^6 · GambC` (see `GambC_eq_C_mul_GambTil`). -/
noncomputable def GambTil (a b h : K) : MvPolynomial (Fin 3) K :=
  kleinTwFhom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (ptilVec K a b h)
    (chartC K)

end Til

section TilField

variable {K : Type*} [Field K]

/-- `pRaC` is the scalar multiple `(a·h)⁻¹ • p̃` of `ptilVec`. -/
theorem pointC_eq_inv_mul_ptilPt (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) (i : Fin 5) :
    pointC K a b h i = (a * h)⁻¹ * ptilPt K a b h i := by
  have hah : a * h ≠ 0 := mul_ne_zero ha hh
  fin_cases i <;>
    simp only [pointC, ptilPt] <;>
    first
      | (rw [mul_zero])
      | (rw [inv_mul_cancel₀ hah])
      | (rw [div_eq_mul_inv, mul_comm])

theorem pRaC_eq_C_mul_ptilVec (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    pRaC K a b h = fun i => MvPolynomial.C ((a * h)⁻¹) * ptilVec K a b h i := by
  funext i
  simp only [pRaC, ptilVec]
  rw [pointC_eq_inv_mul_ptilPt a b h ha hh i, MvPolynomial.C_mul]

/-- The polar form is linear in its *first* argument. -/
theorem kleinTwBilin_smul_left {R : Type*} [CommRing R] (a b h c : R) (u v : Fin 5 → R) :
    kleinTwBilin a b h (fun i => c * u i) v = c * kleinTwBilin a b h u v := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply]
  first | refl_ring1 | ring

/-- The inverse stereographic projection is linear in the point `p` it is taken from. -/
theorem kleinTwStereo_smul_left {R : Type*} [CommRing R] (a b h c : R) (p v : Fin 5 → R) :
    kleinTwStereo a b h (fun i => c * p i) v = fun i => c * kleinTwStereo a b h p v i := by
  funext i
  simp only [kleinTwStereo, kleinTwBilin_smul_left, Pi.sub_apply]
  first | refl_ring1 | ring

/-- The source equation is homogeneous of degree `6` in the point `p`: the polar form is linear and
the secant quintic `S ∘ y` is homogeneous of degree `5`. -/
theorem kleinTwFhom_smul_left {R : Type*} [CommRing R] (a b h c : R) (p v : Fin 5 → R) :
    kleinTwFhom a b h (fun i => c * p i) v = c ^ 6 * kleinTwFhom a b h p v := by
  simp only [kleinTwFhom]
  rw [kleinTwBilin_smul_left, kleinTwStereo_smul_left, kleinTwS_homog]
  first | refl_ring1 | ring

/-- `GambC` is `(a·h)⁻¹` to the power `6` times the division-free `GambTil`. -/
theorem GambC_eq_C_mul_GambTil (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    GambC K a b h = MvPolynomial.C ((a * h)⁻¹) ^ 6 * GambTil K a b h := by
  rw [GambC, pRaC_eq_C_mul_ptilVec (K := K) a b h ha hh]
  change kleinTwFhom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (fun i => MvPolynomial.C ((a * h)⁻¹) * ptilVec K a b h i) (chartC K)
    = MvPolynomial.C ((a * h)⁻¹) ^ 6 * GambTil K a b h
  rw [kleinTwFhom_smul_left, GambTil]

end TilField

end Work.MotK
