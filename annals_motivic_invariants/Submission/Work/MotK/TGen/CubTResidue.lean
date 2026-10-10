/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.CubTDefs
import Submission.Work.MotK.TGen.CubTThetaAux
import Submission.Work.MotK.TGen.CubTFracRange
import Submission.Work.CrauderKatz.BlowUp.fractionRing_mvPolynomial_finTwo
import Submission.Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotK.TGen.CubTResidue` — the residue field of the cubic `cubTRed = 0` is `K(u)(v)`

The cubic `cubTRed a b h` (see `Submission/Work/MotK/TGen/CubTRedDefs.lean`) defines the "junk"
(cone) divisor `D` of the target side of the `T`-twisted Crauder–Katz link.  `D` is a rational
surface: it is birational to the quadric cone `S'`, which is parametrised by the plane via

  `thetaMap a b h : K[x₀,x₁,x₂] →ₐ[K] K(u,v)`,  `x_i ↦ P_{i+1}(y)/P_4(y)`,

`y = paraPt a b h` (see `Submission/Work/MotK/TGen/CubTPara.lean`).  This file assembles the fact
that the residue field of the point `⟨(cubTRed), hprime⟩` of `𝔸³_K` is the iterated rational
function field `RatFunc (RatFunc K) = K(u)(v)`.

The ingredients (all in this directory) are

* `cubQd_four_ne_zero`   : the denominator `D = cubQd a b h 4` of the parametrisation does not vanish;
* `thetaMap_rvec_mul`: `thetaMap a b h (rvec a b h j) · D³ = (s (cubY) · cubY j)` — the two
  "mutually inverse" descriptions of the link map;
* `cubLamY`, `cubLamRvec` (`CubTDefs`): the linear form `Λ(z) = -2ab·z₀ + a²h·z₃ + ab·z₂` vanishes
  at `cubY` and pulls `cubTRed` back;
* `CubTThetaKernel`: `ker (thetaMap a b h)` has height one;
* `CubTFracRange` : the fraction field of `thetaMap a b h`.range is `RatFunc (RatFunc K)`.

Combining: `thetaMap` kills `cubTRed`, so `(cubTRed) ⊆ ker θ`; both are prime ideals of height one,
so `ker θ = (cubTRed)`; hence the residue field `K[x] ⧸ (cubTRed)` is the fraction field of the
image of `thetaMap`, which is `RatFunc (RatFunc K)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

universe u

variable (K : Type) [Field K]



/-- The residue field at the kernel of an algebra homomorphism into a domain is the fraction ring of
its range.  (Local copy of `Work.MotK.TGen.fractionRing_quotient_ker_algEquiv`; kept `private`
because `Submission/Work/MotK/TGen/FwVec4ResF.lean` declares the *same* name, and the two modules
are imported together in the census closure of `Work.MotK.LinkCertT`.) -/
private theorem fractionRing_quotient_ker_algEquiv {R S : Type} [CommRing R] [Algebra K R]
    [CommRing S] [IsDomain S] [Algebra K S] (f : R →ₐ[K] S) :
    Nonempty (FractionRing (R ⧸ RingHom.ker f) ≃ₐ[K] FractionRing f.range) := by
  have i : (R ⧸ RingHom.ker f) ≃ₐ[K] ↥f.range :=
    (AlgHom.ker_rangeRestrict f).symm ▸
      Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective f)
  exact ⟨IsFractionRing.algEquivOfAlgEquiv i⟩

/-- The linear form `Λ(z) = -2ab·z₀ + a²h·z₃ + ab·z₂` of `CubTFactor`, as a polynomial in
`K[x₀,x₁,x₂]`. -/
noncomputable def cubLam (a b h : K) (z : Fin 5 → MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 3) K :=
  -(2 * C a * C b) * z 0 + (C a ^ 2 * C h) * z 3 + (C a * C b) * z 2

/-- `algebraMap` commutes with the linear form `cubLam` (on `K[u,v]`-valued vectors). -/
theorem algebraMap_cubLam_mul (a b h : K) (S : MvPolynomial (Fin 2) K)
    (z : Fin 5 → MvPolynomial (Fin 2) K) :
    algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (S * (-(2 * C a * C b) * z 0 + (C a ^ 2 * C h) * z 3 + (C a * C b) * z 2))
      = -(2 * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
            * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (S * z 0)
        + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a ^ 2
            * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (S * z 3)
        + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
            * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (S * z 2) := by
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_ofNat, MvPolynomial.C_eq_algebraMap,
    IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 2) K)
      (FractionRing (MvPolynomial (Fin 2) K))] <;> ring

/-- `thetaMap` commutes with the linear form `cubLam` (on `K[x₀,x₁,x₂]`-valued vectors). -/
theorem thetaMap_cubLam (a b h : K) (z : Fin 5 → MvPolynomial (Fin 3) K) :
    thetaMap a b h (-(2 * C a * C b) * z 0 + (C a ^ 2 * C h) * z 3 + (C a * C b) * z 2)
      = -(2 * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
            * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
          * thetaMap a b h (z 0)
        + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a ^ 2
            * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
          * thetaMap a b h (z 3)
        + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
            * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
          * thetaMap a b h (z 2) := by
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, MvPolynomial.C_eq_algebraMap,
    AlgHom.commutes] <;> ring

/-- **`thetaMap` kills `cubTRed`.** -/
theorem thetaMap_cubTRed (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    thetaMap a b h (cubTRed a b h) = 0 := by
  have hQ : ∀ j : Fin 5, thetaMap a b h (rvec a b h j)
      * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (cubQd a b h 4)) ^ 3
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (kleinTwS (C a) (C b) (C h) (cubY a b h) * cubY a b h j) :=
    fun j => thetaMap_rvec_mul a b h ha hb hh j
  have hD : (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (cubQd a b h 4)) ≠ 0 := fun h0 => cubQd_four_ne_zero a b h ha hb hh
        (IsFractionRing.injective (MvPolynomial (Fin 2) K)
          (FractionRing (MvPolynomial (Fin 2) K)) (by rw [h0, map_zero]))
  have hD3 : (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (cubQd a b h 4)) ^ 3 ≠ 0 := pow_ne_zero 3 hD
  -- `algebraMap (a·b·h) · thetaMap (cubTRed) = Λ (thetaMap (rvec))`
  have hL1 : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (C (a * b * h)) * thetaMap a b h (cubTRed a b h)
      = -(2 * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
            * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
          * thetaMap a b h (rvec a b h 0)
        + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a ^ 2
            * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
          * thetaMap a b h (rvec a b h 3)
        + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
            * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
          * thetaMap a b h (rvec a b h 2) := by
    have hC : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (C (a * b * h)) = thetaMap a b h (C (a * b * h)) := by
      rw [MvPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply K
        (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))]
      exact ((thetaMap a b h).commutes (a * b * h)).symm
    rw [hC, ← map_mul, ← cubLamRvec K a b h ha hb hh]
    exact thetaMap_cubLam K a b h (rvec a b h)
  have hmain : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (C (a * b * h))
      * (thetaMap a b h (cubTRed a b h)
        * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (cubQd a b h 4)) ^ 3) = 0 := by
    have h1 : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (C (a * b * h))
        * (thetaMap a b h (cubTRed a b h)
          * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (cubQd a b h 4)) ^ 3)
        = (-(2 * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
              * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              * thetaMap a b h (rvec a b h 0)
            + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a ^ 2
                * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
              * thetaMap a b h (rvec a b h 3)
            + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
                * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              * thetaMap a b h (rvec a b h 2))
          * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (cubQd a b h 4)) ^ 3 := by
      rw [← mul_assoc, hL1]
    rw [h1]
    rw [show (-(2 * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
              * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              * thetaMap a b h (rvec a b h 0)
            + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a ^ 2
                * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
              * thetaMap a b h (rvec a b h 3)
            + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
                * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              * thetaMap a b h (rvec a b h 2))
          * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (cubQd a b h 4)) ^ 3
        = -(2 * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
              * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              * (thetaMap a b h (rvec a b h 0)
                  * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
                      (cubQd a b h 4)) ^ 3)
            + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a ^ 2
                * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) h)
              * (thetaMap a b h (rvec a b h 3)
                  * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
                      (cubQd a b h 4)) ^ 3)
            + (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a
                * algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              * (thetaMap a b h (rvec a b h 2)
                  * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
                      (cubQd a b h 4)) ^ 3) from by ring]
    rw [hQ 0, hQ 3, hQ 2,
      ← algebraMap_cubLam_mul K a b h (kleinTwS (C a) (C b) (C h) (cubY a b h)) (cubY a b h)]
    rw [show -(2 * C a * C b) * cubY a b h 0 + (C a ^ 2 * C h) * cubY a b h 3
          + (C a * C b) * cubY a b h 2 = 0 from cubLamY a b h, mul_zero, map_zero]
  have habh : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (C (a * b * h)) ≠ 0 := by
    intro h0
    exact (MvPolynomial.C_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha hb) hh))
      (IsFractionRing.injective (MvPolynomial (Fin 2) K)
        (FractionRing (MvPolynomial (Fin 2) K)) (by rw [h0, map_zero]))
  rcases mul_eq_zero.mp hmain with h | h
  · exact absurd h habh
  · rcases mul_eq_zero.mp h with h1 | h1
    · exact h1
    · exact absurd h1 hD3


/-- The denominator `cubQd a b h 4` of the parametrisation does not vanish in `K(u,v)`. -/
theorem thetaMap_qd_four_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (cubQd a b h 4)) ≠ 0 := fun h0 => cubQd_four_ne_zero a b h ha hb hh
        (IsFractionRing.injective (MvPolynomial (Fin 2) K)
          (FractionRing (MvPolynomial (Fin 2) K)) (by rw [h0, map_zero]))

/-- `thetaMap (rvec a b h 4) ≠ 0`: the common denominator of the inverse parametrisation is a unit
of `K(u,v)`. -/
theorem ker_theta_rvec_four (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    thetaMap a b h (rvec a b h 4) ≠ 0 := by
  intro hcon
  have h4 := thetaMap_rvec_mul a b h ha hb hh 4
  rw [hcon, zero_mul] at h4
  have hS : kleinTwS (C a) (C b) (C h) (cubY a b h) * cubY a b h 4 ≠ 0 :=
    mul_ne_zero (cubS_ne_zero a b h ha hb hh)
      (MvPolynomial.C_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha (pow_ne_zero 3 hb)) hh))
  refine hS (IsFractionRing.injective (MvPolynomial (Fin 2) K)
    (FractionRing (MvPolynomial (Fin 2) K)) (by rw [h4.symm, map_zero]))

/-- `thetaMap (rvec a b h 0) = u · thetaMap (rvec a b h 4)`: the inverse parametrisation recovers
the first coordinate `u` of the parametrising plane. -/
theorem ker_theta_rvec_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    thetaMap a b h (rvec a b h 0)
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (X 0)
        * thetaMap a b h (rvec a b h 4) := by
  have h0 := thetaMap_rvec_mul a b h ha hb hh 0
  have h4 := thetaMap_rvec_mul a b h ha hb hh 4
  have hD3 : (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (cubQd a b h 4)) ^ 3 ≠ 0 := pow_ne_zero 3 (thetaMap_qd_four_ne_zero K a b h ha hb hh)
  have hpoly : kleinTwS (C a) (C b) (C h) (cubY a b h) * cubY a b h 0
      = (X 0 : MvPolynomial (Fin 2) K)
        * (kleinTwS (C a) (C b) (C h) (cubY a b h) * cubY a b h 4) := by
    simp only [cubY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Fin.isValue]
    first | refl_ring1 | ring
  have hkey : (thetaMap a b h (rvec a b h 0)
        - algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (X 0)
          * thetaMap a b h (rvec a b h 4))
      * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (cubQd a b h 4)) ^ 3 = 0 := by
    rw [sub_mul, mul_assoc, h0, h4, ← map_mul, hpoly, sub_self]
  rcases mul_eq_zero.mp hkey with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hD3

/-- `thetaMap (rvec a b h 3) = v · thetaMap (rvec a b h 4)`: the inverse parametrisation recovers
the second coordinate `v` of the parametrising plane. -/
theorem ker_theta_rvec_three (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    thetaMap a b h (rvec a b h 3)
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (X 1)
        * thetaMap a b h (rvec a b h 4) := by
  have h3 := thetaMap_rvec_mul a b h ha hb hh 3
  have h4 := thetaMap_rvec_mul a b h ha hb hh 4
  have hD3 : (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (cubQd a b h 4)) ^ 3 ≠ 0 := pow_ne_zero 3 (thetaMap_qd_four_ne_zero K a b h ha hb hh)
  have hpoly : kleinTwS (C a) (C b) (C h) (cubY a b h) * cubY a b h 3
      = (X 1 : MvPolynomial (Fin 2) K)
        * (kleinTwS (C a) (C b) (C h) (cubY a b h) * cubY a b h 4) := by
    simp only [cubY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Fin.isValue]
    first | refl_ring1 | ring
  have hkey : (thetaMap a b h (rvec a b h 3)
        - algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (X 1)
          * thetaMap a b h (rvec a b h 4))
      * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (cubQd a b h 4)) ^ 3 = 0 := by
    rw [sub_mul, mul_assoc, h3, h4, ← map_mul, hpoly, sub_self]
  rcases mul_eq_zero.mp hkey with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hD3

/-- A finitely generated domain `A` over a field `K` (in the same universe) whose fraction field
has transcendence degree at least two has two nested primes, one of which is non-zero.

Proof: Noether normalisation (`exists_finite_inj_algHom_of_fg`) writes `A` as a finite
`K[T₁,…,T_s]`-algebra with `s = trdeg_K (FractionRing A) ≥ 2`; the prime `(T₁)` of height one of
`K[T]` lifts to `A` by lying over, and going up lifts a chain of length two ending in a prime of
height `≥ 2`, giving a strictly increasing pair `𝔭₁ < 𝔭₂` whose lower member is non-zero
(incomparability of the integral extension). -/
theorem two_primes_of_trdeg {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (h : 2 ≤ Algebra.trdeg K (FractionRing A)) :
    ∃ 𝔭₁ 𝔭₂ : Ideal A, 𝔭₁.IsPrime ∧ 𝔭₂.IsPrime ∧ 𝔭₁ < 𝔭₂ ∧ 𝔭₁ ≠ ⊥ := by
  obtain ⟨s, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI hFin : Module.Finite (MvPolynomial (Fin s) K) A := hg_fin
  haveI hInt : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := Algebra.IsIntegral.of_finite _ _
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin s) K) A) := by
    show Function.Injective (g : MvPolynomial (Fin s) K → A)
    exact hg_inj
  haveI hFaith : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin s) K) A).mpr hinj
  -- the transcendence degree of the normalisation equals `s`
  have htrA : Algebra.trdeg K (FractionRing A) = Algebra.trdeg K A := by
    haveI : Algebra.IsAlgebraic A (FractionRing A) :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
        (C := FractionRing A)).mpr inferInstance
    have hh := trdeg_add_eq K A (A := FractionRing A)
    have hz : Algebra.trdeg A (FractionRing A) = 0 := trdeg_eq_zero
    rw [hz, add_zero] at hh
    exact hh.symm
  have htr : Algebra.trdeg K A = Algebra.trdeg K (MvPolynomial (Fin s) K) := by
    have hh := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A)
    have hz : Algebra.trdeg (MvPolynomial (Fin s) K) A = 0 := trdeg_eq_zero
    rw [hz, add_zero] at hh
    exact hh.symm
  have hs : 2 ≤ s := by
    have h2 := h
    rw [htrA, htr, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin,
      Cardinal.lift_natCast] at h2
    exact Nat.cast_le.mp h2
  -- `K[T₁, …, T_s]` has a prime of height at least two
  have hdimS : ringKrullDim (MvPolynomial (Fin s) K) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_fin]
  obtain ⟨p, hp, hpht⟩ := Ideal.exists_isPrime_le_height
    (R := MvPolynomial (Fin s) K) (n := 2) (by rw [hdimS]; exact_mod_cast hs)
  haveI := hp
  obtain ⟨l, -, hlen⟩ := Order.exists_series_of_le_height (⟨p, hp⟩ : PrimeSpectrum _)
    (n := 2) (by rw [← PrimeSpectrum.height_eq_orderHeight]; exact hpht)
  -- lift the chain of length two along the integral extension `K[T] → A`
  have hker : Ideal.under (MvPolynomial (Fin s) K) (⊥ : Ideal A)
      ≤ (RelSeries.head l).asIdeal := by
    rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨P₀, -, hP₀, hP₀over⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RelSeries.head l).asIdeal (⊥ : Ideal A) hker
  haveI := hP₀
  have hlo : P₀.LiesOver (RelSeries.head l).asIdeal := (Ideal.liesOver_iff _ _).mpr hP₀over.symm
  obtain ⟨L, hLlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P₀
  -- two of the primes of the lifted chain
  set i₁ : Fin (L.length + 1) := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin (L.length + 1) := ⟨2, by omega⟩ with hi₂
  have hlt12 : i₁ < i₂ := by
    rw [hi₁, hi₂, Fin.lt_def]
    norm_num
  refine ⟨(L i₁).asIdeal, (L i₂).asIdeal, (L i₁).isPrime, (L i₂).isPrime,
    L.strictMono hlt12, ?_⟩
  intro hbot
  set i₀ : Fin (L.length + 1) := ⟨0, by omega⟩ with hi₀
  have hlt01 : i₀ < i₁ := by
    rw [hi₀, hi₁, Fin.lt_def]
    norm_num
  have hunder := Ideal.IsIntegral.under_lt_under (R := MvPolynomial (Fin s) K)
    (I := (L i₀).asIdeal) (J := (L i₁).asIdeal) (L.strictMono hlt01)
  have hbot_under : (⊥ : Ideal A).under (MvPolynomial (Fin s) K) = ⊥ := by
    rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  rw [hbot, hbot_under] at hunder
  exact absurd hunder (not_lt_of_ge bot_le)

/-- `RatFunc K = Frac K[t]` is algebraic over `K[t]`, so `trdeg_K RatFunc K = trdeg_K K[t] = 1`. -/
lemma trdeg_ratFunc_eq_one (K : Type*) [Field K] : Algebra.trdeg K (RatFunc K) = 1 := by
  haveI : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial K) (K := RatFunc K)
      (C := RatFunc K)).mpr inferInstance
  have hz : Algebra.trdeg (Polynomial K) (RatFunc K) = 0 := trdeg_eq_zero
  have h := trdeg_add_eq K (Polynomial K) (A := RatFunc K)
  rw [hz, add_zero] at h
  rw [Polynomial.trdeg_of_isDomain] at h
  exact h.symm

/-- `trdeg_K RatFunc (RatFunc K) = 2`: the tower law, both layers contributing one. -/
lemma trdeg_ratFunc_ratFunc_eq_two (K : Type*) [Field K] :
    Algebra.trdeg K (RatFunc (RatFunc K)) = 2 := by
  have h1 : Algebra.trdeg K (RatFunc K) = 1 := trdeg_ratFunc_eq_one K
  have h2 : Algebra.trdeg (RatFunc K) (RatFunc (RatFunc K)) = 1 := by
    haveI : Algebra.IsAlgebraic (Polynomial (RatFunc K)) (RatFunc (RatFunc K)) :=
      (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial (RatFunc K))
        (K := RatFunc (RatFunc K)) (C := RatFunc (RatFunc K))).mpr inferInstance
    have hz : Algebra.trdeg (Polynomial (RatFunc K)) (RatFunc (RatFunc K)) = 0 := trdeg_eq_zero
    have h := trdeg_add_eq (RatFunc K) (Polynomial (RatFunc K)) (A := RatFunc (RatFunc K))
    rw [hz, add_zero] at h
    rw [Polynomial.trdeg_of_isDomain] at h
    exact h.symm
  have h := trdeg_add_eq K (RatFunc K) (A := RatFunc (RatFunc K))
  rw [h1, h2] at h
  rw [← h]
  norm_num


/-- **The residue field of the cubic surface `{cubTRed = 0}` is `K(u)(v)`.** -/
theorem CubTResidue (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hprime : Prime (Work.MotK.TGen.cubTRed a b h)) :
    Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸ Work.MotK.TGen.cubTIdeal a b h) ≃ₐ[K]
      RatFunc (RatFunc K)) := by
  have h4 : thetaMap a b h (cubTRed a b h) = 0 := thetaMap_cubTRed K a b h ha hb hh
  have h3 : thetaMap a b h (rvec a b h 4) ≠ 0 := ker_theta_rvec_four K a b h ha hb hh
  have h1 : thetaMap a b h (rvec a b h 0)
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (X 0)
        * thetaMap a b h (rvec a b h 4) := ker_theta_rvec_zero K a b h ha hb hh
  have h2 : thetaMap a b h (rvec a b h 3)
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (X 1)
        * thetaMap a b h (rvec a b h 4) := ker_theta_rvec_three K a b h ha hb hh
  -- the kernel of `thetaMap` has height one
  have hheightKer : (RingHom.ker (thetaMap a b h)).height = 1 := by
    set P : Ideal (MvPolynomial (Fin 3) K) := RingHom.ker (thetaMap a b h) with hP
    haveI hPprime : P.IsPrime := RingHom.ker_isPrime _
    -- The fraction field of `K[x₀,x₁,x₂] ⧸ ker θ` is the two-variable rational function field.
    have htr : 2 ≤ Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ P)) := by
      obtain ⟨e⟩ := CubTFracRange a b h ha hb hh h3 h1 h2
      have e1 : (MvPolynomial (Fin 3) K ⧸ RingHom.ker (thetaMap a b h)) ≃ₐ[K]
          (thetaMap a b h).range :=
        Ideal.quotientKerEquivRange (thetaMap a b h)
      obtain ⟨e2⟩ := Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv e1
      have e3 : FractionRing (MvPolynomial (Fin 3) K ⧸ P) ≃ₐ[K] RatFunc (RatFunc K) := e2.trans e
      have hte := AlgEquiv.trdeg_eq e3
      rw [hte, trdeg_ratFunc_ratFunc_eq_two]
    -- Two nested primes in the quotient, and their pullbacks to `K[x₀,x₁,x₂]`.
    obtain ⟨𝔭₁, 𝔭₂, h𝔭₁, h𝔭₂, hlt, hne⟩ :=
      two_primes_of_trdeg (A := MvPolynomial (Fin 3) K ⧸ P) htr
    haveI := h𝔭₁
    haveI := h𝔭₂
    have hQ₁prime : (𝔭₁.comap (Ideal.Quotient.mk P)).IsPrime := Ideal.comap_isPrime _ _
    have hQ₂prime : (𝔭₂.comap (Ideal.Quotient.mk P)).IsPrime := Ideal.comap_isPrime _ _
    haveI := hQ₁prime
    haveI := hQ₂prime
    have hPQ₁ : P ≤ 𝔭₁.comap (Ideal.Quotient.mk P) := by
      have h := Ideal.ker_le_comap (Ideal.Quotient.mk P) (K := 𝔭₁)
      rwa [Ideal.mk_ker] at h
    have hlt₁ : P < 𝔭₁.comap (Ideal.Quotient.mk P) := by
      refine lt_of_le_of_ne hPQ₁ fun heq => hne ?_
      have hm := Ideal.map_comap_of_surjective (Ideal.Quotient.mk P)
        Ideal.Quotient.mk_surjective 𝔭₁
      have hmap : Ideal.map (Ideal.Quotient.mk P) (Ideal.comap (Ideal.Quotient.mk P) 𝔭₁) = ⊥ := by
        rw [heq.symm, Ideal.map_quotient_self]
      exact hm.symm.trans hmap
    have hlt₂ : 𝔭₁.comap (Ideal.Quotient.mk P) < 𝔭₂.comap (Ideal.Quotient.mk P) := by
      refine lt_of_le_of_ne (Ideal.comap_mono hlt.le) fun heq => ?_
      have hA := Ideal.map_comap_of_surjective (Ideal.Quotient.mk P)
        Ideal.Quotient.mk_surjective 𝔭₁
      have hB := Ideal.map_comap_of_surjective (Ideal.Quotient.mk P)
        Ideal.Quotient.mk_surjective 𝔭₂
      have hAB : 𝔭₁ = 𝔭₂ := by rw [← hA, ← hB, heq]
      exact absurd hAB (ne_of_lt hlt)
    -- `ringKrullDim K[x₀,x₁,x₂] = 3`, so a chain of length two above `ker θ` gives `height ≤ 1`.
    have hdim : ringKrullDim (MvPolynomial (Fin 3) K) = 3 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
      norm_num
    have ha1 : P.height + 1 ≤ (𝔭₁.comap (Ideal.Quotient.mk P)).height :=
      Ideal.height_add_one_le_of_lt_of_isPrime hlt₁
    have hb1 : (𝔭₁.comap (Ideal.Quotient.mk P)).height + 1
        ≤ (𝔭₂.comap (Ideal.Quotient.mk P)).height :=
      Ideal.height_add_one_le_of_lt_of_isPrime hlt₂
    have hc2 : (𝔭₂.comap (Ideal.Quotient.mk P)).height ≤ 3 := by
      have h := Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔭₂.comap (Ideal.Quotient.mk P))
      rw [hdim] at h
      exact WithBot.coe_le_coe.mp h
    have hle : P.height ≤ 1 := by
      have key : P.height + (1 + 1) ≤ 1 + (1 + 1) := by
        calc P.height + (1 + 1) = (P.height + 1) + 1 := by rw [add_assoc]
          _ ≤ (𝔭₁.comap (Ideal.Quotient.mk P)).height + 1 := add_le_add ha1 le_rfl
          _ ≤ (𝔭₂.comap (Ideal.Quotient.mk P)).height := hb1
          _ ≤ 3 := hc2
          _ = 1 + (1 + 1) := by norm_num
      exact (ENat.add_le_add_iff_right (by norm_num : ((1 : ℕ∞) + 1) ≠ ⊤)).mp key
    -- `cubTRed ∈ ker θ` is non-zero, so the height is at least one.
    have hf4 : cubTRed a b h ≠ 0 := hprime.ne_zero
    have hge : (1 : ℕ∞) ≤ P.height := by
      have hmem : cubTRed a b h ∈ nonZeroDivisors (MvPolynomial (Fin 3) K) := by
        rw [mem_nonZeroDivisors_iff]
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases mul_eq_zero.mp hx with hc | hc
          · exact absurd hc hf4
          · exact hc
        · intro x hx
          rcases mul_eq_zero.mp hx with hc | hc
          · exact hc
          · exact absurd hc hf4
      have hone := Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hmem
      have hle' : Ideal.span {cubTRed a b h} ≤ P := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact RingHom.mem_ker.mpr h4
      exact hone.trans (Ideal.height_mono hle')
    exact hP ▸ le_antisymm hle hge
  -- `(cubTRed) ⊆ ker thetaMap`, of the same height
  have hspan_le : cubTIdeal a b h ≤ RingHom.ker (thetaMap a b h) := by
    rw [cubTIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact h4
  have hne : cubTRed a b h ≠ 0 := hprime.ne_zero
  have hprimeI : (cubTIdeal a b h).IsPrime := by
    rw [cubTIdeal]
    exact (Ideal.span_singleton_prime hne).mpr hprime
  have hheightF : (cubTIdeal a b h).height = 1 := by
    rw [cubTIdeal]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hne) hprime.not_unit
  have hker : RingHom.ker (thetaMap a b h) = cubTIdeal a b h := by
    by_contra hne'
    have hlt : cubTIdeal a b h < RingHom.ker (thetaMap a b h) :=
      lt_of_le_of_ne hspan_le (Ne.symm hne')
    haveI : (RingHom.ker (thetaMap a b h)).IsPrime := RingHom.ker_isPrime (thetaMap a b h)
    have hlt2 := Ideal.height_le_iff.mp (le_of_eq hheightKer) (cubTIdeal a b h) hprimeI hlt
    exact absurd (hheightF ▸ hlt2) (lt_irrefl _)
  -- conclude
  obtain ⟨e⟩ := CubTFracRange a b h ha hb hh h3 h1 h2
  obtain ⟨f⟩ := hker ▸ fractionRing_quotient_ker_algEquiv (K := K) (thetaMap a b h)
  exact ⟨f.trans e⟩

end Work.MotK.TGen
