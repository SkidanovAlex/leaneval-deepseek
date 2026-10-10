import Mathlib
import Submission.Work.MotAS.AzDefs
import Submission.Work.MotAS.AzAux
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.azContent`

The `K`-generic form of `Work.MotV5.ASLocal.azContent`: the content of the quadratic `azQ` is
trivial over an arbitrary field `K` of characteristic `5`.

Concretely: write `A = azA a b`, `B = azB a b`, `E = azE a b` and let
`φ = MvPolynomial.finSuccEquiv K 1` be the isomorphism
`K[X₀,X₁] ≃ K[X₁][X₀]`.  Since `azC2 = C(4A²)·X₁² + C(4AB)` is independent of `X₀` and nonzero
(the leading coefficient is `4A²`, and `A ≠ 0`), any divisor `d` of `azC2` satisfies
`φ d = Polynomial.C d₀` for `d₀ = (φ d).coeff 0` — a polynomial *constant* in `X₀`, i.e. `d` lies in
`K[X₁]`.

Now `φ (azC1) = C(C(4A²)·X₁)·X₀² + C(C(16AB)·X₁)·X₀ + C(c10)` with
`c10 = −C(8AB)X₁³ − C(4AE)X₁ + 8A²g`, so `d | azC1` forces `d₀ | 4A²·X₁` and `d₀ | c10`.  As
`4A² ∈ K` is a unit, `d₀ | X₁`; if `d₀` were a non-unit it would be associated to `X₁`, whence
`X₁ | c10` and hence (evaluating `X₁ = 0`) `8A²g = 0`, i.e. `g = 0`, contradicting the hypothesis
`g ≠ 0`.  So `d₀` is a nonzero constant, `φ d` is a unit, hence so is `d`.

Note that `azC0` is not needed for the argument.  This is the port of the PROVED
`Work.MotV5.ASLocal.azContent` (`RatFunc 𝕜 ↦ K`, `algebraMap 𝕜 (RatFunc 𝕜) x ↦ x`,
`Work.MotV.fAS 𝕜 ↦ g`), the source's internal `fAS 𝕜 ≠ 0` becoming the hypothesis `hg : g ≠ 0`
(its only use).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace Work.MotC5N3

open MvPolynomial

/-! ## §1 The `finSuccEquiv` normal forms -/

section FinSucc

variable {K : Type*} [Field K]

/-- `finSuccEquiv K 1` sends constants to constants. -/
theorem azContent_finSuccEquiv_C (r : K) :
    MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [← MvPolynomial.algebraMap_eq K (Fin 2), AlgEquiv.commutes, Polynomial.algebraMap_apply]
  rfl

/-- `finSuccEquiv K 1` sends the second variable to a constant (the first variable of the target). -/
theorem azContent_finSuccEquiv_X1 :
    MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X (1 : Fin 2))
      = Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
  rw [show (1 : Fin 2) = Fin.succ 0 from rfl, MvPolynomial.finSuccEquiv_X_succ]

/-- `azC2` is independent of the variable `X₀`. -/
theorem azContent_finSuccEquiv_azC2 (a b : K) :
    MvPolynomial.finSuccEquiv K 1 (Work.MotAS.azC2 a b)
      = Polynomial.C (MvPolynomial.C (4 * Work.MotAS.azA a b ^ 2)
            * (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2
          + MvPolynomial.C (4 * Work.MotAS.azA a b * Work.MotAS.azB a b)) := by
  simp only [Work.MotAS.azC2, azContent_finSuccEquiv_C, azContent_finSuccEquiv_X1,
    map_add, map_mul, map_pow]

/-- The `X₀`-quadratic normal form of `azC1` after `finSuccEquiv`. -/
theorem azContent_finSuccEquiv_azC1 (a b g : K) :
    MvPolynomial.finSuccEquiv K 1 (Work.MotAS.azC1 a b g)
      = Polynomial.C (MvPolynomial.C (4 * Work.MotAS.azA a b ^ 2)
            * (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K))
          * Polynomial.X ^ 2
        + Polynomial.C (MvPolynomial.C (16 * Work.MotAS.azA a b * Work.MotAS.azB a b)
            * (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K))
          * Polynomial.X
        + Polynomial.C (-(MvPolynomial.C (8 * Work.MotAS.azA a b * Work.MotAS.azB a b)
              * (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 3)
            - MvPolynomial.C (4 * Work.MotAS.azA a b * Work.MotAS.azE a b)
              * (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K)
            + MvPolynomial.C (8 * Work.MotAS.azA a b ^ 2 * g)) := by
  simp only [Work.MotAS.azC1, azContent_finSuccEquiv_C, azContent_finSuccEquiv_X1,
    MvPolynomial.finSuccEquiv_X_zero, map_add, map_sub, map_mul, map_pow, map_neg]
  first | refl_ring1 | ring

end FinSucc

/-! ## §2 Coefficients of an explicit quadratic -/

section Coeff

variable {S : Type*} [CommSemiring S]

/-- The `X ^ 2`-coefficient of an explicit quadratic. -/
theorem azContent_coeff_two (α β γ : S) :
    (Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ).coeff 2
      = α := by
  simp

/-- The constant coefficient of an explicit quadratic. -/
theorem azContent_coeff_zero (α β γ : S) :
    (Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ).coeff 0
      = γ := by
  simp

end Coeff

/-! ## §3 The content statement -/

/-- **The content of the quadratic `azQ` is trivial**, over an arbitrary field `K` of characteristic
`5`: the three `X₀`-coefficients `azC2 a b`, `azC1 a b g`, `azC0 a b g` of the AS quadratic form
`azQ a b g` (definitions in `Submission/Work/MotAS/AzDefs.lean`) have no common divisor.
Equivalently: any `d` dividing all three is a unit.

This is the `K`-generic form of the PROVED `Work.MotV5.ASLocal.azContent`
(`Submission/Work/MotV5/ASLocal/azContent.lean`, 266 lines), whose base field is `RatFunc 𝕜`, whose
parameters are `algebraMap 𝕜 (RatFunc 𝕜) a`, `algebraMap 𝕜 (RatFunc 𝕜) b` and whose class is
`Work.MotV.fAS 𝕜`.  The port is mechanical (`RatFunc 𝕜 ↦ K`,
`algebraMap 𝕜 (RatFunc 𝕜) x ↦ x`, `Work.MotV.fAS 𝕜 ↦ g`), except that the source derives
`hg : fAS 𝕜 ≠ 0` internally while here it is a hypothesis `hg : g ≠ 0` (the only use of the class).
Everything else in that proof is stated for an arbitrary field of characteristic `5` and only needs
the general results `MvPolynomial.dvd_X_iff_exists`, `Work.MotAS.azC2_ne_zero`,
`MvPolynomial.finSuccEquiv` and `Polynomial.coeff_C_mul`.  The source file must be *copied*, not
imported (it is hardwired to `RatFunc 𝕜`). -/
theorem azContent (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hA : Work.MotAS.azA a b ≠ 0) (hg : g ≠ 0) :
    ∀ d : MvPolynomial (Fin 2) K,
      d ∣ Work.MotAS.azC2 a b → d ∣ Work.MotAS.azC1 a b g →
      d ∣ Work.MotAS.azC0 a b g → IsUnit d := by
  intro d hd2 hd1 _hd0
  let A : K := Work.MotAS.azA a b
  let B : K := Work.MotAS.azB a b
  let E : K := Work.MotAS.azE a b
  have hA' : A ≠ 0 := hA
  have h4 : (4 : K) ≠ 0 := by
    intro h
    have h54 : (5 : ℕ) ∣ 4 := (CharP.cast_eq_zero_iff K 5 4).mp h
    norm_num at h54
  have h8 : (8 : K) ≠ 0 := by
    intro h
    have h54 : (5 : ℕ) ∣ 8 := (CharP.cast_eq_zero_iff K 5 8).mp h
    norm_num at h54
  let u : MvPolynomial (Fin 1) K := MvPolynomial.X 0
  have hu : u = MvPolynomial.X (0 : Fin 1) := rfl
  -- the coefficient ring `K[X₁]` and the three objects of interest
  let c2 : MvPolynomial (Fin 1) K :=
    MvPolynomial.C (4 * A ^ 2) * u ^ 2 + MvPolynomial.C (4 * A * B)
  let c10 : MvPolynomial (Fin 1) K :=
    -(MvPolynomial.C (8 * A * B) * u ^ 3) - MvPolynomial.C (4 * A * E) * u
      + MvPolynomial.C (8 * A ^ 2 * g)
  let Q1 : Polynomial (MvPolynomial (Fin 1) K) :=
    Polynomial.C (MvPolynomial.C (4 * A ^ 2) * u) * Polynomial.X ^ 2
      + Polynomial.C (MvPolynomial.C (16 * A * B) * u) * Polynomial.X + Polynomial.C c10
  let P : Polynomial (MvPolynomial (Fin 1) K) :=
    (MvPolynomial.finSuccEquiv K 1) d
  have hφ2 : (MvPolynomial.finSuccEquiv K 1) (Work.MotAS.azC2 a b) =
      Polynomial.C c2 := azContent_finSuccEquiv_azC2 a b
  have hφ1 : (MvPolynomial.finSuccEquiv K 1) (Work.MotAS.azC1 a b g) = Q1 :=
    azContent_finSuccEquiv_azC1 a b g
  -- `c2 ≠ 0` (this is `azC2 ≠ 0` transported along `finSuccEquiv`)
  have hc2ne : c2 ≠ 0 := by
    intro h
    refine Work.MotAS.azC2_ne_zero a b hA ?_
    have hz : (MvPolynomial.finSuccEquiv K 1) (Work.MotAS.azC2 a b)
        = (MvPolynomial.finSuccEquiv K 1) 0 := by
      rw [hφ2, h]
      simp
    exact (MvPolynomial.finSuccEquiv K 1).injective hz
  -- Step 1: `P` is a constant polynomial in `X₀`; write it as `C d₀`
  have hPdvd2 : P ∣ Polynomial.C c2 := by
    rcases hd2 with ⟨e, he⟩
    refine ⟨(MvPolynomial.finSuccEquiv K 1) e, ?_⟩
    rw [hφ2.symm, he, map_mul]
  rcases hPdvd2 with ⟨R, hR⟩
  have hPne : P ≠ 0 := by
    intro h
    rw [h, zero_mul] at hR
    exact hc2ne (Polynomial.C_eq_zero.mp hR)
  have hRne : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hR
    exact hc2ne (Polynomial.C_eq_zero.mp hR)
  have hnd : P.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hPne hRne
    rw [← hR, Polynomial.natDegree_C] at hmul
    omega
  have hPC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hnd
  set d0 : MvPolynomial (Fin 1) K := P.coeff 0 with hd0
  -- Step 2: `d₀` divides the coefficients `C(4A²)·X₁` and `c10` of `azC1`
  have hPdvd1 : P ∣ Q1 := by
    rcases hd1 with ⟨e, he⟩
    refine ⟨(MvPolynomial.finSuccEquiv K 1) e, ?_⟩
    rw [hφ1.symm, he, map_mul]
  have hCd0dvd1 : Polynomial.C d0 ∣ Q1 := by
    rw [← hPC]
    exact hPdvd1
  rcases hCd0dvd1 with ⟨R1, hR1⟩
  have hcoeff2 : Q1.coeff 2 = MvPolynomial.C (4 * A ^ 2) * u := azContent_coeff_two _ _ _
  have hcoeff0 : Q1.coeff 0 = c10 := azContent_coeff_zero _ _ _
  have hd0u : d0 ∣ MvPolynomial.C (4 * A ^ 2) * u := by
    refine ⟨R1.coeff 2, ?_⟩
    have h := congrArg (fun p : Polynomial (MvPolynomial (Fin 1) K) => p.coeff 2) hR1
    rw [hcoeff2, Polynomial.coeff_C_mul] at h
    exact h
  have hd0c10 : d0 ∣ c10 := by
    refine ⟨R1.coeff 0, ?_⟩
    have h := congrArg (fun p : Polynomial (MvPolynomial (Fin 1) K) => p.coeff 0) hR1
    rw [hcoeff0, Polynomial.coeff_C_mul] at h
    exact h
  -- Step 3: since `4A²` is a unit, `d₀ ∣ X₁`
  have hd0u' : d0 ∣ u := by
    obtain ⟨w, hw⟩ := hd0u
    refine ⟨MvPolynomial.C ((4 * A ^ 2)⁻¹) * w, ?_⟩
    calc u = (MvPolynomial.C ((4 * A ^ 2)⁻¹) * MvPolynomial.C (4 * A ^ 2)) * u := by
            rw [← map_mul, inv_mul_cancel₀ (mul_ne_zero h4 (pow_ne_zero 2 hA')), map_one,
              one_mul]
      _ = MvPolynomial.C ((4 * A ^ 2)⁻¹) * (MvPolynomial.C (4 * A ^ 2) * u) := by ring
      _ = MvPolynomial.C ((4 * A ^ 2)⁻¹) * (d0 * w) := by rw [hw]
      _ = d0 * (MvPolynomial.C ((4 * A ^ 2)⁻¹) * w) := by ring
  -- Step 4: divisors of `X₁` are units or associates of `X₁`
  obtain ⟨r, hrunit, hcases⟩ :=
    (MvPolynomial.dvd_X_iff_exists (p := d0) (i := (0 : Fin 1))).mp hd0u'
  rcases hcases with hrC | hrX
  · -- `d₀` is a unit, hence so are `P = C d₀` and `d`
    have hd0unit : IsUnit d0 := by
      rw [hrC]
      exact IsUnit.map MvPolynomial.C hrunit
    have hPunit : IsUnit P := by
      rw [hPC, Polynomial.isUnit_C]
      exact hd0unit
    have hd : d = (MvPolynomial.finSuccEquiv K 1).symm P := by
      rw [show P = (MvPolynomial.finSuccEquiv K 1) d from rfl]
      exact (AlgEquiv.symm_apply_apply _ _).symm
    rw [hd]
    exact IsUnit.map ((MvPolynomial.finSuccEquiv K 1).symm :
      Polynomial (MvPolynomial (Fin 1) K) →+* MvPolynomial (Fin 2) K) hPunit
  · -- `X₁ ∣ d₀`, hence `X₁ ∣ c10`, which forces `g = 0`, a contradiction
    have hX0d0 : MvPolynomial.X (0 : Fin 1) ∣ d0 := by
      rw [hrX, Algebra.smul_def]
      exact dvd_mul_left _ _
    have hX0c10 : MvPolynomial.X (0 : Fin 1) ∣ c10 := dvd_trans hX0d0 hd0c10
    have hev0 : (MvPolynomial.aeval (fun _ : Fin 1 => (0 : K)) :
        MvPolynomial (Fin 1) K →ₐ[K] K) c10 = 0 := by
      obtain ⟨w, hw⟩ := hX0c10
      rw [hw, map_mul, MvPolynomial.aeval_X]
      simp
    have hev1 : (MvPolynomial.aeval (fun _ : Fin 1 => (0 : K)) :
        MvPolynomial (Fin 1) K →ₐ[K] K) c10 = 8 * A ^ 2 * g := by
      simp only [c10, hu, map_add, map_sub, map_mul, map_pow, map_neg, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, Algebra.algebraMap_self_apply, mul_zero, sub_zero]
      first | refl_ring1 | ring
    have hgz : g = 0 := by
      have hz : 8 * A ^ 2 * g = 0 := by rw [← hev1]; exact hev0
      rcases mul_eq_zero.mp hz with h8A2 | hg0
      · exact absurd h8A2 (mul_ne_zero h8 (pow_ne_zero 2 hA'))
      · exact hg0
    exact absurd hgz hg

end Work.MotC5N3
