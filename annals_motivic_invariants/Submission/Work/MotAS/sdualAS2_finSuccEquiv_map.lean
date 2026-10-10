import Mathlib
import Submission.Work.MotAS.SdualAS2Explicit
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

open MvPolynomial

/-- The substitution `X 0 ↦ X`, `X 1 ↦ 0`, `X 2 ↦ 0` on `Fin 3 → Polynomial K`: it reads off the
coefficient of `X 0` (the `finSuccEquiv` variable) and sets the two remaining variables to zero. -/
noncomputable def sdualCoeffSubst (K : Type*) [CommRing K] : Fin 3 → Polynomial K :=
  (Fin.cases (Polynomial.X : Polynomial K) (fun _ : Fin 2 => (0 : Polynomial K)) :
    Fin 3 → Polynomial K)

@[simp] theorem sdualCoeffSubst_zero (K : Type*) [CommRing K] :
    sdualCoeffSubst K 0 = Polynomial.X := rfl

@[simp] theorem sdualCoeffSubst_one (K : Type*) [CommRing K] :
    sdualCoeffSubst K 1 = 0 := rfl

@[simp] theorem sdualCoeffSubst_two (K : Type*) [CommRing K] :
    sdualCoeffSubst K 2 = 0 := rfl

@[simp] theorem sdualCoeffSubst_succ (K : Type*) [CommRing K] (j : Fin 2) :
    sdualCoeffSubst K (Fin.succ j) = 0 := rfl

/-- The composite ring homomorphism `MvPolynomial (Fin 3) K →+* Polynomial K` which first applies
`finSuccEquiv K 2` and then evaluates the `MvPolynomial (Fin 2) K` coefficient at `0`. -/
noncomputable def sdualCoeffHom (K : Type*) [CommRing K] :
    MvPolynomial (Fin 3) K →+* Polynomial K :=
  (Polynomial.mapRingHom (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))).comp
    (MvPolynomial.finSuccEquiv K 2 :
      MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))

/-- The composite `sdualCoeffHom` is the substitution `X 0 ↦ X`, `X 1 ↦ 0`, `X 2 ↦ 0`. -/
theorem sdualCoeffHom_eq (K : Type*) [CommRing K] :
    sdualCoeffHom K = (MvPolynomial.eval₂Hom (Polynomial.C : K →+* Polynomial K)
      (sdualCoeffSubst K) : MvPolynomial (Fin 3) K →+* Polynomial K) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))
        (MvPolynomial.finSuccEquiv K 2 (MvPolynomial.C r))
      = MvPolynomial.eval₂Hom (Polynomial.C : K →+* Polynomial K) (sdualCoeffSubst K)
          (MvPolynomial.C r)
    have hC : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.C r)
        = Polynomial.C (MvPolynomial.C r) := by
      simp [MvPolynomial.finSuccEquiv_apply]
    rw [hC]
    simp [Polynomial.map_C, MvPolynomial.eval₂Hom_C]
  · rw [Fin.forall_iff_succ]
    constructor
    · change Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))
          (MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X 0))
        = MvPolynomial.eval₂Hom (Polynomial.C : K →+* Polynomial K) (sdualCoeffSubst K)
            (MvPolynomial.X 0)
      simp only [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, MvPolynomial.eval₂Hom_X',
        sdualCoeffSubst_zero]
    · intro j
      change Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))
          (MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X (Fin.succ j)))
        = MvPolynomial.eval₂Hom (Polynomial.C : K →+* Polynomial K) (sdualCoeffSubst K)
            (MvPolynomial.X (Fin.succ j))
      simp [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, MvPolynomial.eval₂Hom_X',
        sdualCoeffSubst_succ, Polynomial.C_0]

theorem sdualAS2_finSuccEquiv_map {K : Type*} [CommRing K] (a b g : K) :
    Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))
        (MvPolynomial.finSuccEquiv K 2 (Work.MotAS.sdualAS2 a b g))
      = Polynomial.C (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10) *
        (Polynomial.C g * Polynomial.X ^ 5 - Polynomial.X ^ 4 + 1) := by
  have key : ∀ p : MvPolynomial (Fin 3) K,
      Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin 2 → K))
          (MvPolynomial.finSuccEquiv K 2 p)
        = MvPolynomial.eval₂Hom (Polynomial.C : K →+* Polynomial K) (sdualCoeffSubst K) p :=
    fun p => DFunLike.congr_fun (sdualCoeffHom_eq K) p
  rw [key]
  rw [Work.MotAS.sdualAS2_explicit]
  simp only [map_add, map_mul, map_pow, map_neg, map_sub, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', sdualCoeffSubst_zero, sdualCoeffSubst_one, sdualCoeffSubst_two]
  first | refl_ring1 | ring

end Work.MotAS
