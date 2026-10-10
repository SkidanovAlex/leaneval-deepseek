import Mathlib
import Submission.Work.MotAS.azThetaDefs
import Submission.Work.MotAS.CensusASFalse
import Submission.Work.MotAS.AzThBricks
import Submission.Work.MotAS.Az.aeval_kleinPAS_gen
import Submission.Work.MotAS.Az.aeval_kleinStereoAS_gen
import Submission.Work.MotAS.Az.map_kleinStereoAS
import Submission.Work.MotAS.AzThNonzero
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.azTheta_fwVecAS2`

The composite of the forward AS chart map `f = P^AS ∘ Stereo^AS(pAS0, ·)` with the inverse chart
map `χ = π_{pAS0} ∘ R^AS` restricted to the target plane `(0,u,v,1,0)`, in the fraction field
`K(u,v) = FractionRing (MvPolynomial (Fin 2) K)`: on the plane the composite is (up to the non-zero
scalar `(χ₄)⁻⁴ · b(e₀,R^AS w)² · s'(w)`) the identity map `(u,v) ↦ (0,u,v,1,0)`, i.e.
`azTheta (f̂_j) = (χ₄)⁻⁴ · ι(b(e₀,R^AS w)² s'(w) · w_j)` with `w = (0,u,v,1,0)`.

The proof is the transfer of the T-twisted argument of `Work.MotK.TGen.FwThetaFwVec4Zero` /
`FwThetaFwVec3NeZero`: `aeval`-commutation (`Az.aeval_kleinPAS_gen`, `Az.aeval_kleinStereoAS_gen`),
homogeneity of `kleinPAS`/`kleinStereoAS` (`AzTh.PAS_smul`, `AzTh.stereo_smul`), the transport
lemmas `Az.map_kleinPAS`/`Az.map_kleinStereoAS`, and the geometric identity `AzTh.comp` (the
hypothesis `hI2` at the plane, via the inverse-stereographic identity `AzTh.stereo_pi`); the
non-vanishing of the two factors `χ₄` and `b(e₀,R^AS w)²s'(w)` is `Az.azZ_four_ne_zero` and
`Az.azBilin_ne_zero`/`Az.azSigma_ne_zero`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

namespace Work.MotAS

open MvPolynomial

theorem azTheta_fwVecAS2 {K : Type*} [Field K] (a b g : K) (h5 : (5 : K) = 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hg : g ≠ 0) (hA : a ^ 2 - a * b - b ^ 2 ≠ 0)
    (hI2 : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
            (Work.MotAS.azP K)) k
        = Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
            (Work.MotAS.azP K) * Work.MotAS.azP K k) :
    (Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 0) = 0) ∧
    (Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 3) ≠ 0) ∧
    (Work.MotAS.azU K * Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 3)
      = Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 1)) ∧
    (Work.MotAS.azV K * Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 3)
      = Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 2)) := by
  -- non-vanishing of the denominator `χ₄`
  have hχ4 : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (azChi a b g 4) ≠ 0 := by
    intro h0
    rw [azChi_four] at h0
    exact AzTh.azZ_four_ne_zero a b g hg hA
      (IsFractionRing.injective (MvPolynomial (Fin 2) K)
        (FractionRing (MvPolynomial (Fin 2) K)) (by rw [h0, map_zero]))
  -- non-vanishing of the numerator `b(e₀,R^AS w)²·s'(w)`
  have hβ : kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (AzTh.Evec K) (azZ a b g) ≠ 0 :=
    AzTh.azBilin_ne_zero h5 a b g hg hA
  have hσ : kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (azP K) ≠ 0 := AzTh.azSigma_ne_zero h5 a b g ha hb hg hA
  have hβσ : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
      (kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (AzTh.Evec K) (azZ a b g) ^ 2
        * kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (azP K)) ≠ 0 := by
    rw [map_mul, map_pow]
    refine mul_ne_zero (pow_ne_zero 2 ?_) ?_
    · intro h0
      exact hβ (IsFractionRing.injective (MvPolynomial (Fin 2) K)
        (FractionRing (MvPolynomial (Fin 2) K)) (by rw [h0, map_zero]))
    · intro h0
      exact hσ (IsFractionRing.injective (MvPolynomial (Fin 2) K)
        (FractionRing (MvPolynomial (Fin 2) K)) (by rw [h0, map_zero]))
  -- ### the master identity
  have key : ∀ j : Fin 5, azTheta a b g (fwVecAS2 a b g j)
      = ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 4))⁻¹) ^ 4
        * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (AzTh.Evec K) (azZ a b g) ^ 2
              * kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
                  (azP K)
              * azP K j) := by
    intro j
    -- (1) `azTheta` commutes with `kleinPAS`
    have h1 : azTheta a b g (fwVecAS2 a b g j)
        = kleinPAS (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
            (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
            (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) g)
            (fun i => azTheta a b g
              (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
                (Work.MotK.chart3 K) i)) j := by
      simpa only [azTheta, fwVecAS2] using
        Az.aeval_kleinPAS_gen (A := FractionRing (MvPolynomial (Fin 2) K)) a b g
          (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K) (Work.MotK.chart3 K))
          (azParam a b g) j
    -- (2) `azTheta` commutes with `kleinStereoAS`
    have h2 : (fun i => azTheta a b g
          (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
            (Work.MotK.chart3 K) i))
        = kleinStereoAS (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
            (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
            (fun i => azTheta a b g (pAS0 K i))
            (fun i => azTheta a b g (Work.MotK.chart3 K i)) := by
      funext i
      simpa only [azTheta] using
        Az.aeval_kleinStereoAS_gen (A := FractionRing (MvPolynomial (Fin 2) K)) a b
          (pAS0 K) (Work.MotK.chart3 K) (azParam a b g) i
    -- (3) the stereographic point is the constant vector `e₀`
    have h3_0 : azTheta a b g (pAS0 K (0 : Fin 5))
        = algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
            ((![1, 0, 0, 0, 0] : Fin 5 → K) (0 : Fin 5)) := by
      simp only [pAS0, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons, azTheta,
        map_one, map_zero]
    have h3_1 : azTheta a b g (pAS0 K (1 : Fin 5))
        = algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
            ((![1, 0, 0, 0, 0] : Fin 5 → K) (1 : Fin 5)) := by
      simp only [pAS0, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.tail_cons, azTheta, map_one, map_zero]
    have h3_2 : azTheta a b g (pAS0 K (2 : Fin 5))
        = algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
            ((![1, 0, 0, 0, 0] : Fin 5 → K) (2 : Fin 5)) := by
      simp only [pAS0, Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, azTheta, map_one, map_zero]
    have h3_3 : azTheta a b g (pAS0 K (3 : Fin 5))
        = algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
            ((![1, 0, 0, 0, 0] : Fin 5 → K) (3 : Fin 5)) := by
      simp only [pAS0, Matrix.cons_val_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, azTheta, map_one, map_zero]
    have h3_4 : azTheta a b g (pAS0 K (4 : Fin 5))
        = algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
            ((![1, 0, 0, 0, 0] : Fin 5 → K) (4 : Fin 5)) := by
      simp only [pAS0, Matrix.cons_val_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, azTheta,
        map_one, map_zero]
    have h3 : (fun i => azTheta a b g (pAS0 K i))
        = fun i => algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
            ((![1, 0, 0, 0, 0] : Fin 5 → K) i) := by
      funext i
      fin_cases i
      · show azTheta a b g (pAS0 K (0 : Fin 5))
            = algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
                ((![1, 0, 0, 0, 0] : Fin 5 → K) (0 : Fin 5))
        exact h3_0
      · show azTheta a b g (pAS0 K (1 : Fin 5))
            = algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
                ((![1, 0, 0, 0, 0] : Fin 5 → K) (1 : Fin 5))
        exact h3_1
      · show azTheta a b g (pAS0 K (2 : Fin 5))
            = algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
                ((![1, 0, 0, 0, 0] : Fin 5 → K) (2 : Fin 5))
        exact h3_2
      · show azTheta a b g (pAS0 K (3 : Fin 5))
            = algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
                ((![1, 0, 0, 0, 0] : Fin 5 → K) (3 : Fin 5))
        exact h3_3
      · show azTheta a b g (pAS0 K (4 : Fin 5))
            = algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
                ((![1, 0, 0, 0, 0] : Fin 5 → K) (4 : Fin 5))
        exact h3_4
    -- (4) the chart substitution `θ(X_i) = χ_{i+1}/χ₄`
    have h4 : (fun i => azTheta a b g (Work.MotK.chart3 K i))
        = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g 4))⁻¹
          • (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g i)) :=
      AzTh.param_chart3 a b g hχ4
    rw [h1, h2, h3, h4]
    -- homogenise: the stereographic vector is `χ₄⁻¹ • χ`
    rw [show ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 4))⁻¹)
          • (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g i))
        = (fun i => (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g 4))⁻¹
            * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
                (azChi a b g i)) from rfl]
    have hhom : ∀ k : Fin 5,
        kleinPAS (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
            (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
            (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) g)
            (kleinStereoAS (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
                ((![1, 0, 0, 0, 0] : Fin 5 → K) i))
              (fun i => (algebraMap (MvPolynomial (Fin 2) K)
                    (FractionRing (MvPolynomial (Fin 2) K)) (azChi a b g 4))⁻¹
                * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
                    (azChi a b g i))) k
          = ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
                (azChi a b g 4))⁻¹) ^ 4
            * kleinPAS (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
                (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
                (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) g)
                (kleinStereoAS (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
                  (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
                  (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
                    ((![1, 0, 0, 0, 0] : Fin 5 → K) i))
                  (fun i => algebraMap (MvPolynomial (Fin 2) K)
                      (FractionRing (MvPolynomial (Fin 2) K)) (azChi a b g i))) k := by
      intro k
      rw [AzTh.stereo_smul, AzTh.PAS_smul]
      first | refl_ring1 | ring
    rw [hhom j]
    -- transport along `K → K[u,v] → K(u,v)`
    have htr : ∀ k : Fin 5,
        kleinPAS (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
            (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
            (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) g)
            (kleinStereoAS (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
                ((![1, 0, 0, 0, 0] : Fin 5 → K) i))
              (fun i => algebraMap (MvPolynomial (Fin 2) K)
                  (FractionRing (MvPolynomial (Fin 2) K)) (azChi a b g i))) k
          = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
                (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (AzTh.Evec K)
                  (azChi a b g)) k) := by
      intro k
      have hE : (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
            ((![1, 0, 0, 0, 0] : Fin 5 → K) i))
          = fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (AzTh.Evec K i) := by
        funext i
        simp only [AzTh.Evec, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 2) K)
          (FractionRing (MvPolynomial (Fin 2) K)), MvPolynomial.algebraMap_eq]
      have hvec : kleinStereoAS (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) a)
              (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) b)
              (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 2) K))
                ((![1, 0, 0, 0, 0] : Fin 5 → K) i))
              (fun i => algebraMap (MvPolynomial (Fin 2) K)
                  (FractionRing (MvPolynomial (Fin 2) K)) (azChi a b g i))
          = fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (AzTh.Evec K)
                (azChi a b g) i) := by
        rw [hE, AzTh.algebraMap_C K a, AzTh.algebraMap_C K b]
        funext i
        exact (Az.map_kleinStereoAS (algebraMap (MvPolynomial (Fin 2) K)
          (FractionRing (MvPolynomial (Fin 2) K))) (MvPolynomial.C a) (MvPolynomial.C b)
          (AzTh.Evec K) (azChi a b g) i).symm
      rw [hvec, AzTh.algebraMap_C K a, AzTh.algebraMap_C K b, AzTh.algebraMap_C K g,
        ← AzTh.map_kleinPAS (algebraMap (MvPolynomial (Fin 2) K)
            (FractionRing (MvPolynomial (Fin 2) K))) (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C g)
          (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (AzTh.Evec K) (azChi a b g)) k]
    rw [htr j]
    -- the geometric composite identity
    rw [AzTh.comp_apply a b g hI2 j]
  -- the master identity with the `azP K j`-factor split off as a separate `algebraMap`
  have keymul : ∀ j : Fin 5, azTheta a b g (fwVecAS2 a b g j)
      = (((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 4))⁻¹) ^ 4
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (AzTh.Evec K) (azZ a b g) ^ 2
                * kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
                    (azP K)))
        * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (azP K j) := by
    intro j
    rw [key j, map_mul]
    first | refl_ring1 | ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key 0, azP_zero, mul_zero, map_zero, mul_zero]
  · rw [key 3, azP_three, mul_one]
    exact mul_ne_zero (pow_ne_zero 4 (inv_ne_zero hχ4)) hβσ
  · rw [keymul 1, keymul 3, azP_one, azP_three, map_one, mul_one]
    rw [show azU K = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (MvPolynomial.X 0) from rfl]
    first | refl_ring1 | ring
  · rw [keymul 2, keymul 3, azP_two, azP_three, map_one, mul_one]
    rw [show azV K = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (MvPolynomial.X 1) from rfl]
    first | refl_ring1 | ring

end Work.MotAS
