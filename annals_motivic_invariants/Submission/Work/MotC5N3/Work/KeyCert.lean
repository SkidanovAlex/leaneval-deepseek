import Mathlib
import Submission.Work.MotC5N3.Work.KeyMod
import Submission.Work.MotV5.ASLocal.asRhoPoly_witPt_wv
import Submission.Work.MotAS.witPfaff
import Submission.Work.MotAS.AsRhoDefs
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Work.MotC5N3.Work

open Polynomial MvPolynomial

/-! ## The value at the witness point and the certificate -/

theorem PhiP_coeff0 {K : Type} [CommRing K] (a b g : K) :
    (Work.MotV5.ASLocal.PhiP a b g).coeff 0 = Work.MotV5.ASLocal.asN0 a b g := by
  simp [Work.MotV5.ASLocal.PhiP, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]

theorem PhiP_coeff1 {K : Type} [CommRing K] (a b g : K) :
    (Work.MotV5.ASLocal.PhiP a b g).coeff 1 = Work.MotV5.ASLocal.asN1 a b g := by
  simp [Work.MotV5.ASLocal.PhiP, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]

theorem PhiP_coeff2 {K : Type} [CommRing K] (a b g : K) :
    (Work.MotV5.ASLocal.PhiP a b g).coeff 2 = Work.MotV5.ASLocal.asN2 a b g := by
  simp [Work.MotV5.ASLocal.PhiP, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]

theorem PhiP_coeff3 {K : Type} [CommRing K] (a b g : K) :
    (Work.MotV5.ASLocal.PhiP a b g).coeff 3 = Work.MotV5.ASLocal.asN3 a b g := by
  simp [Work.MotV5.ASLocal.PhiP, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]

theorem PhiP_coeff4 {K : Type} [CommRing K] (a b g : K) :
    (Work.MotV5.ASLocal.PhiP a b g).coeff 4 = Work.MotV5.ASLocal.asN4 a b g := by
  simp [Work.MotV5.ASLocal.PhiP, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]

theorem PhiP_natDegree_le (K : Type) [CommRing K] (a b g : K) :
    (Work.MotV5.ASLocal.PhiP (K := K) a b g).natDegree ≤ 4 := by
  unfold Work.MotV5.ASLocal.PhiP
  compute_degree!

theorem PhiP_ne_zero (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    Work.MotV5.ASLocal.PhiP (K := K) a b g ≠ 0 := by
  intro hzero
  have h0 : Work.MotV5.ASLocal.asN0 a b g = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 0) hzero
    rw [PhiP_coeff0] at hh; simpa using hh
  have h1 : Work.MotV5.ASLocal.asN1 a b g = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 1) hzero
    rw [PhiP_coeff1] at hh; simpa using hh
  have h2 : Work.MotV5.ASLocal.asN2 a b g = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 2) hzero
    rw [PhiP_coeff2] at hh; simpa using hh
  have h3 : Work.MotV5.ASLocal.asN3 a b g = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 3) hzero
    rw [PhiP_coeff3] at hh; simpa using hh
  have h4 : Work.MotV5.ASLocal.asN4 a b g = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 4) hzero
    rw [PhiP_coeff4] at hh; simpa using hh
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hab : a - 3 * b ≠ 0 := by
    intro h
    apply hd
    have hsq : (a - 3 * b) ^ 2 = a ^ 2 - a * b - b ^ 2 := by
      linear_combination (norm := refl_ring1 (mod := 5))
    rw [h] at hsq
    simpa using hsq.symm
  have key : (a - 3 * b) ^ 14 * b ^ 10 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hab) (pow_ne_zero _ hb)
  rw [← Work.MotV5.ASLocal.bezout a b g] at key
  simpa [h0, h1, h2, h3, h4] using key

theorem aeval_witPt_asRhoPoly (K : Type) [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.aeval (Work.MotAS.witPt a b) (Work.MotAS.asRhoPoly K a b g)
      = Work.MotAS.kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (Work.MotV5.ASLocal.WaV a b g) := by
  rw [Work.MotAS.asRhoPoly, Work.MotV5.ASLocal.aeval_kleinRAS0]
  simp only [Work.MotAS.kleinRAS0, Work.MotV5.ASLocal.WaV, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  rw [Work.MotV5.ASLocal.haeval_Wv0, Work.MotV5.ASLocal.haeval_Wv1,
    Work.MotV5.ASLocal.haeval_Wv2, Work.MotV5.ASLocal.haeval_Wv3,
    Work.MotV5.ASLocal.haeval_Wv4]
  rw [Work.MotV5.ASLocal.hWa0, Work.MotV5.ASLocal.hWa1, Work.MotV5.ASLocal.hWa2,
    Work.MotV5.ASLocal.hWa3, Work.MotV5.ASLocal.hWa4]

theorem asRhoPoly_notMem_span_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    Work.MotAS.asRhoPoly K a b g ∉
      Ideal.span (Set.range (Work.MotAS.kleinPASm (K := K) a b g)) := by
  intro hmem
  obtain ⟨q, hq⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have hdvd : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣
      MvPolynomial.aeval (Work.MotAS.witPt a b) (Work.MotAS.asRhoPoly K a b g) := by
    rw [← hq, map_sum]
    refine Finset.dvd_sum (fun i _ => ?_)
    rw [map_mul]
    exact dvd_mul_of_dvd_right
      ⟨Work.MotAS.witHk i a b g, Work.MotAS.witPfaff K a b g i⟩ _
  rw [aeval_witPt_asRhoPoly K a b g] at hdvd
  have h2 : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣
      Work.MotV5.ASLocal.PhiP (K := K) a b g := by
    have h := dvd_sub hdvd (keyMod K a b g)
    have e : Work.MotAS.kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (Work.MotV5.ASLocal.WaV a b g)
        - (Work.MotAS.kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (Work.MotV5.ASLocal.WaV a b g) - Work.MotV5.ASLocal.PhiP a b g)
        = Work.MotV5.ASLocal.PhiP (K := K) a b g := by ring
    rwa [e] at h
  refine PhiP_ne_zero K a b g ha hb hd (Polynomial.eq_zero_of_dvd_of_natDegree_lt h2 ?_)
  have h3 : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K).natDegree = 5 := by
    compute_degree!
  have h4 := PhiP_natDegree_le K a b g
  omega

end Work.MotC5N3.Work
