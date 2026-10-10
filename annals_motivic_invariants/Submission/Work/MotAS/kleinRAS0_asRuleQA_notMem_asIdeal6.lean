import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotAS.WitPt
import Submission.Work.MotAS.witPfaff
import Submission.Work.MotAS.AsRuleQAValue
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

theorem kleinRAS0_asRuleQA_notMem_asIdeal6 (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    (Work.MotAS.kleinRAS0 (R := MvPolynomial (Fin 5) K) (MvPolynomial.C (σ := Fin 5) a)
        (MvPolynomial.C (σ := Fin 5) b) (MvPolynomial.C (σ := Fin 5) g)
        (Work.MotAS.asRuleQA (R := MvPolynomial (Fin 5) K) (MvPolynomial.C (σ := Fin 5) a)
          (MvPolynomial.C (σ := Fin 5) b) (MvPolynomial.C (σ := Fin 5) g)
          (fun i : Fin 5 => MvPolynomial.X i)))
      ∉ Work.MotAS.asIdeal6 K a b g := by
  intro hmem
  have hdvd : ∀ G : MvPolynomial (Fin 5) K, G ∈ asIdeal6 K a b g →
      (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣ MvPolynomial.aeval (witPt a b) G := by
    intro G hG
    refine Submodule.span_induction
      (p := fun G _ => (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣
        MvPolynomial.aeval (witPt a b) G) ?_ ?_ ?_ ?_ hG
    · rintro G ⟨q, rfl⟩
      have hw : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣
          MvPolynomial.aeval (witPt a b)
            (kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
              (fun i => MvPolynomial.X i) q.1) :=
        ⟨witHk q.1 a b g, witPfaff K a b g q.1⟩
      rw [map_mul]
      exact dvd_mul_of_dvd_left hw _
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact dvd_add hx hy
    · intro c x _ hx
      rw [map_smul, Polynomial.smul_eq_C_mul]
      exact dvd_mul_of_dvd_right hx _
  have hF : MvPolynomial.aeval (witPt a b)
        (kleinRAS0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fun k => qAS_A K a b g k))
      = MvPolynomial.aeval (witPt a b)
        (kleinRAS0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (asRuleQA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
            (fun i => MvPolynomial.X i))) := by
    first | rfl | congr 1
  have hdiv : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣
      MvPolynomial.aeval (witPt a b)
        (kleinRAS0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fun k => qAS_A K a b g k)) := by
    rw [hF]
    exact hdvd _ hmem
  have hdvdPhi : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣ asPhiP a b g := by
    have h := dvd_sub hdiv (asValueMod a b g)
    convert h using 1
    first | refl_ring1 | ring
  have hf5 : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K).natDegree = 5 := by
    compute_degree!
  exact asPhiP_ne_zero a b g ha hb hd
    (Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvdPhi
      (by have := asPhiP_natDegree a b g; omega))

end Work.MotAS
