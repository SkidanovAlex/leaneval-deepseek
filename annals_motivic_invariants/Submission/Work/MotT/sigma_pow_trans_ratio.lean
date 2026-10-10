import Mathlib
import Submission.Work.MotT.T4Setup
import Submission.Work.MotT.AM2_descent
import Submission.Work.MotT.sigma_pow_eq_trans

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

theorem sigma_pow_trans_ratio {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic] (k : ℕ) :
    ∃ A : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point,
      (AM2_sigma D hD h₁ h₂ hk) ^ k =
        Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A ∧
      ∀ i : Fin 5,
        Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
          (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) (zL2 K h₁ h₂ hk)) ^
              ((i : ℕ) * k) *
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
  -- The first conjunct is `sigma_pow_eq_trans`; the second is the statement that the `k`-th power
  -- of the diagonal automorphism scales the `i`-th Klein ratio by `ζ^(i*k)`
  -- (`AM2_sigmaK_pow_ratio`, transported across `restrictScalars K`, `AM2_sigmaK_pow_apply`).
  obtain ⟨A, hA⟩ := sigma_pow_eq_trans D hD h₁ h₂ hk k
  refine ⟨A, hA, fun i => ?_⟩
  calc Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
        (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
          Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0)
      = ((AM2_sigma D hD h₁ h₂ hk) ^ k)
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by rw [hA]
    _ = ((AM2_sigmaK D hD h₁ h₂ hk) ^ k)
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) :=
        (AM2_sigmaK_pow_apply D hD h₁ h₂ hk k _).symm
    _ = (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) (zL2 K h₁ h₂ hk)) ^
            ((i : ℕ) * k) *
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) :=
        AM2_sigmaK_pow_ratio D hD h₁ h₂ hk k i

end Work.MotT
