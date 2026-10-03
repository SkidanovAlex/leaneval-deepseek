import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.clPi_of
import Submission.Work.ORLyndon.CLDirect.clDelta_mul
import Submission.Work.ORLyndon.CLDirect.clDelta_one

namespace Work.ORLyndon.CLDirect

/-- The conjugation formula for `clDelta` at an element that dies in `G`. Sketch: `clDelta_mul` twice; `Δ(g⁻¹) = −π(g⁻¹)Δ(g)` from `clDelta_mul` at `g * g⁻¹` and `clDelta_one`; `π(of (g*h)) = π(of g)` by `clPi_of`, `hh` and `map_one`; finally `π(of g) * π(of g⁻¹) = 1` and `ring`/`abel`. -/
theorem clDelta_conj_of_trivial {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    {u : FreeGroup X} (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ)
    (g h : FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))))
    (hh : Work.ORLyndon.presentRho (u ^ l) (D.e h : FreeGroup X) = 1) :
    Work.ORLyndon.CLDirect.clDelta (K := K) D l (g * h * g⁻¹) =
      Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g) *
        Work.ORLyndon.CLDirect.clDelta (K := K) D l h := by
  -- `π(of (g*h)) = π(of g)`: both are `of (presentRho (u^l) ·)`, and `D.e h` dies in `G`.
  have hE3 : Work.ORLyndon.CLDirect.clPi (K := K) D l
      (MonoidAlgebra.of K (FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X)))) (g * h))
      = Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g) := by
    rw [Work.ORLyndon.CLDirect.clPi_of, Work.ORLyndon.CLDirect.clPi_of]
    congr 1
    have hcoe : ((D.e (g * h) : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) : FreeGroup X)
        = ((D.e g : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) : FreeGroup X) *
          ((D.e h : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) : FreeGroup X) := by
      rw [map_mul, Subgroup.coe_mul]
    rw [hcoe, map_mul, hh, mul_one]
  -- `Δ(g⁻¹) = −π(of g⁻¹) Δ(g)`, from the crossed-homomorphism rule at `g⁻¹ * g`.
  have hE2 : Work.ORLyndon.CLDirect.clDelta (K := K) D l g⁻¹ =
      -(Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g⁻¹) *
        Work.ORLyndon.CLDirect.clDelta (K := K) D l g) := by
    have h := Work.ORLyndon.CLDirect.clDelta_mul (K := K) D l g⁻¹ g
    rw [inv_mul_cancel] at h
    rw [Work.ORLyndon.CLDirect.clDelta_one] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  -- `π(of g) π(of g⁻¹) = 1`.
  have hE4 : Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g) *
      Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g⁻¹) = 1 := by
    rw [← map_mul, ← map_mul (MonoidAlgebra.of K
      (FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))))), mul_inv_cancel]
    simp only [map_one]
  calc
    Work.ORLyndon.CLDirect.clDelta (K := K) D l (g * h * g⁻¹)
        = Work.ORLyndon.CLDirect.clDelta (K := K) D l (g * h) +
            Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ (g * h)) *
              Work.ORLyndon.CLDirect.clDelta (K := K) D l g⁻¹ :=
          Work.ORLyndon.CLDirect.clDelta_mul (K := K) D l (g * h) g⁻¹
    _ = (Work.ORLyndon.CLDirect.clDelta (K := K) D l g +
            Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g) *
              Work.ORLyndon.CLDirect.clDelta (K := K) D l h) +
            Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ (g * h)) *
              Work.ORLyndon.CLDirect.clDelta (K := K) D l g⁻¹ := by
          rw [Work.ORLyndon.CLDirect.clDelta_mul]
    _ = (Work.ORLyndon.CLDirect.clDelta (K := K) D l g +
            Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g) *
              Work.ORLyndon.CLDirect.clDelta (K := K) D l h) +
            Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g) *
              -(Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g⁻¹) *
                Work.ORLyndon.CLDirect.clDelta (K := K) D l g) := by
          rw [hE3, hE2]
    _ = Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g) *
          Work.ORLyndon.CLDirect.clDelta (K := K) D l h := by
          rw [mul_neg, ← mul_assoc, hE4, one_mul]
          abel

end Work.ORLyndon.CLDirect
