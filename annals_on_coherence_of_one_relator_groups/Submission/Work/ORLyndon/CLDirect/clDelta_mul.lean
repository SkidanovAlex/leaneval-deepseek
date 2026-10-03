import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.FoxComp

namespace Work.ORLyndon.CLDirect

/-- Pulling a constant left factor out of a `Finsupp.sum` (the `Finsupp` version of
`Finset.mul_sum`). -/
theorem finsupp_sum_mul_const {α : Type*} {A : Type*} {B : Type*} [Zero A] [Semiring B]
    (f : α →₀ A) (c : B) (H : α → A → B) :
    f.sum (fun i a => c * H i a) = c * f.sum H := by
  simp only [Finsupp.sum, Finset.mul_sum]

/-- The crossed-homomorphism rule for `clDelta`. Sketch: unfold `clDelta`; `Finsupp.ext` + `foxFD_apply` + `foxD_mul` + `Finsupp.smul_apply` give `foxFD (g*h) = foxFD g + (of g) • foxFD h`; then `Finsupp.sum_add_index'` / `Finsupp.sum_smul_index'` with `map_add`, `map_mul`, `add_mul`, `mul_assoc`, `Finsupp.mul_sum`. (`Submission.Work.ORLyndon.FoxComp` has `foxFD_mul`.) -/
theorem clDelta_mul {X : Type*} [DecidableEq X] {K : Type*} [Field K] {u : FreeGroup X}
    (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ)
    (g h : FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X)))) :
    Work.ORLyndon.CLDirect.clDelta (K := K) D l (g * h) =
      Work.ORLyndon.CLDirect.clDelta (K := K) D l g +
        Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g) *
          Work.ORLyndon.CLDirect.clDelta (K := K) D l h := by
  classical
  -- `clDelta` unfolds using `Classical.decEq` for the coset space; mirror this instance so that
  -- the `foxFD` occurrences we write by hand are the ones appearing in the goal.
  letI : DecidableEq (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))) :=
    Classical.decEq _
  simp only [clDelta]
  set H : (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))) →
      MonoidAlgebra K
        (FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X)))) →
      MonoidAlgebra K (OneRelatorGroup (u ^ l)) :=
    fun q c => clPi (K := K) D l c *
      MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (presentRho (u ^ l) (D.s q)) with hH
  have H0 : ∀ q, H q 0 = 0 := by
    intro q
    simp [hH]
  have Hadd : ∀ q (a b : MonoidAlgebra K
      (FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))))),
      H q (a + b) = H q a + H q b := by
    intro q a b
    simp only [hH, map_add, add_mul]
  have Hlin : ∀ (x : FreeGroup
        (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))))
      (q : FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X)))
      (a : MonoidAlgebra K
        (FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))))),
      H q (MonoidAlgebra.of K _ x * a) =
        clPi (K := K) D l (MonoidAlgebra.of K _ x) * H q a := by
    intro x q a
    simp only [hH]
    rw [map_mul, mul_assoc]
  have hcongr : (fun i a => H i (MonoidAlgebra.of K _ g * a)) =
      (fun i a => clPi (K := K) D l (MonoidAlgebra.of K _ g) * H i a) := by
    funext i a
    exact Hlin g i a
  have hlast : (Work.ORLyndon.foxFD (K := K) h).sum
        (fun i a => clPi (K := K) D l (MonoidAlgebra.of K _ g) * H i a) =
      clPi (K := K) D l (MonoidAlgebra.of K _ g) *
        (Work.ORLyndon.foxFD (K := K) h).sum H :=
    finsupp_sum_mul_const _ _ _
  rw [Work.ORLyndon.foxFD_mul,
    Finsupp.sum_add_index (fun a _ => H0 a) (fun a _ b1 b2 => Hadd a b1 b2),
    Finsupp.sum_smul_index H0,
    hcongr,
    hlast]

end Work.ORLyndon.CLDirect
