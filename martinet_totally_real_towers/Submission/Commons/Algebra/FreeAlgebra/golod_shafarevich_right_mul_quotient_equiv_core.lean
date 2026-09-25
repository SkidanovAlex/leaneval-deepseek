import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_ideal_degree_le
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_quotient_map_equiv
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_graded_mul_quotient_equiv

namespace Commons.Algebra.FreeAlgebra

open _root_.FreeAlgebra

theorem golod_shafarevich_right_mul_quotient_equiv_core
    {K ι : Type*} [Field K] [DecidableEq ι] (n : ℕ) (hn : 0 < n)
    (A : Submodule K (golodShafarevich_gradedPart K ι (n - 1))) :
    let V := golodShafarevich_gradedPart K ι
    let T := Submodule.span K {x | ∃ a ∈ A, ∃ i : ι,
      x = (a : FreeAlgebra K ι) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
    Nonempty ((Submodule.map T.mkQ (V n)) ≃ₗ[K]
      TensorProduct K ((golodShafarevich_gradedPart K ι (n - 1)) ⧸ A)
        (golodShafarevich_gradedPart K ι 1)) := by
  dsimp only
  let V := golodShafarevich_gradedPart K ι
  let T := Submodule.span K {x | ∃ a ∈ A, ∃ i : ι,
      x = (a : FreeAlgebra K ι) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
  have hq := golod_shafarevich_quotient_map_equiv (K := K) (ι := ι) T (V n)
  have ht := golod_shafarevich_graded_mul_quotient_equiv (K := K) (ι := ι) n hn A
  dsimp only at ht
  obtain ⟨e1⟩ := hq
  obtain ⟨e2⟩ := ht
  exact ⟨e1.trans e2.symm⟩

end Commons.Algebra.FreeAlgebra
