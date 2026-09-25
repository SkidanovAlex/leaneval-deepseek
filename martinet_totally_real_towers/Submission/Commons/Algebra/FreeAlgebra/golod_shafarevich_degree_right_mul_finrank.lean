import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_degree_zero_finrank
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_ideal_degree_le
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_quotient_map_equiv
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_graded_part_one_finrank
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_right_mul_quotient_equiv

namespace Commons.Algebra.FreeAlgebra

open _root_.FreeAlgebra

set_option linter.unusedVariables false in
theorem golod_shafarevich_degree_right_mul_finrank
    {K ι σ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype σ]
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (n : ℕ) (hn : 0 < n) :
    let V := golodShafarevich_gradedPart K ι
    let I := golodShafarevich_twoSidedIdeal K ι σ rel
    let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
    Module.finrank K (Submodule.map T.mkQ (V n)) =
      Fintype.card ι * Module.finrank K (Submodule.map I.mkQ (V (n - 1))) := by
  dsimp only
  let V := golodShafarevich_gradedPart K ι
  let I := golodShafarevich_twoSidedIdeal K ι σ rel
  let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
  let A : Submodule K (V (n - 1)) := Submodule.comap (V (n - 1)).subtype I
  let T' := Submodule.span K {x | ∃ a ∈ A, ∃ i : ι,
      x = (a : FreeAlgebra K ι) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
  have hset : {x : FreeAlgebra K ι | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)} =
      {x : FreeAlgebra K ι | ∃ a ∈ A, ∃ i : ι,
        x = (a : FreeAlgebra K ι) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)} := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨a, haInt, i, rfl⟩
      rcases haInt with ⟨haI, haV⟩
      refine ⟨⟨a, haV⟩, ?_, i, rfl⟩
      rw [Submodule.mem_comap]
      simpa [A] using haI
    · intro hx
      rcases hx with ⟨a, haA, i, rfl⟩
      refine ⟨(a : FreeAlgebra K ι), ?_, i, rfl⟩
      have haI : (a : FreeAlgebra K ι) ∈ I := by
        rw [Submodule.mem_comap] at haA
        simpa [A] using haA
      exact ⟨haI, a.2⟩
  have hT : T = T' := by
    dsimp [T, T']
    rw [hset]
  have hnonempty : Nonempty ((Submodule.map T.mkQ (V n)) ≃ₗ[K]
      TensorProduct K ((V (n - 1)) ⧸ A) (V 1)) := by
    rw [hT]
    exact golod_shafarevich_right_mul_quotient_equiv (K := K) (ι := ι) n hn A
  obtain ⟨e⟩ := hnonempty
  have hfin_left : Module.finrank K (Submodule.map T.mkQ (V n)) =
      Module.finrank K (TensorProduct K ((V (n - 1)) ⧸ A) (V 1)) :=
    LinearEquiv.finrank_eq e
  have hfin_right : Module.finrank K (Submodule.map I.mkQ (V (n - 1))) =
      Module.finrank K ((V (n - 1)) ⧸ A) := by
    obtain ⟨eqv⟩ := golod_shafarevich_quotient_map_equiv (K := K) (ι := ι) I (V (n - 1))
    have hA : A = Submodule.comap (V (n - 1)).subtype I := rfl
    rw [hA]
    exact LinearEquiv.finrank_eq eqv
  rw [hfin_left, Module.finrank_tensorProduct, golod_shafarevich_graded_part_one_finrank, hfin_right]
  ring

end Commons.Algebra.FreeAlgebra
