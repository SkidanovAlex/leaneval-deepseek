import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_ideal_degree_le

namespace Commons.Algebra.FreeAlgebra

open _root_.FreeAlgebra

lemma freeMonoid_eq_of_of_length_one {ι : Type*} {w : FreeMonoid ι}
    (h : (FreeMonoid.toList w).length = 1) :
    ∃ i : ι, w = FreeMonoid.of i := by
  induction w using FreeMonoid.recOn with
  | one => simp at h
  | of_mul x xs ih =>
      have hlen : (FreeMonoid.toList xs).length = 0 := by
        have htot := congrArg List.length (FreeMonoid.toList_mul (FreeMonoid.of x) xs)
        rw [FreeMonoid.toList_of, List.length_append, List.length_singleton] at htot
        omega
      have hxs : xs = 1 := by
        apply FreeMonoid.toList.injective
        have hlist : FreeMonoid.toList xs = [] := List.eq_nil_of_length_eq_zero hlen
        simpa [FreeMonoid.toList_one] using hlist
      refine ⟨x, ?_⟩
      rw [hxs]
      simp

lemma golodShafarevich_gradedPart_one_eq_span_ι (K ι : Type*) [Field K] :
    golodShafarevich_gradedPart K ι 1 =
      Submodule.span K (Set.range (fun i : ι => FreeAlgebra.ι K i)) := by
  apply le_antisymm
  · rw [golodShafarevich_gradedPart, Submodule.span_le]
    intro x hx
    rcases hx with ⟨w, hlen, rfl⟩
    rcases freeMonoid_eq_of_of_length_one hlen with ⟨i, rfl⟩
    rw [golodShafarevich_basisFreeMonoid_of]
    exact Submodule.subset_span ⟨i, rfl⟩
  · rw [golodShafarevich_gradedPart]
    refine Submodule.span_mono ?_
    intro x hx
    rcases hx with ⟨i, rfl⟩
    change FreeAlgebra.ι K i ∈ {x | ∃ w : FreeMonoid ι,
      (FreeMonoid.toList w).length = 1 ∧ x = FreeAlgebra.basisFreeMonoid K ι w}
    rw [← golodShafarevich_basisFreeMonoid_of]
    refine ⟨FreeMonoid.of i, ?_, rfl⟩
    simp [FreeMonoid.toList_of]

theorem golod_shafarevich_graded_part_one_finrank
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    Module.finrank K (golodShafarevich_gradedPart K ι 1) = Fintype.card ι := by
  rw [golodShafarevich_gradedPart_one_eq_span_ι]
  have hli : LinearIndependent K (fun i : ι => FreeAlgebra.ι K i) := by
    have hcomp := (FreeAlgebra.basisFreeMonoid K ι).linearIndependent.comp
      FreeMonoid.of FreeMonoid.of_injective
    change LinearIndependent K (fun i : ι => FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)) at hcomp
    simpa [golodShafarevich_basisFreeMonoid_of] using hcomp
  exact finrank_span_eq_card (R := K) (M := FreeAlgebra K ι)
    (b := fun i : ι => FreeAlgebra.ι K i) hli

end Commons.Algebra.FreeAlgebra
