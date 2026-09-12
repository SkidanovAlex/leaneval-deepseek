import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.parallel_body_valuation

namespace Commons.Geometry.Convex.Hadwiger

open scoped Pointwise
open Set

theorem valuation_add_convexBody
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V]
    (φ : ConvexBody V → ℝ)
    (hcont : Continuous φ)
    (hadd : ∀ A B C D : ConvexBody V,
          (A : Set V) = (C : Set V) ∪ (D : Set V) →
          (B : Set V) = (C : Set V) ∩ (D : Set V) →
          φ A + φ B = φ C + φ D)
    (htrans : ∀ A B : ConvexBody V, ∀ t : V,
          (B : Set V) = (fun x => x + t) '' (A : Set V) → φ A = φ B)
    (K : ConvexBody V) :
    let ψ : ConvexBody V → ℝ := fun A => φ (K + A)
    Continuous ψ ∧
      (∀ A B C D : ConvexBody V,
          (A : Set V) = (C : Set V) ∪ (D : Set V) →
          (B : Set V) = (C : Set V) ∩ (D : Set V) →
          ψ A + ψ B = ψ C + ψ D) ∧
      (∀ A B : ConvexBody V, ∀ t : V,
          (B : Set V) = (fun x => x + t) '' (A : Set V) → ψ A = ψ B) := by
  classical
  change Continuous (fun A : ConvexBody V => φ (K + A)) ∧
    (∀ A B C D : ConvexBody V,
          (A : Set V) = (C : Set V) ∪ (D : Set V) →
          (B : Set V) = (C : Set V) ∩ (D : Set V) →
          φ (K + A) + φ (K + B) = φ (K + C) + φ (K + D)) ∧
    (∀ A B : ConvexBody V, ∀ t : V,
          (B : Set V) = (fun x => x + t) '' (A : Set V) → φ (K + A) = φ (K + B))
  refine ⟨?_, ?_, ?_⟩
  · -- continuity
    have h_add_cont : Continuous (fun A : ConvexBody V => K + A) := by
      simpa [add_comm] using
        (Commons.Geometry.Convex.Hadwiger.continuous_add_left (V := V) K)
    exact hcont.comp h_add_cont
  · -- additivity
    intro A B C D hU hI
    have hUA : ((A + K : ConvexBody V) : Set V) =
        ((C + K : ConvexBody V) : Set V) ∪ ((D + K : ConvexBody V) : Set V) := by
      rw [ConvexBody.coe_add, ConvexBody.coe_add, ConvexBody.coe_add, hU]
      simpa [Set.image2_add] using
        (Set.image2_union_left (f := fun a b : V => a + b)
          (s := (C : Set V)) (s' := (D : Set V)) (t := (K : Set V)))
    have hIB : ((B + K : ConvexBody V) : Set V) =
        ((C + K : ConvexBody V) : Set V) ∩ ((D + K : ConvexBody V) : Set V) := by
      rw [ConvexBody.coe_add, ConvexBody.coe_add, ConvexBody.coe_add, hI]
      have hC_closed : IsClosed (C : Set V) := (C : ConvexBody V).isCompact.isClosed
      have hD_closed : IsClosed (D : Set V) := (D : ConvexBody V).isCompact.isClosed
      have hK_conv : Convex ℝ (K : Set V) := K.convex
      have hunion_conv : Convex ℝ ((C : Set V) ∪ (D : Set V)) := by
        rw [← hU]
        exact A.convex
      exact (add_inter_eq_of_convex_union (V := V) hC_closed hD_closed hK_conv hunion_conv).symm
    have hmain := hadd (A + K) (B + K) (C + K) (D + K) hUA hIB
    calc
      φ (K + A) + φ (K + B) = φ (A + K) + φ (B + K) := by
        rw [add_comm K A, add_comm K B]
      _ = φ (C + K) + φ (D + K) := hmain
      _ = φ (K + C) + φ (K + D) := by
        rw [add_comm C K, add_comm D K]
  · -- translation
    intro A B t hB
    have hBK : ((B + K : ConvexBody V) : Set V) =
        (fun x => x + t) '' ((A + K : ConvexBody V) : Set V) := by
      rw [ConvexBody.coe_add, ConvexBody.coe_add, hB]
      exact (image_add_right_set_add (A : Set V) (K : Set V) t).symm
    have hmain := htrans (A + K) (B + K) t hBK
    calc
      φ (K + A) = φ (A + K) := by rw [add_comm K A]
      _ = φ (B + K) := hmain
      _ = φ (K + B) := by rw [add_comm B K]

end Commons.Geometry.Convex.Hadwiger
