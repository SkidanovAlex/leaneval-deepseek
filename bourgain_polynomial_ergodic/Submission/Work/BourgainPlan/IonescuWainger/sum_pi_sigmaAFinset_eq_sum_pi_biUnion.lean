import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.coe_sigmaAFinset
import Submission.Work.BourgainPlan.IonescuWainger.ArcCRT
import Submission.Work.BourgainPlan.IonescuWainger.sum_biUnion_sigmaAFinset

/-!
# Summing over products of exact-denominator arc sets

This file records the multi-dimensional (i.e. `r`-fold product) version of
`sum_biUnion_sigmaAFinset`: for a family `(A)_{A ∈ F}` of subsets of a pairwise coprime set `S` of
integers `≥ 2`, the sums over the tuples `(Σ_{A_1}, …, Σ_{A_r})` assemble into the single sum over
tuples of points of the union `⋃_{A ∈ F} Σ_A`:

`∑_{A_1,…,A_r ∈ F} ∑_{α_i ∈ Σ_{A_i}} Φ (α_1, …, α_r) = ∑_{β_i ∈ ⋃_A Σ_A} Φ (β_1, …, β_r)`.

The point is exactly the pairwise disjointness of the arc sets `Σ_A` for distinct `A ⊆ S`
(`disjoint_sigmaAFinset`): it makes the tautological map
`((A_i), (α_i ∈ Σ_{A_i})) ↦ (α_i ∈ ⋃_A Σ_A)` a bijection.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

theorem sum_pi_sigmaAFinset_eq_sum_pi_biUnion {S : Finset ℕ} {F : Finset (Finset ℕ)}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hF : ∀ A ∈ F, A ⊆ S) {r : ℕ} (Φ : (Fin r → Circle) → ℝ) :
    (∑ A : (i : Fin r) → ↥F,
        ∑ α : (i : Fin r) → ↥(sigmaAFinset ((A i).1)), Φ (fun i => (α i).1))
      = ∑ β : (i : Fin r) → ↥(F.biUnion sigmaAFinset), Φ (fun i => (β i).1) := by
  classical
  -- the arc sets of distinct members of `F` are disjoint
  have hdisj : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint (sigmaAFinset A) (sigmaAFinset B) :=
    fun A hA B hB hAB => disjoint_sigmaAFinset h2 hS (hF A hA) (hF B hB) hAB
  -- the set of tuples of arc points belonging to the prescribed denominators
  set Q : ((i : Fin r) → ↥F) → Finset (Fin r → Circle) :=
    fun A => Fintype.piFinset (fun i => sigmaAFinset ((A i).1)) with hQ
  -- the set of tuples of points of the union `⋃_{A ∈ F} Σ_A`
  set T : Finset (Fin r → Circle) :=
    (Finset.univ : Finset ((i : Fin r) → ↥(F.biUnion sigmaAFinset))).image
      (fun β i => (β i).1) with hT
  -- (1) each inner sum is a sum over the corresponding set of tuples
  have hQA : ∀ A : (i : Fin r) → ↥F,
      (∑ α : (i : Fin r) → ↥(sigmaAFinset ((A i).1)), Φ (fun i => (α i).1))
        = ∑ f ∈ Q A, Φ f := by
    intro A
    refine Finset.sum_bij (fun (α : (i : Fin r) → ↥(sigmaAFinset ((A i).1))) _ i => (α i).1)
      ?_ ?_ ?_ ?_
    · intro α _
      rw [hQ]
      exact Fintype.mem_piFinset.mpr fun i => (α i).2
    · intro α₁ _ α₂ _ h
      funext i
      exact Subtype.ext (congrFun h i)
    · intro f hf
      rw [hQ] at hf
      refine ⟨fun i => ⟨f i, (Fintype.mem_piFinset.mp hf) i⟩, mem_univ _, ?_⟩
      funext i
      rfl
    · intro α _
      rfl
  -- (2) the sets `Q A` (over `A`) are pairwise disjoint
  have hQdisj : (↑(Finset.univ : Finset ((i : Fin r) → ↥F)) : Set ((i : Fin r) → ↥F)).PairwiseDisjoint Q := by
    intro A _ B _ hAB
    show Disjoint (Q A) (Q B)
    rw [hQ, Finset.disjoint_left]
    intro f hfA hfB
    have hfA' : ∀ i, f i ∈ sigmaAFinset ((A i).1) := Fintype.mem_piFinset.mp hfA
    have hfB' : ∀ i, f i ∈ sigmaAFinset ((B i).1) := Fintype.mem_piFinset.mp hfB
    obtain ⟨i, hi⟩ : ∃ i : Fin r, A i ≠ B i := by
      by_contra h
      push Not at h
      exact hAB (funext fun i => h i)
    exact Finset.disjoint_left.mp
      (hdisj (A i).1 (A i).2 (B i).1 (B i).2 (fun h => hi (Subtype.ext h))) (hfA' i) (hfB' i)
  -- (3) `T` is the union of the sets `Q A`
  have hTQ : (Finset.univ : Finset ((i : Fin r) → ↥F)).biUnion Q = T := by
    ext f
    rw [hT]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, hQ,
      Fintype.mem_piFinset]
    constructor
    · rintro ⟨A, hA⟩
      refine ⟨fun i => ⟨f i, Finset.mem_biUnion.mpr ⟨(A i).1, (A i).2, hA i⟩⟩, ?_⟩
      funext i
      rfl
    · rintro ⟨β, hβ⟩
      choose A hA hmem using fun i => Finset.mem_biUnion.mp (β i).2
      refine ⟨fun i => ⟨A i, hA i⟩, fun i => ?_⟩
      have hfi : f i = (β i).1 := (congrFun hβ i).symm
      rw [hfi]
      exact hmem i
  -- (4) the sum over `T` is the sum over tuples of points of the union
  have hTsum : (∑ f ∈ T, Φ f)
      = ∑ β : (i : Fin r) → ↥(F.biUnion sigmaAFinset), Φ (fun i => (β i).1) := by
    rw [hT]
    exact Finset.sum_image (fun β _ β' _ h => funext fun i => Subtype.ext (congrFun h i))
  calc (∑ A : (i : Fin r) → ↥F,
          ∑ α : (i : Fin r) → ↥(sigmaAFinset ((A i).1)), Φ (fun i => (α i).1))
      = ∑ A : (i : Fin r) → ↥F, ∑ f ∈ Q A, Φ f := Finset.sum_congr rfl fun A _ => hQA A
    _ = ∑ f ∈ (Finset.univ : Finset ((i : Fin r) → ↥F)).biUnion Q, Φ f :=
        (Finset.sum_biUnion hQdisj).symm
    _ = ∑ f ∈ T, Φ f := by rw [hTQ]
    _ = ∑ β : (i : Fin r) → ↥(F.biUnion sigmaAFinset), Φ (fun i => (β i).1) := hTsum

end Work.BourgainPlan.IonescuWainger
