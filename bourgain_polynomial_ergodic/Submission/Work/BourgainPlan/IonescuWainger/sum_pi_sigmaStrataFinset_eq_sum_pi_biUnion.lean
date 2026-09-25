import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2_endpoint_strata

/-!
# Summing over products of Tao's strata

This is the strata analogue of `sum_pi_sigmaAFinset_eq_sum_pi_biUnion`: for a family `F` of subsets
of a pairwise coprime set `S` of integers `≥ 2`, the sums over the tuples of strata
`(Σ_{A_1}, …, Σ_{A_r})` assemble into the single sum over tuples of points of the union
`⋃_{A ∈ F} Σ_A = F.biUnion sigmaStrataFinset`:

`∑_{A_1,…,A_r ∈ F} ∑_{α_i ∈ Σ_{A_i}} Φ (α_1, …, α_r) = ∑_{β_i ∈ ⋃_A Σ_A} Φ (β_1, …, β_r)`.

The only input is the pairwise disjointness of the strata of distinct subsets of `S`
(`circle_strata_disjoint`), which makes the tautological map a bijection.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- The strata of distinct subsets of `S` are disjoint (`Finset` form of
`circle_strata_disjoint`). -/
theorem disjoint_sigmaStrataFinset {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) (hB : B ⊆ S) (hAB : A ≠ B) :
    Disjoint (sigmaStrataFinset A) (sigmaStrataFinset B) :=
  Finset.disjoint_left.mpr fun x hxA hxB => hAB (circle_strata_disjoint h2 hS hA hB hxA hxB)

theorem sum_pi_sigmaStrataFinset_eq_sum_pi_biUnion {S : Finset ℕ} {F : Finset (Finset ℕ)}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hF : ∀ A ∈ F, A ⊆ S) {r : ℕ} (Φ : (Fin r → Circle) → ℝ) :
    (∑ A : (i : Fin r) → ↥F,
        ∑ α : (i : Fin r) → ↥(sigmaStrataFinset ((A i).1)), Φ (fun i => (α i).1))
      = ∑ β : (i : Fin r) → ↥(F.biUnion sigmaStrataFinset), Φ (fun i => (β i).1) := by
  classical
  have hdisj : ∀ A ∈ F, ∀ B ∈ F, A ≠ B →
      Disjoint (sigmaStrataFinset A) (sigmaStrataFinset B) :=
    fun A hA B hB hAB => disjoint_sigmaStrataFinset h2 hS (hF A hA) (hF B hB) hAB
  set Q : ((i : Fin r) → ↥F) → Finset (Fin r → Circle) :=
    fun A => Fintype.piFinset (fun i => sigmaStrataFinset ((A i).1)) with hQ
  set T : Finset (Fin r → Circle) :=
    (Finset.univ : Finset ((i : Fin r) → ↥(F.biUnion sigmaStrataFinset))).image
      (fun β i => (β i).1) with hT
  have hQA : ∀ A : (i : Fin r) → ↥F,
      (∑ α : (i : Fin r) → ↥(sigmaStrataFinset ((A i).1)), Φ (fun i => (α i).1))
        = ∑ f ∈ Q A, Φ f := by
    intro A
    refine Finset.sum_bij (fun (α : (i : Fin r) → ↥(sigmaStrataFinset ((A i).1))) _ i => (α i).1)
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
  have hQdisj : (↑(Finset.univ : Finset ((i : Fin r) → ↥F)) :
      Set ((i : Fin r) → ↥F)).PairwiseDisjoint Q := by
    intro A _ B _ hAB
    show Disjoint (Q A) (Q B)
    rw [hQ, Finset.disjoint_left]
    intro f hfA hfB
    have hfA' : ∀ i, f i ∈ sigmaStrataFinset ((A i).1) := Fintype.mem_piFinset.mp hfA
    have hfB' : ∀ i, f i ∈ sigmaStrataFinset ((B i).1) := Fintype.mem_piFinset.mp hfB
    obtain ⟨i, hi⟩ : ∃ i : Fin r, A i ≠ B i := by
      by_contra h
      push Not at h
      exact hAB (funext fun i => h i)
    exact Finset.disjoint_left.mp
      (hdisj (A i).1 (A i).2 (B i).1 (B i).2 (fun h => hi (Subtype.ext h))) (hfA' i) (hfB' i)
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
  have hTsum : (∑ f ∈ T, Φ f)
      = ∑ β : (i : Fin r) → ↥(F.biUnion sigmaStrataFinset), Φ (fun i => (β i).1) := by
    rw [hT]
    exact Finset.sum_image (fun β _ β' _ h => funext fun i => Subtype.ext (congrFun h i))
  calc (∑ A : (i : Fin r) → ↥F,
          ∑ α : (i : Fin r) → ↥(sigmaStrataFinset ((A i).1)), Φ (fun i => (α i).1))
      = ∑ A : (i : Fin r) → ↥F, ∑ f ∈ Q A, Φ f := Finset.sum_congr rfl fun A _ => hQA A
    _ = ∑ f ∈ (Finset.univ : Finset ((i : Fin r) → ↥F)).biUnion Q, Φ f :=
        (Finset.sum_biUnion hQdisj).symm
    _ = ∑ f ∈ T, Φ f := by rw [hTQ]
    _ = ∑ β : (i : Fin r) → ↥(F.biUnion sigmaStrataFinset), Φ (fun i => (β i).1) := hTsum

end Work.BourgainPlan.IonescuWainger
