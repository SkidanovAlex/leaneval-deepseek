import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Prob.Basic
import Submission.Work.Deep.Prob.Spaces

namespace Work.Deep.Prob.LLL

open scoped BigOperators
open Finset

/-- **Lopsided (asymmetric) Lovász local lemma.**

Let `A : ι → Set Ω` be a finite family of bad events in a finite probability space, `D i` a
finite set of "neighbours" of `i` and `x i ∈ [0,1)` numbers with
`ℙ[A i] ≤ x i * ∏ j ∈ D i, (1 - x j)`.  If, moreover, every `A i` is negatively correlated
with the conjunction of the complements of the events far from it (the *lopsided* hypothesis
`hlops`), then `∏ i, (1 - x i) ≤ ℙ[⋂ i, (A i)ᶜ]`. -/
theorem lovaszLocalLemma_lopsided {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω) {ι : Type*}
    [Fintype ι] (A : ι → Set Ω) (D : ι → Finset ι) (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1) (hbound : ∀ i, P.prob (A i) ≤ x i * ∏ j ∈ D i, (1 - x j))
    (hlops : ∀ i (T : Finset ι), (∀ j ∈ T, j ∉ D i ∧ j ≠ i) →
      FinProbSpace.LopsidedIndep P (A i) A T) :
    ∏ i, (1 - x i) ≤ P.prob (⋂ i, (A i)ᶜ) := by
  classical
  -- `Q T` is the probability that none of the events indexed by `T` occurs, and `N i T` is
  -- the probability that `A i` occurs and none of the events indexed by `T` does.
  let Q : Finset ι → ℝ := fun T => P.prob (⋂ j ∈ T, (A j)ᶜ)
  let N : ι → Finset ι → ℝ := fun i T => P.prob (A i ∩ ⋂ j ∈ T, (A j)ᶜ)
  have hx1' : ∀ j, 0 ≤ 1 - x j := fun j => by linarith [hx1 j]
  have hxle : ∀ j, 1 - x j ≤ 1 := fun j => by linarith [hx0 j]
  have hQnn : ∀ (T : Finset ι), 0 ≤ Q T := fun T => P.prob_nonneg _
  have hprodnn : ∀ s : Finset ι, 0 ≤ ∏ j ∈ s, (1 - x j) :=
    fun s => Finset.prod_nonneg fun j _ => hx1' j
  -- Monotonicity in the set of conditioned events.
  have hNmono : ∀ (i : ι) {S T : Finset ι}, S ⊆ T → N i T ≤ N i S := by
    intro i S T hST
    show P.prob (A i ∩ ⋂ j ∈ T, (A j)ᶜ) ≤ P.prob (A i ∩ ⋂ j ∈ S, (A j)ᶜ)
    refine P.prob_mono ?_
    intro ω hω
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff] at hω ⊢
    exact ⟨hω.1, fun j hj => hω.2 j (hST hj)⟩
  -- Splitting off one conditioned event.
  have hsplit : ∀ (i : ι) (T : Finset ι), Q (insert i T) = Q T - N i T := by
    intro i T
    show P.prob (⋂ j ∈ (insert i T : Finset ι), (A j)ᶜ)
        = P.prob (⋂ j ∈ T, (A j)ᶜ) - P.prob (A i ∩ ⋂ j ∈ T, (A j)ᶜ)
    have hset : (⋂ j ∈ (insert i T : Finset ι), (A j)ᶜ : Set Ω)
        = (⋂ j ∈ T, (A j)ᶜ) ∩ (A i)ᶜ := by
      ext ω; simp [Finset.mem_insert, and_comm]
    rw [hset, P.prob_inter_compl, Set.inter_comm]
  have hQempty : Q ∅ = 1 := by
    show P.prob (⋂ j ∈ (∅ : Finset ι), (A j)ᶜ) = 1
    rw [show (⋂ j ∈ (∅ : Finset ι), (A j)ᶜ : Set Ω) = Set.univ by ext ω; simp]
    exact P.prob_univ
  -- Peeling a whole set off, given the single-element peel inequality.
  have peel_of : ∀ (T : Finset ι),
      (∀ (U : Finset ι), U ⊆ T → ∀ (a : ι), a ∈ U → (1 - x a) * Q (U.erase a) ≤ Q U) →
      ∀ (S : Finset ι), S ⊆ T → Q (T \ S) * ∏ j ∈ S, (1 - x j) ≤ Q T := by
    intro T hsingle S
    induction S using Finset.induction_on with
    | empty =>
        intro _
        simp
    | insert a S ha ih =>
        intro hS
        have haT : a ∈ T := hS (Finset.mem_insert_self a S)
        have hST : S ⊆ T := fun j hj => hS (Finset.mem_insert_of_mem hj)
        have hIH := ih hST
        have hamem : a ∈ T \ S := Finset.mem_sdiff.mpr ⟨haT, ha⟩
        have hsp := hsingle (T \ S) Finset.sdiff_subset a hamem
        have herase : (T \ S).erase a = T \ insert a S := by
          ext b; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hbne, hbT, hbS⟩
            exact ⟨hbT, fun h => h.elim hbne (fun hb => hbS hb)⟩
          · rintro ⟨hbT, hb⟩
            exact ⟨fun hbae => hb (Or.inl hbae), hbT, fun hbS => hb (Or.inr hbS)⟩
        calc Q (T \ insert a S) * ∏ j ∈ insert a S, (1 - x j)
            = ((1 - x a) * Q ((T \ S).erase a)) * ∏ j ∈ S, (1 - x j) := by
              rw [herase, Finset.prod_insert ha]; ring
          _ ≤ Q (T \ S) * ∏ j ∈ S, (1 - x j) :=
              mul_le_mul_of_nonneg_right hsp (hprodnn S)
          _ ≤ Q T := hIH
  -- The main statement, by strong induction on `T`.
  have key : ∀ (T : Finset ι) (i : ι), i ∉ T → N i T ≤ x i * Q T := by
    intro T
    refine Finset.strongInductionOn T ?_
    intro T IH i hiT
    have hsingle : ∀ (U : Finset ι), U ⊆ T →
        ∀ (a : ι), a ∈ U → (1 - x a) * Q (U.erase a) ≤ Q U := by
      intro U hU a ha
      have hlt : U.erase a ⊂ T := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨(Finset.erase_subset a U).trans hU, ?_⟩
        intro hEq
        have : a ∈ U.erase a := by rw [hEq]; exact hU ha
        exact Finset.notMem_erase a U this
      have hk := IH (U.erase a) hlt a (Finset.notMem_erase a U)
      have hsp := hsplit a (U.erase a)
      rw [Finset.insert_erase ha] at hsp
      linarith
    have hpeel := peel_of T hsingle
    have hfar : ∀ j ∈ T \ D i, j ∉ D i ∧ j ≠ i := by
      intro j hj
      rw [Finset.mem_sdiff] at hj
      exact ⟨hj.2, fun hji => hiT (hji ▸ hj.1)⟩
    have hN1 : N i T ≤ N i (T \ D i) := hNmono i Finset.sdiff_subset
    have hN2 : N i (T \ D i) ≤ P.prob (A i) * Q (T \ D i) := hlops i (T \ D i) hfar
    have hN3 : P.prob (A i) * Q (T \ D i) ≤ (x i * ∏ j ∈ D i, (1 - x j)) * Q (T \ D i) :=
      mul_le_mul_of_nonneg_right (hbound i) (hQnn _)
    have hprod_le : (∏ j ∈ D i, (1 - x j)) ≤ ∏ j ∈ T ∩ D i, (1 - x j) :=
      Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right
        (fun j _ => hx1' j) (fun j _ _ => hxle j)
    have hpeel' : Q (T \ D i) * ∏ j ∈ T ∩ D i, (1 - x j) ≤ Q T := by
      have h := hpeel (T ∩ D i) Finset.inter_subset_left
      rwa [show T \ (T ∩ D i) = T \ D i from by
        ext b; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto] at h
    calc N i T ≤ N i (T \ D i) := hN1
      _ ≤ P.prob (A i) * Q (T \ D i) := hN2
      _ ≤ (x i * ∏ j ∈ D i, (1 - x j)) * Q (T \ D i) := hN3
      _ = x i * ((∏ j ∈ D i, (1 - x j)) * Q (T \ D i)) := by ring
      _ ≤ x i * ((∏ j ∈ T ∩ D i, (1 - x j)) * Q (T \ D i)) := by
            refine mul_le_mul_of_nonneg_left ?_ (hx0 i)
            exact mul_le_mul_of_nonneg_right hprod_le (hQnn _)
      _ = x i * (Q (T \ D i) * ∏ j ∈ T ∩ D i, (1 - x j)) := by ring
      _ ≤ x i * Q T := mul_le_mul_of_nonneg_left hpeel' (hx0 i)
  -- Single-element peel, now for every set.
  have hsingleG : ∀ (U : Finset ι) (a : ι), a ∈ U → (1 - x a) * Q (U.erase a) ≤ Q U := by
    intro U a ha
    have hk := key (U.erase a) a (Finset.notMem_erase a U)
    have hsp := hsplit a (U.erase a)
    rw [Finset.insert_erase ha] at hsp
    linarith
  have hpeelG : ∀ S : Finset ι, ∏ j ∈ S, (1 - x j) ≤ Q S := by
    intro S
    have h := peel_of S (fun U _ => hsingleG U) S subset_rfl
    rwa [Finset.sdiff_self, hQempty, one_mul] at h
  have hQuniv : Q Finset.univ = P.prob (⋂ i, (A i)ᶜ) := by
    show P.prob (⋂ j ∈ (Finset.univ : Finset ι), (A j)ᶜ) = P.prob (⋂ i, (A i)ᶜ)
    congr 1
    ext ω; simp
  calc ∏ i, (1 - x i) = ∏ j ∈ (Finset.univ : Finset ι), (1 - x j) := rfl
    _ ≤ Q Finset.univ := hpeelG Finset.univ
    _ = P.prob (⋂ i, (A i)ᶜ) := hQuniv

end Work.Deep.Prob.LLL
