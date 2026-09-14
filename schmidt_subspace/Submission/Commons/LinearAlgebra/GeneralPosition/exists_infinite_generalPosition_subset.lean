import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.GeneralPosition

open Submodule

/-- `Good K V n Y` means: every finite subset of `Y` of cardinality at most `n` is linearly
independent (with respect to `id : V → V`). -/
def Good (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (n : ℕ) (Y : Set V) : Prop :=
  ∀ T : Finset V, (↑T : Set V) ⊆ Y → T.card ≤ n → LinearIndepOn K id (↑T : Set V)

lemma good_empty (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (n : ℕ) :
    Good K V n (∅ : Set V) := by
  intro T hT _
  have hTe : (T : Set V) = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hT hx)
  rw [hTe]
  exact linearIndepOn_empty K (id : V → V)

/-- **General-position extraction.** Let `V` be a finite-dimensional vector space over a field
`K` and let `X ⊆ V` be infinite. If `X` is not contained in any finite union of proper
subspaces, then there is an infinite subset `Y ⊆ X` in *general position*: every finite
subset of `Y` with at most `Module.finrank K V` elements is linearly independent
(equivalently `LinearIndepOn K id ↑T` for such `T`).

This is a greedy construction: enumerate points of `X`, at each step avoiding the
(finitely many, proper) spans of the previously chosen subsets of size `≤ finrank K V - 1`,
which is possible because `X` is not finitely covered by proper subspaces. -/
theorem exists_infinite_generalPosition_subset {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (X : Set V) (hX : X.Infinite)
    (hcover : ¬ ∃ T : Set (Submodule K V), T.Finite ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x ∈ X, ∃ W ∈ T, x ∈ W) :
    ∃ Y : Set V, Y ⊆ X ∧ Y.Infinite ∧
      ∀ T : Finset V, (↑T : Set V) ⊆ Y → T.card ≤ Module.finrank K V →
        LinearIndepOn K id (↑T : Set V) := by
  by_cases hle : Module.finrank K V ≤ 1
  · -- small dimension: take `Y = X \ {0}`
    refine ⟨X \ {0}, Set.sdiff_subset, hX.sdiff (Set.finite_singleton 0), ?_⟩
    intro T hT hcard
    rw [linearIndepOn_iff_notMem_span]
    intro i hi
    have hle1 : T.card ≤ 1 := le_trans hcard hle
    have hsub : (↑T : Set V) ⊆ {i} := by
      intro j hj
      exact Finset.card_le_one.mp hle1 j hj i hi
    have hdiff : (↑T : Set V) \ {i} = ∅ := Set.sdiff_eq_empty.mpr hsub
    have himg : id '' ((↑T : Set V) \ {i}) = ∅ := by rw [hdiff, Set.image_empty]
    show i ∉ span K (id '' ((↑T : Set V) \ {i}))
    rw [himg, Submodule.span_empty, Submodule.mem_bot]
    exact fun h => (hT hi).2 (by simpa using h)
  · -- large dimension: a maximal `Good` subset of `X` is infinite (Zorn)
    push Not at hle
    classical
    let S : Set (Set V) := { Y | Y ⊆ X ∧ Good K V (Module.finrank K V) Y }
    have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
      intro c hc hic
      rcases c.eq_empty_or_nonempty with rfl | hne
      · exact ⟨∅, ⟨Set.empty_subset X, good_empty K V (Module.finrank K V)⟩,
          fun s hs => absurd hs (Set.notMem_empty s)⟩
      · refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
        · rintro x ⟨s, hs, hxs⟩
          exact (hc hs).1 hxs
        · intro T hT hcard
          obtain ⟨s, hs, hsub⟩ := hic.directedOn.exists_mem_subset_of_finite_of_subset_sUnion
            hne T.finite_toSet hT
          exact (hc hs).2 T hsub hcard
    obtain ⟨m, hmS, hmmax⟩ := zorn_subset S hchain
    have hminf : m.Infinite := by
      by_contra hcon
      have hfin : m.Finite := Set.not_infinite.mp hcon
      let B : Finset (Submodule K V) :=
        Finset.image (fun s : Finset V => span K (↑s : Set V))
          (Finset.filter (fun s : Finset V => s.card ≤ Module.finrank K V - 1)
            (hfin.toFinset).powerset)
      have mem_B : ∀ s : Finset V, (↑s : Set V) ⊆ m → s.card ≤ Module.finrank K V - 1 →
          span K (↑s : Set V) ∈ (↑B : Set (Submodule K V)) := by
        intro s hs hsc
        rw [Finset.mem_coe, Finset.mem_image]
        refine ⟨s, ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, hsc⟩
        rwa [← Finset.coe_subset, hfin.coe_toFinset]
      have hBproper : ∀ W ∈ (↑B : Set (Submodule K V)), W ≠ ⊤ := by
        intro W hW htop
        rw [Finset.mem_coe, Finset.mem_image] at hW
        obtain ⟨s, hs, rfl⟩ := hW
        rw [Finset.mem_filter, Finset.mem_powerset] at hs
        obtain ⟨-, hsc⟩ := hs
        have hle' : Module.finrank K (span K (↑s : Set V)) ≤ s.card :=
          finrank_span_finset_le_card s
        rw [htop, finrank_top] at hle'
        omega
      have hcoverB : ¬ (∀ x ∈ X, ∃ W ∈ (↑B : Set (Submodule K V)), x ∈ W) :=
        fun hc => hcover ⟨(↑B : Set (Submodule K V)), B.finite_toSet, hBproper, hc⟩
      push Not at hcoverB
      obtain ⟨x, hxX, hxout⟩ := hcoverB
      have hxnotm : x ∉ m := by
        intro hxm
        have hmem : span K (↑({x} : Finset V) : Set V) ∈ (↑B : Set (Submodule K V)) := by
          refine mem_B {x} ?_ ?_
          · intro z hz
            rw [Finset.mem_coe, Finset.mem_singleton] at hz
            rw [hz]; exact hxm
          · rw [Finset.card_singleton]; omega
        exact hxout _ hmem (Submodule.subset_span (by simp))
      have hm'S : insert x m ∈ S := by
        refine ⟨?_, ?_⟩
        · rintro z (rfl | hz)
          · exact hxX
          · exact hmS.1 hz
        · intro T hT hcard
          by_cases hxT : x ∈ T
          · have hTeq : T = insert x (T.erase x) := (Finset.insert_erase hxT).symm
            have hcard' : (T.erase x).card ≤ Module.finrank K V - 1 := by
              have := Finset.card_erase_add_one hxT
              omega
            have hmem' : (↑(T.erase x) : Set V) ⊆ m := by
              intro z hz
              have hzT : z ∈ T := Finset.mem_of_mem_erase hz
              have hz' : z ∈ (insert x m : Set V) := hT hzT
              rcases Set.mem_insert_iff.mp hz' with rfl | hzm
              · exact absurd rfl (Finset.mem_erase.mp hz).1
              · exact hzm
            have hgood0 : LinearIndepOn K id (↑(T.erase x) : Set V) :=
              hmS.2 (T.erase x) hmem' (le_trans hcard' (Nat.sub_le _ _))
            have hxns : x ∉ span K (↑(T.erase x) : Set V) :=
              fun h => hxout _ (mem_B (T.erase x) hmem' hcard') h
            rw [hTeq, Finset.coe_insert]
            exact hgood0.id_insert hxns
          · have hTm : (↑T : Set V) ⊆ m := by
              intro z hz
              have hz' : z ∈ (insert x m : Set V) := hT hz
              rcases Set.mem_insert_iff.mp hz' with rfl | hzm
              · exact absurd hz hxT
              · exact hzm
            exact hmS.2 T hTm hcard
      have hsub2 : (insert x m : Set V) ⊆ m := hmmax hm'S (Set.subset_insert x m)
      exact hxnotm (hsub2 (Set.mem_insert x m))
    exact ⟨m, hmS.1, hminf, hmS.2⟩

end Commons.LinearAlgebra.GeneralPosition