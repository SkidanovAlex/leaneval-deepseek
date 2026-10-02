import Mathlib.Data.Set.Card
import Mathlib.Order.CompletePartialOrder

namespace Commons.Combinatorics.Finset

/-- A finite set `A` of even cardinality `2*k` can be partitioned into two-element
subsets (a set of disjoint unordered pairs covering `A`). -/
lemma exists_pair_partition_of_ncard {V : Type*} [Fintype V] (k : ℕ) (A : Set V)
    (hA : A.ncard = 2 * k) :
    ∃ P : Set (Set V),
      (∀ e ∈ P, e ⊆ A) ∧
      (∀ e ∈ P, ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ e = ({u, v} : Set V)) ∧
      (∀ x ∈ A, ∃ e ∈ P, x ∈ e) ∧
      P.Pairwise (fun e₁ e₂ => Disjoint e₁ e₂) := by
  classical
  induction k generalizing A with
  | zero =>
      have hAempty : A = ∅ := (Set.ncard_eq_zero (s := A)).mp (by simpa using hA)
      refine ⟨∅, ?_, ?_, ?_, ?_⟩ <;> simp [hAempty]
  | succ k ih =>
      have hAcard : A.ncard = 2 * k + 2 := by omega
      have hExists : ∃ a ∈ A, ∃ b ∈ A, a ≠ b := by
        by_contra hc
        push Not at hc
        have hle : A.ncard ≤ 1 := (Set.ncard_le_one (s := A)).mpr hc
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := hExists
      have hbA : b ∈ A \ {a} :=
        (Set.mem_sdiff b).mpr ⟨hb, by simpa using hab.symm⟩
      have hA'' : ((A \ {a}) \ {b}).ncard = 2 * k := by
        rw [Set.ncard_sdiff_singleton_of_mem hbA, Set.ncard_sdiff_singleton_of_mem ha]
        omega
      obtain ⟨P, hsub, hpair, hcover, hdisj⟩ := ih ((A \ {a}) \ {b}) hA''
      have hBA : ((A \ {a}) \ {b}) ⊆ A := by
        intro x hx
        exact ((Set.mem_sdiff x).mp ((Set.mem_sdiff x).mp hx).1).1
      refine ⟨insert ({a, b} : Set V) P, ?_, ?_, ?_, ?_⟩
      · intro e he
        rw [Set.mem_insert_iff] at he
        rcases he with rfl | he
        · exact Set.pair_subset_iff.mpr ⟨ha, hb⟩
        · exact (hsub e he).trans hBA
      · intro e he
        rw [Set.mem_insert_iff] at he
        rcases he with rfl | he
        · exact ⟨a, ha, b, hb, hab, rfl⟩
        · obtain ⟨u, hu, v, hv, huv, heq⟩ := hpair e he
          exact ⟨u, hBA hu, v, hBA hv, huv, heq⟩
      · intro x hx
        by_cases hxa : x = a
        · exact ⟨{a, b}, Set.mem_insert_iff.mpr (Or.inl rfl), by rw [hxa]; simp⟩
        · by_cases hxb : x = b
          · exact ⟨{a, b}, Set.mem_insert_iff.mpr (Or.inl rfl), by rw [hxb]; simp⟩
          · have hxB : x ∈ (A \ {a}) \ {b} :=
              (Set.mem_sdiff x).mpr
                ⟨(Set.mem_sdiff x).mpr ⟨hx, by simpa using hxa⟩, by simpa using hxb⟩
            obtain ⟨e, heP, hxe⟩ := hcover x hxB
            exact ⟨e, Set.mem_insert_iff.mpr (Or.inr heP), hxe⟩
      · rw [Set.pairwise_insert]
        refine ⟨hdisj, ?_⟩
        intro e he _
        have heA' : e ⊆ (A \ {a}) \ {b} := hsub e he
        have ha_not : a ∉ (A \ {a}) \ {b} := by
          intro hmem
          have h1 : a ∈ A \ {a} := ((Set.mem_sdiff a).mp hmem).1
          exact ((Set.mem_sdiff a).mp h1).2 (Set.mem_singleton_iff.mpr rfl)
        have hb_not : b ∉ (A \ {a}) \ {b} := by
          intro hmem
          exact ((Set.mem_sdiff b).mp hmem).2 (Set.mem_singleton_iff.mpr rfl)
        have hdisj_ab : Disjoint ({a, b} : Set V) e := by
          rw [Set.disjoint_left]
          intro x hx hxe
          have hx' : x = a ∨ x = b := by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
          rcases hx' with rfl | rfl
          · exact ha_not (heA' hxe)
          · exact hb_not (heA' hxe)
        exact ⟨hdisj_ab, hdisj_ab.symm⟩

theorem set_pair_partition {V : Type*} [Fintype V] [DecidableEq V] (A : Set V) (hpar : Even A.ncard) :
    ∃ P : Set (Set V),
      (∀ e ∈ P, e ⊆ A) ∧
      (∀ e ∈ P, ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ e = ({u, v} : Set V)) ∧
      (∀ x ∈ A, ∃ e ∈ P, x ∈ e) ∧
      P.Pairwise fun e₁ e₂ => Disjoint e₁ e₂ := by
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hpar
  exact exists_pair_partition_of_ncard k A hk

end Commons.Combinatorics.Finset