import Mathlib

namespace Work.SimplyConnected.ABS

/-- If `l` is an `R`-chain whose last element is `m`, and `m :: ms` is an `R`-chain,
then `l ++ ms` is an `R`-chain: the junction is `R` between `m` and the second
element of the second chain. -/
private lemma isChain_append_tail {ι : Type*} {R : ι → ι → Prop} {m : ι} {l ms : List ι}
    (hl : l.IsChain R) (hM : (m :: ms).IsChain R) (h : l.getLast? = some m) :
    (l ++ ms).IsChain R := by
  rw [List.isChain_append]
  exact ⟨hl, hM.tail, fun x hx y hy => by
    rw [h] at hx
    rw [Option.mem_some_iff] at hx
    subst hx
    exact (List.isChain_cons.mp hM).1 y hy⟩

/-- If `b` and `v` are related by the reflexive transitive closure of `R`, there is an
`R`-chain from `b` to `v`, i.e. a list with head `b`, last element `v`, and every
element of which is reachable from `b`. -/
private lemma exists_chain_of_reflTransGen {ι : Type*} {R : ι → ι → Prop} {b v : ι}
    (h : Relation.ReflTransGen R b v) :
    ∃ P : List ι, P.IsChain R ∧ P.head? = some b ∧ P.getLast? = some v ∧
      ∀ x ∈ P, Relation.ReflTransGen R b x := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨[v], List.isChain_singleton v, rfl, rfl, fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact Relation.ReflTransGen.refl⟩
  · intro c d hcd hdb ih
    obtain ⟨P, hPc, hPh, hPl, hPr⟩ := ih
    refine ⟨c :: P, ?_, rfl, ?_, ?_⟩
    · refine List.IsChain.cons hPc ?_
      intro y hy
      rw [hPh] at hy
      rw [Option.mem_some_iff] at hy
      subst hy
      exact hcd
    · rw [List.getLast?_cons, hPl]
      rfl
    · intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Relation.ReflTransGen.refl
      · exact (Relation.ReflTransGen.single hcd).trans (hPr x hx)

theorem chain_of_reflTransGen_finset {ι : Type*} {R : ι → ι → Prop} (hR : ∀ a b, R a b → R b a)
    {a : ι} {s : Finset ι} (hs : ∀ i ∈ s, Relation.ReflTransGen R a i) :
    ∃ L : List ι, L.IsChain R ∧ L.head? = some a ∧ (∀ i ∈ s, i ∈ L) ∧
      (∀ i ∈ L, Relation.ReflTransGen R a i) := by
  classical
  have hsymm : Std.Symm R := ⟨hR⟩
  have key : ∀ (s : Finset ι) (b : ι), (∀ i ∈ s, Relation.ReflTransGen R b i) →
      ∃ L : List ι, L.IsChain R ∧ L.head? = some b ∧ (∀ i ∈ s, i ∈ L) ∧
        (∀ i ∈ L, Relation.ReflTransGen R b i) := by
    intro s
    refine Finset.induction ?_ ?_ s
    · intro b _
      exact ⟨[b], List.isChain_singleton b, rfl, by simp, fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact .refl⟩
    · intro i t hit ih b hb
      have hbi : Relation.ReflTransGen R b i := hb i (Finset.mem_insert_self i t)
      have ht : ∀ j ∈ t, Relation.ReflTransGen R i j := fun j hj =>
        (Std.Symm.symm b i hbi).trans (hb j (Finset.mem_insert_of_mem hj))
      obtain ⟨Q, hQc, hQh, hQt, hQr⟩ := ih i ht
      obtain ⟨P, hPc, hPh, hPl, hPr⟩ := exists_chain_of_reflTransGen hbi
      obtain ⟨Q', rfl⟩ := List.head?_eq_some_iff.mp hQh
      have hPne : P ≠ [] := by
        intro hh; rw [hh] at hPh; simp at hPh
      have hiP : i ∈ P := by
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hPl
        exact List.mem_concat_self
      refine ⟨P ++ Q', isChain_append_tail hPc hQc hPl, ?_, ?_, ?_⟩
      · rw [List.head?_append_of_ne_nil P hPne, hPh]
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact List.mem_append_left _ hiP
        · refine List.mem_append_right _ ?_
          rcases List.mem_cons.mp (hQt j hj) with heq | hmem
          · exfalso; exact hit (heq ▸ hj)
          · exact hmem
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hPr x hx
        · exact hbi.trans (hQr x (List.mem_cons_of_mem i hx))
  exact key s a hs

end Work.SimplyConnected.ABS
