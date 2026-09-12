import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Order.CompletePartialOrder

open scoped BigOperators

noncomputable section

namespace Commons.LinearAlgebra.Independence

/-- Given a linearly independent pair `a, b` in a real vector space `E` of dimension
`n + 1` and `n` further vectors `v i` such that the whole family `{a, b} ∪ range v`
spans `E`, there is a linearly independent `(n+1)`-element subfamily still containing
`a` and `b`, obtained by dropping one of the `v i`'s. -/
theorem li_pair_drop_some {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = n + 1)
    {a b : E} (hab : LinearIndependent ℝ (![a, b] : Fin 2 → E))
    (v : Fin n → E)
    (hspan : Submodule.span ℝ ({a, b} ∪ Set.range v) = ⊤) :
    ∃ f : Fin (n + 1) → E,
      LinearIndependent ℝ f ∧ f 0 = a ∧ f 1 = b ∧
      ∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → f i ∈ Set.range v := by
  classical
  by_cases hn0 : n = 0
  · subst n
    exfalso
    have hcard_eq : Fintype.card (Fin 2) = (Set.range (![a, b] : Fin 2 → E)).finrank ℝ :=
      (linearIndependent_iff_card_eq_finrank_span (R := ℝ) (M := E) (b := ![a, b])).mp hab
    have h2le : 2 ≤ Module.finrank ℝ E := by
      have hc : (2 : ℕ) = Fintype.card (Fin 2) := by simp
      calc
        (2 : ℕ) = Fintype.card (Fin 2) := hc
        _ = (Set.range (![a, b] : Fin 2 → E)).finrank ℝ := hcard_eq
        _ ≤ Module.finrank ℝ E := by
          unfold Set.finrank
          exact Submodule.finrank_le (Submodule.span ℝ (Set.range (![a, b] : Fin 2 → E)))
    omega
  · have hn : 1 ≤ n := by omega
    let S : Set E := ({a, b} : Set E) ∪ Set.range v
    have hab_set : LinearIndepOn ℝ id ({a, b} : Set E) := by
      have h1 : LinearIndepOn ℝ (![a, b] : Fin 2 → E) (Set.univ : Set (Fin 2)) := by
        exact (linearIndepOn_univ_iff (v := (![a, b] : Fin 2 → E))).2 hab
      have h2 := (LinearIndepOn_iff_linearIndepOn_image_injOn (R := ℝ)
          (v := (![a, b] : Fin 2 → E)) (s := Set.univ)).1 h1
      have hset' : LinearIndepOn ℝ id (Set.range (![a, b] : Fin 2 → E)) := by
        simpa using h2.1
      have hrange : Set.range (![a, b] : Fin 2 → E) = ({a, b} : Set E) := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp
        · intro hx
          simp at hx
          rcases hx with rfl | rfl
          · exact ⟨0, by simp⟩
          · exact ⟨1, by simp⟩
      rwa [hrange] at hset'
    have hsub : ({a, b} : Set E) ⊆ S := by
      intro x hx
      exact Or.inl hx
    obtain ⟨B, hBsubS, h01subB, hSsubspanB, hBli⟩ :=
      exists_linearIndepOn_id_extension (K := ℝ) (V := E) (s := ({a, b} : Set E)) (t := S)
        hab_set hsub
    have hspanB_top : Submodule.span ℝ B = ⊤ := by
      apply le_antisymm
      · exact le_top
      · rw [← hspan]
        exact (Submodule.span_le).2 (by simpa [S] using hSsubspanB)
    have hS_fin : S.Finite := by
      refine Set.Finite.union ?_ ?_
      · have hf : ({b} : Set E).Finite := Set.finite_singleton b
        simpa using hf.insert a
      · exact Set.finite_range v
    have hB_fin : B.Finite := hS_fin.subset hBsubS
    haveI : Fintype B := hB_fin.fintype
    have hBcard : B.ncard = n + 1 := by
      have hspan_fin : Module.finrank ℝ (Submodule.span ℝ B) = B.ncard := by
        have h₁ := finrank_span_set_eq_card (R := ℝ) (s := B) hBli
        simpa [Set.toFinset_card] using h₁
      have hfinE : Module.finrank ℝ (Submodule.span ℝ B) = n + 1 := by
        calc Module.finrank ℝ (Submodule.span ℝ B) = Module.finrank ℝ E := by
              rw [hspanB_top]
              simp
            _ = n + 1 := hE
      rw [← hspan_fin]
      exact hfinE
    have hB_a : a ∈ B := h01subB (Or.inl rfl)
    have hB_b : b ∈ B := h01subB (Or.inr rfl)
    have hne : a ≠ b := by
      intro h
      have hinj : Function.Injective (![a, b] : Fin 2 → E) := hab.injective
      have h01 : (0 : Fin 2) = (1 : Fin 2) := hinj (by simp [h])
      norm_num at h01
    -- build the answer
    let C : Set E := B \ ({a, b} : Set E)
    have hCfin : C.Finite := hB_fin.subset (by intro x hx; exact hx.1)
    have hCcard : C.ncard = n - 1 := by
      have hdisj : Disjoint C ({a, b} : Set E) := by
        rw [Set.disjoint_left]
        intro x hxC hxab
        exact hxC.2 hxab
      have hBdecomp : B = C ∪ ({a, b} : Set E) := by
        ext x
        constructor
        · intro hxB
          by_cases hxab : x ∈ ({a, b} : Set E)
          · exact Or.inr hxab
          · exact Or.inl ⟨hxB, hxab⟩
        · rintro (⟨hxB, hxab⟩ | hxab)
          · exact hxB
          · rcases hxab with rfl | rfl <;> assumption
      have hp2 : ({a, b} : Set E).ncard = 2 := by
        rw [show ({a, b} : Set E) = insert a ({b} : Set E) by ext x; simp]
        rw [Set.ncard_insert_of_notMem (a := a) (s := ({b} : Set E)) (by simpa using hne)]
        simp
      have hcardunion : B.ncard = C.ncard + 2 := by
        calc
          B.ncard = (C ∪ ({a, b} : Set E)).ncard := by rw [hBdecomp]
          _ = C.ncard + ({a, b} : Set E).ncard := Set.ncard_union_eq hdisj hCfin (by simpa using (Set.finite_pair a b).finite)
          _ = C.ncard + 2 := by rw [hp2]
      have htotal : C.ncard + 2 = n + 1 := by omega
      omega
    have hCsub : C ⊆ Set.range v := by
      intro x hxC
      have hxS : x ∈ ({a, b} : Set E) ∪ Set.range v := hBsubS hxC.1
      rcases hxS with hxab | hxv
      · exfalso; exact hxC.2 hxab
      · exact hxv
    have hCno_a : a ∉ C := by simp [C]
    have hCno_b : b ∉ C := by simp [C]
    have hCsubB : C ⊆ B := by intro x hx; exact hx.1
    letI : Fintype C := hCfin.fintype
    have hCcard' : Fintype.card C = n - 1 := by simpa using hCcard
    let eC : Fin (n - 1) ≃ {x : E // x ∈ C} := (Fintype.equivFinOfCardEq hCcard').symm
    let f : Fin (n + 1) → E := fun i =>
      if h0 : (i : ℕ) = 0 then a
      else if h1 : (i : ℕ) = 1 then b
      else (eC ⟨(i : ℕ) - 2, by omega⟩).1
    have hmod : 1 % (n + 1) = 1 := by
      rw [Nat.mod_eq_of_lt]
      omega
    have hf0 : f 0 = a := by
      simp [f]
    have hf1 : f 1 = b := by
      simp [f, hmod]
      intro hn0
      omega
    have hf_head0 : ∀ i : Fin (n + 1), (i : ℕ) = 0 → f i = a := by
      intro i hi
      unfold f
      rw [dif_pos hi]
    have hf_head1 : ∀ i : Fin (n + 1), (i : ℕ) = 1 → f i = b := by
      intro i hi
      have hi0 : (i : ℕ) ≠ 0 := by omega
      unfold f
      rw [dif_neg hi0, dif_pos hi]
    have hf_memC : ∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → f i ∈ C := by
      intro i hi
      have hi0 : (i : ℕ) ≠ 0 := by omega
      have hi1 : (i : ℕ) ≠ 1 := by omega
      have hval : f i = (eC ⟨(i : ℕ) - 2, by omega⟩).1 := by
        unfold f
        rw [dif_neg hi0, dif_neg hi1]
      rw [hval]
      exact (eC ⟨(i : ℕ) - 2, by omega⟩).2
    have hf_tail_val : ∀ (i : Fin (n + 1)), 2 ≤ (i : ℕ) → ∀ j : Fin (n - 1),
        (j : ℕ) = (i : ℕ) - 2 → f i = (eC j).1 := by
      intro i hi j hjv
      have hi0 : (i : ℕ) ≠ 0 := by omega
      have hi1 : (i : ℕ) ≠ 1 := by omega
      unfold f
      rw [dif_neg hi0, dif_neg hi1]
      have hteq : (⟨(i : ℕ) - 2, by omega⟩ : Fin (n - 1)) = j := by
        apply Fin.ext
        change (i : ℕ) - 2 = (j : ℕ)
        omega
      rw [hteq]
    have htri : ∀ k : Fin (n + 1), (k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ 2 ≤ (k : ℕ) := by
      intro k
      have hk0 : (k : ℕ) = 0 ∨ 1 ≤ (k : ℕ) := by omega
      rcases hk0 with hk0 | hk1
      · exact Or.inl hk0
      · by_cases hk : (k : ℕ) = 1
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (by omega))
    have hfinj : Function.Injective f := by
      intro i j hij
      rcases htri i with hi0 | hi1 | hii2
      · rcases htri j with hj0 | hj1 | hjj2
        · apply Fin.ext; omega
        · exfalso
          apply hne
          rwa [hf_head0 i hi0, hf_head1 j hj1] at hij
        · exfalso
          apply hCno_a
          have hmem : f j ∈ C := hf_memC j hjj2
          rwa [← hij, hf_head0 i hi0] at hmem
      · rcases htri j with hj0 | hj1 | hjj2
        · exfalso
          apply hne.symm
          rwa [hf_head1 i hi1, hf_head0 j hj0] at hij
        · apply Fin.ext; omega
        · exfalso
          apply hCno_b
          have hmem : f j ∈ C := hf_memC j hjj2
          rwa [← hij, hf_head1 i hi1] at hmem
      · rcases htri j with hj0 | hj1 | hjj2
        · exfalso
          apply hCno_a
          have hmem : f i ∈ C := hf_memC i hii2
          rwa [hij, hf_head0 j hj0] at hmem
        · exfalso
          apply hCno_b
          have hmem : f i ∈ C := hf_memC i hii2
          rwa [hij, hf_head1 j hj1] at hmem
        · have hji : (⟨(i : ℕ) - 2, by omega⟩ : Fin (n - 1)) = ⟨(j : ℕ) - 2, by omega⟩ := by
            apply eC.injective
            apply Subtype.ext
            have h1 : f i = (eC ⟨(i : ℕ) - 2, by omega⟩).1 :=
              hf_tail_val i hii2 ⟨(i : ℕ) - 2, by omega⟩ rfl
            have h2 : f j = (eC ⟨(j : ℕ) - 2, by omega⟩).1 :=
              hf_tail_val j hjj2 ⟨(j : ℕ) - 2, by omega⟩ rfl
            exact h1.symm.trans (hij.trans h2)
          apply Fin.ext
          have hvaleq : (i : ℕ) - 2 = (j : ℕ) - 2 := by
            have hv := congrArg (fun z : Fin (n - 1) => (z : ℕ)) hji
            simpa using hv
          omega
    have hfB : ∀ i : Fin (n + 1), f i ∈ B := by
      intro i
      rcases htri i with hi0 | hi1 | hii2
      · simpa [hf_head0 i hi0] using hB_a
      · simpa [hf_head1 i hi1] using hB_b
      · exact hCsubB (hf_memC i hii2)
    have hli : LinearIndependent ℝ f := by
      have hrange_sub : Set.range f ⊆ B := by
        intro x hx
        rcases hx with ⟨i, rfl⟩
        exact hfB i
      have hli_range : LinearIndepOn ℝ id (Set.range f) := LinearIndepOn.mono hBli hrange_sub
      have h1 : LinearIndepOn ℝ id (f '' Set.univ) ∧ Set.InjOn f Set.univ := by
        constructor
        · simpa [Set.image_univ] using hli_range
        · exact hfinj.injOn
      have h2 : LinearIndepOn ℝ f (Set.univ : Set (Fin (n + 1))) :=
        (LinearIndepOn_iff_linearIndepOn_image_injOn (R := ℝ) (v := f) (s := Set.univ)).2 h1
      exact (linearIndepOn_univ_iff (v := f)).1 h2
    refine ⟨f, hli, hf0, hf1, ?_⟩
    intro i hi2
    exact hCsub (hf_memC i hi2)

end Commons.LinearAlgebra.Independence
