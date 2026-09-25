import Mathlib.RingTheory.Valuation.ValuationSubring

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical

namespace Commons.RingTheory.Valuation

noncomputable section

/-- Two proofs of nonemptiness of a finset give the same `Finset.sup'`. -/
private lemma clusterSup'_irrel {α β : Type*} [SemilatticeSup α] {s : Finset β}
    (H H' : s.Nonempty) (f : β → α) : s.sup' H f = s.sup' H' f := by
  rw [Subsingleton.elim H H']

/-- The fibre of a surjection is nonempty. -/
private lemma fiber_nonempty {ι σ : Type*} [Fintype ι] (f : ι → σ) (hf : Function.Surjective f)
    (u : σ) : (Finset.univ.filter (fun i => f i = u)).Nonempty := by
  obtain ⟨i, hi⟩ := hf u
  exact ⟨i, by simp [hi]⟩

/-- The supremum of the valuation subrings `C i` over the fibre of `f` at `u`. -/
private def fibSup {F : Type*} [Field F] {ι σ : Type} [Fintype ι]
    (C : ι → ValuationSubring F) (f : ι → σ) (hf : Function.Surjective f) (u : σ) :
    ValuationSubring F :=
  (Finset.univ.filter (fun i => f i = u)).sup' (fiber_nonempty f hf u) C

private lemma fibSup_le_iff {F : Type*} [Field F] {ι σ : Type} [Fintype ι]
    {C : ι → ValuationSubring F} {f : ι → σ} {hf : Function.Surjective f} {u : σ}
    {a : ValuationSubring F} : fibSup C f hf u ≤ a ↔ ∀ i, f i = u → C i ≤ a := by
  simp only [fibSup]
  rw [Finset.sup'_le_iff]
  constructor
  · intro h i hi; exact h i (by simp [hi])
  · intro h i hi; exact h i (by simpa using hi)

private lemma le_fibSup {F : Type*} [Field F] {ι σ : Type} [Fintype ι]
    {C : ι → ValuationSubring F} {f : ι → σ} {hf : Function.Surjective f} {u : σ} {i : ι}
    (hi : f i = u) : C i ≤ fibSup C f hf u := by
  simp only [fibSup]
  rw [clusterSup'_irrel (fiber_nonempty f hf u) ⟨i, by simp [hi]⟩ C]
  exact Finset.le_sup' C (by simp [hi])

private lemma fibSup_eq_of_forall {F : Type*} [Field F] {ι σ : Type} [Fintype ι]
    {C : ι → ValuationSubring F} {f : ι → σ} {hf : Function.Surjective f} {u : σ}
    {a : ValuationSubring F} (h : ∀ i, f i = u → C i = a) : fibSup C f hf u = a := by
  simp only [fibSup]
  exact Finset.sup'_eq_of_forall _ C (fun i hi => h i (by simpa using hi))

/-- Merging two clusters of a fibre partition: if the two cluster suprema do not exhaust `⊤`,
the two clusters can be merged into a single (larger) cluster, decreasing the number of
clusters by one while keeping all cluster suprema proper. -/
private lemma merge_witness {F : Type*} [Field F] {ι σ : Type} [Fintype ι] [Fintype σ]
    (C : ι → ValuationSubring F) (f : ι → σ) (hf : Function.Surjective f)
    (hfne : ∀ u : σ, fibSup C f hf u ≠ ⊤)
    (s t : σ) (hst : s ≠ t)
    (hne : fibSup C f hf s ⊔ fibSup C f hf t ≠ ⊤) :
    ∃ (σ' : Type) (_ : Fintype σ') (g : ι → σ') (hg : Function.Surjective g),
      Nat.card σ' = Nat.card σ - 1 ∧ ∀ u : σ', fibSup C g hg u ≠ ⊤ := by
  have htne : t ≠ s := fun hh => hst hh.symm
  let g : ι → {u : σ // u ≠ s} := fun i => if h : f i = s then ⟨t, htne⟩ else ⟨f i, h⟩
  have gval : ∀ i, (g i).1 = if f i = s then t else f i := by
    intro i
    by_cases h : f i = s
    · simp only [g, h, dif_pos, if_pos]
    · simp only [g, h, dif_neg, if_neg, not_false_iff]
  have hg : Function.Surjective g := by
    intro u
    obtain ⟨i, hi⟩ := hf u.1
    have hfi : f i ≠ s := by rw [hi]; exact u.2
    exact ⟨i, Subtype.ext (by rw [gval i, if_neg hfi, hi])⟩
  refine ⟨{u : σ // u ≠ s}, inferInstance, g, hg, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl (fun u : σ => u = s), Fintype.card_subtype_eq]
  · intro u
    by_cases hut : u.1 = t
    · have key : fibSup C g hg u = fibSup C f hf s ⊔ fibSup C f hf t := by
        apply le_antisymm
        · rw [fibSup_le_iff]
          intro i hi
          have hval : (if f i = s then t else f i) = t := by
            have h1 := congrArg Subtype.val hi
            rw [gval i, hut] at h1
            exact h1
          rcases eq_or_ne (f i) s with h | h
          · exact le_trans (le_fibSup (f := f) (hf := hf) (u := s) (i := i) h) le_sup_left
          · have hit : f i = t := by rwa [if_neg h] at hval
            exact le_trans (le_fibSup (f := f) (hf := hf) (u := t) (i := i) hit) le_sup_right
        · apply sup_le
          · rw [fibSup_le_iff]
            intro i hi
            exact le_fibSup (f := g) (hf := hg) (u := u) (i := i)
              (Subtype.ext (by rw [gval i, if_pos hi, hut.symm]))
          · rw [fibSup_le_iff]
            intro i hi
            exact le_fibSup (f := g) (hf := hg) (u := u) (i := i)
              (Subtype.ext (by rw [gval i, if_neg (by rw [hi]; exact htne), hi, hut.symm]))
      rw [key]; exact hne
    · have key : fibSup C g hg u = fibSup C f hf u.1 := by
        apply le_antisymm
        · rw [fibSup_le_iff]
          intro i hi
          have hval : (if f i = s then t else f i) = u.1 := by
            have h1 := congrArg Subtype.val hi
            rw [gval i] at h1
            exact h1
          rcases eq_or_ne (f i) s with h | h
          · rw [if_pos h] at hval
            exact absurd hval.symm hut
          · have hfi : f i = u.1 := by rwa [if_neg h] at hval
            exact le_fibSup (f := f) (hf := hf) (u := u.1) (i := i) hfi
        · rw [fibSup_le_iff]
          intro i hi
          have hfi : f i ≠ s := by rw [hi]; exact u.2
          exact le_fibSup (f := g) (hf := hg) (u := u) (i := i)
            (Subtype.ext (by rw [gval i, if_neg hfi, hi]))
      rw [key]; exact hfne u.1

theorem exists_cluster_decomposition_nonempty {F : Type*} [Field F] {ι : Type} [Fintype ι] [Nonempty ι]
    (C : ι → ValuationSubring F) (hC : ∀ i, C i ≠ ⊤)
    (hincomp : ∀ i j, i ≠ j → ¬ (C i ≤ C j)) :
    ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (f : ι → σ) (E : σ → ValuationSubring F),
      Function.Surjective f ∧
      (∀ i, C i ≤ E (f i)) ∧
      (∀ s, E s ≠ ⊤) ∧
      (∀ s t, s ≠ t → E s ⊔ E t = ⊤) ∧
      (Nat.card σ = 1 ∨ ∀ s, Nat.card {i // f i = s} < Nat.card ι) := by
  let P : ℕ → Prop := fun k =>
    ∃ (σ : Type) (_ : Fintype σ) (f : ι → σ) (hf : Function.Surjective f),
      Nat.card σ = k ∧ ∀ u : σ, fibSup C f hf u ≠ ⊤
  have hex : ∃ k, P k := by
    refine ⟨Fintype.card ι, Fin (Fintype.card ι), inferInstance, Fintype.equivFin ι,
      (Fintype.equivFin ι).surjective, ?_, ?_⟩
    · rw [Nat.card_fin]
    · intro u
      have heq : fibSup C (Fintype.equivFin ι) (Fintype.equivFin ι).surjective u =
          C ((Fintype.equivFin ι).symm u) :=
        fibSup_eq_of_forall (fun i hi =>
          congrArg C ((Equiv.eq_symm_apply (Fintype.equivFin ι)).mpr hi))
      rw [heq]
      exact hC _
  set m := Nat.find hex with hm
  have hmP : P m := Nat.find_spec hex
  have hmin : ∀ k, k < m → ¬ P k := fun k hk => Nat.find_min hex hk
  obtain ⟨σ, hσfin, f, hf, hcard, hfne⟩ := hmP
  letI : Fintype σ := hσfin
  have hneσ : Nonempty σ := ⟨f (Classical.choice (inferInstance : Nonempty ι))⟩
  letI : Nonempty σ := hneσ
  have hmpos : 0 < m := by rw [← hcard]; exact Nat.card_pos
  refine ⟨σ, hσfin, hneσ, f, fun u => fibSup C f hf u, hf, ?_, hfne, ?_, ?_⟩
  · intro i
    exact le_fibSup (f := f) (hf := hf) (u := f i) (i := i) rfl
  · intro s t hst
    by_contra hcon
    obtain ⟨σ', hσ'fin, g, hg, hcard', hgne⟩ := merge_witness C f hf hfne s t hst hcon
    have hP : P (Nat.card σ') := ⟨σ', hσ'fin, g, hg, rfl, hgne⟩
    have hlt : Nat.card σ' < m := by
      rw [hcard', hcard]
      omega
    exact (hmin (Nat.card σ') hlt) hP
  · by_cases h1 : Nat.card σ = 1
    · exact Or.inl h1
    · refine Or.inr (fun s => ?_)
      have h2 : 1 < Fintype.card σ := by
        rw [← Nat.card_eq_fintype_card]; omega
      obtain ⟨t, ht⟩ := Fintype.exists_ne_of_one_lt_card h2 s
      obtain ⟨it, hit⟩ := hf t
      have hcardlt : Fintype.card {i // f i = s} < Fintype.card ι :=
        Fintype.card_subtype_lt (p := fun i => f i = s) (x := it) (by rw [hit]; exact ht)
      simpa only [Nat.card_eq_fintype_card] using hcardlt

end

end Commons.RingTheory.Valuation