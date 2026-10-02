import Submission.Work.Deep.GKO.NarrowImports

namespace Work.Deep.GKO.OneFact

/-- Splitting the index set of a `Fin.cons`-family: the fibre of `x₀` contributes the new term
`a`, and the remaining fibres are those of the tail family. -/
lemma sum_filter_cons {X : Type*} [DecidableEq X] {n : ℕ}
    (a : ℕ) (g : Fin n → ℕ) (x₀ : X) (f : Fin n → X) (x : X) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) =>
        Fin.cons (α := fun _ => X) x₀ f k = x), Fin.cons (α := fun _ => ℕ) a g k)
      = (if x₀ = x then a else 0) +
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => f k = x), g k) := by
  rw [Finset.sum_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_filter]

/-- Common refinement of two compositions of an integer, with the sharp count
`t ≤ #{nonzero parts of lam} + #{nonzero parts of mu}`. -/
private lemma refine_aux {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (lam : ι → ℕ) (mu : κ → ℕ) (h : ∑ i, lam i = ∑ j, mu j) :
    ∃ (t : ℕ) (ν : Fin t → ℕ) (idxA : Fin t → ι) (idxB : Fin t → κ),
      (∀ k, 0 < ν k) ∧
      (∀ i, ∑ k ∈ Finset.univ.filter (fun k => idxA k = i), ν k = lam i) ∧
      (∀ j, ∑ k ∈ Finset.univ.filter (fun k => idxB k = j), ν k = mu j) ∧
      (∀ k, ν k ≤ lam (idxA k)) ∧ (∀ k, ν k ≤ mu (idxB k)) ∧
      t ≤ (Finset.univ.filter (fun i => lam i ≠ 0)).card +
            (Finset.univ.filter (fun j => mu j ≠ 0)).card := by
  have key : ∀ S : ℕ, ∀ (lam : ι → ℕ) (mu : κ → ℕ),
      (∑ i, lam i = S) → (∑ j, mu j = S) →
      ∃ (t : ℕ) (ν : Fin t → ℕ) (idxA : Fin t → ι) (idxB : Fin t → κ),
        (∀ k, 0 < ν k) ∧
        (∀ i, ∑ k ∈ Finset.univ.filter (fun k => idxA k = i), ν k = lam i) ∧
        (∀ j, ∑ k ∈ Finset.univ.filter (fun k => idxB k = j), ν k = mu j) ∧
        (∀ k, ν k ≤ lam (idxA k)) ∧ (∀ k, ν k ≤ mu (idxB k)) ∧
        t ≤ (Finset.univ.filter (fun i => lam i ≠ 0)).card +
              (Finset.univ.filter (fun j => mu j ≠ 0)).card := by
    intro S
    refine Nat.strongRecOn S ?_
    intro n ih lam mu hlam hmu
    by_cases hS : n = 0
    · -- all parts vanish; the empty refinement is the only one
      subst hS
      have hlam0 : ∀ i, lam i = 0 := by
        intro i
        have h1 : lam i ≤ ∑ i, lam i :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hmu0 : ∀ j, mu j = 0 := by
        intro j
        have h1 : mu j ≤ ∑ j, mu j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
        omega
      refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _⟩
      · intro k; exact k.elim0
      · intro i; simp [hlam0 i]
      · intro j; simp [hmu0 j]
      · intro k; exact k.elim0
      · intro k; exact k.elim0
    · -- the greedy step: chop `min (lam i₀) (mu j₀)` off the two sums
      have hSpos : 0 < n := Nat.pos_of_ne_zero hS
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hlam]; exact hS)
      obtain ⟨j₀, -, hj₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hmu]; exact hS)
      set c : ℕ := min (lam i₀) (mu j₀) with hcdef
      have hcpos : 0 < c := by
        rw [hcdef]
        exact Nat.lt_min.mpr ⟨Nat.pos_of_ne_zero hi₀, Nat.pos_of_ne_zero hj₀⟩
      have hc1 : c ≤ lam i₀ := by rw [hcdef]; exact min_le_left _ _
      have hc2 : c ≤ mu j₀ := by rw [hcdef]; exact min_le_right _ _
      set lam' : ι → ℕ := Function.update lam i₀ (lam i₀ - c) with hlam'def
      set mu' : κ → ℕ := Function.update mu j₀ (mu j₀ - c) with hmu'def
      have hle_lam : ∀ i, lam' i ≤ lam i := by
        intro i
        by_cases h' : i = i₀
        · subst h'; rw [hlam'def, Function.update_self]; exact Nat.sub_le _ _
        · rw [hlam'def, Function.update_of_ne h']
      have hle_mu : ∀ j, mu' j ≤ mu j := by
        intro j
        by_cases h' : j = j₀
        · subst h'; rw [hmu'def, Function.update_self]; exact Nat.sub_le _ _
        · rw [hmu'def, Function.update_of_ne h']
      have hlam_i₀_le : lam i₀ ≤ n := by
        rw [← hlam]
        exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i₀)
      have hmu_j₀_le : mu j₀ ≤ n := by
        rw [← hmu]
        exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j₀)
      have herase_lam : (∑ x ∈ Finset.univ \ ({i₀} : Finset ι), lam x) = n - lam i₀ := by
        have hh := Finset.sum_sdiff (Finset.subset_univ ({i₀} : Finset ι)) (f := lam)
        rw [Finset.sum_singleton, hlam] at hh
        exact Nat.eq_sub_of_add_eq hh
      have herase_mu : (∑ x ∈ Finset.univ \ ({j₀} : Finset κ), mu x) = n - mu j₀ := by
        have hh := Finset.sum_sdiff (Finset.subset_univ ({j₀} : Finset κ)) (f := mu)
        rw [Finset.sum_singleton, hmu] at hh
        exact Nat.eq_sub_of_add_eq hh
      have hsumlam' : ∑ i, lam' i = n - c := by
        rw [hlam'def, Finset.sum_update_of_mem (Finset.mem_univ i₀), herase_lam]
        omega
      have hsummu' : ∑ j, mu' j = n - c := by
        rw [hmu'def, Finset.sum_update_of_mem (Finset.mem_univ j₀), herase_mu]
        omega
      obtain ⟨t', ν', iA', iB', hpos', hA', hB', hleA', hleB', ht'⟩ :=
        ih (n - c) (Nat.sub_lt hSpos hcpos) lam' mu' hsumlam' hsummu'
      have hsubA : (Finset.univ.filter (fun i => lam' i ≠ 0)) ⊆
          (Finset.univ.filter (fun i => lam i ≠ 0)) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        have := hle_lam i
        omega
      have hsubB : (Finset.univ.filter (fun j => mu' j ≠ 0)) ⊆
          (Finset.univ.filter (fun j => mu j ≠ 0)) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        have := hle_mu j
        omega
      have hcardB : (Finset.univ.filter (fun j => mu' j ≠ 0)).card ≤
          (Finset.univ.filter (fun j => mu j ≠ 0)).card := Finset.card_le_card hsubB
      have hmemA : i₀ ∈ Finset.univ.filter (fun i => lam i ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩
      have hmemB : j₀ ∈ Finset.univ.filter (fun j => mu j ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hj₀⟩
      have hcount : t' + 1 ≤ (Finset.univ.filter (fun i => lam i ≠ 0)).card +
            (Finset.univ.filter (fun j => mu j ≠ 0)).card := by
        rcases le_total (lam i₀) (mu j₀) with hc | hc
        · -- the row `i₀` disappears, so the row count strictly drops
          have hceq : c = lam i₀ := by rw [hcdef]; exact min_eq_left hc
          have hz : lam' i₀ = 0 := by simp [hlam'def, Function.update_self, hceq]
          have hsub : (Finset.univ.filter (fun i => lam' i ≠ 0)) ⊆
              (Finset.univ.filter (fun i => lam i ≠ 0)).erase i₀ := by
            intro i hi
            rw [Finset.mem_erase]
            refine ⟨?_, hsubA hi⟩
            intro h'
            rw [h'] at hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact hi hz
          have hcard' : (Finset.univ.filter (fun i => lam' i ≠ 0)).card ≤
              (Finset.univ.filter (fun i => lam i ≠ 0)).card - 1 := by
            have hh := Finset.card_le_card hsub
            rwa [Finset.card_erase_of_mem hmemA] at hh
          have hpos1 : 1 ≤ (Finset.univ.filter (fun i => lam i ≠ 0)).card :=
            Finset.card_pos.mpr ⟨i₀, hmemA⟩
          omega
        · -- otherwise the column `j₀` disappears
          have hceq : c = mu j₀ := by rw [hcdef]; exact min_eq_right hc
          have hz : mu' j₀ = 0 := by simp [hmu'def, Function.update_self, hceq]
          have hsub : (Finset.univ.filter (fun j => mu' j ≠ 0)) ⊆
              (Finset.univ.filter (fun j => mu j ≠ 0)).erase j₀ := by
            intro j hj
            rw [Finset.mem_erase]
            refine ⟨?_, hsubB hj⟩
            intro h'
            rw [h'] at hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact hj hz
          have hcard' : (Finset.univ.filter (fun j => mu' j ≠ 0)).card ≤
              (Finset.univ.filter (fun j => mu j ≠ 0)).card - 1 := by
            have hh := Finset.card_le_card hsub
            rwa [Finset.card_erase_of_mem hmemB] at hh
          have hpos1 : 1 ≤ (Finset.univ.filter (fun j => mu j ≠ 0)).card :=
            Finset.card_pos.mpr ⟨j₀, hmemB⟩
          have hcardA : (Finset.univ.filter (fun i => lam' i ≠ 0)).card ≤
              (Finset.univ.filter (fun i => lam i ≠ 0)).card := Finset.card_le_card hsubA
          omega
      refine ⟨t' + 1, Fin.cons (α := fun _ => ℕ) c ν', Fin.cons (α := fun _ => ι) i₀ iA',
        Fin.cons (α := fun _ => κ) j₀ iB', ?_, ?_, ?_, ?_, ?_, hcount⟩
      · rw [Fin.forall_fin_succ]
        exact ⟨by rw [Fin.cons_zero]; exact hcpos,
          fun k => by rw [Fin.cons_succ]; exact hpos' k⟩
      · intro i
        rw [sum_filter_cons c ν' i₀ iA' i]
        by_cases hii : i₀ = i
        · rw [if_pos hii, hA' i, ← hii]
          rw [hlam'def, Function.update_self]
          omega
        · rw [if_neg hii, zero_add, hA' i]
          simp only [hlam'def, Function.update_of_ne (Ne.symm hii)]
      · intro j
        rw [sum_filter_cons c ν' j₀ iB' j]
        by_cases hjj : j₀ = j
        · rw [if_pos hjj, hB' j, ← hjj]
          rw [hmu'def, Function.update_self]
          omega
        · rw [if_neg hjj, zero_add, hB' j]
          simp only [hmu'def, Function.update_of_ne (Ne.symm hjj)]
      · rw [Fin.forall_fin_succ]
        exact ⟨by rw [Fin.cons_zero]; exact hc1,
          fun k => by rw [Fin.cons_succ]; exact le_trans (hleA' k) (hle_lam (iA' k))⟩
      · rw [Fin.forall_fin_succ]
        exact ⟨by rw [Fin.cons_zero]; exact hc2,
          fun k => by rw [Fin.cons_succ]; exact le_trans (hleB' k) (hle_mu (iB' k))⟩
  exact key _ lam mu rfl h.symm

/-- Two finite sequences of naturals with the same sum have a common refinement: a third sequence whose terms are positive and split (in consecutive blocks) into the terms of each of the two given sequences. -/
theorem gridRefine {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (lam : ι → ℕ) (mu : κ → ℕ) (h : ∑ i, lam i = ∑ j, mu j) :
    ∃ (t : ℕ) (ν : Fin t → ℕ) (idxA : Fin t → ι) (idxB : Fin t → κ),
      (∀ k, 0 < ν k) ∧
      (∀ i, ∑ k ∈ Finset.univ.filter (fun k => idxA k = i), ν k = lam i) ∧
      (∀ j, ∑ k ∈ Finset.univ.filter (fun k => idxB k = j), ν k = mu j) ∧
      (∀ k, ν k ≤ lam (idxA k)) ∧ (∀ k, ν k ≤ mu (idxB k)) ∧
      t ≤ Fintype.card ι + Fintype.card κ := by
  obtain ⟨t, ν, iA, iB, hpos, hA, hB, hleA, hleB, ht⟩ := refine_aux lam mu h
  have h1 : (Finset.univ.filter (fun i => lam i ≠ 0)).card ≤ Fintype.card ι := by
    simpa using Finset.card_filter_le (Finset.univ : Finset ι) (fun i => lam i ≠ 0)
  have h2 : (Finset.univ.filter (fun j => mu j ≠ 0)).card ≤ Fintype.card κ := by
    simpa using Finset.card_filter_le (Finset.univ : Finset κ) (fun j => mu j ≠ 0)
  exact ⟨t, ν, iA, iB, hpos, hA, hB, hleA, hleB, le_trans ht (add_le_add h1 h2)⟩

end Work.Deep.GKO.OneFact
