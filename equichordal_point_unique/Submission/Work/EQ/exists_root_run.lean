import Mathlib

namespace Work.EQ

/-- A finite set `S ⊆ ℤ` containing `0` in which every element has at least one
of its two immediate neighbours again in `S` contains a maximal run of consecutive
integers through `0`: an interval `[m, M] ⊆ S` with `m ≤ 0 ≤ M`, `m + 1 ≤ M`,
`m - 1 ∉ S` and `M + 1 ∉ S`. -/
theorem exists_root_run (S : Set ℤ) (hfin : S.Finite) (h0 : (0 : ℤ) ∈ S)
    (hprop : ∀ n ∈ S, n - 1 ∈ S ∨ n + 1 ∈ S) :
    ∃ m M : ℤ, m ≤ 0 ∧ 0 ≤ M ∧ m + 1 ≤ M ∧ (∀ k ∈ Set.Icc m M, k ∈ S) ∧
      m - 1 ∉ S ∧ M + 1 ∉ S := by
  -- Work with the finset version `s` of `S`.
  let s : Finset ℤ := hfin.toFinset
  have hmem : ∀ x : ℤ, x ∈ s ↔ x ∈ S := fun x => hfin.mem_toFinset
  have h0s : (0 : ℤ) ∈ s := (hmem 0).mpr h0
  -- Left endpoint: the smallest `a` with `[a, 0] ⊆ s`.
  let A : Finset ℤ := s.filter (fun a : ℤ => a ≤ 0 ∧ ∀ k ∈ Finset.Icc a 0, k ∈ s)
  have hA0 : (0 : ℤ) ∈ A := by
    rw [Finset.mem_filter]
    refine ⟨h0s, le_refl 0, ?_⟩
    intro k hk
    rw [Finset.mem_Icc] at hk
    have : k = 0 := le_antisymm hk.2 hk.1
    rw [this]; exact h0s
  let hAne : A.Nonempty := ⟨0, hA0⟩
  let a₀ : ℤ := A.min' hAne
  have ha₀A : a₀ ∈ A := Finset.min'_mem A hAne
  have ha₀le : a₀ ≤ 0 := ((Finset.mem_filter.mp ha₀A).2).1
  have hleft : ∀ k ∈ Finset.Icc a₀ 0, k ∈ s := ((Finset.mem_filter.mp ha₀A).2).2
  have hmin : ∀ x ∈ A, a₀ ≤ x := by
    intro x hx
    have h := Finset.min'_le A x hx
    have heq : A.min' (⟨x, hx⟩ : A.Nonempty) = A.min' hAne :=
      congrArg A.min' (Subsingleton.elim _ _)
    calc a₀ = A.min' hAne := rfl
      _ = A.min' (⟨x, hx⟩ : A.Nonempty) := heq.symm
      _ ≤ x := h
  have ha₀_sub : a₀ - 1 ∉ S := by
    intro hcon
    have hcon_s : a₀ - 1 ∈ s := (hmem _).mpr hcon
    have hmemA : a₀ - 1 ∈ A := by
      rw [Finset.mem_filter]
      refine ⟨hcon_s, by omega, ?_⟩
      intro k hk
      rw [Finset.mem_Icc] at hk
      rcases eq_or_lt_of_le hk.1 with h | h
      · rw [← h]; exact hcon_s
      · exact hleft k (by rw [Finset.mem_Icc]; exact ⟨by omega, hk.2⟩)
    have := hmin (a₀ - 1) hmemA
    omega
  -- Right endpoint: the largest `b` with `[0, b] ⊆ s`.
  let B : Finset ℤ := s.filter (fun b : ℤ => 0 ≤ b ∧ ∀ k ∈ Finset.Icc (0:ℤ) b, k ∈ s)
  have hB0 : (0 : ℤ) ∈ B := by
    rw [Finset.mem_filter]
    refine ⟨h0s, le_refl 0, ?_⟩
    intro k hk
    rw [Finset.mem_Icc] at hk
    have : k = 0 := le_antisymm hk.2 hk.1
    rw [this]; exact h0s
  let hBne : B.Nonempty := ⟨0, hB0⟩
  let b₀ : ℤ := B.max' hBne
  have hb₀B : b₀ ∈ B := Finset.max'_mem B hBne
  have hb₀ge : 0 ≤ b₀ := ((Finset.mem_filter.mp hb₀B).2).1
  have hright : ∀ k ∈ Finset.Icc (0:ℤ) b₀, k ∈ s := ((Finset.mem_filter.mp hb₀B).2).2
  have hmax : ∀ x ∈ B, x ≤ b₀ := by
    intro x hx
    have h := Finset.le_max' B x hx
    have heq : B.max' hBne = B.max' (⟨x, hx⟩ : B.Nonempty) :=
      congrArg B.max' (Subsingleton.elim _ _)
    calc x ≤ B.max' (⟨x, hx⟩ : B.Nonempty) := h
      _ = B.max' hBne := heq.symm
      _ = b₀ := rfl
  have hb₀_add : b₀ + 1 ∉ S := by
    intro hcon
    have hcon_s : b₀ + 1 ∈ s := (hmem _).mpr hcon
    have hmemB : b₀ + 1 ∈ B := by
      rw [Finset.mem_filter]
      refine ⟨hcon_s, by omega, ?_⟩
      intro k hk
      rw [Finset.mem_Icc] at hk
      rcases eq_or_lt_of_le hk.2 with h | h
      · rw [h]; exact hcon_s
      · exact hright k (by rw [Finset.mem_Icc]; exact ⟨hk.1, by omega⟩)
    have := hmax (b₀ + 1) hmemB
    omega
  refine ⟨a₀, b₀, ha₀le, hb₀ge, ?_, ?_, ha₀_sub, hb₀_add⟩
  · -- `a₀ + 1 ≤ b₀`: the run has length at least one, by `hprop` at `0`.
    rcases lt_or_eq_of_le ha₀le with h | h
    · omega
    · rcases eq_or_lt_of_le hb₀ge with h' | h'
      · exfalso
        rcases hprop 0 h0 with hc | hc
        · exact ha₀_sub (by simpa [h] using hc)
        · exact hb₀_add (by simpa [h'] using hc)
      · omega
  · -- Every element of `[a₀, b₀]` lies in `s`.
    intro k hk
    rw [Set.mem_Icc] at hk
    rcases le_total k 0 with hk0 | hk0
    · exact (hmem k).mp (hleft k (by rw [Finset.mem_Icc]; exact ⟨hk.1, hk0⟩))
    · exact (hmem k).mp (hright k (by rw [Finset.mem_Icc]; exact ⟨hk0, hk.2⟩))

end Work.EQ
