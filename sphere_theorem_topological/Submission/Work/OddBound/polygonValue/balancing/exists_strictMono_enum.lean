import Mathlib

namespace Work.OddBound.polygonValue.balancing

/-- A finite subset `A ⊆ [0,1]` containing `0` and `1` can be enumerated as a strictly
increasing sequence `a 0 < a 1 < ⋯ < a k` with `a 0 = 0`, `a k = 1` and range `A`.

This is the sorted enumeration of `A`: the increasing bijection `Fin A.card → A` provided by
`Finset.orderEmbOfFin`, reindexed along `Fin (A.card - 1 + 1) ≃o Fin A.card`. -/
theorem exists_strictMono_enum {A : Finset ℝ} (h0 : (0 : ℝ) ∈ A) (h1 : (1 : ℝ) ∈ A)
    (hsub : ∀ x ∈ A, x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (k : ℕ) (a : Fin (k + 1) → ℝ), StrictMono a ∧ a 0 = 0 ∧ a (Fin.last k) = 1 ∧
      Set.range a = (↑A : Set ℝ) := by
  classical
  -- `A` is nonempty, so `A.card = (A.card - 1) + 1`.
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨0, h0⟩
  have hc : A.card - 1 + 1 = A.card := by omega
  -- The sorted enumeration of `A`, viewed on `Fin (A.card - 1 + 1)`.
  have hmono : StrictMono (fun i : Fin (A.card - 1 + 1) =>
      A.orderEmbOfFin rfl (Fin.castOrderIso hc i)) :=
    (A.orderEmbOfFin rfl).strictMono.comp (Fin.castOrderIso hc).strictMono
  have hmem : ∀ i : Fin (A.card - 1 + 1),
      A.orderEmbOfFin rfl (Fin.castOrderIso hc i) ∈ A :=
    fun i => A.orderEmbOfFin_mem rfl (Fin.castOrderIso hc i)
  have hsurj : ∀ y : ℝ, y ∈ A → ∃ i : Fin (A.card - 1 + 1),
      A.orderEmbOfFin rfl (Fin.castOrderIso hc i) = y := by
    intro y hy
    have hy' : y ∈ Set.range (A.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin A rfl]
      exact Finset.mem_coe.mpr hy
    obtain ⟨j, hj⟩ := hy'
    refine ⟨(Fin.castOrderIso hc).symm j, ?_⟩
    rw [OrderIso.apply_symm_apply]
    exact hj
  refine ⟨A.card - 1, fun i => A.orderEmbOfFin rfl (Fin.castOrderIso hc i), hmono, ?_, ?_, ?_⟩
  · -- the smallest value is `0`
    have hbot : ∀ i : Fin (A.card - 1 + 1),
        A.orderEmbOfFin rfl (Fin.castOrderIso hc (0 : Fin (A.card - 1 + 1))) ≤
          A.orderEmbOfFin rfl (Fin.castOrderIso hc i) :=
      fun i => hmono.monotone (Fin.zero_le i)
    obtain ⟨i₀, hi₀⟩ := hsurj 0 h0
    have hle : A.orderEmbOfFin rfl (Fin.castOrderIso hc (0 : Fin (A.card - 1 + 1))) ≤ 0 := by
      have h := hbot i₀
      rw [hi₀] at h
      exact h
    have hge : (0 : ℝ) ≤
        A.orderEmbOfFin rfl (Fin.castOrderIso hc (0 : Fin (A.card - 1 + 1))) :=
      (hsub _ (hmem _)).1
    exact le_antisymm hle hge
  · -- the largest value is `1`
    have htop : ∀ i : Fin (A.card - 1 + 1),
        A.orderEmbOfFin rfl (Fin.castOrderIso hc i) ≤
          A.orderEmbOfFin rfl (Fin.castOrderIso hc (Fin.last (A.card - 1))) :=
      fun i => hmono.monotone (Fin.le_last i)
    obtain ⟨i₁, hi₁⟩ := hsurj 1 h1
    have hle : (1 : ℝ) ≤
        A.orderEmbOfFin rfl (Fin.castOrderIso hc (Fin.last (A.card - 1))) := by
      have h := htop i₁
      rw [hi₁] at h
      exact h
    have hge : A.orderEmbOfFin rfl (Fin.castOrderIso hc (Fin.last (A.card - 1))) ≤ 1 :=
      (hsub _ (hmem _)).2
    exact le_antisymm hge hle
  · -- the range is exactly `A`
    have hsub1 : (Set.range (fun i : Fin (A.card - 1 + 1) =>
        A.orderEmbOfFin rfl (Fin.castOrderIso hc i))) ⊆ (↑A : Set ℝ) := by
      intro y hy
      obtain ⟨i, rfl⟩ := Set.mem_range.mp hy
      exact Finset.mem_coe.mpr (hmem i)
    have hsub2 : (↑A : Set ℝ) ⊆ Set.range (fun i : Fin (A.card - 1 + 1) =>
        A.orderEmbOfFin rfl (Fin.castOrderIso hc i)) := by
      intro y hy
      obtain ⟨i, hi⟩ := hsurj y (Finset.mem_coe.mp hy)
      exact Set.mem_range.mpr ⟨i, hi⟩
    exact Set.Subset.antisymm hsub1 hsub2

end Work.OddBound.polygonValue.balancing
