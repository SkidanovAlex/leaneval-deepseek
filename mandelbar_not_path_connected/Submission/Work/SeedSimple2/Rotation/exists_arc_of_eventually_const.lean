import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedSimple2.Rotation

theorem exists_arc_of_eventually_const {v : ℕ → ℝ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hv0 : ∀ n : ℕ, 0 ≤ v n) (hv1 : ∀ n : ℕ, v n < 1) (h : (∀ n : ℕ, p < v n) ∨ (∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n → v n = v n₀)) : ∃ c0 d0 : ℝ, d0 ≤ c0 + 1 ∧ ∀ n : ℕ, v n ∈ Set.Ioo c0 d0 := by
  rcases h with h1 | ⟨n₀, hn₀⟩
  · -- If every value strictly exceeds `p ∈ [0,1)`, the interval `(p,1)` works.
    exact ⟨p, 1, by linarith, fun n => ⟨h1 n, hv1 n⟩⟩
  · -- Otherwise `v` is eventually constant: only finitely many values occur,
    -- all in `[0,1)`.  Let `m` and `M` be their min and max, then
    -- `c0 = (M - 1 + m)/2` satisfies `M - 1 < c0 < m`.
    let s : Finset ℝ := (Finset.range (n₀ + 1)).image v
    have hne : s.Nonempty :=
      ⟨v 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos n₀), rfl⟩⟩
    let m := s.min' hne
    let M := s.max' hne
    have hm_mem : m ∈ s := s.min'_mem hne
    have hM_mem : M ∈ s := s.max'_mem hne
    have hm_nonneg : 0 ≤ m := by
      rcases (Finset.mem_image.mp hm_mem) with ⟨n, _, hn⟩
      rw [← hn]; exact hv0 n
    have hM_lt_one : M < 1 := by
      rcases (Finset.mem_image.mp hM_mem) with ⟨n, _, hn⟩
      rw [← hn]; exact hv1 n
    have hv_le_M : ∀ n, v n ≤ M := by
      intro n
      rcases le_or_gt n n₀ with hn | hn
      · exact Finset.le_max' s (v n)
          (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), rfl⟩)
      · rw [hn₀ n hn]
        exact Finset.le_max' s (v n₀)
          (Finset.mem_image.mpr ⟨n₀, Finset.mem_range.mpr (Nat.lt_succ_self n₀), rfl⟩)
    have hm_le_v : ∀ n, m ≤ v n := by
      intro n
      rcases le_or_gt n n₀ with hn | hn
      · exact Finset.min'_le s (v n)
          (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), rfl⟩)
      · rw [hn₀ n hn]
        exact Finset.min'_le s (v n₀)
          (Finset.mem_image.mpr ⟨n₀, Finset.mem_range.mpr (Nat.lt_succ_self n₀), rfl⟩)
    refine ⟨(M - 1 + m)/2, (M - 1 + m)/2 + 1, le_refl _, fun n => ⟨?_, ?_⟩⟩
    · have hlt : (M - 1 + m)/2 < m := by linarith
      linarith [hm_le_v n]
    · have hlt : M < (M - 1 + m)/2 + 1 := by linarith
      linarith [hv_le_M n]

end Work.SeedSimple2.Rotation
