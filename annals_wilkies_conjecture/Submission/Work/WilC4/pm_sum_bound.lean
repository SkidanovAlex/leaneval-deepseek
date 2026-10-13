import Mathlib

namespace Work.WilC4

theorem pm_sum_bound {g : ℝ → ℝ} {a b C : ℝ} {m : ℕ} {x : ℕ → ℝ}
    (hab : a ≤ b)
    (hmono : MonotoneOn g (Set.Icc a b) ∨ AntitoneOn g (Set.Icc a b))
    (hmem : ∀ i ≤ m, x i ∈ Set.Icc a b)
    (hxinc : ∀ i, i < m → x i ≤ x (i + 1))
    (hxm : x m = b) (hx0 : x 0 = a)
    (hbd : ∀ t ∈ Set.Icc a b, 0 < g t ∧ g t ≤ C) :
    ∑ i ∈ Finset.range m, |g (x (i + 1)) - g (x i)| ≤ C := by
  rcases hmono with hmono | hanti
  · -- `g` is monotone on `[a,b]`: the absolute values vanish and the sum telescopes.
    have hterm : ∀ i ∈ Finset.range m, |g (x (i + 1)) - g (x i)| = g (x (i + 1)) - g (x i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hgi : g (x i) ≤ g (x (i + 1)) :=
        hmono (hmem i (le_of_lt hi)) (hmem (i + 1) (Nat.succ_le_of_lt hi)) (hxinc i hi)
      exact abs_of_nonneg (sub_nonneg.mpr hgi)
    rw [Finset.sum_congr rfl hterm]
    have htel : ∑ i ∈ Finset.range m, (g (x (i + 1)) - g (x i)) = g (x m) - g (x 0) :=
      Finset.sum_range_sub (fun i => g (x i)) m
    rw [htel, hxm, hx0]
    have hb : g b ≤ C := (hbd b (Set.mem_Icc.mpr ⟨hab, le_rfl⟩)).2
    have ha : 0 < g a := (hbd a (Set.mem_Icc.mpr ⟨le_rfl, hab⟩)).1
    linarith
  · -- `g` is antitone on `[a,b]`: the sum telescopes the other way round.
    have hterm : ∀ i ∈ Finset.range m, |g (x (i + 1)) - g (x i)| = g (x i) - g (x (i + 1)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hgi : g (x (i + 1)) ≤ g (x i) :=
        hanti (hmem i (le_of_lt hi)) (hmem (i + 1) (Nat.succ_le_of_lt hi)) (hxinc i hi)
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hgi)
    rw [Finset.sum_congr rfl hterm]
    have htel : ∑ i ∈ Finset.range m, (g (x i) - g (x (i + 1))) = g (x 0) - g (x m) :=
      Finset.sum_range_sub' (fun i => g (x i)) m
    rw [htel, hxm, hx0]
    have hb : 0 < g b := (hbd b (Set.mem_Icc.mpr ⟨hab, le_rfl⟩)).1
    have ha : g a ≤ C := (hbd a (Set.mem_Icc.mpr ⟨le_rfl, hab⟩)).2
    linarith

end Work.WilC4
