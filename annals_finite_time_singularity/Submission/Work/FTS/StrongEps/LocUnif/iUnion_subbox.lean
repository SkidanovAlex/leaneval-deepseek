import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Lattice.Nat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- One-dimensional exhaustion: the closed intervals with margins `(b-a)/(k+2)` around `[a,b]`
increase with `k` to the whole open interval `(a,b)`. -/
private lemma iUnion_Icc_div_eq_Ioo {a b : ℝ} (hab : a < b) :
    (⋃ k : ℕ, Set.Icc (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2)))
      = Set.Ioo a b := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_Ioo]
  constructor
  · rintro ⟨k, h1, h2⟩
    have hpos : 0 < (b - a) / ((k : ℝ) + 2) := div_pos (by linarith) (by positivity)
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hx1, hx2⟩
    have hm : 0 < min (x - a) (b - x) := lt_min (by linarith) (by linarith)
    obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / min (x - a) (b - x))
    have hkey : b - a < (k : ℝ) * min (x - a) (b - x) := (div_lt_iff₀ hm).mp hk
    have hsmall : (b - a) / ((k : ℝ) + 2) ≤ min (x - a) (b - x) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 2)]
      nlinarith [hkey, hm]
    exact ⟨k, by linarith [min_le_left (x - a) (b - x), hsmall],
      by linarith [min_le_right (x - a) (b - x), hsmall]⟩

/-- The family of closed sub-boxes is increasing in `k`. -/
private lemma monotone_Icc_div {a b : ℝ} (hab : a < b) :
    Monotone
      (fun k : ℕ => Set.Icc (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2))) := by
  intro k j hkj
  have hkj' : (k : ℝ) + 2 ≤ (j : ℝ) + 2 := by
    have : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
    linarith
  have hle : (b - a) / ((j : ℝ) + 2) ≤ (b - a) / ((k : ℝ) + 2) := by
    gcongr
  exact Set.Icc_subset_Icc (by linarith) (by linarith)

theorem iUnion_subbox {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    (⋃ k : ℕ, (Set.Icc (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2)) ×ˢ
      Set.Icc (c + (d - c) / ((k : ℝ) + 2)) (d - (d - c) / ((k : ℝ) + 2)) : Set (ℝ × ℝ)))
      = Set.Ioo a b ×ˢ Set.Ioo c d := by
  rw [Set.iUnion_prod_of_monotone (monotone_Icc_div hab) (monotone_Icc_div hcd),
    iUnion_Icc_div_eq_Ioo hab, iUnion_Icc_div_eq_Ioo hcd]

end Work.FTS.StrongEps.LocUnif
