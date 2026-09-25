import Mathlib
import Submission.Work.NN.Final.PolarDefs
import Submission.Work.NN.Final.PolarRegions

namespace Work.NN.Final

/-- Folding the one-coordinate radial extensions over the tail of `List.finRange n` starting
at `t` peels off the coordinate `t` outermost. -/
private lemma drop_foldr_radialExt {n : ℕ} (ρ : Fin n → ℝ) (a b : ℕ → ℝ)
    (G : (Fin n → ℂ) → ℂ) {t : ℕ} (h : t < n) :
    ((List.finRange n).drop t).foldr (fun j H => radialExt n ρ a b j H) G
      = radialExt n ρ a b ⟨t, h⟩
          (((List.finRange n).drop (t + 1)).foldr (fun j H => radialExt n ρ a b j H) G) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp only [List.foldr_cons]
  congr 1
  rw [List.getElem_finRange]
  exact Fin.ext rfl

/-- The explicit iteration `iterateFrom` unfolds to the fold over the corresponding tail of
`List.finRange n`. -/
private lemma iterateFrom_eq_drop_foldr {n : ℕ} (ρ : Fin n → ℝ) (a b : ℕ → ℝ)
    (G : (Fin n → ℂ) → ℂ) :
    ∀ j t, t + j = n → iterateFrom n ρ a b t G
      = ((List.finRange n).drop t).foldr (fun j H => radialExt n ρ a b j H) G := by
  intro j
  induction j with
  | zero =>
      intro t ht
      have htn : n ≤ t := by omega
      rw [iterateFrom_of_le htn]
      rw [List.drop_eq_nil_of_le (by rw [List.length_finRange]; exact htn)]
      rfl
  | succ j ih =>
      intro t ht
      have ht' : t < n := by omega
      rw [iterateFrom_of_lt ht']
      rw [ih (t + 1) (by omega)]
      rw [drop_foldr_radialExt ρ a b G ht']

theorem iterExt_eq_iterateFrom {n : ℕ} (ρ : Fin n → ℝ) (a b : ℕ → ℝ)
    (G : (Fin n → ℂ) → ℂ) :
    Work.NN.Final.iterExt n ρ a b G = Work.NN.Final.iterateFrom n ρ a b 0 G := by
  rw [iterateFrom_eq_drop_foldr ρ a b G n 0 (by omega)]
  rw [List.drop_zero]
  rfl

end Work.NN.Final
