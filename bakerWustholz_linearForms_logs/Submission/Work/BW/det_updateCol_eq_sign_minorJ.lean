import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.det_cols_eq_sign_minorJ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Cramer's determinant step: for a `ρ × r` integer matrix `M`, a `ρ`-element column set `J` and
an index `i ∉ J`, replacing the `b`-th column of the `ρ × ρ` submatrix on `J` by the `i`-th column
of `M` produces the minor on the column set `(J \ {c_b}) ∪ {i}` (`c_b = J.orderEmbOfFin hJ b`), up
to sign. -/
theorem det_updateCol_eq_sign_minorJ {ρ r : ℕ} (M : Fin ρ → Fin r → ℤ)
    {J : Finset (Fin r)} (hJ : J.card = ρ) {i : Fin r} (hi : i ∉ J) (b : Fin ρ) :
    ∃ (hcard : (insert i (J.erase (J.orderEmbOfFin hJ b))).card = ρ) (ε : ℝ),
      (ε = 1 ∨ ε = -1) ∧
      (Matrix.updateCol (fun k l : Fin ρ => (M k (J.orderEmbOfFin hJ l) : ℝ)) b
          (fun k => (M k i : ℝ))).det =
        ε * ((minorJ M (insert i (J.erase (J.orderEmbOfFin hJ b))) hcard : ℤ) : ℝ) := by
  classical
  -- The new column set `J' = insert i (J.erase c_b)` has cardinality `ρ`, because `i ∉ J`.
  have hcbJ : J.orderEmbOfFin hJ b ∈ J := J.orderEmbOfFin_mem hJ b
  have hcard : (insert i (J.erase (J.orderEmbOfFin hJ b))).card = ρ := by
    rw [Finset.card_insert_of_notMem (fun h => hi (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hcbJ, hJ]
    have hb := b.isLt
    omega
  -- The column map of the updated matrix: column `b` is replaced by the `i`-th column of `M`.
  let c : Fin ρ → Fin r := fun l => if l = b then i else J.orderEmbOfFin hJ l
  have hc : Function.Injective c := by
    intro l1 l2 h
    simp only [c] at h
    by_cases h1 : l1 = b
    · rw [ite_eq_left h1] at h
      by_cases h2 : l2 = b
      · rw [ite_eq_left h2] at h; rw [h1, h2]
      · rw [ite_eq_right h2] at h
        exact absurd (h ▸ J.orderEmbOfFin_mem hJ l2) hi
    · rw [ite_eq_right h1] at h
      by_cases h2 : l2 = b
      · rw [ite_eq_left h2] at h
        exact absurd (h ▸ J.orderEmbOfFin_mem hJ l1) hi
      · rw [ite_eq_right h2] at h
        exact (J.orderEmbOfFin hJ).injective h
  have hcJ' : ∀ l, c l ∈ insert i (J.erase (J.orderEmbOfFin hJ b)) := by
    intro l
    by_cases hl : l = b
    · dsimp only [c]; rw [ite_eq_left hl]; exact Finset.mem_insert_self _ _
    · dsimp only [c]; rw [ite_eq_right hl]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr
        ⟨fun hh => hl ((J.orderEmbOfFin hJ).injective hh), J.orderEmbOfFin_mem hJ l⟩))
  -- Apply the column-permutation lemma to the column map `c` and the set `J'`.
  obtain ⟨ε, hε, hdet⟩ := det_cols_eq_sign_minorJ M hcard hc hcJ'
  refine ⟨hcard, ε, hε, ?_⟩
  have hmat : Matrix.updateCol (fun k l : Fin ρ => (M k (J.orderEmbOfFin hJ l) : ℝ)) b
        (fun k => (M k i : ℝ)) = fun a l => (M a (c l) : ℝ) := by
    ext a l
    by_cases hl : l = b
    · simp [Matrix.updateCol, Function.update, hl, c]
    · simp [Matrix.updateCol, Function.update, hl, c]
  rw [hmat, hdet]

end Work.BW
