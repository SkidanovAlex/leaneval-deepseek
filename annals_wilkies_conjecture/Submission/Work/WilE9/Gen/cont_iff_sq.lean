import Mathlib

namespace Work.WilE9.Gen

theorem cont_iff_sq {n : ℕ} (G : Set (Fin (n + 1) → ℝ)) (v : Fin (n + 1) → ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Fin n → ℝ,
        (∀ j : Fin n, |x' j - Fin.init v j| < δ) →
        ∀ v' : ℝ, Fin.snoc x' v' ∈ G → |v' - v (Fin.last n)| < ε)
      ↔
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ w : Fin (n + 1) → ℝ, w ∈ G →
        (∀ j : Fin n, (w (Fin.castSucc j) - v (Fin.castSucc j)) ^ 2 < δ ^ 2) →
        (w (Fin.last n) - v (Fin.last n)) ^ 2 < ε ^ 2) := by
  constructor
  · -- Assume the "snoc" continuity condition; pass to the graph formulation
    -- by taking the first `n` coordinates of `w` and its last coordinate.
    intro h ε hε
    obtain ⟨δ, hδ, hmain⟩ := h ε hε
    refine ⟨δ, hδ, fun w _ hsq => ?_⟩
    have hx : ∀ j : Fin n, |Fin.init w j - Fin.init v j| < δ := by
      intro j
      have h := hsq j
      rw [sq_lt_sq, abs_of_pos hδ] at h
      change |w j.castSucc - v j.castSucc| < δ
      exact h
    have := hmain (Fin.init w) hx (w (Fin.last n)) (by rwa [Fin.snoc_init_self])
    rw [sq_lt_sq, abs_of_pos hε]
    exact this
  · -- Conversely, rebuild a point of `G` with the prescribed last coordinate
    -- by `Fin.snoc`, and translate the squared estimates back to absolute ones.
    intro h ε hε
    obtain ⟨δ, hδ, hmain⟩ := h ε hε
    refine ⟨δ, hδ, fun x' hx v' hv' => ?_⟩
    have hsq : ∀ j : Fin n,
        ((Fin.snoc x' v' : Fin (n + 1) → ℝ) (Fin.castSucc j) - v (Fin.castSucc j)) ^ 2 < δ ^ 2 := by
      intro j
      have h := hx j
      rw [Fin.snoc_castSucc]
      rw [sq_lt_sq, abs_of_pos hδ]
      change |x' j - Fin.init v j| < δ
      exact h
    have hmem : (Fin.snoc x' v' : Fin (n + 1) → ℝ) ∈ G := hv'
    have := hmain (Fin.snoc x' v') hmem hsq
    rw [Fin.snoc_last] at this
    rw [sq_lt_sq, abs_of_pos hε] at this
    exact this

end Work.WilE9.Gen
