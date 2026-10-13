import Mathlib

namespace Work.WilE9G.Mult

theorem exists_of_surjective_of_forall_proj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n j : ℕ} (P : E →L[ℝ] (Fin n → ℝ)) (D : E →L[ℝ] (Fin j → ℝ))
    (hD : Function.Surjective D)
    (hcond : ∀ w : Fin n → ℝ, ∃ v : E, P v = w ∧ D v = 0) :
    ∀ (w : Fin n → ℝ) (y : Fin j → ℝ), ∃ v : E, P v = w ∧ D v = y := by
  intro w y
  -- choose a preimage of `y` under the surjective map `D`
  obtain ⟨u, hu⟩ := hD y
  -- correct the `P`-component by an element of the kernel of `D`
  obtain ⟨k, hk1, hk2⟩ := hcond (w - P u)
  refine ⟨u + k, ?_, ?_⟩
  · rw [map_add, hk1]
    abel
  · rw [map_add, hu, hk2, add_zero]

end Work.WilE9G.Mult
