import Mathlib

namespace Work.CR.Flat.Cauchy

/-- Currying a bounded `k`-multilinear map `φ : (Fin k → E) → (E →L[ℝ] ℂ)` in its last
(`E`-valued) slot produces a continuous `(k+1)`-multilinear map. -/
theorem exists_multilinearMap_curryLeft {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {φ : (Fin k → E) → (E →L[ℝ] ℂ)} {K : ℝ} (hK : 0 ≤ K)
    (hadd : ∀ (u : Fin k → E) (i : Fin k) (x y : E),
      φ (Function.update u i (x + y)) = φ (Function.update u i x) + φ (Function.update u i y))
    (hsmul : ∀ (u : Fin k → E) (i : Fin k) (a : ℝ) (x : E),
      φ (Function.update u i (a • x)) = a • φ (Function.update u i x))
    (hbound : ∀ u : Fin k → E, ‖φ u‖ ≤ K * ∏ i, ‖u i‖) :
    ∃ M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℂ,
      (∀ w : Fin (k + 1) → E, M w = φ (Fin.tail w) (w 0)) ∧ ‖M‖ ≤ K := by
  classical
  -- The underlying curried function.
  let F : (Fin (k + 1) → E) → ℂ := fun w => φ (Fin.tail w) (w 0)
  -- Multilinearity of `F`.
  have h_add : ∀ (w : Fin (k + 1) → E) (i : Fin (k + 1)) (x y : E),
      F (Function.update w i (x + y)) = F (Function.update w i x) + F (Function.update w i y) := by
    intro w i x y
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
    · -- first coordinate: use linearity of `φ (tail w)`
      rw [h]
      simp only [F, Fin.tail_update_zero, Function.update_self]
      exact map_add (φ (Fin.tail w)) x y
    · -- remaining coordinates: use multilinearity of `φ`
      simp only [F, Fin.tail_update_succ]
      rw [hadd (Fin.tail w) j x y]
      rfl
  have h_smul : ∀ (w : Fin (k + 1) → E) (i : Fin (k + 1)) (a : ℝ) (x : E),
      F (Function.update w i (a • x)) = a • F (Function.update w i x) := by
    intro w i a x
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
    · rw [h]
      simp only [F, Fin.tail_update_zero, Function.update_self]
      exact map_smul (φ (Fin.tail w)) a x
    · simp only [F, Fin.tail_update_succ]
      rw [hsmul (Fin.tail w) j a x]
      rfl
  let Ml : MultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℂ := MultilinearMap.mk' F h_add h_smul
  -- The uniform bound, which is exactly the norm bound for the curried map.
  have hbound' : ∀ w : Fin (k + 1) → E, ‖Ml w‖ ≤ K * ∏ i, ‖w i‖ := by
    intro w
    have h1 : ‖φ (Fin.tail w) (w 0)‖ ≤ ‖φ (Fin.tail w)‖ * ‖w 0‖ :=
      (φ (Fin.tail w)).le_opNorm (w 0)
    have h2 : ‖φ (Fin.tail w)‖ ≤ K * ∏ i : Fin k, ‖Fin.tail w i‖ := hbound (Fin.tail w)
    calc
      ‖Ml w‖ = ‖φ (Fin.tail w) (w 0)‖ := by simp [Ml, F]
      _ ≤ ‖φ (Fin.tail w)‖ * ‖w 0‖ := h1
      _ ≤ (K * ∏ i : Fin k, ‖Fin.tail w i‖) * ‖w 0‖ := by gcongr
      _ = K * ∏ i : Fin (k + 1), ‖w i‖ := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.tail]
          ring
  refine ⟨Ml.mkContinuous K hbound', ?_, ?_⟩
  · intro w
    simp [Ml, F]
  · exact Ml.mkContinuous_norm_le hK hbound'

end Work.CR.Flat.Cauchy
