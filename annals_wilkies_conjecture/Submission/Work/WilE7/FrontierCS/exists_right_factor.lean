import Mathlib

namespace Work.WilE7.FrontierCS

theorem exists_right_factor {d j : ℕ} (P : Matrix (Fin j) (Fin d) ℝ) (Q : Matrix (Fin j) (Fin j) ℝ)
    (hsurj : ∀ y : Fin j → ℝ, ∃ t e, P.mulVec t + Q.mulVec e = y) :
    ∃ L_t : Matrix (Fin d) (Fin j) ℝ, ∃ L_u : Matrix (Fin j) (Fin j) ℝ, P * L_t + Q * L_u = 1 := by
  classical
  -- For each standard basis vector of the target, pick a preimage under `(t,e) ↦ P t + Q e`.
  let t : Fin j → (Fin d → ℝ) := fun k => (hsurj (Pi.single k (1:ℝ))).choose
  let e : Fin j → (Fin j → ℝ) := fun k => (hsurj (Pi.single k (1:ℝ))).choose_spec.choose
  have he : ∀ k, P.mulVec (t k) + Q.mulVec (e k) = Pi.single k (1:ℝ) :=
    fun k => (hsurj (Pi.single k (1:ℝ))).choose_spec.choose_spec
  -- Use those preimages as the columns of the right inverses.
  let Lt : Matrix (Fin d) (Fin j) ℝ := fun a k => t k a
  let Lu : Matrix (Fin j) (Fin j) ℝ := fun b k => e k b
  refine ⟨Lt, Lu, ?_⟩
  ext i k
  have hk : P.mulVec (t k) i + Q.mulVec (e k) i = (Pi.single k (1:ℝ) : Fin j → ℝ) i := by
    have := congrFun (he k) i; simpa using this
  have hPl : (P * Lt) i k = P.mulVec (t k) i := by
    rw [Matrix.mul_apply, Matrix.mulVec_apply]; simp only [Lt]; rfl
  have hQl : (Q * Lu) i k = Q.mulVec (e k) i := by
    rw [Matrix.mul_apply, Matrix.mulVec_apply]; simp only [Lu]; rfl
  rw [Matrix.add_apply, hPl, hQl, hk, Matrix.one_apply, Pi.single_apply]

end Work.WilE7.FrontierCS
