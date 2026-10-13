import Mathlib
import Submission.Work.WilE3K.Elim

namespace Work.WilE3K

open WilkiesDesign WilkiesDesign.E

/-! ## Helper facts about the sphere polynomial

`ETData.spherePoly (N := N) c = ∑_k x_k² - c` involves only the ambient coordinates, so its
partial derivatives in the chain directions vanish and its derivative in an ambient direction is
`2 x_i`.  These are the only computations needed for the last diagonal entry of the Jacobian of
the sphere step. -/

/-- `∂_{x_i}` of the sphere polynomial `∑_k x_k² - c` is `2 x_i`. -/
lemma spherePoly_pderiv_inl {N re : ℕ} (c : ℝ) (i : Fin (N+2)) :
    MvPolynomial.pderiv (Sum.inl i) (ETData.spherePoly (N:=N) (re:=re) c)
      = (2 : MvPolynomial (Fin (N+2) ⊕ Fin re) ℝ) * MvPolynomial.X (Sum.inl i) := by
  simp only [ETData.spherePoly]
  rw [map_sub, map_sum, MvPolynomial.pderiv_C, sub_zero]
  rw [Finset.sum_eq_single i]
  · rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self]
    ring
  · intro b _ hb
    rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro h
      exact hb (Sum.inl_injective h)
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `∂_{ψ_j}` of the sphere polynomial vanishes: it does not involve the chain coordinates. -/
lemma spherePoly_pderiv_inr {N re : ℕ} (c : ℝ) (j : Fin re) :
    MvPolynomial.pderiv (Sum.inr j) (ETData.spherePoly (N:=N) (re:=re) c) = 0 := by
  simp only [ETData.spherePoly]
  rw [map_sub, map_sum, MvPolynomial.pderiv_C, sub_zero]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_of_ne]
  · simp
  · intro h
    exact Sum.inr_ne_inl h.symm

/-- The symbolic derivative `dPoly` of the sphere polynomial in the direction `x_i` is `2 x_i`:
the chain terms drop out by `spherePoly_pderiv_inr`. -/
lemma sphereData_dPoly_spherePoly {N rt n re : ℕ} (E : ETData (N+1) rt n re) (c : ℝ)
    (i : Fin (N+2)) :
    E.dPoly i (ETData.spherePoly (N:=N) (re:=re) c)
      = (2 : MvPolynomial (Fin (N+2) ⊕ Fin re) ℝ) * MvPolynomial.X (Sum.inl i) := by
  simp only [ETData.dPoly]
  have hsum : (∑ j : Fin re, MvPolynomial.C (E.dcoef i j) * MvPolynomial.X (Sum.inr j) *
      MvPolynomial.pderiv (Sum.inr j) (ETData.spherePoly (N:=N) (re:=re) c)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [spherePoly_pderiv_inr]; ring
  rw [hsum, add_zero]
  exact spherePoly_pderiv_inl c i

/-- Evaluation along the chain of `2 x_i` gives `2 z_i`. -/
lemma sphereData_evalPoly_two_X {N rt n re : ℕ} (E : ETData (N+1) rt n re)
    (z : Fin (N+2) → ℝ) (i : Fin (N+2)) :
    E.evalPoly ((2 : MvPolynomial (Fin (N+2) ⊕ Fin re) ℝ) * MvPolynomial.X (Sum.inl i)) z
      = 2 * z i := by
  simp [ETData.evalPoly]

theorem sphereData_jac_last_last {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (c : ℝ) (z : Fin ((N + 1) + 1) → ℝ) :
    ((E.sphereData c).jac z) (Fin.last (N + 1)) (Fin.last (N + 1)) = 2 * z (Fin.last (N + 1)) := by
  -- the last row of the sphere step is a polynomial row, namely the sphere equation itself,
  -- located at the last free coordinate
  have hlast : (Fin.last (N + 1) : Fin ((N + 1) + 1)) =
      (E.sphereData c).freeCoord ⟨n, by omega⟩ := by
    have h := E.h
    apply Fin.ext
    simp only [ETData.freeCoord, Fin.val_last]
    omega
  have hG : (E.sphereData c).G ⟨n, by omega⟩ = ETData.spherePoly (N:=N) (re:=re) c := by
    simp only [ETData.sphereData]
    simp
  rw [hlast, ETData.jac_free, hG]
  rw [sphereData_dPoly_spherePoly]
  exact sphereData_evalPoly_two_X _ _ _

end Work.WilE3K
