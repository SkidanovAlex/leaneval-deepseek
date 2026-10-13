/-
  Work.WilE2 — the symbolic derivative `ESys.d` commutes with the Khovanskii lift `liftP`.

  The lift `liftP : EPoly n (s+1) → EPoly (n+1) s` of `Submission.Work.WilE2.Lift` replaces the
  last chain variable `ψ_{s+1}` by the new coordinate `x_{n+1}`, and restricts the chain to its
  first `s` functions.  Under it the symbolic derivative `∂_j` (`ESys.d`) of the *short* system
  becomes the symbolic derivative `∂_j` of the *lifted* system, **plus one correction term**:
  the derivative with respect to the new coordinate, weighted by the coefficient
  `(liftChain).a (last) j` that the lift discards (it is `S.a (last s) j` in `S`).

  This is the algebraic heart of the Khovanskii–Rolle elimination: it says that the Jacobian
  matrix `[∂_j F_i]` of the system is carried by `liftP` into the Jacobian matrix of the lifted
  system, up to an explicit rank-one type correction.  Since `liftP` is `rename (liftVar n s)`
  it is a ring homomorphism, so the identity is a term-by-term computation on the defining sum
  of `ESys.d`; the only non-formal input is that `liftVar n s` is injective, which is what makes
  `rename` commute with `pderiv`.
-/
import Mathlib
import Submission.Work.WilE2.Lift

namespace Work.WilE2

/-! ## §1. The index map `liftVar` -/

/-- `liftVar n s` is injective: the two copies of the old coordinates (`Sum.inl`) land on the
`n` first coordinates of the target, while `Sum.inr` is sent to the new chain indices except
for the very last one, which is sent to the new coordinate `x_{n+1}`. -/
private theorem liftVar_injective (n s : ℕ) : Function.Injective (liftVar n s) := by
  rintro (i | j) (i' | j') h
  · simp only [liftVar, Sum.inl.injEq] at h
    exact congrArg Sum.inl (Fin.castSucc_inj.mp h)
  · by_cases hj : (j' : ℕ) < s
    · have hh : liftVar n s (Sum.inr j') = (Sum.inr (⟨j', hj⟩ : Fin s)) := by
        simp only [liftVar]; rw [Fin.lastCases_of_lt hj]
      rw [hh] at h
      exact absurd h Sum.inl_ne_inr
    · have hh : liftVar n s (Sum.inr j') = Sum.inl (Fin.last n) := by
        simp only [liftVar]; rw [Fin.lastCases_of_not_lt hj]
      rw [hh] at h
      have h2 : (Fin.castSucc i : Fin (n + 1)) = Fin.last n := Sum.inl.inj h
      have : (i : ℕ) = n := by simpa using congrArg Fin.val h2
      omega
  · by_cases hj : (j : ℕ) < s
    · have hh : liftVar n s (Sum.inr j) = (Sum.inr (⟨j, hj⟩ : Fin s)) := by
        simp only [liftVar]; rw [Fin.lastCases_of_lt hj]
      rw [hh] at h
      exact absurd h Sum.inr_ne_inl
    · have hh : liftVar n s (Sum.inr j) = Sum.inl (Fin.last n) := by
        simp only [liftVar]; rw [Fin.lastCases_of_not_lt hj]
      rw [hh] at h
      have h2 : (Fin.castSucc i' : Fin (n + 1)) = Fin.last n := Sum.inl.inj h.symm
      have : (i' : ℕ) = n := by simpa using congrArg Fin.val h2
      omega
  · by_cases hj : (j : ℕ) < s <;> by_cases hj' : (j' : ℕ) < s
    · have hh : liftVar n s (Sum.inr j) = (Sum.inr (⟨j, hj⟩ : Fin s)) := by
        simp only [liftVar]; rw [Fin.lastCases_of_lt hj]
      have hh' : liftVar n s (Sum.inr j') = (Sum.inr (⟨j', hj'⟩ : Fin s)) := by
        simp only [liftVar]; rw [Fin.lastCases_of_lt hj']
      rw [hh, hh'] at h
      have h2 : (⟨j, hj⟩ : Fin s) = ⟨j', hj'⟩ := Sum.inr.inj h
      have h3 : (j : ℕ) = (j' : ℕ) := by simpa using congrArg Fin.val h2
      exact congrArg Sum.inr (Fin.ext h3)
    · have hh : liftVar n s (Sum.inr j) = (Sum.inr (⟨j, hj⟩ : Fin s)) := by
        simp only [liftVar]; rw [Fin.lastCases_of_lt hj]
      have hh' : liftVar n s (Sum.inr j') = Sum.inl (Fin.last n) := by
        simp only [liftVar]; rw [Fin.lastCases_of_not_lt hj']
      rw [hh, hh'] at h
      exact absurd h Sum.inr_ne_inl
    · have hh : liftVar n s (Sum.inr j) = Sum.inl (Fin.last n) := by
        simp only [liftVar]; rw [Fin.lastCases_of_not_lt hj]
      have hh' : liftVar n s (Sum.inr j') = (Sum.inr (⟨j', hj'⟩ : Fin s)) := by
        simp only [liftVar]; rw [Fin.lastCases_of_lt hj']
      rw [hh, hh'] at h
      exact absurd h.symm Sum.inr_ne_inl
    · have hh : liftVar n s (Sum.inr j) = Sum.inl (Fin.last n) := by
        simp only [liftVar]; rw [Fin.lastCases_of_not_lt hj]
      have hh' : liftVar n s (Sum.inr j') = Sum.inl (Fin.last n) := by
        simp only [liftVar]; rw [Fin.lastCases_of_not_lt hj']
      rw [hh, hh'] at h
      have hjv : (j : ℕ) = s := by have := j.isLt; omega
      have hj'v : (j' : ℕ) = s := by have := j'.isLt; omega
      rw [show j = j' from Fin.ext (by omega)]

/-- `liftVar` on the old ambient coordinate `Sum.inl`. -/
private theorem liftVar_inl {n s : ℕ} (i : Fin n) :
    liftVar n s (Sum.inl i) = Sum.inl (Fin.castSucc i) := rfl

/-- `liftVar` on a (non-last) chain index: chain variables below the last are kept. -/
private theorem liftVar_inr_castSucc {n s : ℕ} (k : Fin s) :
    liftVar n s (Sum.inr (Fin.castSucc k)) = (Sum.inr k : Fin (n + 1) ⊕ Fin s) := by
  simp only [liftVar]; rw [Fin.lastCases_castSucc]

/-- `liftVar` on the last chain index: the last chain variable becomes the new coordinate. -/
private theorem liftVar_inr_last {n s : ℕ} :
    liftVar n s (Sum.inr (Fin.last s)) = (Sum.inl (Fin.last n) : Fin (n + 1) ⊕ Fin s) := by
  simp only [liftVar]; rw [Fin.lastCases_last]

/-! ## §2. `liftP` as a ring homomorphism -/

private theorem liftP_add {n s : ℕ} (P R : EPoly n (s + 1)) :
    liftP (P + R) = liftP P + liftP R := by
  simp only [liftP, map_add]

private theorem liftP_mul {n s : ℕ} (P R : EPoly n (s + 1)) :
    liftP (P * R) = liftP P * liftP R := by
  simp only [liftP, map_mul]

private theorem liftP_C {n s : ℕ} (r : ℝ) :
    liftP (MvPolynomial.C r : EPoly n (s + 1)) = MvPolynomial.C r := by
  simp only [liftP, MvPolynomial.rename_C]

private theorem liftP_X {n s : ℕ} (i : Fin n ⊕ Fin (s + 1)) :
    liftP (MvPolynomial.X i : EPoly n (s + 1)) = MvPolynomial.X (liftVar n s i) := by
  simp only [liftP, MvPolynomial.rename_X]

private theorem liftP_sum {n s : ℕ} {ι : Type*} [Fintype ι] (g : ι → EPoly n (s + 1)) :
    liftP (∑ i, g i) = ∑ i, liftP (g i) := by
  simp only [liftP, map_sum]

/-- `liftP` commutes with the symbolic derivative, the variables being moved by `liftVar`. -/
private theorem liftP_pderiv {n s : ℕ} (i : Fin n ⊕ Fin (s + 1)) (Q : EPoly n (s + 1)) :
    liftP (MvPolynomial.pderiv i Q) = MvPolynomial.pderiv (liftVar n s i) (liftP Q) := by
  rw [liftP]
  exact (MvPolynomial.pderiv_rename (liftVar_injective n s) i Q).symm

/-! ## §3. The main computation -/

theorem liftP_d {n s : ℕ} (S : ESys n (s + 1)) (j : Fin n) (Q : EPoly n (s + 1)) :
    liftP (S.d j Q) =
      (S.liftChain).d (Fin.castSucc j) (liftP Q) +
        MvPolynomial.C (S.a (Fin.last s) j) * MvPolynomial.X (Sum.inl (Fin.last n)) *
          MvPolynomial.pderiv (Sum.inl (Fin.last n)) (liftP Q) := by
  -- `liftP` is `rename (liftVar n s)`, hence additive and multiplicative; applying it to the
  -- defining sum of `ESys.d` and splitting off the last chain index leaves exactly the
  -- defining sum of the derivative of the lifted chain plus the announced correction term.
  simp only [ESys.d, liftP_add, liftP_sum, liftP_mul, liftP_C, liftP_X, liftP_pderiv,
    liftVar_inl, liftVar_inr_castSucc, liftVar_inr_last, ESys.liftChain_a_lt,
    Fin.sum_univ_castSucc]
  rw [add_assoc]

end Work.WilE2
