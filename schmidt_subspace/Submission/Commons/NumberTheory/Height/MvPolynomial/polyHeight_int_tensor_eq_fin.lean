import Mathlib
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_int_tensor_eq
import Submission.Commons.NumberTheory.Height.MvPolynomial.logHeight_gP_rename

namespace Commons.NumberTheory.Height.MvPolynomial

/-- The canonical identification `Fin 1 ⊕ Fin n ≃ Fin (n+1)` sending `Sum.inl _ ↦ 0` and
`Sum.inr j ↦ j.succ`. -/
noncomputable def finSumFinEquivSucc (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  (finSumFinEquiv : Fin 1 ⊕ Fin n ≃ Fin (1 + n)).trans (finCongr (Nat.add_comm 1 n))

lemma finSumFinEquivSucc_inl (n : ℕ) (i : Fin 1) :
    finSumFinEquivSucc n (Sum.inl i) = 0 := by
  apply Fin.ext
  simp only [finSumFinEquivSucc, Equiv.trans_apply, finSumFinEquiv_apply_left,
    finCongr_apply_coe, Fin.val_zero]
  exact Nat.lt_one_iff.mp i.isLt

lemma finSumFinEquivSucc_inr (n : ℕ) (j : Fin n) :
    finSumFinEquivSucc n (Sum.inr j) = Fin.succ j := by
  apply Fin.ext
  simp only [finSumFinEquivSucc, Equiv.trans_apply, finSumFinEquiv_apply_right,
    finCongr_apply_coe]
  simp [Fin.succ, Nat.add_comm]

theorem polyHeight_int_tensor_eq_fin {n : ℕ}
    (W₁ : MvPolynomial (Fin 1) ℤ) (W₂ : MvPolynomial (Fin n) ℤ) (h₁ : W₁ ≠ 0) (h₂ : W₂ ≠ 0) :
    Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP
        ((MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) W₁ *
          MvPolynomial.rename Fin.succ W₂).map (Int.castRingHom ℚ))) =
      Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP
        (W₁.map (Int.castRingHom ℚ))) +
      Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP
        (W₂.map (Int.castRingHom ℚ))) := by
  have he1 : (finSumFinEquivSucc n ∘ Sum.inl) = (fun _ : Fin 1 => (0 : Fin (n + 1))) :=
    funext fun i => finSumFinEquivSucc_inl n i
  have he2 : (finSumFinEquivSucc n ∘ Sum.inr) = (Fin.succ : Fin n → Fin (n + 1)) :=
    funext fun j => finSumFinEquivSucc_inr n j
  have hT : MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) W₁ *
        MvPolynomial.rename Fin.succ W₂
      = MvPolynomial.rename (⇑(finSumFinEquivSucc n))
          (MvPolynomial.rename Sum.inl W₁ * MvPolynomial.rename Sum.inr W₂) := by
    rw [map_mul, MvPolynomial.rename_rename, MvPolynomial.rename_rename, he1, he2]
  have hA : (MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) W₁ *
        MvPolynomial.rename Fin.succ W₂).map (Int.castRingHom ℚ)
      = MvPolynomial.rename (⇑(finSumFinEquivSucc n))
          ((MvPolynomial.rename Sum.inl W₁ * MvPolynomial.rename Sum.inr W₂).map
            (Int.castRingHom ℚ)) := by
    rw [hT, MvPolynomial.map_rename]
  rw [hA]
  rw [logHeight_gP_rename (finSumFinEquivSucc n)]
  exact polyHeight_int_tensor_eq W₁ W₂ h₁ h₂

end Commons.NumberTheory.Height.MvPolynomial
