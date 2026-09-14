import Mathlib
import Submission.Subspace.ElimIter

/-!
# Block homogeneity of the elimination iteration

The elimination iteration (`Submission.Subspace.elimF`) divides out the lowest power of each
variable of a list.  If the initial polynomial is homogeneous of degree `e h` in the block
`h : Fin m` of the variables `Fin m × Fin N`, then so is the result, with degrees `e' h ≤ e h`.
-/

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

variable {K : Type*} [Field K] {m N : ℕ}

/-- `IsBlockHom e F` means that every monomial of `F` has total degree `e h` in the block
`h : Fin m` of the variables `Fin m × Fin N`. -/
def IsBlockHom (e : Fin m → ℕ) (F : MvPolynomial (Fin m × Fin N) K) : Prop :=
  ∀ u ∈ F.support, ∀ h : Fin m, ∑ j : Fin N, u (h, j) = e h

lemma isBlockHom_lowestCoeff {y : Fin m × Fin N} {e : Fin m → ℕ}
    {F : MvPolynomial (Fin m × Fin N) K} (h : IsBlockHom e F) :
    IsBlockHom (Function.update e y.1 (e y.1 - lowestDeg y F)) (lowestCoeff y F) := by
  intro u hu h'
  obtain ⟨w, hw, hwy, hw'⟩ := mem_support_lowestCoeff hu
  rcases eq_or_ne h' y.1 with hh | hh
  · subst hh
    rw [Function.update_self]
    have hzero : u y = 0 := by rw [hw']; simp [hwy]
    have hL : ∑ j : Fin N, u (y.1, j) =
        ∑ j ∈ Finset.univ.erase y.2, w (y.1, j) := by
      rw [← Finset.sum_erase_add (Finset.univ) (fun j : Fin N => u (y.1, j))
        (Finset.mem_univ y.2)]
      rw [show u (y.1, y.2) = 0 from hzero, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_erase] at hj
      rw [hw']
      have hne : (y.1, j) ≠ y := fun hcon => hj.1 (congrArg Prod.snd hcon)
      simp [Finsupp.single_eq_of_ne hne]
    have hW : (∑ j ∈ Finset.univ.erase y.2, w (y.1, j)) + w y = e y.1 := by
      rw [Finset.sum_erase_add (Finset.univ) (fun j : Fin N => w (y.1, j))
        (Finset.mem_univ y.2)]
      exact h w hw y.1
    rw [hL]
    omega
  · rw [Function.update_of_ne hh]
    have : ∑ j : Fin N, u (h', j) = ∑ j : Fin N, w (h', j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw']
      have hne : (h', j) ≠ y := fun hcon => hh (congrArg Prod.fst hcon)
      simp [Finsupp.single_eq_of_ne hne]
    rw [this]
    exact h w hw h'

/-- The elimination iteration preserves block homogeneity, with possibly smaller block degrees. -/
theorem exists_isBlockHom_elimF :
    ∀ (ys : List (Fin m × Fin N)) (F : MvPolynomial (Fin m × Fin N) K) (e : Fin m → ℕ),
      IsBlockHom e F → ∃ e' : Fin m → ℕ, IsBlockHom e' (elimF ys F) ∧ ∀ h, e' h ≤ e h := by
  intro ys
  induction ys with
  | nil => intro F e h; exact ⟨e, by simpa only [elimF] using h, fun _ => le_rfl⟩
  | cons y ys ih =>
      intro F e h
      have h1 := isBlockHom_lowestCoeff (y := y) h
      have h2 : ∀ h', Function.update e y.1 (e y.1 - lowestDeg y F) h' ≤ e h' := by
        intro h'
        by_cases hh : h' = y.1
        · subst hh; rw [Function.update_self]; exact Nat.sub_le _ _
        · rw [Function.update_of_ne hh]
      obtain ⟨e', he', hle⟩ := ih (lowestCoeff y F)
        (Function.update e y.1 (e y.1 - lowestDeg y F)) h1
      exact ⟨e', by simpa only [elimF] using he', fun h' => le_trans (hle h') (h2 h')⟩

end Submission.Subspace
