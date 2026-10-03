import Mathlib
import Submission.Work.Peluse.UControl.levStepRef

/-!
# The atom sums of a level state are injective

`levStepRef` (the class-reduction step of a level round) needs the hypothesis that the atom sums
`Aatom atom h = Σ_{s : h s} atom s` separate the Boolean histories.  In the first round of the level
chain the atoms are `atom s = d·lc·a_s` — i.e. `c · X s` — and here we prove that hypothesis:
`h ↦ c · shift h` is injective for `c ≠ 0` and `h ↦ shift h` is injective.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

/-- The coefficient of `X i` in `shift h` is the `i`-th bit of `h`. -/
lemma histShift_coeff_single {n : ℕ} (h : Fin n → Bool) (i : Fin n) :
    (HistData.shift h).coeff (Finsupp.single i 1) = if h i then 1 else 0 := by
  classical
  rw [HistData.shift, MvPolynomial.coeff_sum, Finset.sum_eq_single i]
  · by_cases hi : h i <;> simp [hi, MvPolynomial.coeff_X]
  · intro j _ hji
    by_cases hj : h j
    · rw [if_pos hj, MvPolynomial.coeff_X]
      have hne : (Finsupp.single j 1 : Fin n →₀ ℕ) ≠ Finsupp.single i 1 := by
        intro hcon
        have h3 : ((Finsupp.single j 1 : Fin n →₀ ℕ) : Fin n → ℕ) j
            = ((Finsupp.single i 1 : Fin n →₀ ℕ) : Fin n → ℕ) j :=
          congrFun (congrArg (fun f : Fin n →₀ ℕ => (f : Fin n → ℕ)) hcon) j
        rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hji] at h3
        exact absurd h3 one_ne_zero
      rw [if_neg hne]
    · rw [if_neg hj]; simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The history shift `h ↦ Σ_{s : h s} X s` is injective. -/
lemma histShift_injective {n : ℕ} : Function.Injective (HistData.shift (n := n)) := by
  intro h g hhg
  funext i
  have h1 := histShift_coeff_single h i
  have h2 := histShift_coeff_single g i
  have h3 : (if h i then (1 : ℤ) else 0) = (if g i then (1 : ℤ) else 0) := by
    rw [← h1, hhg, h2]
  by_cases hhi : h i <;> by_cases hgi : g i <;> simp_all

/-- **The atom sums are injective** when the atom of `s` is `c · X s` with `c ≠ 0` (the shape of
the first level round of the PET chain, where `c = d·lc`). -/
theorem Aatom_mul_X_injective {n : ℕ} (c : MvPolynomial (Fin n) ℤ) (hc : c ≠ 0) :
    ∀ h g : Fin n → Bool,
      Aatom (fun s : Fin n => c * MvPolynomial.X s) h
        = Aatom (fun s : Fin n => c * MvPolynomial.X s) g → h = g := by
  have hshift : ∀ k : Fin n → Bool,
      Aatom (fun s : Fin n => c * MvPolynomial.X s) k = c * HistData.shift k := by
    intro k
    rw [Aatom, Finset.sum_filter, HistData.shift, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hk : k s <;> simp [hk, mul_comm]
  intro h g hhg
  rw [hshift h, hshift g] at hhg
  exact histShift_injective (mul_left_cancel₀ hc hhg)

end

end Work.Peluse.UControl
