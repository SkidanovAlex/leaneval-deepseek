import Mathlib
import Submission.Commons.Combinatorics.Transference.poly_lemma_abstract

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- If two reals have equal floors after division by the same `ε > 0`, they differ by less
than `ε`. -/
lemma abs_sub_lt_of_floor_div_eq {a b ε : ℝ} (hε : 0 < ε)
    (h : ⌊a / ε⌋ = ⌊b / ε⌋) : |a - b| < ε := by
  have hle_a : ((⌊a / ε⌋ : ℤ) : ℝ) ≤ a / ε := Int.floor_le _
  have hlt_a : a / ε < ((⌊a / ε⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hle_b : ((⌊b / ε⌋ : ℤ) : ℝ) ≤ b / ε := Int.floor_le _
  have hlt_b : b / ε < ((⌊b / ε⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hab : ((⌊a / ε⌋ : ℤ) : ℝ) = ((⌊b / ε⌋ : ℤ) : ℝ) := by rw [h]
  have hba : ((⌊b / ε⌋ : ℤ) : ℝ) = ((⌊a / ε⌋ : ℤ) : ℝ) := by rw [← h]
  have habs : |a / ε - b / ε| < 1 := by
    rw [abs_sub_lt_iff]
    exact ⟨by linarith, by linarith⟩
  have hmul : ε * (a / ε - b / ε) = a - b := by
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hε), mul_div_cancel₀ _ (ne_of_gt hε)]
  rw [← hmul, abs_mul, abs_of_pos hε]
  simpa using mul_lt_mul_of_pos_left habs hε

/-- **The join of level sets is a partition, on whose atoms every generator is nearly constant.**

Let `F : Fin K → ZMod p → ℝ` and let `A(x)` be the atom containing `x` of the join of the
level-set σ-algebras of the functions `davg d (F j)` at resolution `ε > 0` with shifts `α j`
(`davg` is the Green–Tao dual function, `Combinatorics/Transference/poly_lemma_abstract`).
Then (i) `x ∈ A(x)`, (ii) `A(y) = A(x)` for `y ∈ A(x)`, and (iii) for `y ∈ A(x)` and every `j`,
`|davg d (F j) y - davg d (F j) x| < ε`.

This is the "each function lies in its own σ-algebra" estimate (Green–Tao Proposition 6.4)
used in the proof of the Koopman–von Neumann decomposition (Green–Tao §7). -/
theorem levelJoin_atom_close {p : ℕ} [Fact p.Prime] (d : ℕ) {K : ℕ} (F : Fin K → ZMod p → ℝ)
    {ε : ℝ} (hε : 0 < ε) (α : Fin K → ℝ) :
    (∀ x : ZMod p, x ∈ Finset.univ.filter (fun y => ∀ j : Fin K,
        ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)) ∧
    (∀ x y : ZMod p, y ∈ Finset.univ.filter (fun y => ∀ j : Fin K,
        ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋) →
      Finset.univ.filter (fun z => ∀ j : Fin K,
          ⌊(davg d (F j) z - α j) / ε⌋ = ⌊(davg d (F j) y - α j) / ε⌋)
        = Finset.univ.filter (fun z => ∀ j : Fin K,
          ⌊(davg d (F j) z - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)) ∧
    (∀ x y : ZMod p, y ∈ Finset.univ.filter (fun y => ∀ j : Fin K,
        ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋) →
      ∀ j : Fin K, |davg d (F j) y - davg d (F j) x| < ε) := by
  set lv : Fin K → ZMod p → ℤ := fun j z => ⌊(davg d (F j) z - α j) / ε⌋ with hlv
  have hA : ∀ x : ZMod p,
      Finset.univ.filter (fun y => ∀ j : Fin K,
        ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)
      = Finset.univ.filter (fun y => ∀ j : Fin K, lv j y = lv j x) := by
    intro x
    apply Finset.filter_congr
    intro y _
    simp only [hlv]
  have hmem : ∀ x y : ZMod p,
      (y ∈ Finset.univ.filter (fun y => ∀ j : Fin K,
        ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋))
      ↔ (∀ j : Fin K, lv j y = lv j x) := by
    intro x y
    rw [hA x]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [hmem x x]
    intro j
    rfl
  · intro x y hy
    rw [hmem x y] at hy
    rw [hA y, hA x]
    apply Finset.filter_congr
    intro z _
    constructor
    · intro hz j
      rw [hz j]
      exact hy j
    · intro hz j
      rw [hz j]
      exact (hy j).symm
  · intro x y hy j
    rw [hmem x y] at hy
    have h := abs_sub_lt_of_floor_div_eq hε (hy j)
    rwa [show (davg d (F j) y - α j) - (davg d (F j) x - α j)
        = davg d (F j) y - davg d (F j) x by ring] at h

end Commons.Combinatorics.Transference
