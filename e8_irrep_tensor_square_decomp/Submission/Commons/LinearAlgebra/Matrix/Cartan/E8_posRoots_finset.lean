import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_height_bound
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_posRoots_fixes_rho
import Submission.Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_count

namespace Commons.LinearAlgebra.Matrix.Cartan

/-!
# The `120` positive roots of `E₈` form a finset

The `E₈` Cartan matrix `A = CartanMatrix.E₈` is inverted by `E8inv`; a weight `v : Fin 8 → ℤ`
is written in the fundamental-weight basis, so its coordinates in the simple-root basis are
`coords v = A⁻¹ v` and its squared length is `E8NormTwo.qZ v = v ⬝ A⁻¹ v`.

The positive roots of `E₈` are the nonzero lattice vectors of squared length `2` all of whose
simple-root coordinates are nonnegative; there are `120` of them.  The proof exhibits them as the
finset `E8posRoots.P` (`Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_posRoots_fixes_rho`) and counts
them:

* by `Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_count` the `E₈` lattice has exactly `240`
  vectors of squared length `2`;
* by `E8_coords_same_sign` every such vector is either a positive root or the negative of one;
* negation is a bijection between the positive roots and their negatives, and the two classes are
  disjoint (a nonzero vector cannot have `coords` both `≥ 0` and `≤ 0`, since `A` is invertible).

Hence the `240` roots split into two classes of `120`.
-/

/-- The squared length `qZ` is invariant under negation. -/
lemma E8_qZ_neg (v : Fin 8 → ℤ) : E8NormTwo.qZ (-v) = E8NormTwo.qZ v := by
  rw [E8posRoots.qz_eq_sum, E8posRoots.qz_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [Pi.neg_apply]
  ring

/-- The zero vector has squared length `0`. -/
lemma E8_qZ_zero : E8NormTwo.qZ (0 : Fin 8 → ℤ) = 0 := by
  simp [E8posRoots.qz_eq_sum]

theorem E8_posRoots_finset : ∃ s : Finset (Fin 8 → ℤ), (∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords v i) ∧ s.card = 120 := by
  obtain ⟨L, hnodup, hmem, h0, h2, h4, h6, h8, h10⟩ := e8_lattice_count
  refine ⟨E8posRoots.P, ?_, ?_⟩
  · intro v
    rw [E8posRoots.memP]
    simp only [E8posRoots.IsPosRoot]
    tauto
  · set R : Finset (Fin 8 → ℤ) := (L.filter (fun v => E8NormTwo.qZ v = 2)).toFinset with hRdef
    set Q : Finset (Fin 8 → ℤ) := E8posRoots.P.image (fun v => -v) with hQdef
    have hRcard : R.card = 240 := by
      rw [hRdef, List.toFinset_card_of_nodup (hnodup.filter _), h2]
    have hPsub : E8posRoots.P ⊆ R := by
      intro v hv
      obtain ⟨hq, -, -⟩ := (E8posRoots.memP v).mp hv
      rw [hRdef]
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨hmem v (by omega), hq⟩
    have hQsub : Q ⊆ R := by
      intro v hv
      rw [hQdef, Finset.mem_image] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      obtain ⟨hq, -, -⟩ := (E8posRoots.memP w).mp hw
      rw [← hwv, hRdef]
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨hmem (-w) (by rw [E8_qZ_neg]; omega), by rw [E8_qZ_neg]; exact hq⟩
    have hRsub : R ⊆ E8posRoots.P ∪ Q := by
      intro v hv
      rw [hRdef] at hv
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hv
      obtain ⟨hvL, hq⟩ := hv
      have hne : v ≠ 0 := by
        intro h; rw [h] at hq; rw [E8_qZ_zero] at hq; exact absurd hq (by norm_num)
      have hsign := E8_coords_same_sign v hne hq
      rw [Finset.mem_union]
      rcases hsign with hpos | hneg
      · left
        rw [E8posRoots.memP]
        refine ⟨hq, hne, fun i => ?_⟩
        rw [E8posRoots.coords_apply]
        exact hpos i
      · right
        rw [hQdef, Finset.mem_image]
        refine ⟨-v, ?_, by simp⟩
        rw [E8posRoots.memP]
        refine ⟨?_, ?_, fun i => ?_⟩
        · rw [E8_qZ_neg]; exact hq
        · exact fun h => hne (neg_eq_zero.mp h)
        · have hh := hneg i
          have h2 : E8posRoots.coords (-v) i = - ∑ j, E8NormTwo.E8inv i j * v j := by
            rw [E8posRoots.coords_neg]
            simp only [Pi.neg_apply, E8posRoots.coords_apply]
          rw [h2]
          omega
    have hdisj : Disjoint E8posRoots.P Q := by
      rw [Finset.disjoint_left]
      intro v hv hvQ
      rw [hQdef, Finset.mem_image] at hvQ
      obtain ⟨w, hw, hwv⟩ := hvQ
      obtain ⟨-, hwne, hwc⟩ := (E8posRoots.memP w).mp hw
      obtain ⟨-, -, hvc⟩ := (E8posRoots.memP v).mp hv
      have hall : ∀ i, E8posRoots.coords w i = 0 := by
        intro i
        have h1 : 0 ≤ E8posRoots.coords v i := hvc i
        have h2 : E8posRoots.coords v i = - E8posRoots.coords w i := by
          rw [← hwv, E8posRoots.coords_neg]
          rfl
        have h3 : 0 ≤ E8posRoots.coords w i := hwc i
        omega
      have hwq : E8NormTwo.qZ w = 0 := by
        rw [E8posRoots.qz_eq_dot]
        exact Finset.sum_eq_zero (fun i _ => by rw [hall i, zero_mul])
      exact hwne (E8posRoots.qz_eq_zero w hwq)
    have heq : R = E8posRoots.P ∪ Q :=
      Finset.Subset.antisymm hRsub (Finset.union_subset hPsub hQsub)
    have hQcard : Q.card = E8posRoots.P.card := by
      rw [hQdef]
      exact Finset.card_image_of_injective E8posRoots.P (fun a b h => neg_inj.mp h)
    have hsum : R.card = E8posRoots.P.card + Q.card := by
      rw [heq, Finset.card_union_of_disjoint hdisj]
    omega

end Commons.LinearAlgebra.Matrix.Cartan
