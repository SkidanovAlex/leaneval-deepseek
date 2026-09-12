import Mathlib
import Submission.Work.Lattice.GraysonLattice
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.sublattice_ge

/-!
# P2/P3-general (b): sublattice successive-minima-ge for family-span subgroups

The last ingredient of the uniform boundedness theorem: for a subgroup `W` of a lattice
`Λ` presented as the `ℤ`-span of an `ℝ`-independent member family `u : Fin r → E d`
(the `PresentationLattice.exists_basis_family_of_le_lattice` presentation), the
successive minima of `Λ` are dominated by those of `W`:

    `successiveMinimum_ge_of_le_span` :  λᵢ(Λ) ≤ λᵢ(W)`   (`1 ≤ i ≤ r`)

This is `Commons.Lattice.SuccessiveMinima.sublattice_ge` (sublattices have larger
successive minima — delegated to the fleet, TC-free on the submodule side) instantiated
with `W ≤ Λ`, together with an explicit nonemptyness witness for the defining set of
`λᵢ(W)`: the first `i` members of `u` (`ℝ`-independent hence `ℤ`-independent, with norms
bounded by their sum).  All declarations are Mathlib + Submission (GraysonLattice) +
Commons.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 800000

namespace Submission.SublatticeGe

open Submission.GraysonData
open Commons.Lattice.SuccessiveMinima

/-- An `ℝ`-linearly independent family in `ℝᵈ` is `ℤ`-linearly independent. -/
lemma li_int_of_li_real {d n : ℕ} (f : Fin n → E d) (h : LinearIndependent ℝ f) :
    LinearIndependent ℤ f := by
  exact LinearIndependent.restrict_scalars (R := ℤ) (K := ℝ) (M := E d) (v := f)
    (by
      intro a b hab
      have hab' : (a : ℝ) = (b : ℝ) := by simpa [zsmul_eq_mul] using hab
      exact_mod_cast hab') h

/-- **Nonemptyness witness for the `i`-th defining set of a family-span lattice**: for an
`ℝ`-independent `u : Fin r → E d` and `i ≤ r`, the first `i` members witness
`Nonempty (successiveMinimumSet (span ℤ (range u)) i)` (radii bounded by the sum of the
member norms). -/
lemma smSet_span_nonempty_of_linearIndependent {d r i : ℕ} (u : Fin r → E d) (hri : i ≤ r)
    (hli : LinearIndependent ℝ u) :
    (successiveMinimumSet (E := E d) (Submodule.span ℤ (Set.range u)) i).Nonempty := by
  classical
  let f : Fin i → Submodule.span ℤ (Set.range u) := fun k =>
    ⟨u (Fin.castLE hri k), Submodule.subset_span ⟨Fin.castLE hri k, rfl⟩⟩
  let R : ℝ := ∑ k : Fin i, ‖u (Fin.castLE hri k)‖
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg (fun k hk => norm_nonneg _)
  have hlin : LinearIndependent ℤ (fun k : Fin i => ((f k : Submodule.span ℤ (Set.range u)) : E d)) := by
    have hli₀ : LinearIndependent ℝ (fun k : Fin i => u (Fin.castLE hri k)) :=
      hli.comp (fun k : Fin i => Fin.castLE hri k) (Fin.castLEEmb hri).injective
    have hz : LinearIndependent ℤ (fun k : Fin i => u (Fin.castLE hri k)) :=
      li_int_of_li_real (fun k : Fin i => u (Fin.castLE hri k)) hli₀
    simpa [f] using hz
  have hb : ∀ k : Fin i, ‖((f k : Submodule.span ℤ (Set.range u)) : E d)‖ ≤ R := by
    intro k
    dsimp [f, R]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin i => ‖u (Fin.castLE hri j)‖) (a := k)
      (by intro j hj; exact norm_nonneg _) (by simp)
  exact successiveMinimumSet_nonempty_of_exists_linearIndependent (E := E d)
    (Submodule.span ℤ (Set.range u)) i f hlin R hb hR0

/-- **Sublattice minima dominate the ambient lattice**: for `Λ ≤ ℝᵈ` and a rank-`r`
subgroup `W = span ℤ (range u)` of `Λ` (`u : Fin r → E d` `ℝ`-independent, members of
`Λ`), the successive minima of `Λ` are bounded above by those of `W`:
`λᵢ(Λ) ≤ λᵢ(W)` for `1 ≤ i ≤ r`. -/
theorem successiveMinimum_ge_of_le_span {d r i : ℕ} (Λ : Submodule ℤ (E d))
    (u : Fin r → E d) (huΛ : ∀ k : Fin r, u k ∈ (Λ : Set (E d)))
    (hli : LinearIndependent ℝ u) (_hi1 : 1 ≤ i) (hri : i ≤ r) :
    successiveMinimum (E := E d) Λ i ≤
      successiveMinimum (E := E d) (Submodule.span ℤ (Set.range u)) i := by
  classical
  have hWleΛ : Submodule.span ℤ (Set.range u) ≤ Λ := by
    rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    exact huΛ k
  have hS : (successiveMinimumSet (E := E d) (Submodule.span ℤ (Set.range u)) i).Nonempty :=
    smSet_span_nonempty_of_linearIndependent u hri hli
  exact sublattice_ge (E := E d) (Submodule.span ℤ (Set.range u)) Λ hWleΛ i hS

end Submission.SublatticeGe

end
