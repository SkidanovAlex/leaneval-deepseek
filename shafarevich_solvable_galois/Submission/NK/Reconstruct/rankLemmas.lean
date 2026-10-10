import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Elementary rank lemmas for the rank computation of Shimizu's §4

These are the two purely algebraic facts on which the rank computation of Shimizu's Proposition 4f.5
(and of Lemma 4f.1) rests.  Both are statements about `Module.rank` over a ring of characteristic
zero, i.e. in the application over `ℤ_ℓ`.

* `NK.Reconstruct.rankEqRankRangeOfFiniteCoker`: if `f : M →ₗ[R] N` has **finite cokernel**
  (over a ring of characteristic zero, so that a finite module is torsion, hence of rank `0`), then
  `rank N = rank (range f)`.  This is what lets one read off the rank of `Γ_K` from the image of the
  base change `π_{L/K}`, whose cokernel is finite
  (`NK.Reconstruct.finite_coker_gammaBaseChangeHom`).

* `NK.Reconstruct.rankQuotientLeQuotientOfLe`: for `N' ≤ N`, `M ⧸ N` is a quotient of `M ⧸ N'`,
  hence has no larger rank.  This is the rank monotonicity used for the "base field" monotonicity
  step of Proposition 4f.5.

Note that *finiteness* of the cokernel alone does not force its rank to vanish over an arbitrary
ring (over a finite field `M = R`, `f = 0` is a counterexample); the hypothesis
`NK.Reconstruct.isTorsionOfFinite` supplies the missing torsion property over a ring of
characteristic zero.
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct

universe u v

/-- **A finite module over a ring of characteristic zero is torsion**: `n • x = 0` for
`n = Nat.card M ≠ 0` (`card_nsmul_eq_zero`), and `(n : R) ≠ 0` because `R` has characteristic zero.
-/
theorem isTorsionOfFinite {R : Type v} [Ring R] [NoZeroDivisors R] [CharZero R] {M : Type u}
    [AddCommGroup M] [Module R M] [Finite M] : Module.IsTorsion R M := by
  intro x
  refine ⟨⟨(Nat.card M : R), ?_⟩, ?_⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero, Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨x⟩, inferInstance⟩
  · change (Nat.card M : R) • x = 0
    haveI : Fintype M := Fintype.ofFinite M
    rw [Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card]
    exact card_nsmul_eq_zero

/-- **The rank of a module with finite cokernel**: if `f : M →ₗ[R] N` has finite cokernel over a
ring of characteristic zero, then `N` and `f.range` have the same rank. -/
theorem rankEqRankRangeOfFiniteCoker {R : Type v} [Ring R] [Nontrivial R] [NoZeroDivisors R]
    [CharZero R] {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [HasRankNullity.{u, v} R]
    (f : M →ₗ[R] N) (h : Finite (N ⧸ LinearMap.range f)) :
    Module.rank R N = Module.rank R ↥(LinearMap.range f) := by
  have htor : Module.IsTorsion R (N ⧸ LinearMap.range f) := isTorsionOfFinite
  have h0 : Module.rank R (N ⧸ LinearMap.range f) = 0 := Module.IsTorsion.rank_eq_zero htor
  have hadd := Submodule.rank_quotient_add_rank (R := R) (LinearMap.range f)
  rw [h0, zero_add] at hadd
  exact hadd.symm

/-- **Rank monotonicity in the submodule of a quotient**: if `N' ≤ N` then `M ⧸ N` is a quotient of
`M ⧸ N'`, hence of no larger rank. -/
theorem rankQuotientLeQuotientOfLe {R : Type v} [Ring R] {M : Type u}
    [AddCommGroup M] [Module R M] {N N' : Submodule R M} (h : N' ≤ N) :
    Module.rank R (M ⧸ N) ≤ Module.rank R (M ⧸ N') := by
  have hker : N' ≤ (Submodule.mkQ N).ker := by
    rw [Submodule.ker_mkQ]; exact h
  let φ : M ⧸ N' →ₗ[R] M ⧸ N := Submodule.liftQ N' (Submodule.mkQ N) hker
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N y
    exact ⟨Submodule.Quotient.mk x, by rw [Submodule.liftQ_apply, Submodule.mkQ_apply]⟩
  exact LinearMap.rank_le_of_surjective φ hsurj

end NK.Reconstruct
