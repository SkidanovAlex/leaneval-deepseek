import Mathlib
import Submission.NK.LocalCFT.Units.EllRank.Defs
import Submission.NK.LocalCFT.Units.EllRank.infinite_codim_submodule
import Submission.NK.LocalCFT.Units.EllRank.finite_of_finite_quot_nsmulTop

/-!
# Infinitely many index-`p ^ e` subgroups in an infinite bounded-exponent abelian group

Let `A` be an infinite additive commutative group all of whose elements are killed by
`p ^ e`, where `p` is a prime and `e ≥ 1`.  Then `A` has infinitely many subgroups of
index `p ^ e`.

The proof goes through the elementary abelian quotient `ellQuot p A = A ⧸ pA`.  Because
`A` is infinite (and of bounded exponent), `A ⧸ pA` is infinite-dimensional over `𝔽_p`
(`finite_of_finite_quot_nsmulTop`), so it has infinitely many subspaces of codimension `e`
(`infinite_codim_submodule`).  Pulling such a subspace back along the quotient map
`A → A ⧸ pA` produces a subgroup of `A` of index `p ^ e`, and distinct subspaces give
distinct subgroups.
-/

set_option linter.style.haveILetI false

open scoped Classical

namespace NK.LocalCFT.Units.EllRank

noncomputable section

/-- **The elementary abelian quotient of an infinite bounded-exponent group is
infinite-dimensional.**  If `A` is infinite and killed by `p ^ e`, then `A ⧸ pA` cannot be
finite-dimensional over `𝔽_p`: a finite-dimensional `𝔽_p`-vector space is finite, and
`A ⧸ pA` finite forces `A` finite (`finite_of_finite_quot_nsmulTop`). -/
theorem ellQuot_not_finiteDimensional {A : Type*} [AddCommGroup A] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hexp : ∀ x : A, (p ^ e) • x = 0) (hinf : Infinite A) :
    ¬ FiniteDimensional (ZMod p) (ellQuot p A) := by
  intro hfd
  haveI : Module.Finite (ZMod p) (ellQuot p A) := hfd
  have hfinA : Finite A :=
    finite_of_finite_quot_nsmulTop Fact.out he hexp (Module.finite_of_finite (ZMod p))
  exact (not_finite_iff_infinite.mpr hinf) hfinA

/-- **Pulling back a codimension-`e` subspace of `A ⧸ pA`.**  If `W ≤ A ⧸ pA` is a subspace
whose quotient has cardinality `p ^ e`, then its preimage in `A` along the quotient map is a
subgroup of index `p ^ e`. -/
theorem index_comap_mk_ellQuot {A : Type*} [AddCommGroup A] {p e : ℕ}
    (W : Submodule (ZMod p) (ellQuot p A)) (hW : Nat.card (ellQuot p A ⧸ W) = p ^ e) :
    (W.toAddSubgroup.comap (QuotientAddGroup.mk' (nsmulTop p A))).index = p ^ e := by
  rw [AddSubgroup.index_comap,
    AddMonoidHom.range_eq_top.mpr (QuotientAddGroup.mk'_surjective (nsmulTop p A)),
    AddSubgroup.relIndex_top_right]
  exact hW

theorem infinite_index_prime_pow_add {A : Type*} [AddCommGroup A] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hexp : ∀ x : A, (p ^ e) • x = 0) (hinf : Infinite A) :
    Infinite {K : AddSubgroup A // K.index = p ^ e} := by
  letI : Fact p.Prime := ⟨hp⟩
  have hV : ¬ FiniteDimensional (ZMod p) (ellQuot p A) :=
    ellQuot_not_finiteDimensional he hexp hinf
  haveI hInf :
      Infinite {W : Submodule (ZMod p) (ellQuot p A) // Nat.card (ellQuot p A ⧸ W) = p ^ e} :=
    infinite_codim_submodule he hV
  let φ : {W : Submodule (ZMod p) (ellQuot p A) // Nat.card (ellQuot p A ⧸ W) = p ^ e} →
      {K : AddSubgroup A // K.index = p ^ e} :=
    fun W => ⟨W.1.toAddSubgroup.comap (QuotientAddGroup.mk' (nsmulTop p A)),
      index_comap_mk_ellQuot W.1 W.2⟩
  have hφ : Function.Injective φ := by
    intro W₁ W₂ h
    have hc : W₁.1.toAddSubgroup.comap (QuotientAddGroup.mk' (nsmulTop p A))
        = W₂.1.toAddSubgroup.comap (QuotientAddGroup.mk' (nsmulTop p A)) := congrArg Subtype.val h
    have hsub : W₁.1.toAddSubgroup = W₂.1.toAddSubgroup :=
      AddSubgroup.comap_injective (QuotientAddGroup.mk'_surjective (nsmulTop p A)) hc
    exact Subtype.ext (Submodule.toAddSubgroup_injective hsub)
  exact Infinite.of_injective φ hφ

end

end NK.LocalCFT.Units.EllRank
